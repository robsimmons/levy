(** An efficient interpreter; everything is boxed *)

open Syntax

type environment = (name * runtime) list

and runtime = heapdata ref

and heapdata = 
  | Null 
  | Boxed of int
  | Tagged of name * runtime list * (int * runtime) option
  | Thunked of environment * expr
  | Closed of environment * name * expr
  | Zipped of zipper ref

and zipper = 
  | Identity
  | Zipper of runtime * runtime (* Pointer to first, last *)
  | Invalid                     (* Enforce affine usage *)

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error ("Runtime error: " ^ msg))

let vtrue = ref (Tagged ("true", [], None))
let vfalse = ref (Tagged ("false", [], None))
let mkbool = function
  | true -> vtrue
  | false -> vfalse

let match_failure = function
  | [] -> runtime_error "Match failure"
  | (pat, _) :: _ -> runtime_error ("Bad pattern: " ^ string_of_expr pat)

let rec string_of_runtime: runtime -> string = function
  | { contents = Null } -> "[]"
  | { contents = Boxed k } -> string_of_int k
  | { contents = Tagged (x, vs, _) } -> 
      if List.length vs = 0 then x 
      else "(" ^ x ^ " " ^ 
           String.concat " " (List.map string_of_runtime vs) ^ ")"
  | { contents = Thunked _ } -> "<thunk>"
  | { contents = Closed _ } -> "<fun>" 
  | { contents = Zipped { contents = Invalid } } -> "<used zipper>"
  | { contents = Zipped { contents = Identity } } -> 
    "(<zipper> [])"
  | { contents = Zipped { contents = Zipper (r, _) } } -> 
    "(<zipper> " ^ string_of_runtime r ^ ")"

let bindpat = function
  | Var x -> fun v -> (x, v)
  | _ -> runtime_error "Multiple-depth pattern matching"

(** [bindlin (last, r)] binds the end of one linked list to a regular runtime
    value *)
let bindlin = function
  | { contents = Tagged (_, vs, Some (n, _))}, v2 ->
      ignore (mapbut (fun _ -> ()) (fun v -> v := !v2) vs (Some n))
  | r1, _ -> runtime_error ("Bad link: expected tagged linear data, got " 
			    ^ string_of_runtime r1)

(** [linklin (last, first)] merges the end of one linked list with the 
    beginning of another *)
let linklin = function
  | ({ contents = Tagged (_, vs, Some (n, _))} as last),
    ({ contents = Tagged (_, _, Some (_, backptr))} as first) ->
      ignore (mapbut (fun _ -> ()) (fun v -> v := !first) vs (Some n)) ;
      backptr := !last 
  | { contents = Tagged (_, vs, Some (n, _))}, r2 ->
      runtime_error ("Bad link: expected tagged linear data " 
                     ^ "in 1st position, got " ^ string_of_runtime r2) 
  | r1, _ -> 
      runtime_error ("Bad link: expected tagged linear data " 
                     ^ "in 1st position, got " ^ string_of_runtime r1)

let rec interp env = function
  | Var x ->
      (try
	List.assoc x env
      with
	Not_found -> runtime_error ("Unknown variable " ^ x))
  | Int k -> ref (Boxed k)
  | Const (c, vs, None) -> ref (Tagged (c, List.map (interp env) vs, None))
  | Const (c, vs, Some n) -> runtime_error "Not supposed to be a hole here"
  | Lin (x, ty, v) -> 
      (match interp_lin env x v with
      |	None -> ref (Zipped (ref Identity))
      |	Some (first, last) -> ref (Zipped (ref (Zipper (first, last)))))
  | Thunk e -> ref (Thunked (env, e))
  | Fun (x, _, e) -> ref (Closed (env, x, e))
  | Times (e1, e2) ->
      (match (interp env e1), (interp env e2) with
         | { contents = Boxed k1 }, { contents = Boxed k2 } -> 
             ref (Boxed (k1 * k2))
	 | _ -> runtime_error "Integers expected in multiplication")
  | Plus (e1, e2) ->
      (match (interp env e1), (interp env e2) with
         | { contents = Boxed k1 }, { contents = Boxed k2 } -> 
             ref (Boxed (k1 + k2))
	 | _ -> runtime_error "Integers expected in addition")
  | Minus (e1, e2) ->
      (match (interp env e1), (interp env e2) with
         | { contents = Boxed k1 }, { contents = Boxed k2 } -> 
             ref (Boxed (k1 - k2))
	 | _ -> runtime_error "Integers expected in subtraction")
  | Equal (e1, e2) ->
      (match (interp env e1), (interp env e2) with
         | { contents = Boxed k1 }, { contents = Boxed k2 } -> mkbool (k1 = k2)
	 | _ -> runtime_error "Integers expected in =")
  | Less (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | { contents = Boxed k1 }, { contents = Boxed k2 } -> mkbool (k1 < k2)
	 | _ -> runtime_error "Integers expected in <")
  | Case (e, pats, _) -> 
      (match interp env e with 
         | { contents = Boxed i } -> match_int env i pats
         | { contents = Tagged (c, vs, _) } -> match_struct env (c, vs) pats
         | { contents = Zipped orig } ->
	     (match !orig with
	     | Identity -> match_linear_id env orig pats
	     | Zipper (first, last) ->
	       let rec follow_nextptr r = 
		 match !r with 
                 | Tagged (c, rs, Some (n, _)) -> List.nth rs n
                 | Null -> runtime_error ("Broken list invariant: wrong end")
		 | _ -> runtime_error ("Tagged linear data expected, got " 
                                       ^ string_of_runtime first) in
	       let smaller = 
                 (* This is a little bit scary, would be hard to do in ML *)
		 if !first == !last 
                 then Identity
		 else Zipper (follow_nextptr first, last) in
	       let (c, vs, n) = 
		 match !first with
		 | Tagged (c, vs, Some (n, _)) -> (c, vs, n)
		 | _ -> runtime_error ("Tagged linear data expected, got " 
                                       ^ string_of_runtime first) in
	       match_linear env (c, vs, n, orig, smaller) pats
             | Invalid -> runtime_error "Zipper reused more than once")
         | v -> match_whatever env v pats)
  | Case' (e, pats) -> 
      (match interp env e with
         | { contents = Zipped orig } ->
             (match !orig with 
             | Identity -> match_linear_id env orig pats
             | Zipper (first, last) -> 
               let rec follow_backptr r = 
                 match !r with 
                 | Tagged (c, rs, Some (n, r)) -> r
                 | Null -> runtime_error ("Broken list invariant: wrong end")
		 | _ -> runtime_error ("Tagged linear data expected, got " 
                                       ^ string_of_runtime last) in
               let smaller = 
                 if !first == !last
                 then Identity
                 else Zipper (first, follow_backptr last) in
               let (c, vs, n) = 
                 match !last with
                 | Tagged (c, vs, (Some (n, _))) -> (c, vs, n)
                 | _ -> runtime_error ("Tagged linear data expected, got " 
                                       ^ string_of_runtime first) in
               match_linear_inside env (c, vs, n, orig, smaller) pats
             | Invalid -> runtime_error "Zipper reused more than once")
         | _ -> match_failure pats)
  | Apply (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | { contents = Closed (env, x, e) }, v2 -> interp ((x,v2)::env) e
         | { contents = Zipped ({ contents = Zipper (first, last) } as r) }, v2 
           -> r := Invalid ; bindlin (last, v2) ; first
	 | { contents = Zipped ({ contents = Identity} as r) }, v2 ->
	     r := Invalid ; v2
         | { contents = Zipped { contents = Invalid } }, _ ->
             runtime_error "Zipper reused more than once"
	 | _, _ -> runtime_error "Function expected in application")
  | To (e1, x, e2) -> interp ((x, interp env e1)::env) e2
  | Return e -> interp env e
  | Force e ->
      (match interp env e with
	 | { contents = Thunked (env, e) } -> interp env e
	 | _ -> runtime_error "Thunk expected in force")
  | Rec (x, _, e') as e -> interp ((x, ref (Thunked (env, e))) :: env) e'

(** [interp_lin env y v] interprets the value expression [v] in environment
    [env] with hole [y]. 
    It returns None if the v is just the variable.
    It otherwise returns Some (r1, r2), where r1 is a reference to the first
    struct in the linked list and r2 is a reference to the last struct in
    the linked list (the one closest to the hole). These may be the same. *)
and interp_lin env y = function
  | Var x -> 
      if x <> y then runtime_error ("Wrong linear variable!") ;
      None
  | Const (c, vs, Some n) -> 
      (* Intepretation on all arguments normally, except for the hole one *)
      let rec interp_lins n = function
        | [] -> runtime_error "Wrong number of arguments" 
        | v :: vs -> 
            if n = 0 then 
              let (v, maybe_zipper) = 
                match interp_lin env y v with
                  | None -> let hole = ref Null in (hole, None)
                  | Some (first, last) -> (first, Some (first, last)) in
              (v :: List.map (interp env) vs, maybe_zipper)
            else
              let (vs, maybe_zipper) = interp_lins (n - 1) vs in 
              (interp env v :: vs, maybe_zipper) in
      let (rs, maybe_zipper) = interp_lins n vs in
      let newcell = ref (Tagged (c, rs, Some (n, ref Null))) in
      (match maybe_zipper with
      | None -> Some (newcell, newcell)
      | Some (first, last) -> bindlin (newcell, first) ; Some (newcell, last))
  | Apply (v1, v2) ->
      (match interp env v1 with
      | { contents = Zipped ({ contents = Zipper (first1, last1)} as r)} ->
          r := Invalid ;
          (match interp_lin env y v2 with
          | None -> Some (first1, last1)
          | Some (first2, last2) ->
              linklin (last1, first2) ;
              Some (first1, last2))
      |	{ contents = Zipped ({ contents = Identity} as r)} ->
          r := Invalid ;
          interp_lin env y v2
      | { contents = Zipped { contents = Invalid}} ->
          runtime_error "Zipper reused more than once"
      | _ -> runtime_error "Linear function expected in application")
  | e -> runtime_error ("expression " ^ string_of_expr e ^ " can't have holes")

and match_int env i = function
  | (Var x, e) :: _ -> interp ((x, ref (Boxed i)) :: env) e
  | (Int j, e) :: pats -> 
      if i = j then interp env e else match_int env i pats
  | pats -> match_failure pats

and match_struct env (c, vs) = function
  | (Var x, e) :: _ -> interp ((x, ref (Tagged (c, vs, None))) :: env) e
  | (Const (c', vars, None), e) :: pats ->
      if c = c' 
      then interp (List.map2 bindpat vars vs @ env) e 
      else match_struct env (c, vs) pats
  | pats -> match_failure pats

and match_linear_id env orig = function
  (* Catch-all case *)
  | ((Var x, e) :: _ | (Lin (_, _, Apply (Var x, Var _)), e) :: _) -> 
      interp ((x, ref (Zipped orig)) :: env) e

  (* Match *)
  | (Lin (_, _, Var x), e) :: _ -> 
      (orig := Invalid ; interp env e)

  (* Miss - ([x] x) never matches ([x] c ...) or ([x] f (c ...)) *)
  | (Lin (_, _, Const _), _) :: pats -> 
      match_linear_id env orig pats
  | (Lin (_, _, Apply (Var _, Const _)), _) :: pats ->
      match_linear_id env orig pats

  | pats -> match_failure pats

and match_linear_inside env (c, vs, n, orig, smaller) = function
  (* Catch-all case *)
  | ((Var x, e) :: _ | (Lin (_, _, Apply (Var x, Var _)), e) :: _) ->
      interp ((x, ref (Zipped orig)) :: env) e

  (* Miss - ([x] x) never matches ([x] c ...) *)
  | (Lin (_, _, Var _), _) :: pats ->
      match_linear_inside env (c, vs, n, orig, smaller) pats

  (* Possible match *)
  | (Lin (y, _, Apply (Var f, Const (c', vars, Some m))), e) :: pats ->
      (* Assumed: that List.nth vars m = Var y *)
      (* (The pattern would be rejected by coverage checking otherwise) *)
      if c = c' && n = m
      then (orig := Invalid ; 
            let env' =
              (f, ref (Zipped (ref smaller))) ::
              (mapbut2 bindpat (fun _ _ -> ("_", ref Null)) vars vs (Some n)) @
              env in
            interp env' e)
      else match_linear_inside env (c, vs, n, orig, smaller) pats

  | pats -> match_failure pats

and match_linear env (c, vs, (n: int), orig, smaller) = function
  (* Catch-all case *)
  | ((Var x, e) :: _ | (Lin (_, _, Apply (Var x, Var _)), e) :: _) ->
      interp ((x, ref (Zipped orig)) :: env) e

  (* Miss - ([x] x) never matches ([x] c ...) *)
  | (Lin (_, _, Var _), _) :: pats ->
      match_linear env (c, vs, n, orig, smaller) pats

  (* Possible match *)
  | (Lin (_, _, Const (c', vars, Some m)), e) :: pats -> 
      let bindpat_lin = function
        (* Optimized case: known to be a match *)
        (* (The pattern would be rejected by coverage checking otherwise) *)
        | Var _ -> fun v -> ("_", v) 
        (* Common case: bind a new zipper *)
        | Apply (Var x, Var _) -> fun v -> (x, ref (Zipped (ref smaller)))
        | _ -> runtime_error "Multiple-depth pattern matching" in
      if c = c' && n = m
      then (orig := Invalid ; 
            interp (mapbut2 bindpat bindpat_lin vars vs (Some m) @ env) e)
      else match_linear env (c, vs, n, orig, smaller) pats 

  | pats -> match_failure pats

and match_whatever env v = function
  | (Var x, e) :: _ -> interp ((x, v) :: env) e
  | pats -> match_failure pats


