(** An efficient interpreter; everything is boxed *)

open Syntax

type environment = (name * runtime) list

and runtime = heapdata ref

and heapdata = 
  | Null 
  | Boxed of int
  | Tagged of name * runtime list * int option
  | Thunked of environment * expr
  | Closed of environment * name * expr
  | Zipped of zipper ref

and zipper = 
  | Zipper of runtime * runtime (* Pointer to start, hole *)
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
  | _ -> runtime_error "Bad pattern"

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
  | { contents = Zipped { contents = Zipper (r, _) } } -> 
    "(<zipper> " ^ string_of_runtime r ^ ")"

let bindpat = function
  | Var x -> fun v -> (x, v)
  | _ -> runtime_error "Multiple-depth pattern matching"

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
      let (r1, r2) = interp_lin env x v in
      ref (Zipped (ref (Zipper (r1, r2))))
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
  | Case (e, pats) -> 
      (match (interp env e) with 
         | { contents = Boxed i } -> match_int env i pats
         | { contents = Tagged (c, vs, _) } -> match_struct env (c, vs) pats
         | { contents = Zipped { contents = Invalid } } -> 
           runtime_error "Zipper reused more than once"
         | { contents = Zipped ({ contents = 
               Zipper ({ contents = Null }, hole) } as r) } -> 
           r := Invalid ; match_linear_id env pats
         | { contents = Zipped ({ contents = 
               Zipper ({ contents = Tagged (c, vs, Some n) }, hole) } as r) }->
           r := Invalid ; match_linear env (c, vs, n, hole) pats
         | v -> match_whatever env v pats)
  | Apply (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | { contents = Closed (env, x, e) }, v2 -> interp ((x,v2)::env) e
         | { contents = Zipped ({ contents = Zipper (v, hole) } as r) }, v2 ->
           r := Invalid ; hole := !v2 ; v
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
    [env] with hole [y]. It returns a reference to the first struct in the 
    linked list (if there is one) and a pointer to the hole. *)
and interp_lin env y = function
  | Var x -> 
      if x <> y then runtime_error ("Wrong linear variable!") ;
      let r = ref Null in
      (r, r) 
  | Const (c, vs, Some n) -> 
      (* Intepretation on all arguments normally, except for the hole one *)
      let rec interp_lins n = function
        | [] -> runtime_error "Wrong number of arguments" 
        | v :: vs -> 
            if n = 0 then 
              let (v, hole) = interp_lin env y v in
              (v :: List.map (interp env) vs, hole)
            else
              let (vs, hole) = interp_lins (n - 1) vs in 
              (interp env v :: vs, hole) in
      let (vs, hole) = interp_lins n vs in
      (ref (Tagged (c, vs, Some n)), hole)
  | Apply (v1, v2) ->
      (match (interp env v1), (interp_lin env y v2) with
         | { contents = Zipped ({ contents = Zipper (v1, old_hole) } as r) }, 
           (v2, hole) ->
           r := Invalid ; old_hole := !v2 ; (v1, hole)
         | { contents = Zipped { contents = Invalid } }, _ ->
           runtime_error "Zipper reused more than once"
	 | _, _ -> runtime_error "Function expected in application")
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

and match_linear_id env = function
  | ((Var x, e) :: _ | (Lin (_, _, Apply (Var x, Var _)), e) :: _) -> 
      let r = ref Null in 
      interp ((x, ref (Zipped (ref (Zipper (r, r))))) :: env) e
  | (Lin (_, _, Var x), e) :: _ -> interp env e
  | (Lin (_, _, Const (_, _, _)), _) :: pats -> match_linear_id env pats
  | pats -> match_failure pats

and match_linear env (c, vs, n, hole) = function
  | ((Var x, e) :: _ | (Lin (_, _, Apply (Var x, Var _)), e) :: _) ->
      let z = ref (Zipper (ref (Tagged (c, vs, Some n)), hole)) in 
      interp ((x, ref (Zipped z)) :: env) e
  | (Lin (_, _, Var _), _) :: pats -> match_linear env (c, vs, n, hole) pats
  | (Lin (_, _, Const (c', vars, Some m)), e) :: pats -> 
      let bindpat_lin = function
        (* Optimized case: known to be a match *)
        | Var x -> fun v -> ("_", v) 
        (* Common case: bind a new zipper *)
        | Apply (Var x, Var _) -> fun v -> 
            (x, ref (Zipped (ref (Zipper (v, hole)))))
        | _ -> runtime_error "Multiple-depth pattern matching" in
      if c = c' && n = m
      then interp (mapbut2 bindpat bindpat_lin vars vs (Some m) @ env) e
      else match_linear env (c, vs, n, hole) pats 
  | pats -> match_failure pats

and match_whatever env v = function
  | (Var x, e) :: _ -> interp ((x, v) :: env) e
  | pats -> match_failure pats


