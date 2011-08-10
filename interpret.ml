(** An efficient interpreter; everything is boxed *)

open Syntax

type environment = (name * runtime) list

and runtime = heapdata ref

and heapdata = 
  | Null 
  | Boxed of int
  | Tagged of name * runtime list
  | Thunked of environment * expr
  | Closed of environment * name * expr
  | Zipped of zipper ref

and zipper = 
  | Zipper of runtime * runtime (* Pointer to start, hole *)
  | Invalid                     (* Enforce affine usage *)

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error ("Runtime error: " ^ msg))

let vtrue = ref (Tagged ("true", []))
let vfalse = ref (Tagged ("false", []))
let mkbool = function
  | true -> vtrue
  | false -> vfalse

let match_failure = function
  | [] -> runtime_error "Match failure"
  | _ -> runtime_error "Bad pattern"

let rec string_of_runtime: runtime -> string = function
  | { contents = Null } -> "[]"
  | { contents = Boxed k } -> string_of_int k
  | { contents = Tagged (x, vs) } -> 
      if List.length vs = 0 then x 
      else "(" ^ x ^ " " ^ 
           String.concat " " (List.map string_of_runtime vs) ^ ")"
  | { contents = Thunked _ } -> "<thunk>"
  | { contents = Closed _ } -> "<fun>" 
  | { contents = Zipped { contents = Invalid } } -> "<used zipper>"
  | { contents = Zipped { contents = Zipper (r, _) } } -> 
    "<zipper> " ^ string_of_runtime r

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
  | Const (c, vs, None) -> ref (Tagged (c, List.map (interp env) vs))
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
         | { contents = Tagged (c, vs) } -> match_struct env (c, vs) pats
         | v -> match_whatever env v pats)
  | Apply (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | { contents = Closed (env, x, e) }, v2 -> interp ((x,v2)::env) e
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
      (ref (Tagged (c, vs)), hole)
  | Apply (f, Var x) ->
      if x <> y then runtime_error ("Wrong linear variable!") ;
      runtime_error "not ready to handle applies"
  | e -> runtime_error ("expression " ^ string_of_expr e ^ " can't have holes")

and match_int env i = function
  | (Var x, e) :: _ -> interp ((x, ref (Boxed i)) :: env) e
  | (Int j, e) :: pats -> 
      if i = j then interp env e else match_int env i pats
  | pats -> match_failure pats

and match_struct env (c, vs) = function
  | (Var x, e) :: _ -> interp ((x, ref (Tagged (c, vs))) :: env) e
  | (Const (c', vars, None), e) :: pats ->
      if c = c' 
      then interp (List.map2 bindpat vars vs @ env) e 
      else match_struct env (c, vs) pats
  | pats -> match_failure pats

and match_whatever env v = function
  | (Var x, e) :: _ -> interp ((x, v) :: env) e
  | pats -> match_failure pats


