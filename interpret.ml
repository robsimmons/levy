(** An efficient interpreter. *)

open Syntax

type environment = (name * runtime) list

and runtime =
  | VInt of int
  | VConst of name 
  | VThunk of environment * expr
  | VFun of environment * name * expr
  | VReturn of runtime

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error ("Runtime error: " ^ msg))

let rec string_of_runtime = function
  | VInt k -> string_of_int k
  | VConst a -> a
  | VThunk _ -> "<thunk>"
  | VFun _ -> "<fun>"
  | VReturn v -> "return " ^ string_of_runtime v

let mkbool = function
  | true -> VConst "true"
  | false -> VConst "false"

let rec filter f = function
  | [] -> None
  | x :: xs -> 
    (match f x with
     | None -> filter f xs
     | Some y -> Some y)

let rec matchpat v = function
  | (Const c, e) -> 
      (match v with 
         | VConst c' -> if c = c' then Some ([], e) else None
         | _ -> runtime_error "type error in match?")
  | (Int i, e) -> 
      (match v with
         | VInt i' -> if i = i' then Some ([], e) else None
         | _ -> runtime_error "type error in match?")
  | (Var x, e) -> Some ([ (x, v) ], e)
  | _ -> runtime_error "bad pattern"

let rec interp env = function
  | Var x ->
      (try
	 List.assoc x env
       with
	   Not_found -> runtime_error ("Unknown variable " ^ x))
  | Int k -> VInt k
  | Const c -> VConst c
  | Thunk e -> VThunk (env, e)
  | Fun (x, _, e) -> VFun (env, x, e)
  | Times (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | VInt k1, VInt k2 -> VInt (k1 * k2)
	 | _ -> runtime_error "Integers expected in multiplication")
  | Plus (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | VInt k1, VInt k2 -> VInt (k1 + k2)
	 | _ -> runtime_error "Integers expected in addition")
  | Minus (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | VInt k1, VInt k2 -> VInt (k1 - k2)
	 | _ -> runtime_error "Integers expected in subtraction")
  | Equal (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | VInt k1, VInt k2 -> mkbool (k1 = k2) 
	 | _ -> runtime_error "Integers expected in =")
  | Less (e1, e2) ->
      (match (interp env e1), (interp env e2) with
	 | VInt k1, VInt k2 -> mkbool (k1 < k2)
	 | _ -> runtime_error "Integers expected in <")
  | Case (e, pats) -> 
      (match filter (matchpat (interp env e)) pats with
         | None -> runtime_error "Match failure"
         | Some (subst, e') -> interp (subst @ env) e')
  | Apply (e1, e2) ->
      (match interp env e1, interp env e2 with
	 | VFun (env, x, e), v2 -> interp ((x,v2)::env) e
	 | _, _ -> runtime_error "Function expected in application")
  | To (e1, x, e2) ->
      (match interp env e1 with
         | VReturn v -> interp ((x,v)::env) e2
         | _ -> runtime_error "Return expected in sequencing")
  | Return e -> VReturn (interp env e)
  | Force e ->
      (match interp env e with
	 | VThunk (env, e) -> interp env e
	 | _ -> runtime_error "Thunk expected in force")
  | Rec (x, _, e') as e -> interp ((x, VThunk (env, e)) :: env) e'
