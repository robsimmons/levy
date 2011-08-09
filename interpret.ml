(** An efficient interpreter. *)

open Syntax

type environment = (name * runtime) list

and runtime =
  | VInt of int
  | VStruct of pointer
  | VThunk of environment * expr
  | VFun of environment * name * expr
  | VReturn of runtime
  | VZipper of zipper ref 

and pointer = allocated option ref

and allocated = Struct of name * runtime list * (int * pointer) option

and zipper = 
  | Ident                                   (* [^x] ^x *)
  | Zipper of allocated ref * allocated ref (* Pointer to first and last *)
  | Invalid                                 (* Enforce affine usage *)

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error ("Runtime error: " ^ msg))

let cons c vs = ref (Some (Struct (c, vs, None))) (* Normal references *)
let bang r = 
  match !r with 
    | None -> runtime_error "null pointer dereference"
    | Some (Struct (c, vs, _)) -> (c, vs)

let vtrue = VStruct (cons "true" [])
let vfalse = VStruct (cons "false" [])
let mkbool = function
  | true -> vtrue
  | false -> vfalse

let match_failure = function
  | [] -> runtime_error "Match failure"
  | _ -> runtime_error "Bad pattern"

let rec string_of_runtime: runtime -> string = function
  | VInt k -> string_of_int k
  | VStruct r -> 
      let (x, vs) = bang r in
        if List.length vs = 0 then x else         
        "(" ^ x ^ " " ^ String.concat " " (List.map string_of_runtime vs) ^ ")"
  | VThunk _ -> "<thunk>"
  | VFun _ -> "<fun>"
  | VReturn v -> "return " ^ string_of_runtime v
  | VZipper _ -> "<zipper>"

let return = function
  | VReturn v -> v
  | _ -> runtime_error "Return expected in sequencing"

let bindpat = function
  | Var x -> fun v -> (x, v)
  | _ -> runtime_error "Multiple-depth pattern matching"

let rec interp env = function
  | Var x ->
      (try
	 List.assoc x env
       with
	   Not_found -> runtime_error ("Unknown variable " ^ x))
  | Int k -> VInt k
  | Const (c, vs) -> VStruct (cons c (List.map (interp env) vs))
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
      (match (interp env e) with 
         | VInt i -> match_int env i pats
         | VStruct r -> match_struct env (bang r) pats
         | v -> match_whatever env v pats)
  | Apply (e1, e2) ->
      (match interp env e1, interp env e2 with
	 | VFun (env, x, e), v2 -> interp ((x,v2)::env) e
	 | _, _ -> runtime_error "Function expected in application")
  | To (e1, x, e2) -> 
      let v = return (interp env e1) in interp ((x,v)::env) e2
  | Return e -> VReturn (interp env e)
  | Force e ->
      (match interp env e with
	 | VThunk (env, e) -> interp env e
	 | _ -> runtime_error "Thunk expected in force")
  | Rec (x, _, e') as e -> interp ((x, VThunk (env, e)) :: env) e'

and match_int env i = function
  | (Var x, e) :: _ -> interp ((x, VInt i) :: env) e
  | (Int j, e) :: pats -> 
      if i = j then interp env e else match_int env i pats
  | pats -> match_failure pats

and match_struct env (c, vs) = function
  | (Var x, e) :: _ -> interp ((x, VStruct (cons c vs)) :: env) e
  | (Const (c', vars), e) :: pats ->
      if c = c' 
      then interp (List.map2 bindpat vars vs @ env) e 
      else match_struct env (c, vs) pats
  | pats -> match_failure pats

and match_whatever env v = function
  | (Var x, e) :: _ -> interp ((x, v) :: env) e
  | pats -> match_failure pats


