(** Type checking. *)

open Syntax

module MapS = 
  Map.Make(struct type t = string let compare = String.compare end)
let consTable: (name, (vtype list * name)) Hashtbl.t = Hashtbl.create 5
let dataTable: (name, (vtype list) MapS.t) Hashtbl.t = Hashtbl.create 5

(** Exception indicating a type-checking error. *)
exception Type_error of string

(** [ty_error msg] raises exception [Type_error msg]. *)
let type_error msg = raise (Type_error ("Type error: " ^ msg))

let rec is_ctype = function
  | (VInt | VConst _ | VForget _) -> false
  | CFree ty -> is_vtype ty
  | CArrow (ty1, ty2) -> is_vtype ty1 && is_ctype ty2
  | VLolli _ -> false

and is_vtype = function
  | (VInt | VConst _) -> true
  | VForget ty -> is_ctype ty
  | (CFree _ | CArrow _) -> false
  | VLolli _ -> false (** VLolli is currently just an intermediate type *)

let check_ctype ty =
  if not (is_ctype ty) 
  then type_error (string_of_type ty ^ " is not a computation type")

let check_vtype ty =
  if not (is_vtype ty) 
  then type_error (string_of_type ty ^ " is not a value type")

let return e = function
  | CFree ty -> ty
  | ty -> type_error (string_of_expr e ^ " is used in sequencing but its type is " ^ string_of_type ty)

(** [check ctx ty e] checks that expression [e] has type [ty] in context [ctx].
    It raises [Type_error] if it does not. *)
let rec check ctx ty e =
  let ty' = type_of ctx e in
    if ty' <> ty then
      type_error
	(string_of_expr e ^ " has type " ^ string_of_type ty' ^
	   " but is used as if it had type " ^ string_of_type ty)

(** [type_of_cases ctx ty cases] computes the type of the match expressions 
    [cases] matching against a value of type [ty] in the context [ctx].
    It raises [Type_error] if any arms do not typecheck or disagree on type. *)
and type_of_cases ctx ty = function
  | [] -> (function
      | None -> type_error "no cases in match expression"
      | Some ty -> check_ctype ty ; ty)
  | (pat, e) :: cases -> (function
    | None -> 
        let tyc = type_of (pat_ty ty pat @ ctx) e in
          type_of_cases ctx ty cases (Some tyc) 
    | Some tyc -> 
        check (pat_ty ty pat @ ctx) tyc e ;
        type_of_cases ctx ty cases (Some tyc))

(** [type_of ctx e] computes the type of expression [e] in context [ctx].
    It raises [Type_error] if [e] does not have a type. *)
and type_of ctx = function
  | Var x ->
      (try 
	 List.assoc x ctx
       with
	   Not_found -> type_error ("unknown identifier " ^ x))
  | Int _ -> VInt
  | Const (c, vs) -> 
      if not (Hashtbl.mem consTable c)
      then type_error ("unknown constructor " ^ c) ; 
      let (tys, a) = Hashtbl.find consTable c in
      if List.length vs <> List.length tys 
      then type_error ("constructor " ^ c ^ " expects " ^ 
                       string_of_int (List.length tys) ^ " arg(s), given " ^
                       string_of_int (List.length vs)) ;
      ignore (List.map2 (check ctx) tys vs) ;
      VConst a

  | Times (e1, e2) -> check ctx VInt e1 ; check ctx VInt e2 ; VInt
  | Plus (e1, e2) -> check ctx VInt e1 ; check ctx VInt e2 ; VInt
  | Minus (e1, e2) -> check ctx VInt e1 ; check ctx VInt e2 ; VInt
  | Equal (e1, e2) -> 
      check ctx VInt e1 ; check ctx VInt e2 ; VConst "bool"
  | Less (e1, e2) -> 
      check ctx VInt e1 ; check ctx VInt e2 ; VConst "bool"
  | Case (e, cases) ->
      let ty = type_of ctx e in
        type_of_cases ctx ty cases None
  | Fun (x, ty, e) ->
      check_vtype ty ;
      let ty2 = type_of ((x,ty)::ctx) e in
	check_ctype ty2 ; CArrow (ty, ty2)
  | Apply (e1, e2) ->
      (match type_of ctx e1 with
	 | CArrow (ty1, ty2) -> check ctx ty1 e2 ; ty2
	 | ty ->
	     type_error (string_of_expr e1 ^
			 " is used as a function but its type is " ^
			 string_of_type ty))
  | To (e1, x, e2) ->
      let ty1 = return e1 (type_of ctx e1) in
	check_vtype ty1;
        let ty2 = type_of ((x,ty1)::ctx) e2 in
          check_ctype ty2 ; ty2
  | Let (x, e1, e2) ->
      let ty1 = type_of ctx e1 in
	check_vtype ty1;
	let ty2 = type_of ((x,ty1)::ctx) e2 in
	  check_ctype ty2 ; ty2
  | Return e ->
      let ty = type_of ctx e in
	check_vtype ty ; CFree ty
  | Force e ->
      (match type_of ctx e with
	 | VForget ty -> check_ctype ty ; ty
	 | ty -> type_error (string_of_expr e ^ " is forced but its type is " ^ string_of_type ty))
  | Thunk e ->
      let ty = type_of ctx e in
	check_ctype ty ; VForget ty
  | Rec (x, ty, e) ->
      check_ctype ty ;
      check ((x, VForget ty)::ctx) ty e ;
      ty
