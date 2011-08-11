(** Type checking. *)

open Syntax

module MapS = 
  Map.Make(struct type t = string let compare = String.compare end)
let consTable: (name, (vtype list * name)) Hashtbl.t = Hashtbl.create 5
let dataTable: (name, (vtype list) MapS.t) Hashtbl.t = Hashtbl.create 5

(** Exception indicating a type-checking error. *)
exception Type_error of string

(** [type_error msg] raises exception [Type_error msg]. *)
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

let check_cons c = 
  if not (Hashtbl.mem consTable c)
  then type_error ("unknown constructor " ^ c) ; 
  Hashtbl.find consTable c

(** [unfold_lolli collected ty] is a tail recursive function that exposes
    all the right-nested implications in the type ty to get at the head type *)
let rec unfold_lolli collected = function
  | VConst a -> (List.rev collected, a)
  | VLolli (ty1, ty2) -> check_vtype ty1 ; unfold_lolli (ty1 :: collected) ty2
  | ty -> type_error (string_of_type ty ^ " is not a valid constructed type")

(** [chk_data to_add data] is a tail recursive function that collects data
    in the map [to_add], checking that a set of datatype declarations are 
    kosher. May not be exactly right. *)
let rec chk_data (to_add: vtype list MapS.t MapS.t) = function
  | [] -> 
    (* All cases covered, add them to the persistant store *)
      ignore (MapS.mapi (function a -> function constructors -> 
        Hashtbl.add dataTable a constructors ;
        ignore (MapS.mapi (function c -> function tys -> 
          Hashtbl.add consTable c (tys, a)) constructors)) to_add) 
  
  | (c, ty) :: data -> 
    (* Check for duplicate constructor declarations *)
      if Hashtbl.mem consTable c 
      then type_error ("constructor " ^ c ^ " already declared") ;
      if MapS.exists (function _ -> function constructors ->
           MapS.exists (function c' -> function _ -> c = c') constructors)
           to_add
      then type_error ("constructor " ^ c ^ " duplicated in this declaration") ;
      let (tys, a) = unfold_lolli [] ty in 
    (* Check that we're not extending previous datatype declarations *)
      if Hashtbl.mem dataTable a
      then type_error ("type " ^ a ^ " cannot be extended") ;
    (* Either extend an existing type map or add a new one *)
      if not (MapS.mem a to_add)
      then chk_data (MapS.add a (MapS.singleton c tys) to_add) data
      else chk_data 
        (MapS.add a (MapS.add c tys (MapS.find a to_add)) to_add) data

(** [check_data data] checkes the well-formedness of the data declarations 
    [data] and loads information into the global tables *)
let check_data = chk_data MapS.empty
let () = check_data [ ("true", VConst "bool") ; ("false", VConst "bool") ]

(** [pat_ty ty pat] checks that the pattern [pat] is a valid pattern of type
    [ty] and generates the extended context produced by that pattern. *)
let rec pat_ty ty = function
  | Var x -> [ (x, ty) ]
  | Const (c, pats) -> 
      let (tys, a) = check_cons c in
      if List.length tys <> List.length pats
      then 
        type_error 
          ("constructor " ^ c ^ " expects " ^ string_of_int (List.length tys) ^
           " argument(s), but was given " ^ string_of_int (List.length pats)) ;
      if ty <> VConst a then
        type_error 
          ("constructor " ^ c ^ " not of type " ^ string_of_type ty) ;
      List.concat (List.map2 pat_ty tys pats)
  | Int _ ->
      if ty = VInt then [] else 
        type_error 
          ("integer constant not is not of type " ^ string_of_type ty)
  | pat -> type_error (string_of_expr pat ^ " not a valid pattern")

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
  | Var "_" -> type_error ("underscores cannot be used as identifiers")
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
