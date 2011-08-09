(** Abstract syntax *)

(** The type of variable names. *)
type name = string

(** Levy types are separated into value types and computation types, but
    it is convenient to have a single datatype for all of them. *)
type ltype =
  | VInt                          (** integer [int] *)
  | VConst of name                (** defined inductive types *)
  | VForget of ctype              (** thunked type [U t] *)
  | VLolli of vtype * vtype       (** construction type [s -o t] *)
  | CFree of vtype                (** free type [F s] *)
  | CArrow of vtype * ctype       (** function type [s -> t] *)

and vtype = ltype

and ctype = ltype

(** Levy expressions. We actually use the same type for values
    and computations because it makes the code shorter and produces
    more reasonable error messages during type checking. *)

type value = expr

and pattern = expr

and expr =
  | Var of name            	  (** variable *)
  | Const of name * value list    (** defined constant *)
  | Int of int             	  (** integer constant *)
  | Times of value * value 	  (** product [v1 * v2] *)
  | Plus of value * value  	  (** sum [v1 + v2] *)
  | Minus of value * value 	  (** difference [v1 - v2] *)
  | Equal of value * value 	  (** integer equality [v1 = v2] *)
  | Less of value * value  	  (** integer comparison [v1 < v2] *)
  | Thunk of expr          	  (** thunk [thunk e] *)
  | Force of value             	  (** [force v] *)
  | Return of value            	  (** [return v] *)
  | To of expr * name * expr  	  (** sequencing [e1 to x . e2] *)
  | Case of value * matches       (** case analysis [match x with ...] *)
  | Fun of name * ltype * expr 	  (** function [fun x:s -> e] *)
  | Apply of expr * value      	  (** application [e v] *)
  | Rec of name * ltype * expr 	  (** recursion [rec x : t is e] *)

and matches = (pattern * expr) list

let cLet (x, v, e) = 
  Case (v, [ (Var x, e) ])
let cIf (v, et, ef) = 
  Case (v, [ (Const ("true", []), et); (Const ("false", []), ef) ])
let cApply (e, v) = 
  match e with
    | Const (x, vs) -> Const (x, vs @ [ v ])
    | _ -> Apply (e, v)

(** Toplevel commands *)
type toplevel_cmd =
  | Expr of expr                  (** an expression to be evaluated *)
  | Def of name * expr            (** toplevel definition [let x = e] *)
  | RunDef of name * expr         (** toplevel definition [do x = e] *)
  | Use of string                 (** load a file [$use "<filename>"] *)
  | Data of (name * ltype) list   (** datatype declaration [data ...] *)
  | Quit                          (** exit toplevel [$quit] *)

(** Conversion from a type to a string *)
let string_of_type ty =
  let rec to_str n ty =
    let (m, str) =
      match ty with
	| VInt -> (3, "int")
	| VConst a -> (3, a)
	| VForget ty -> (2, "U " ^ to_str 1 ty)
	| VLolli (ty1, ty2) -> (1, (to_str 1 ty1) ^ " -o " ^ (to_str 0 ty2))
	| CFree ty -> (2, "F " ^ to_str 1 ty)
	| CArrow (ty1, ty2) -> (1, (to_str 1 ty1) ^ " -> " ^ (to_str 0 ty2))
    in
      if m > n then str else "(" ^ str ^ ")"
  in
    to_str (-1) ty

(** Conversion from an expression to a string *)
let string_of_expr e =
  let rec to_str_cases cases = "..." 
    and to_str n e =
    let (m, str) =
      match e with
	| Int n ->           (10, string_of_int n)
	| Var x ->           (10, x)
	| Const (x, []) ->   (10, x)
        | Const (x, vs) ->   ( 9, x ^ " " ^ String.concat " " (List.map (to_str 9) vs))
	| Return e ->        ( 9, "return " ^ (to_str 9 e))
	| Force e ->         ( 9, "force " ^ (to_str 9 e))
	| Thunk e ->         ( 9, "thunk " ^ (to_str 9 e))
	| Apply (e1, e2) ->  ( 9, (to_str 8 e1) ^ " " ^ (to_str 9 e2))
	| Times (e1, e2) ->  ( 8, (to_str 7 e1) ^ " * " ^ (to_str 8 e2))
	| Plus (e1, e2) ->   ( 7, (to_str 6 e1) ^ " + " ^ (to_str 7 e2))
	| Minus (e1, e2) ->  ( 7, (to_str 6 e1) ^ " - " ^ (to_str 7 e2))
	| Equal (e1, e2) ->  ( 5, (to_str 5 e1) ^ " = " ^ (to_str 5 e2))
	| Less (e1, e2) ->   ( 5, (to_str 5 e1) ^ " < " ^ (to_str 5 e2))
        | Case (e, cases) -> ( 4, "match " ^ (to_str 4 e) ^ " with " ^ (to_str_cases cases))
	| Fun (x, ty, e) ->  ( 2, "fun " ^ x ^ " : " ^ (string_of_type ty) ^ " -> " ^ (to_str 0 e))
	| Rec (x, ty, e) ->  ( 2, "rec " ^ x ^ " : " ^ (string_of_type ty) ^ " is " ^ (to_str 0 e))
	| To (e1, x, e2) ->  ( 1, to_str 1 e1 ^ " to " ^ x ^ " . " ^ to_str 0 e2)
    in
      if m > n then str else "(" ^ str ^ ")"
  in
    to_str (-1) e

(** [remove_assocs s pats] removes all the variables bound in the patterns
    [pats] from the substitution [s] *)
let rec remove_assocs s = function
  | [] -> s
  | Var x :: pats -> remove_assocs (List.remove_assoc x s) pats
  | Const (c, vs) :: pats -> remove_assocs s (vs @ pats)
  | _ :: pats -> remove_assocs s pats (* Only matches case Int if typechecked *)

(** [subst [(x1,e1);...;(xn;en)] e] replaces in [e] free occurrences
    of variables [x1], ..., [xn] with expressions [e1], ..., [en]. *)
let rec subst s = function
  | (Var x) as e -> (try List.assoc x s with Not_found -> e)
  | (Int _) as e -> e
  | Const (x, vs) -> Const (x, List.map (subst s) vs)
  | Times (e1, e2) -> Times (subst s e1, subst s e2)
  | Plus (e1, e2) -> Plus (subst s e1, subst s e2)
  | Minus (e1, e2) -> Minus (subst s e1, subst s e2)
  | Equal (e1, e2) -> Equal (subst s e1, subst s e2)
  | Less (e1, e2) -> Less (subst s e1, subst s e2)
  | Case (e, cases) -> Case (subst s e, List.map (subst_case s) cases)
  | Fun (x, ty, e) -> let s' = List.remove_assoc x s in Fun (x, ty, subst s' e)
  | To (e1, x, e2) -> To (subst s e1, x, subst (List.remove_assoc x s) e2)
  | Return e -> Return (subst s e)
  | Force e -> Force (subst s e)
  | Thunk e -> Thunk (subst s e)
  | Apply (e1, e2) -> Apply (subst s e1, subst s e2)
  | Rec (x, ty, e) -> let s' = List.remove_assoc x s in Rec (x, ty, subst s' e)

and subst_case s (pat, e) = (pat, subst (remove_assocs s [ pat ]) e)
