(** Check well-formedness of case expressions as a second pass *)

open Syntax
open Type_check

let redundant_error pats = 
  match string_of_int (List.length pats) with
    | "1" -> print_endline ("WARNING: at least 1 redundant case") 
    | n -> print_endline ("WARNING: at least " ^ n ^ " redundant cases") 

let duplicate_error c = 
  print_endline ("WARNING: duplicate cases matching constructor " ^ c)

let nonexhaustive_error missing = 
  print_endline ("WARNING: nonexaustive match, missing pattern: " ^ missing)

let rec cover_ints i = function
  | [] -> nonexhaustive_error (string_of_int (i + 1)) (* XXX bug at max_int *)
  | [ (Var x, _) ] -> ()
  | (Var x, _) :: pats -> redundant_error pats
  | (Int x, _) :: pats -> cover_ints (if x > i then x else i) pats
  | _ -> type_error "type invariant violated"

let rec cover_defined consts = function
  | [] -> 
      if not (MapS.is_empty consts) 
      then 
        let (c, tys) = MapS.choose consts in
        nonexhaustive_error
          (String.concat " " (c :: List.map (fun _ -> "_") tys))
  | [ (Var x, _) ] -> if MapS.is_empty consts then redundant_error [ () ]
  | (Var x, _) :: pats -> redundant_error pats
  | (Const (c, pats'), _) :: pats ->
      let folder set = function
        | Var "_" -> set
        | Var x -> 
            if MapS.mem x set
            then type_error ("variable " ^ x ^ " bound twice in pattern") ;
            MapS.add x () set
        | e -> type_error (string_of_expr e ^ " not allowed in pattern " ^
                           "(depth-1 pattern matching only)") in
      if not (MapS.mem c consts) then duplicate_error c ;
      ignore (List.fold_left folder MapS.empty pats') ; 
      cover_defined (MapS.remove c consts) pats
  | _ -> type_error "type invariant violated"

let check_simple_coverage = function
  | [] -> type_error "empty case analysis"
  | [ (Var x, _) ] -> ()
  | (Var x, _) :: pats -> redundant_error pats
  | (Int i, _) :: pats -> cover_ints i pats
  | ((Const (c, _), _) :: _) as pats -> 
      let (_, a) = Hashtbl.find consTable c in
      let consts = Hashtbl.find dataTable a in
      cover_defined consts pats
  | _ -> type_error "type invariant violated"

(** [coverage e] does coverage checking on a well-typed expression [e] *)
let rec coverage = function
  | (Var _ | Int _ | Times _ | Plus _ | Minus _ | Equal _ | Less _) -> ()
  | Const (_, vs) -> ignore (List.map coverage vs)
  | Thunk e -> coverage e
  | Force e -> coverage e
  | Return e -> coverage e
  | To (e1, _, e2) -> coverage e1 ; coverage e2
  | Fun (_, _, e) -> coverage e
  | Apply (e, v) -> coverage e ; coverage v
  | Rec (_, _, e) -> coverage e
  | Case (e, cases) -> 
      coverage e ; 
      check_simple_coverage cases ;  
      ignore (List.map (fun (_, e) -> coverage e) cases)