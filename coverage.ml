(** Check well-formedness of case expressions as a second pass *)

open Syntax
open Type_check

module SetI = Set.Make(struct type t = int let compare = compare end)

let redundant_error pats = 
  match string_of_int (List.length pats) with
    | "1" -> print_endline ("WARNING: at least 1 redundant case") 
    | n -> print_endline ("WARNING: at least " ^ n ^ " redundant cases") 

let duplicate_error c = 
  print_endline ("WARNING: duplicate (or vaculous) cases matching constructor "
                 ^ c)

let nonexhaustive_error missing = 
  print_endline ("WARNING: nonexaustive match, missing pattern: " ^ missing)

(** Coverage checking at type int *)
let rec cover_ints i = function
  | [] -> nonexhaustive_error (string_of_int (i + 1)) (* XXX bug at max_int *)
  | [ (Var x, _) ] -> ()
  | (Var x, _) :: pats -> redundant_error pats
  | (Int x, _) :: pats -> cover_ints (if x > i then x else i) pats
  | _ -> type_error "type invariant violated"

(** Check for duplicates *)
  let check_duplicate_variable_occurances pats =
    let folder set = function  
        | Var "_" -> set
        | Var x -> 
            if MapS.mem x set
            then type_error ("variable " ^ x ^ " bound twice in pattern") ;
            MapS.add x () set
        | e -> type_error (string_of_expr e ^ " not allowed in pattern " ^
                           "(depth-1 pattern matching only)") in
    ignore (List.fold_left folder MapS.empty pats)

(** Coverage checking at defined type *)
let rec cover_defined consts = function
  | [] -> 
      if not (MapS.is_empty consts) 
      then 
        let (c, tys) = MapS.choose consts in
        nonexhaustive_error
          (String.concat " " (c :: List.map (fun _ -> "_") tys))
  | [ (Var x, _) ] -> if MapS.is_empty consts then redundant_error [ () ]
  | (Var x, _) :: pats -> redundant_error pats
  | (Const (c, pats', None), _) :: pats ->
      if not (MapS.mem c consts) then duplicate_error c ;
      check_duplicate_variable_occurances pats' ;
      cover_defined (MapS.remove c consts) pats
  | _ -> type_error "type invariant violated"

(* turn the argument type into a string *)
let string_of_lambdaty = function 
  | VInt -> "int"
  | VConst a -> a
  | lty -> type_error ("can't match against lambda binding a type " ^
                     string_of_type lty) 


(** Coverage checking for a linear function pattern *)
let rec cover_linear goals = function
  | [] -> 
      if MapS.mem "id" goals then nonexhaustive_error ("[hole] hole") ;
      let unfinished_goals = 
        MapS.filter (fun _ set -> not (SetI.is_empty set)) goals in
      if not (MapS.is_empty unfinished_goals)
      then
        let (c, pos) = MapS.choose unfinished_goals in
        let n = SetI.choose pos in
        let (tys, _) = Hashtbl.find consTable c in
        let args = 
          mapbut (fun _ -> "_") (fun _ -> "(_ hole)") tys (Some n) in 
        nonexhaustive_error (String.concat " " ("[hole] " :: c :: args)) 
  | ([ (Var _, _) ] | [ (Lin (_, _, Apply (Var _, Var _)), _) ]) -> 
      let unfinished_goals = 
        MapS.filter (fun _ set -> not (SetI.is_empty set)) goals in
      if MapS.is_empty unfinished_goals then redundant_error [ () ]
  | ((Var _, _) :: pats | (Lin (_, _, Apply (Var _, Var _)), _) :: pats) ->
      redundant_error pats
  | (Lin (x, ty, Var _), _) :: pats -> 
      if not (MapS.mem "id" goals) 
      then print_endline "WARNING: duplicate cases matching the identity" ;
      cover_linear (MapS.remove "id" goals) pats
  | (Lin (x, ty, Const (c, pats', Some n)), _) :: pats ->
      (* print_endline ("Pattern: constructor " ^ c ^ ", position " 
       *                ^ string_of_int n) ; 
       * print_endline ("Remaining goals: ") ; 
       * MapS.fold (fun c set () -> 
       *   print_string ("Constructor " ^ c ^ ", position(s) ") ;
       *   SetI.fold (fun n () -> print_int n; print_string " ") set () ;
       *   print_endline "") goals () ; *)
      if not (SetI.mem n (MapS.find c goals)) then duplicate_error c ;
      let pats'' = 
        mapbut 
          (fun pat -> pat) 
          (function 
             | Var x -> 
                 if Closure.is_final subord (string_of_lambdaty ty) 
                 then Var "_"
                 else type_error ("Depth-1 pattern matching only: " ^
                                  "finding " ^ x ^ " in position " ^ 
                                  string_of_int n ^ " of constructor " ^
                                  c ^ " counts.")
             | Apply (Var y, Var x) -> Var y
             | e -> 
                 type_error (string_of_expr e ^ " not allowed in linear " ^
                           "pattern (depth-1 pattern matching only)"))
          pats' (Some n) in
      check_duplicate_variable_occurances pats'' ;
      cover_linear (MapS.add c (SetI.remove n (MapS.find c goals)) goals) pats
  | _ -> type_error "type invariant violated"

(** Calculate the coverage checking problem for a type with subordination *)
let coverage_goals lty ty = 
  let lty = string_of_lambdaty lty in
  
  (* Get the set of relevant argument positions for a single constant *)
  let const_args c _ goalmap = 
    let folder (n, set) argty =
      let argty = match argty with 
                    | VInt -> "int" 
                    | VConst a -> a
                    | _ -> "" in
      if argty = lty || Closure.check_path subord (argty, lty) 
      then (n+1, SetI.add n set)
      else (n+1, set) in
    let (_, goalset) = 
      List.fold_left folder (0, SetI.empty)
        (fst (Hashtbl.find consTable c)) in
    MapS.add c goalset goalmap in

  let starting_map = 
    if ty = lty then (MapS.singleton "id" SetI.empty) else MapS.empty in

  MapS.fold const_args (Hashtbl.find dataTable ty) starting_map
  

let check_simple_coverage = function
  | [] -> type_error "empty case analysis"

  (* Identity *)
  | [ (Var x, _) ] -> () (* Identity *)
  | (Var x, _) :: pats -> redundant_error pats

  (* eta-expanded identity *)
  | [ (Lin (x, ty, Apply (Var _, Var _)), _) ] -> ()
  | (Lin (x, ty, Apply (Var _, Var _)), _) :: pats -> redundant_error pats
   
  (* Known constants *)
  | (Int i, _) :: pats -> cover_ints i pats
  | ((Const (c, _, None), _) :: _) as pats -> 
      let (_, a) = Hashtbl.find consTable c in
      let consts = Hashtbl.find dataTable a in
      cover_defined consts pats
  | ((Lin (_, ty, Var _), _) :: _) as pats ->
      let goals = coverage_goals ty (string_of_lambdaty ty) in
      cover_linear goals pats
  | ((Lin (_, ty, Const (c, _, _)), _) :: _) as pats ->
      let (_, a) = Hashtbl.find consTable c in
      let goals = coverage_goals ty a in
      cover_linear goals pats
      
  | _ -> type_error "type invariant violated (check_simple_coverage)"

(** [coverage e] does coverage checking on a well-typed expression [e] *)
let rec coverage = function
  | (Var _ | Int _ | Times _ | Plus _ | Minus _ | Equal _ | Less _) -> ()
  | Const (_, vs, _) -> ignore (List.map coverage vs)
  | Thunk e -> coverage e
  | Force e -> coverage e
  | Return e -> coverage e
  | To (e1, _, e2) -> coverage e1 ; coverage e2
  | Fun (_, _, e) -> coverage e
  | Lin (_, _, e) -> coverage e
  | Apply (e, v) -> coverage e ; coverage v
  | Rec (_, _, e) -> coverage e
  | Case (e, cases) -> 
      coverage e ; 
      check_simple_coverage cases ;  
      ignore (List.map (fun (_, e) -> coverage e) cases)