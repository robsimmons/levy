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
	
(** Coverage checking for an interior linear function pattern *)
let rec cover_linear_inside goals = function
  | [] -> 
      if MapS.mem "id" goals then nonexhaustive_error ("[hole] hole") ;
      let unfinished_goals = 
        MapS.filter (fun _ set -> not (SetI.is_empty set)) goals in
      if not (MapS.is_empty unfinished_goals)
      then 
        let (c, pos) = MapS.choose unfinished_goals in 
        let n = SetI.choose pos in 
        let (tys, _) = Hashtbl.find consTable c in
        let args = mapbut (fun _ -> "_") (fun _ -> "hole") tys (Some n) in
        nonexhaustive_error ("[hole] _ (" ^ c ^ String.concat " " args ^ ")")
  | ([ (Var _, _) ] | [ (Lin (_, _, Apply (Var _, Var _)), _) ]) -> 
      let unfinished_goals = 
        MapS.filter (fun _ set -> not (SetI.is_empty set)) goals in
      if MapS.is_empty unfinished_goals then redundant_error [ () ]
  | ((Var _, _) :: pats | (Lin (_, _, Apply (Var _, Var _)), _) :: pats) ->
      redundant_error pats
  | (Lin (x, ty, Var _), _) :: pats ->
      if not (MapS.mem "id" goals)
      then print_endline "WARNING: duplicate cases matching the identity" ;
      cover_linear_inside (MapS.remove "id" goals) pats
  | (Lin (x, ty, Apply (Var f, Const (c, pats', Some n))) as pat, _) :: pats ->
      let pats'' = 
        mapbut 
          (fun pat -> pat) 
          (function 
            | Var x -> Var f (* Bit of a hack, to count all variables *)
            | pat' -> type_error  ("Depth-1 pattern matching only: " ^
                                   "in pattern '" ^ string_of_expr pat ^
                                   "', found pattern '" ^ string_of_expr pat' ^ 
                                   "' where '" ^ x ^ "' was required."))
	  pats' (Some n) in
      check_duplicate_variable_occurances pats'' ;
      cover_linear_inside
        (MapS.add c (SetI.remove n (MapS.find c goals)) goals) 
        pats
  | (pat, _) :: _ -> type_error ("Bad pattern: " ^ string_of_expr pat)
	
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
        nonexhaustive_error (String.concat " " ("[hole]" :: c :: args)) 
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
                if Closure.is_initial subord (string_of_lambdaty ty)
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
  | (pat, _) :: _ -> type_error ("Bad pattern: " ^ string_of_expr pat)
	
(** Calculate the coverage checking problem for a type with subordination *)
let coverage_goals lty ty = 
  let lty = string_of_lambdaty lty in
  
  (* Get the set of relevant argument positions for a single constant *)
  let const_args c _ goalmap = 
    let folder (n, set) argty =
      let argty =
	match argty with 
        | VInt -> "int" 
	| VConst a -> a
	| _ -> "" in
      if argty = lty || Closure.path subord (lty, argty) 
      then (n+1, SetI.add n set)
      else (n+1, set) in
    let (_, goalset) = 
      List.fold_left folder (0, SetI.empty)
        (fst (Hashtbl.find consTable c)) in
    MapS.add c goalset goalmap in
  
  let starting_map = 
    if ty = lty then (MapS.singleton "id" SetI.empty) else MapS.empty in
  
  MapS.fold const_args (Hashtbl.find dataTable ty) starting_map
    
let coverage_goals_inside lty ty =
  (* For a list of types, find where the lty type occurs  *)
  let rec find_possible_holes n = function 
    | [] -> SetI.empty
    | VConst ty' :: tys -> 
      if lty = ty' 
      then SetI.add n (find_possible_holes (n+1) tys)
      else find_possible_holes (n+1) tys 
    | _ :: tys -> find_possible_holes (n+1) tys in

  (* Collect patterns over all the predecessor types of ty *)
  let ty_args pred_ty goalmap = 
    if Closure.path subord (lty, pred_ty) 
    then MapS.fold 
          (* Potentially add a goal map... *)
          (fun c tys goalmap -> 
            let hole_locs = find_possible_holes 0 tys in
            if SetI.is_empty hole_locs 
            then goalmap
            else MapS.add c hole_locs goalmap)
          (* ...for each constructor of the predecessor type... *)
          (Hashtbl.find dataTable pred_ty)
          (* ...to the existing goal map *)
          goalmap
    else goalmap in

  let starting_map = 
    if ty = lty then (MapS.singleton "id" SetI.empty) else MapS.empty in

  Closure.SetS.fold ty_args (Closure.imm_pred subord ty) starting_map

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
  | (Var _ | Int _ | Times _ | Plus _ | Minus _ | Equal _ | Less _) as e -> e
  | Const (c, vs, pos) -> Const (c, List.map coverage vs, pos)
  | Thunk e -> Thunk (coverage e)
  | Force e -> Force (coverage e)
  | Return e -> Return (coverage e)
  | To (e1, x, e2) -> To (coverage e1, x, coverage e2)
  | Fun (x, ty, e) -> Fun (x, ty, coverage e)
  | Lin (x, ty, e) -> Lin (x, ty, coverage e)
  | Apply (e, v) -> Apply (coverage e, coverage v)
  | Rec (x, ty, e) -> Rec (x, ty, coverage e)
  | Case' _ -> type_error "Case' statement found during typechecking?"
  | Case (e, cases, r) -> 
      (* Check for a possible inside-linear match *)
      if List.exists 
	  (function
	    | (Lin (_, _, (Apply (Var _, Const _))), _) -> true
	    | _ -> false) cases
      then 
        (Case' (coverage e, List.map (fun (pat, e) -> (pat, coverage e)) cases))
      else
        (check_simple_coverage cases ;
	 Case (coverage e, List.map (fun (pat, e) -> (pat, coverage e)) cases,
               r))
