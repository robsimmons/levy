%{
  open Syntax

  type syntax = 
    | UnkVar of name               (* How the token VAR is parsed *)
    | Ty of ltype                  (* Syntax known to be a type *)
    | Ex of expr                   (* Syntax known to be an expression *)
    | Cases of (expr * expr) list  (* Syntax known to be a case expression *)
    | Arrowey of (syntax * syntax) (* Arrows are particularly ambiguous *)

  exception Syntax_error of string

  (** [syntax_error msg] raises exception [Syntax_error msg]. *)
  let syntax_error msg = raise (Syntax_error ("Parse error: " ^ msg))

  (* Force syntax to be a type *)
  let rec mkTy = function
    | UnkVar x -> VConst x
    | Ty ty -> ty
    | Arrowey (x, y) -> CArrow (mkTy x, mkTy y)
    | Ex e -> 
      syntax_error ("badly formed type " ^ string_of_expr e ^ 
                   " parsed as an expression")
    | Cases _ -> syntax_error ("badly formed type includes a pipe symbol")

  (* Force syntax to be an expression *)
  let mkEx = function
    | UnkVar x -> Var x
    | Ex expr -> expr
    | Ty x -> syntax_error ("badly formed expression " ^ string_of_type x ^
                           " parsed as a type")
    | Cases _ -> syntax_error ("badly formed expression includes pipe")
    | Arrowey (x, y) -> 
      syntax_error ("badly formed expression includes pipe/arrow")

  (* Force syntax to be a case statement *)
  let mkCases = function
    | Cases x -> x
    | Arrowey (x, y) -> [ (mkEx x, mkEx y) ]
    | _ -> syntax_error "poorly formed case statements"

  (* Force syntax to be a (ty -> e) expression *)
  let mkFn = function
    | Arrowey (x, y) -> (mkTy x, mkEx y)
    | Ex e -> syntax_error ("function body (form 'type -> expression') " ^ 
                           " parsed as expression " ^ string_of_expr e)
    | Ty ty -> syntax_error ("function body (form 'type -> expression') " ^ 
                            " parsed as type " ^ string_of_type ty)
    | Cases _ -> syntax_error ("function body (form 'type -> expression') " ^ 
                              " includes pipe")
    | UnkVar x -> syntax_error ("function body (form 'type -> expression') " ^ 
                               " parsed as single variable " ^ x)

  (* Search for the linear occurrance within a datatype, transform the
   * expression accordingly. *)
  let rec cLinFun (x, ty) = function
    | Var y -> (x = y, Var y) 
    | Const (c, vs, None) -> 
        let folder (found_here, v) (found_later, vs, n) = 
          if found_here && found_later 
          then syntax_error ("linear " ^ x ^ " appears more than once") ; 
          if found_later then (true, v :: vs, n+1)
          else (found_here, v :: vs, n) in
        let vs' = List.map (cLinFun (x, ty)) vs in
        let (found, vs'', pos) = List.fold_right folder vs' (false, [], 0) in
        (found, Const (c, vs'', if found then Some pos else None))
    | Const (x, vs, Some _) ->
        syntax_error ("linear " ^ x ^ " shares scope with another " ^ 
                      "linear variable")
    | Apply (v1, v2) -> 
        let (found1, v1') = cLinFun (x, ty) v1 in 
        let (found2, v2') = cLinFun (x, ty) v2 in 
        if found1 && found2 
        then syntax_error ("linear " ^ x ^ " appears more than once") ; 
        (found1 || found2, Apply (v1', v2'))
    | v -> (false, v)

  let cLinFun (x, ty, e) = 
    let (occ, v) = cLinFun (x, ty) e in
    if not occ then syntax_error ("linear " ^ x ^ " did not occur") ;
    Lin (x, ty, v)    

%}

%token TINT
%token TBOOL
%token TFORGET
%token TFREE
%token <Syntax.name> VAR
%token <Syntax.name> UVAR
%token <int> INT
%token TRUE FALSE
%token PLUS
%token MINUS
%token TIMES
%token EQUAL LESS
%token IF THEN ELSE
%token FUN ARROW
%token REC IS
%token COLON
%token LPAREN RPAREN
%token LBRACK RBRACK
%token LET IN
%token LET VAL COMP IN BE
%token DO
%token TO
%token SEMICOLON2
%token RETURN THUNK FORCE
%token QUIT
%token USE
%token <string>STRING
%token COMMA
%token CARAT
%token EOF
%token DATA LOLLI
%token MATCH WITH PIPE END

%start toplevel
%type <Syntax.toplevel_cmd list> toplevel

%right PIPE
%right ARROW FUN REC RBRACK
%right TO LET DO
%nonassoc IF THEN ELSE
%right THUNK RETURN

%nonassoc EQUAL LESS
%left PLUS MINUS
%left TIMES

%right LOLLI
%right TFREE TFORGET

%%

toplevel:
  | EOF                         { [] }
  | lettop                      { $1 }
  | exprtop                     { $1 }
  | cmdtop                      { $1 }
  | DATA datatop                { Data (fst $2) :: (snd $2) }

lettop:
  | def EOF                     { [$1] }
  | def lettop                  { $1 :: $2 }
  | def SEMICOLON2 toplevel     { $1 :: $3 }

exprtop:
  | expr EOF                    { [Expr (mkEx $1)] }
  | expr SEMICOLON2 toplevel    { Expr (mkEx $1) :: $3 }

cmdtop:
  | cmd EOF                     { [$1] }
  | cmd SEMICOLON2 toplevel     { $1 :: $3 }

datatop:
  | UVAR COLON expr PIPE datatop        { (($1, mkTy $3) :: fst $5, snd $5) }
  | UVAR COLON expr EOF                 { ([ ($1, mkTy $3) ], []) }
  | UVAR COLON expr SEMICOLON2 toplevel { ([ ($1, mkTy $3) ], $5) }

cmd:
  | USE STRING                  { Use $2 }
  | QUIT                        { Quit }

def: 
  | VAL VAR EQUAL expr %prec LET { Def ($2, mkEx $4) }
  | COMP VAR EQUAL expr  %prec LET { RunDef ($2, mkEx $4) }

expr:
  | app                          { $1 }
  | infix                        { $1 }
  | LET expr BE expr IN expr %prec LET { Ex (cLet (mkEx $2, mkEx $4, mkEx $6)) }
  | expr TO VAR IN expr %prec TO { Ex (To (mkEx $1, $3, mkEx $5)) }
  | IF expr THEN expr ELSE expr  { Ex (cIf (mkEx $2, mkEx $4, mkEx $6)) }
  | FUN VAR COLON expr %prec FUN { Ex (Fun ($2, fst (mkFn $4), snd (mkFn $4))) }
  | REC VAR COLON expr IS expr  %prec REC { Ex (Rec ($2, mkTy $4, mkEx $6)) }
  | MATCH expr WITH PIPE expr    { Ex (Case (mkEx $2, mkCases $5)) }
  | RETURN expr                  { Ex (Return (mkEx $2)) }
  | THUNK expr                   { Ex (Thunk (mkEx $2)) }
  | TFORGET expr                 { Ty (VForget (mkTy $2)) }
  | TFREE expr                   { Ty (CFree (mkTy $2)) }
  | LBRACK VAR COLON expr RBRACK expr { Ex (cLinFun ($2, mkTy $4, mkEx $6)) }
  
app:
  | atm                         { $1 }
  | FORCE atm                   { Ex (Force (mkEx $2)) }
  | app atm                     { Ex (cApply (mkEx $1, mkEx $2)) }

atm:
  | VAR                         { UnkVar $1 }
  | UVAR                        { Ex (Const ($1, [], None)) }
  | TRUE                        { Ex (Const ("true", [], None)) }
  | FALSE                       { Ex (Const ("false", [], None)) }
  | INT                         { Ex (Int $1) }
  | TINT                        { Ty (VInt) }
  | TBOOL                       { Ty (VConst "bool") }
  | LPAREN expr RPAREN          { $2 }    

infix:
  | MINUS INT                   { Ex (Int (-$2)) }
  | expr PLUS expr              { Ex (Plus (mkEx $1, mkEx $3)) }
  | expr MINUS expr             { Ex (Minus (mkEx $1, mkEx $3)) }
  | expr TIMES expr             { Ex (Times (mkEx $1, mkEx $3)) }
  | expr EQUAL expr             { Ex (Equal (mkEx $1, mkEx $3)) }
  | expr LESS expr              { Ex (Less (mkEx $1, mkEx $3)) }
  | expr PIPE expr              { Cases (mkCases $1 @ mkCases $3) }
  | expr LOLLI expr             { Ty (VLolli (mkTy $1, mkTy $3)) }
  | expr ARROW expr             { Arrowey ($1, $3) }


%%
