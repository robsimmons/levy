%{
  open Syntax

  type syntax = 
    | UnkVar of name              (* How the token VAR is parsed *)
    | Ty of ltype                 (* Syntax known to be a type *)
    | Ex of expr                  (* Syntax known to be an expression *)
    | Cases of (expr * expr) list (* Syntax known to be a case expression *)

  exception Parse_error of string

  (* Force syntax to be a type *)
  let mkTy = function
    | UnkVar x -> VConst x
    | Ty ty -> ty
    | Ex _ -> raise (Parse_error "expression found where type was required")
    | Cases _ -> raise (Parse_error "badly formed type?")

  (* Force syntax to be an expression *)
  let mkEx = function
    | UnkVar x -> Var x
    | Ty _ -> raise (Parse_error "type found where expression was required")
    | Ex expr -> expr
    | Cases _ -> raise (Parse_error "cases found without match expression")

  (* Force syntax to be a case statement *)
  let mkCases = function
    | Cases x -> x
    | _ -> raise (Parse_error "poorly formed case statements")

  (* Handle | *)
  let cPipe = function 
    | (Cases x, Cases y) -> Cases (x @ y)
    | _ -> raise (Parse_error "poorly formed case statements")

  (* Handle -> *)
  let cArrow = function
    | (Ty x, y) -> Ty (CArrow (x, mkTy y))
    | (x, Ty y) -> Ty (CArrow (mkTy x, y))
    | (x, y) -> Cases [ (mkEx x, mkEx y) ]
      (* Due to the fact that type variables are values, ("x -> y") can only
       * be a case, not a pattern *)
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
%token LET IN
%token TO
%token SEMICOLON2
%token RETURN THUNK FORCE
%token QUIT
%token USE
%token <string>STRING
%token COMMA
%token EOF
%token DATA LOLLI
%token MATCH WITH PIPE END

%start toplevel
%type <Syntax.toplevel_cmd list> toplevel

%right PIPE
%nonassoc TO 
%nonassoc LET IN
%right ARROW LOLLI
%nonassoc FUN REC IS
%nonassoc IF THEN ELSE
%nonassoc EQUAL LESS 
%left PLUS MINUS
%left TIMES
%right TFREE TFORGET

%%

toplevel:
  | EOF                      { [] }
  | lettop                   { $1 }
  | exprtop                  { $1 }
  | cmdtop                   { $1 }
  | DATA datatop             { Data (fst $2) :: (snd $2) }

lettop:
  | def EOF                  { [$1] }
  | def lettop               { $1 :: $2 }
  | def SEMICOLON2 toplevel  { $1 :: $3 }

exprtop:
  | expr EOF                 { [Expr (mkEx $1)] }
  | expr SEMICOLON2 toplevel { Expr (mkEx $1) :: $3 }

cmdtop:
  | cmd EOF                  { [$1] }
  | cmd SEMICOLON2 toplevel  { $1 :: $3 }

datatop:
  | UVAR COLON expr PIPE datatop         { (($1, mkTy $3) :: (fst $5), (snd $5)) }
  | UVAR COLON expr EOF                 { ([ ($1, mkTy $3) ], []) }
  | UVAR COLON expr SEMICOLON2 toplevel { ([ ($1, mkTy $3) ], $5) }

cmd:
  | USE STRING { Use $2 }
  | QUIT       { Quit }

def: LET VAR EQUAL expr          { Def ($2, mkEx $4) }

expr:
  | app                           { $1 }
  | infixed                       { $1 }
  | LET VAR EQUAL expr IN expr    { Ex (cLet ($2, mkEx $4, mkEx $6)) }
  | expr TO VAR IN expr           { Ex (To (mkEx $1, $3, mkEx $5)) }
  | IF expr THEN expr ELSE expr   { Ex (cIf (mkEx $2, mkEx $4, mkEx $6)) }
  | FUN VAR COLON expr ARROW expr { Ex (Fun ($2, mkTy $4, mkEx $6)) }
  | REC VAR COLON expr IS expr    { Ex (Rec ($2, mkTy $4, mkEx $6)) }
  | MATCH expr WITH PIPE expr     { Ex (Case (mkEx $2, mkCases $5)) }

app:
  | atm                           { $1 }
  | FORCE atm                     { Ex (Force (mkEx $2)) }
  | RETURN atm                    { Ex (Return (mkEx $2)) }
  | THUNK atm                     { Ex (Thunk (mkEx $2)) }
  | app atm                       { Ex (cApply (mkEx $1, mkEx $2)) }

atm:
  | VAR                           { UnkVar $1 }

  | UVAR                          { Ex (Const ($1, [])) }
  | TRUE                          { Ex (Const ("true", [])) }
  | FALSE                         { Ex (Const ("false", [])) }
  | INT                           { Ex (Int $1) }

  | TINT         	          { Ty (VInt) }
  | TBOOL	 	          { Ty (VConst "bool") }
  | TFORGET atm                   { Ty (VForget (mkTy $2)) }
  | TFREE atm                     { Ty (CFree (mkTy $2)) }
  | atm LOLLI atm                 { Ty (VLolli (mkTy $1, mkTy $3)) }
 
  | LPAREN expr RPAREN            { $2 }    

infixed:
  | MINUS INT                     { Ex (Int (-$2)) }
  | expr PLUS expr                { Ex (Plus (mkEx $1, mkEx $3)) }
  | expr MINUS expr               { Ex (Minus (mkEx $1, mkEx $3)) }
  | expr TIMES expr	          { Ex (Times (mkEx $1, mkEx $3)) }
  | expr EQUAL expr               { Ex (Equal (mkEx $1, mkEx $3)) }
  | expr LESS expr                { Ex (Less (mkEx $1, mkEx $3)) }

  | expr ARROW expr               { cArrow ($1, $3) }
  | expr PIPE expr                { cPipe ($1, $3) }

%%
