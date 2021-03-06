{
  open Parser
  open Lexing

  let incr_linenum lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

let var = ['_' 'a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*

rule token = parse
  | '#' [^'\n']* '\n' { incr_linenum lexbuf; token lexbuf }
  | '\n'            { incr_linenum lexbuf; token lexbuf }
  | [' ' '\t']      { token lexbuf }
  | ['0'-'9']+      { INT (int_of_string(lexeme lexbuf)) }

  | 'U'             { TFORGET }
  | 'F'             { TFREE }
  | "->"            { ARROW }
  | "bool"          { TBOOL }
  | "int"           { TINT }

  | "do"            { DO }
  | "else"          { ELSE }
  | "false"         { FALSE }
  | "force"         { FORCE }
  | "fun"           { FUN }
  | "if"            { IF }
  | "in"            { IN }
  | "is"            { IS }
  | "let"           { LET }  
  | "rec"           { REC }
  | "return"        { RETURN }
  | "then"          { THEN }
  | "thunk"         { THUNK }
  | "to"            { TO }
  | "true"          { TRUE }

  | "$use"           { USE }
  | "$quit"          { QUIT }
  | ";;"            { SEMICOLON2 }
  | '\"' [^'\"']* '\"' { let str = lexeme lexbuf in
			STRING (String.sub str 1 (String.length str - 2)) }

  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '*'             { TIMES }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | ':'             { COLON }
  | '<'             { LESS }
  | '='             { EQUAL }

  | var             { VAR (lexeme lexbuf) }
  | eof             { EOF }

{
}
