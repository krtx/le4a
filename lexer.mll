{
open Parser

let reservedWords = [
  (* Keywords *)
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("in", Parser.IN);
  ("let", Parser.LET);
  ("and", Parser.AND);
  ("fun", Parser.FUN);
  ("rec", Parser.REC);
  ("dfun", Parser.DFUN);
  ("match", Parser.MATCH);
  ("with", Parser.WITH);
  ("as", Parser.AS);
  ("when", Parser.WHEN);
  (* infix operations *)
  ("mod", Parser.MOD "mod");
  ("land", Parser.LAND "land");
  ("lor", Parser.LOR "lor");
  ("lxor", Parser.LXOR "lxor");
  ("lsl", Parser.LSL "lsl");
  ("lsr", Parser.LSR "lsr");
  ("asr", Parser.ASR "asr");
  ("or", Parser.OR "or");
]

exception End_of_file
}

let operator_char = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "-"? ['0'-'9']+
    { INTV (int_of_string (Lexing.lexeme lexbuf)) }

| "(*" { comments 0 lexbuf }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| ";;" { SEMISEMI }
| ";" { SEMICOLON }
| "::" { CONS (Lexing.lexeme lexbuf) }
| "->" { Parser.RARROW }
| "_" { UNDERSCORE }
| "=" { EQUAL (Lexing.lexeme lexbuf) }

| "|" { VBAR }
| "&" { AMPERSAND (Lexing.lexeme lexbuf) }
| "&&" { BAND (Lexing.lexeme lexbuf) }
| "||" { BOR (Lexing.lexeme lexbuf) }

| "=" operator_char+ { EQUALOP (Lexing.lexeme lexbuf) }
| "<" operator_char* { LCHEVRON (Lexing.lexeme lexbuf) }
| ">" operator_char* { RCHEVRON (Lexing.lexeme lexbuf) }
| "@" operator_char* { AT (Lexing.lexeme lexbuf) }
| "^" operator_char* { CARET (Lexing.lexeme lexbuf) }
| "|" ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' (* missing vbar *) '~'] operator_char* { VBAROP (Lexing.lexeme lexbuf) }
| "&" ['!' '$' '%' (* missing ampersand *) '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] operator_char* { AMPERSANDOP (Lexing.lexeme lexbuf) }
| "+" operator_char* { PLUS (Lexing.lexeme lexbuf) }
| "-" operator_char* { HYPHEN (Lexing.lexeme lexbuf) }
| "*"
| "*" ['!' '$' '%' '&' (* missing asterisk *) '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] operator_char* { ASTERISK (Lexing.lexeme lexbuf) }
| "**" operator_char* { ASTERISKTWO (Lexing.lexeme lexbuf) }
| "/" operator_char* { SLASH (Lexing.lexeme lexbuf) }
| "$" operator_char* { DOLLAR (Lexing.lexeme lexbuf) }
| "%" operator_char* { PERCENT (Lexing.lexeme lexbuf) }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| eof { EOF }

and comments level = parse
    | "*)" { if level = 0 then main lexbuf else comments (level - 1) lexbuf }
    | "(*" { comments (level + 1) lexbuf }
    | _ { comments level lexbuf }
