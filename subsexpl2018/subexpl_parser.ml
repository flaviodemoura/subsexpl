type token =
  | IDENT of (string)
  | LAMBDA
  | DOT
  | COMMA
  | OPEN_PARENTHESIS
  | CLOSE_PARENTHESIS
  | EOL

open Parsing;;
# 4 "subexpl_parser.mly"
  open Translation
  exception Eof
# 15 "subexpl_parser.ml"
let yytransl_const = [|
  258 (* LAMBDA *);
  259 (* DOT *);
  260 (* COMMA *);
  261 (* OPEN_PARENTHESIS *);
  262 (* CLOSE_PARENTHESIS *);
  263 (* EOL *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\004\000\004\000\005\000\005\000\005\000\
\002\000\000\000"

let yylen = "\002\000\
\002\000\001\000\003\000\001\000\002\000\001\000\003\000\004\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\006\000\000\000\000\000\010\000\000\000\009\000\
\000\000\000\000\000\000\000\000\001\000\005\000\000\000\000\000\
\007\000\003\000\008\000"

let yydgoto = "\002\000\
\006\000\007\000\011\000\008\000\009\000"

let yysindex = "\005\000\
\000\255\000\000\000\000\006\255\000\255\000\000\001\255\000\000\
\000\255\005\255\007\255\008\255\000\000\000\000\006\255\000\255\
\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\253\254\009\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\251\255\254\255\006\000\000\000"

let yytablesize = 15
let yytable = "\012\000\
\003\000\004\000\004\000\004\000\005\000\001\000\010\000\013\000\
\015\000\016\000\019\000\002\000\018\000\017\000\014\000"

let yycheck = "\005\000\
\001\001\002\001\006\001\007\001\005\001\001\000\001\001\007\001\
\004\001\003\001\016\000\003\001\015\000\006\001\009\000"

let yynames_const = "\
  LAMBDA\000\
  DOT\000\
  COMMA\000\
  OPEN_PARENTHESIS\000\
  CLOSE_PARENTHESIS\000\
  EOL\000\
  "

let yynames_block = "\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 17 "subexpl_parser.mly"
                              ( _1 )
# 87 "subexpl_parser.ml"
               : Translation.lambda_sentence))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 21 "subexpl_parser.mly"
                        ( [_1] )
# 94 "subexpl_parser.ml"
               : 'ident_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ident_list) in
    Obj.repr(
# 22 "subexpl_parser.mly"
                              ( _1 :: _3 )
# 102 "subexpl_parser.ml"
               : 'ident_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'no_recursion_expl) in
    Obj.repr(
# 25 "subexpl_parser.mly"
                                              ( [_1] )
# 109 "subexpl_parser.ml"
               : 'expr_application_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'no_recursion_expl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr_application_list) in
    Obj.repr(
# 26 "subexpl_parser.mly"
                                              ( _1 :: _2 )
# 117 "subexpl_parser.ml"
               : 'expr_application_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 29 "subexpl_parser.mly"
                                              ( Identifier(_1) )
# 124 "subexpl_parser.ml"
               : 'no_recursion_expl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 30 "subexpl_parser.mly"
                                              ( _2 )
# 131 "subexpl_parser.ml"
               : 'no_recursion_expl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'ident_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 31 "subexpl_parser.mly"
                                              ( (construct_lambdas _2 _4) )
# 139 "subexpl_parser.ml"
               : 'no_recursion_expl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr_application_list) in
    Obj.repr(
# 34 "subexpl_parser.mly"
                                              ( (construct_applications _1) )
# 146 "subexpl_parser.ml"
               : 'expr))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Translation.lambda_sentence)
