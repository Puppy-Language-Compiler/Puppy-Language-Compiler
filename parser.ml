type token =
  | EOF
  | NIL
  | VAR
  | WHILE
  | FOR
  | TO
  | BREAK
  | LET
  | IN
  | END
  | FUNCTION
  | TYPE
  | ARRAY
  | IF
  | THEN
  | ELSE
  | DO
  | OF
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACKET
  | RBRACKET
  | COMMA
  | DOT
  | SEMICOLON
  | COLON
  | ASSIGN
  | PLUS
  | MINUS
  | TIMES
  | DIVIDE
  | OR
  | AND
  | EQUAL
  | NOTEQUAL
  | LT
  | LE
  | GT
  | GE
  | STRING of (string)
  | ID of (string)
  | INT of (int)

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
  open Printf

  let parse_error s =
    print_endline s;
    flush stdout

  let mk_pos i =
    Parsing.rhs_start_pos i
# 59 "parser.ml"
let yytransl_const = [|
    0 (* EOF *);
  257 (* NIL *);
  258 (* VAR *);
  259 (* WHILE *);
  260 (* FOR *);
  261 (* TO *);
  262 (* BREAK *);
  263 (* LET *);
  264 (* IN *);
  265 (* END *);
  266 (* FUNCTION *);
  267 (* TYPE *);
  268 (* ARRAY *);
  269 (* IF *);
  270 (* THEN *);
  271 (* ELSE *);
  272 (* DO *);
  273 (* OF *);
  274 (* LPAREN *);
  275 (* RPAREN *);
  276 (* LBRACE *);
  277 (* RBRACE *);
  278 (* LBRACKET *);
  279 (* RBRACKET *);
  280 (* COMMA *);
  281 (* DOT *);
  282 (* SEMICOLON *);
  283 (* COLON *);
  284 (* ASSIGN *);
  285 (* PLUS *);
  286 (* MINUS *);
  287 (* TIMES *);
  288 (* DIVIDE *);
  289 (* OR *);
  290 (* AND *);
  291 (* EQUAL *);
  292 (* NOTEQUAL *);
  293 (* LT *);
  294 (* LE *);
  295 (* GT *);
  296 (* GE *);
    0|]

let yytransl_block = [|
  297 (* STRING *);
  298 (* ID *);
  299 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\004\000\004\000\004\000\005\000\
\008\000\008\000\008\000\009\000\009\000\009\000\010\000\006\000\
\007\000\007\000\011\000\012\000\012\000\013\000\013\000\013\000\
\013\000\013\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\014\000\014\000\015\000\
\015\000\020\000\016\000\016\000\016\000\017\000\017\000\017\000\
\017\000\018\000\018\000\018\000\018\000\018\000\018\000\019\000\
\019\000\000\000"

let yylen = "\002\000\
\002\000\000\000\001\000\002\000\001\000\001\000\001\000\004\000\
\001\000\003\000\003\000\000\000\001\000\003\000\003\000\004\000\
\001\000\002\000\008\000\000\000\002\000\001\000\003\000\003\000\
\004\000\004\000\001\000\001\000\003\000\001\000\001\000\002\000\
\004\000\004\000\006\000\003\000\003\000\003\000\005\000\003\000\
\004\000\006\000\004\000\008\000\001\000\001\000\003\000\001\000\
\003\000\003\000\000\000\001\000\003\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\027\000\000\000\000\000\045\000\000\000\000\000\
\000\000\000\000\031\000\000\000\030\000\066\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\003\000\005\000\
\006\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\054\000\055\000\056\000\057\000\
\065\000\064\000\062\000\063\000\058\000\059\000\060\000\061\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\004\000\018\000\000\000\029\000\
\000\000\000\000\000\000\000\000\000\000\048\000\000\000\023\000\
\000\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\034\000\000\000\
\000\000\033\000\000\000\000\000\026\000\000\000\000\000\000\000\
\000\000\013\000\000\000\000\000\009\000\008\000\039\000\000\000\
\000\000\000\000\049\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\015\000\000\000\000\000\
\014\000\011\000\010\000\000\000\021\000\000\000\000\000"

let yydgoto = "\002\000\
\014\000\015\000\022\000\023\000\024\000\025\000\026\000\102\000\
\097\000\098\000\027\000\120\000\016\000\030\000\069\000\067\000\
\049\000\050\000\051\000\070\000"

let yysindex = "\007\000\
\065\255\000\000\000\000\065\255\227\254\000\000\052\255\065\255\
\065\255\065\255\000\000\245\254\000\000\000\000\130\000\064\255\
\243\254\016\255\023\255\055\255\061\255\027\255\000\000\000\000\
\000\000\102\255\000\000\143\255\105\001\017\255\079\255\065\255\
\073\255\065\255\074\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\065\255\065\255\065\255\065\255\078\255\065\255\065\255\065\255\
\086\255\099\255\084\255\065\255\000\000\000\000\065\255\000\000\
\065\255\105\001\056\255\088\255\247\254\000\000\201\255\000\000\
\105\001\105\001\105\001\042\001\000\000\105\001\105\001\104\255\
\065\255\082\255\246\254\116\255\181\255\105\001\000\000\065\255\
\065\255\000\000\073\255\109\255\000\000\065\255\105\001\094\255\
\057\255\000\000\110\255\082\255\000\000\000\000\000\000\065\255\
\105\001\105\001\000\000\065\255\168\255\087\255\101\255\082\255\
\089\255\010\255\105\001\105\001\065\255\000\000\090\255\123\255\
\000\000\000\000\000\000\105\001\000\000\065\255\105\001"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\151\255\000\000\
\000\000\000\000\000\000\040\000\000\000\000\000\000\000\079\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\062\255\000\000\000\000\034\255\000\000\118\000\063\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\069\255\000\000\000\000\000\000\000\000\000\000\000\000\
\169\000\189\000\209\000\000\000\000\000\229\000\249\000\000\000\
\000\000\072\255\000\000\000\000\107\001\048\255\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\000\000\031\255\000\000\
\000\000\000\000\000\000\077\255\000\000\000\000\000\000\000\000\
\075\255\081\255\000\000\000\000\000\000\000\000\125\255\000\000\
\000\000\000\000\013\001\043\001\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\082\001\000\000\000\000\047\255"

let yygindex = "\000\000\
\000\000\252\255\000\000\139\000\000\000\000\000\000\000\000\000\
\062\000\051\000\138\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\074\000"

let yytablesize = 657
let yytable = "\017\000\
\025\000\099\000\055\000\028\000\029\000\031\000\032\000\001\000\
\033\000\100\000\034\000\090\000\018\000\035\000\091\000\037\000\
\038\000\039\000\040\000\041\000\042\000\043\000\044\000\045\000\
\046\000\047\000\048\000\066\000\019\000\071\000\123\000\101\000\
\016\000\112\000\060\000\064\000\020\000\021\000\016\000\022\000\
\016\000\016\000\065\000\056\000\073\000\074\000\075\000\076\000\
\019\000\078\000\079\000\080\000\046\000\019\000\019\000\084\000\
\019\000\019\000\085\000\046\000\086\000\020\000\021\000\007\000\
\057\000\003\000\047\000\004\000\005\000\007\000\006\000\007\000\
\007\000\047\000\087\000\111\000\095\000\008\000\028\000\088\000\
\112\000\051\000\009\000\105\000\106\000\052\000\051\000\052\000\
\053\000\109\000\012\000\054\000\052\000\053\000\010\000\012\000\
\058\000\012\000\053\000\115\000\012\000\050\000\059\000\116\000\
\050\000\011\000\012\000\013\000\094\000\039\000\040\000\020\000\
\124\000\081\000\068\000\072\000\082\000\032\000\083\000\077\000\
\110\000\127\000\089\000\096\000\103\000\108\000\113\000\119\000\
\118\000\036\000\122\000\125\000\037\000\038\000\039\000\040\000\
\041\000\042\000\043\000\044\000\045\000\046\000\047\000\048\000\
\037\000\038\000\039\000\040\000\041\000\042\000\043\000\044\000\
\045\000\046\000\047\000\048\000\063\000\126\000\002\000\020\000\
\061\000\114\000\121\000\062\000\107\000\000\000\000\000\000\000\
\036\000\000\000\000\000\037\000\038\000\039\000\040\000\041\000\
\042\000\043\000\044\000\045\000\046\000\047\000\048\000\117\000\
\000\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\
\000\000\000\000\000\000\104\000\037\000\038\000\039\000\040\000\
\041\000\042\000\043\000\044\000\045\000\046\000\047\000\048\000\
\038\000\037\000\038\000\039\000\040\000\041\000\042\000\043\000\
\044\000\045\000\046\000\047\000\048\000\000\000\000\000\092\000\
\000\000\000\000\000\000\000\000\040\000\037\000\038\000\039\000\
\040\000\041\000\042\000\043\000\044\000\045\000\046\000\047\000\
\048\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\043\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\025\000\000\000\000\000\025\000\000\000\000\000\
\025\000\025\000\025\000\025\000\042\000\000\000\025\000\025\000\
\025\000\000\000\000\000\025\000\000\000\025\000\025\000\025\000\
\025\000\025\000\025\000\000\000\025\000\025\000\025\000\025\000\
\025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
\025\000\022\000\035\000\000\000\022\000\000\000\000\000\022\000\
\022\000\022\000\022\000\000\000\000\000\022\000\022\000\022\000\
\000\000\000\000\022\000\000\000\022\000\000\000\022\000\022\000\
\000\000\022\000\000\000\022\000\022\000\022\000\022\000\022\000\
\022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
\028\000\044\000\000\000\028\000\000\000\000\000\028\000\028\000\
\028\000\028\000\000\000\000\000\028\000\028\000\028\000\000\000\
\000\000\028\000\000\000\028\000\000\000\028\000\028\000\000\000\
\028\000\000\000\041\000\028\000\028\000\028\000\028\000\028\000\
\028\000\028\000\028\000\028\000\028\000\028\000\028\000\032\000\
\000\000\000\000\032\000\000\000\000\000\032\000\032\000\032\000\
\032\000\000\000\000\000\032\000\032\000\032\000\000\000\000\000\
\032\000\000\000\032\000\000\000\032\000\032\000\000\000\032\000\
\000\000\000\000\032\000\032\000\000\000\000\000\032\000\032\000\
\032\000\032\000\032\000\032\000\032\000\032\000\037\000\038\000\
\039\000\040\000\041\000\042\000\043\000\044\000\045\000\046\000\
\047\000\048\000\036\000\000\000\000\000\036\000\000\000\000\000\
\036\000\036\000\036\000\036\000\000\000\000\000\036\000\036\000\
\036\000\000\000\000\000\036\000\000\000\036\000\037\000\036\000\
\036\000\037\000\036\000\000\000\037\000\037\000\037\000\037\000\
\000\000\000\000\037\000\037\000\037\000\000\000\000\000\037\000\
\000\000\037\000\038\000\037\000\037\000\038\000\037\000\000\000\
\038\000\038\000\038\000\038\000\000\000\000\000\038\000\038\000\
\038\000\000\000\000\000\038\000\000\000\038\000\040\000\038\000\
\038\000\040\000\038\000\000\000\040\000\040\000\040\000\040\000\
\000\000\000\000\040\000\040\000\040\000\000\000\000\000\040\000\
\000\000\040\000\043\000\040\000\040\000\043\000\040\000\000\000\
\043\000\043\000\043\000\043\000\000\000\000\000\043\000\043\000\
\043\000\000\000\000\000\043\000\000\000\043\000\042\000\043\000\
\043\000\042\000\043\000\000\000\042\000\042\000\042\000\042\000\
\000\000\000\000\042\000\042\000\042\000\000\000\000\000\042\000\
\000\000\042\000\000\000\042\000\042\000\000\000\042\000\000\000\
\000\000\000\000\000\000\000\000\035\000\000\000\000\000\035\000\
\000\000\000\000\035\000\035\000\035\000\035\000\000\000\000\000\
\035\000\035\000\035\000\000\000\000\000\035\000\000\000\035\000\
\093\000\035\000\035\000\000\000\035\000\000\000\037\000\038\000\
\039\000\040\000\041\000\042\000\043\000\044\000\045\000\046\000\
\047\000\048\000\000\000\044\000\000\000\000\000\044\000\000\000\
\000\000\044\000\044\000\044\000\044\000\000\000\000\000\044\000\
\044\000\044\000\000\000\000\000\044\000\000\000\044\000\000\000\
\044\000\044\000\000\000\044\000\041\000\000\000\000\000\041\000\
\000\000\000\000\041\000\041\000\041\000\041\000\000\000\000\000\
\041\000\000\000\041\000\000\000\000\000\041\000\000\000\041\000\
\000\000\041\000\041\000\000\000\041\000\037\000\038\000\039\000\
\040\000\041\000\042\000\043\000\044\000\045\000\046\000\047\000\
\048\000"

let yycheck = "\004\000\
\000\000\012\001\016\001\008\000\009\000\010\000\018\001\001\000\
\020\001\020\001\022\001\021\001\042\001\025\001\024\001\029\001\
\030\001\031\001\032\001\033\001\034\001\035\001\036\001\037\001\
\038\001\039\001\040\001\032\000\002\001\034\000\021\001\042\001\
\002\001\024\001\008\001\019\001\010\001\011\001\008\001\000\000\
\010\001\011\001\026\001\028\001\049\000\050\000\051\000\052\000\
\002\001\054\000\055\000\056\000\019\001\002\001\008\001\060\000\
\010\001\011\001\063\000\026\001\065\000\010\001\011\001\002\001\
\042\001\001\001\019\001\003\001\004\001\008\001\006\001\007\001\
\011\001\026\001\019\001\019\001\081\000\013\001\000\000\024\001\
\024\001\019\001\018\001\088\000\089\000\022\001\024\001\019\001\
\025\001\094\000\019\001\028\001\024\001\019\001\030\001\024\001\
\042\001\021\001\024\001\104\000\024\001\021\001\042\001\108\000\
\024\001\041\001\042\001\043\001\005\001\031\001\032\001\010\001\
\117\000\028\001\042\001\042\001\018\001\000\000\035\001\042\001\
\027\001\126\000\035\001\042\001\009\001\017\001\017\001\027\001\
\042\001\000\000\042\001\042\001\029\001\030\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\029\001\030\001\031\001\032\001\033\001\034\001\035\001\036\001\
\037\001\038\001\039\001\040\001\014\001\035\001\008\001\035\001\
\022\000\100\000\112\000\026\000\091\000\255\255\255\255\255\255\
\000\000\255\255\255\255\029\001\030\001\031\001\032\001\033\001\
\034\001\035\001\036\001\037\001\038\001\039\001\040\001\016\001\
\255\255\255\255\255\255\255\255\000\000\255\255\255\255\255\255\
\255\255\255\255\255\255\015\001\029\001\030\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\000\000\029\001\030\001\031\001\032\001\033\001\034\001\035\001\
\036\001\037\001\038\001\039\001\040\001\255\255\255\255\023\001\
\255\255\255\255\255\255\255\255\000\000\029\001\030\001\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\002\001\255\255\255\255\005\001\255\255\255\255\
\008\001\009\001\010\001\011\001\000\000\255\255\014\001\015\001\
\016\001\255\255\255\255\019\001\255\255\021\001\022\001\023\001\
\024\001\025\001\026\001\255\255\028\001\029\001\030\001\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\002\001\000\000\255\255\005\001\255\255\255\255\008\001\
\009\001\010\001\011\001\255\255\255\255\014\001\015\001\016\001\
\255\255\255\255\019\001\255\255\021\001\255\255\023\001\024\001\
\255\255\026\001\255\255\028\001\029\001\030\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\002\001\000\000\255\255\005\001\255\255\255\255\008\001\009\001\
\010\001\011\001\255\255\255\255\014\001\015\001\016\001\255\255\
\255\255\019\001\255\255\021\001\255\255\023\001\024\001\255\255\
\026\001\255\255\000\000\029\001\030\001\031\001\032\001\033\001\
\034\001\035\001\036\001\037\001\038\001\039\001\040\001\002\001\
\255\255\255\255\005\001\255\255\255\255\008\001\009\001\010\001\
\011\001\255\255\255\255\014\001\015\001\016\001\255\255\255\255\
\019\001\255\255\021\001\255\255\023\001\024\001\255\255\026\001\
\255\255\255\255\029\001\030\001\255\255\255\255\033\001\034\001\
\035\001\036\001\037\001\038\001\039\001\040\001\029\001\030\001\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\040\001\002\001\255\255\255\255\005\001\255\255\255\255\
\008\001\009\001\010\001\011\001\255\255\255\255\014\001\015\001\
\016\001\255\255\255\255\019\001\255\255\021\001\002\001\023\001\
\024\001\005\001\026\001\255\255\008\001\009\001\010\001\011\001\
\255\255\255\255\014\001\015\001\016\001\255\255\255\255\019\001\
\255\255\021\001\002\001\023\001\024\001\005\001\026\001\255\255\
\008\001\009\001\010\001\011\001\255\255\255\255\014\001\015\001\
\016\001\255\255\255\255\019\001\255\255\021\001\002\001\023\001\
\024\001\005\001\026\001\255\255\008\001\009\001\010\001\011\001\
\255\255\255\255\014\001\015\001\016\001\255\255\255\255\019\001\
\255\255\021\001\002\001\023\001\024\001\005\001\026\001\255\255\
\008\001\009\001\010\001\011\001\255\255\255\255\014\001\015\001\
\016\001\255\255\255\255\019\001\255\255\021\001\002\001\023\001\
\024\001\005\001\026\001\255\255\008\001\009\001\010\001\011\001\
\255\255\255\255\014\001\015\001\016\001\255\255\255\255\019\001\
\255\255\021\001\255\255\023\001\024\001\255\255\026\001\255\255\
\255\255\255\255\255\255\255\255\002\001\255\255\255\255\005\001\
\255\255\255\255\008\001\009\001\010\001\011\001\255\255\255\255\
\014\001\015\001\016\001\255\255\255\255\019\001\255\255\021\001\
\023\001\023\001\024\001\255\255\026\001\255\255\029\001\030\001\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\040\001\255\255\002\001\255\255\255\255\005\001\255\255\
\255\255\008\001\009\001\010\001\011\001\255\255\255\255\014\001\
\015\001\016\001\255\255\255\255\019\001\255\255\021\001\255\255\
\023\001\024\001\255\255\026\001\002\001\255\255\255\255\005\001\
\255\255\255\255\008\001\009\001\010\001\011\001\255\255\255\255\
\014\001\255\255\016\001\255\255\255\255\019\001\255\255\021\001\
\255\255\023\001\024\001\255\255\026\001\029\001\030\001\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001"

let yynames_const = "\
  EOF\000\
  NIL\000\
  VAR\000\
  WHILE\000\
  FOR\000\
  TO\000\
  BREAK\000\
  LET\000\
  IN\000\
  END\000\
  FUNCTION\000\
  TYPE\000\
  ARRAY\000\
  IF\000\
  THEN\000\
  ELSE\000\
  DO\000\
  OF\000\
  LPAREN\000\
  RPAREN\000\
  LBRACE\000\
  RBRACE\000\
  LBRACKET\000\
  RBRACKET\000\
  COMMA\000\
  DOT\000\
  SEMICOLON\000\
  COLON\000\
  ASSIGN\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIVIDE\000\
  OR\000\
  AND\000\
  EQUAL\000\
  NOTEQUAL\000\
  LT\000\
  LE\000\
  GT\000\
  GE\000\
  "

let yynames_block = "\
  STRING\000\
  ID\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 45 "parser.mly"
          ( _1 )
# 424 "parser.ml"
               : Absyn.exp))
; (fun __caml_parser_env ->
    Obj.repr(
# 48 "parser.mly"
        ( [] )
# 430 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 49 "parser.mly"
        ( _1 :: [] )
# 437 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 50 "parser.mly"
             ( _2 :: _1 )
# 445 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tydec) in
    Obj.repr(
# 53 "parser.mly"
          ( _1 )
# 452 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'vardec) in
    Obj.repr(
# 54 "parser.mly"
           ( _1 )
# 459 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fundecs) in
    Obj.repr(
# 55 "parser.mly"
            ( Absyn.FunctionDec(_1) )
# 466 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'ty) in
    Obj.repr(
# 58 "parser.mly"
                     ( Absyn.TypeDec{name = Symbol.symbol _2; ty = _4; pos = mk_pos 1} )
# 474 "parser.ml"
               : 'tydec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 61 "parser.mly"
       ( Absyn.NameTy(Symbol.symbol _1, mk_pos 1) )
# 481 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'tyfields) in
    Obj.repr(
# 62 "parser.mly"
                           ( Absyn.RecordTy( _2 ) )
# 488 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 63 "parser.mly"
                ( Absyn.ArrayTy(Symbol.symbol _3, mk_pos 1) )
# 495 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    Obj.repr(
# 66 "parser.mly"
            ( [] )
# 501 "parser.ml"
               : 'tyfields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tyfield) in
    Obj.repr(
# 67 "parser.mly"
            ( _1 :: [] )
# 508 "parser.ml"
               : 'tyfields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'tyfields) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tyfield) in
    Obj.repr(
# 68 "parser.mly"
                           ( _3 :: _1 )
# 516 "parser.ml"
               : 'tyfields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 71 "parser.mly"
                ( {name = Symbol.symbol _1; escape = ref true; typ = Symbol.symbol _3; pos = mk_pos 1} )
# 524 "parser.ml"
               : 'tyfield))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 73 "parser.mly"
                      ( Absyn.VarDec{name = Symbol.symbol _2; escape = ref true; typ = None; init = _4; pos = mk_pos 1} )
# 532 "parser.ml"
               : 'vardec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fundec) in
    Obj.repr(
# 76 "parser.mly"
                   ( _1 :: [] )
# 539 "parser.ml"
               : 'fundecs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'fundecs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fundec) in
    Obj.repr(
# 77 "parser.mly"
                   ( _2 :: _1 )
# 547 "parser.ml"
               : 'fundecs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'tyfields) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'resultty) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 79 "parser.mly"
                                                          ( {name = Symbol.symbol _2; params = _4; result = _6; body = _8; pos = mk_pos 1} )
# 557 "parser.ml"
               : 'fundec))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "parser.mly"
          ( None )
# 563 "parser.ml"
               : 'resultty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 83 "parser.mly"
              ( Some(Symbol.symbol _2, mk_pos 2) )
# 570 "parser.ml"
               : 'resultty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 85 "parser.mly"
       ( Absyn.Ident{name = Symbol.symbol _1; pos = mk_pos 1} )
# 577 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 86 "parser.mly"
              ( Absyn.RecordAccess{record = Absyn.Ident{name = Symbol.symbol _1; pos = mk_pos 1}; name = Symbol.symbol _3; pos = mk_pos 1} )
# 585 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lvalue) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 87 "parser.mly"
                  ( Absyn.RecordAccess{record = _1; name = Symbol.symbol _3; pos = mk_pos 1} )
# 593 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 88 "parser.mly"
                             ( Absyn.ArrayAccess{array = Absyn.Ident{name = Symbol.symbol _1; pos = mk_pos 1}; exp = _3; pos = mk_pos 1} )
# 601 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'lvalue) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 89 "parser.mly"
                                 ( Absyn.ArrayAccess{array = _1; exp = _3; pos = mk_pos 1} )
# 609 "parser.ml"
               : 'lvalue))
; (fun __caml_parser_env ->
    Obj.repr(
# 92 "parser.mly"
        ( Absyn.NilExp(mk_pos 1) )
# 615 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'lvalue) in
    Obj.repr(
# 93 "parser.mly"
           ( Absyn.LValue{l = _1; pos = mk_pos 1} )
# 622 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expseq) in
    Obj.repr(
# 94 "parser.mly"
                         ( Absyn.SeqExp(_2) )
# 629 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 95 "parser.mly"
        ( Absyn.IntExp(_1) )
# 636 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 96 "parser.mly"
           ( Absyn.StringExp(_1, mk_pos 1) )
# 643 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 97 "parser.mly"
              ( Absyn.OpExp{left = Absyn.IntExp(0); op = Absyn.MinusOp; right = _2; pos = mk_pos 1} )
# 650 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'records) in
    Obj.repr(
# 99 "parser.mly"
                             ( Absyn.RecordExp{rec_exp_fields = _3; typ = Symbol.symbol _1; pos = mk_pos 1} )
# 658 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'funargs) in
    Obj.repr(
# 101 "parser.mly"
                             ( Absyn.CallExp{func = Symbol.symbol _1; args = _3; pos = mk_pos 1} )
# 666 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 103 "parser.mly"
                                    ( Absyn.ArrayExp{typ = Symbol.symbol _1; size = _3; init = _6; pos = mk_pos 1} )
# 675 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'op) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 104 "parser.mly"
               ( Absyn.OpExp{left = _1; op = _2; right = _3; pos = mk_pos 1} )
# 684 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'compar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 105 "parser.mly"
                   ( Absyn.OpExp{left = _1; op = _2; right = _3; pos = mk_pos 1} )
# 693 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'boolean) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 106 "parser.mly"
                    ( Absyn.OpExp{left = _1; op = _2; right = _3; pos = mk_pos 1} )
# 702 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'decs) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 107 "parser.mly"
                        ( Absyn.LetExp{decs = _2; body = _4; pos = mk_pos 1} )
# 710 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lvalue) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 108 "parser.mly"
                      ( Absyn.AssignExp{lvalue = _1; exp = _3; pos = mk_pos 1} )
# 718 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 109 "parser.mly"
                    ( Absyn.IfExp{test = _2; then' = _4; else' = None; pos = mk_pos 1} )
# 726 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 110 "parser.mly"
                             ( Absyn.IfExp{test = _2; then' = _4; else' = Some(_6); pos = mk_pos 1} )
# 735 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 111 "parser.mly"
                     ( Absyn.WhileExp{test = _2; body = _4; pos = mk_pos 1} )
# 743 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'exp) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 112 "parser.mly"
                                    ( Absyn.ForExp{var = Symbol.symbol _2; escape = ref true; lo = _4; hi = _6; body = _8; pos = mk_pos 1} )
# 753 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    Obj.repr(
# 113 "parser.mly"
          ( Absyn.BreakExp (mk_pos 1) )
# 759 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 116 "parser.mly"
        ( (_1, mk_pos 1) :: [] )
# 766 "parser.ml"
               : 'expseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expseq) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 117 "parser.mly"
                         ( (_3, Parsing.rhs_start_pos 3) :: _1 )
# 774 "parser.ml"
               : 'expseq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'record) in
    Obj.repr(
# 120 "parser.mly"
           ( _1 :: [] )
# 781 "parser.ml"
               : 'records))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'records) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'record) in
    Obj.repr(
# 121 "parser.mly"
                         ( _3 :: _1 )
# 789 "parser.ml"
               : 'records))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 124 "parser.mly"
                 ( (Symbol.symbol _1, _3, mk_pos 1) )
# 797 "parser.ml"
               : 'record))
; (fun __caml_parser_env ->
    Obj.repr(
# 126 "parser.mly"
        ( [] )
# 803 "parser.ml"
               : 'funargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 127 "parser.mly"
        ( _1 :: [] )
# 810 "parser.ml"
               : 'funargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'funargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 128 "parser.mly"
                      ( _3 :: _1 )
# 818 "parser.ml"
               : 'funargs))
; (fun __caml_parser_env ->
    Obj.repr(
# 131 "parser.mly"
         ( Absyn.PlusOp )
# 824 "parser.ml"
               : 'op))
; (fun __caml_parser_env ->
    Obj.repr(
# 132 "parser.mly"
          ( Absyn.MinusOp )
# 830 "parser.ml"
               : 'op))
; (fun __caml_parser_env ->
    Obj.repr(
# 133 "parser.mly"
          ( Absyn.TimesOp )
# 836 "parser.ml"
               : 'op))
; (fun __caml_parser_env ->
    Obj.repr(
# 134 "parser.mly"
           ( Absyn.DivideOp )
# 842 "parser.ml"
               : 'op))
; (fun __caml_parser_env ->
    Obj.repr(
# 137 "parser.mly"
       ( Absyn.LtOp )
# 848 "parser.ml"
               : 'compar))
; (fun __caml_parser_env ->
    Obj.repr(
# 138 "parser.mly"
       ( Absyn.LeOp )
# 854 "parser.ml"
               : 'compar))
; (fun __caml_parser_env ->
    Obj.repr(
# 139 "parser.mly"
       ( Absyn.GtOp )
# 860 "parser.ml"
               : 'compar))
; (fun __caml_parser_env ->
    Obj.repr(
# 140 "parser.mly"
       ( Absyn.GeOp )
# 866 "parser.ml"
               : 'compar))
; (fun __caml_parser_env ->
    Obj.repr(
# 141 "parser.mly"
          ( Absyn.EqOp )
# 872 "parser.ml"
               : 'compar))
; (fun __caml_parser_env ->
    Obj.repr(
# 142 "parser.mly"
             ( Absyn.NeqOp )
# 878 "parser.ml"
               : 'compar))
; (fun __caml_parser_env ->
    Obj.repr(
# 145 "parser.mly"
        ( Absyn.AndOp )
# 884 "parser.ml"
               : 'boolean))
; (fun __caml_parser_env ->
    Obj.repr(
# 146 "parser.mly"
       ( Absyn.OrOp )
# 890 "parser.ml"
               : 'boolean))
(* Entry prog *)
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
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Absyn.exp)
;;
