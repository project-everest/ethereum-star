(**
 Javascript token syntax (from ECMA 262 rev 5)
**)
open Parser
open Ulexing
open Printf
open Globals
 
let c b = (lasttok := utf8_lexeme b; col := !col + lexeme_length b) 
let nl () = lasttok := "\\n"; ln:=!ln+1; col := 0
let subs s i = String.sub s i ((String.length s)-i)

(* Whitespace and line breaks *)
let regexp whitespace = ['\t' '\x0B' '\x0C' ' ' '\xA0' 0x1680 0x180E 0x2000-0x200A 0x202F 0x205F 0x3000 0xFEFF]
let regexp newline = "\r\n" | ['\010' '\013' 0x2028 0x2029]
let regexp notnewline = [^ '\010' '\013' 0x2028 0x2029]
let regexp blank = whitespace | newline

(* Numeric literals §7.8.3 *)
let regexp nonz_digit = ['1'-'9']
let regexp digit = '0' | nonz_digit
let regexp hex_digit = digit | ['a'-'f' 'A'-'F']
let regexp hex_literal = '0' ['x' 'X'] hex_digit+
let regexp signed_integer = ['-' '+']? digit+
let regexp exponent = ['e' 'E'] signed_integer
let regexp decimal_int_literal = '0' | (nonz_digit digit* )

let regexp decimal_literal = (decimal_int_literal ('.' (digit* ))? exponent?) | ('.' (digit+) (exponent?))   
let regexp numeric_literal = hex_literal | decimal_literal 

(* Escape sequences *)
let regexp unicode_escape_seq = 'u' hex_digit hex_digit hex_digit hex_digit
let regexp hex_escape_seq = 'x' hex_digit hex_digit
let regexp single_escape_seq = ['\'' "\"" '\\' 'b' 'f' 'n' 'r' 't' 'v' '0']

(* Escaping functions *)
let escape_single = function "b"->"\x08" | "t"->"\x09" | "n"->"\x0A" | "v"->"\x0B" | "f"->"\x0C" | "r"->"\x0D" | "0" -> "\x00" |_ as s -> s
let escape_hex x = string_of_bytelist [int_of_string ("0" ^ x)] 
let escape_unicode x = String.set x 0 'x'; let c = int_of_string ("0"^x) in utf8_char c

(* Keywords and reserved words *)
let regexp reserved = "class" | "enum" | "extends" | "super" | "export" | "import"
let regexp future_reserved = "implements" | "let" | "yield" | "interface" | "package" | "protected" | "static"

let regexp right_keyword = "typeof" | "new" | "var" | "constant" | "do" | "case" | "void" | "for" | "switch" | "contract" | "struct" | "enum" | "mapping" | "modifier" | "event" | "internal" | "external" | "public" | "private"
  | "while" | "delete" | "function" | "with" | "default" | "if" | "else" | "try"
let regexp bi_keyword = "instanceof" | "in" | "finally" | "catch"
let regexp keyword = "debugger" | "this" | "continue" | "break" | "return" | "throw" | "++" | "--" | "returns"
let regexp munit = "seconds" | "minutes" | "hours" | "days" | "weeks" | "years" | "wei" | "finney" | "szabo" | "ether"

let regexp bi_punctuator = "=>" | "<=" | ">=" | "==" | "!=" | "===" | "!==" | ">>" | "<<" | ">>>" | "&&" | "||"  | "+=" | "-=" | "*=" 
  | "%=" | "<<=" | ">>=" | ">>>=" | "&=" | "|=" | "^=" | [';' ',' '<' '>' '+' '-' '*' '%' '=' '&' '^' '|' '?' ':' '(' '[']
let regexp right_punctuator = ['!' '~' '{']
let regexp left_punctuator = [')' ']']

let regexp bi_kw = bi_punctuator | bi_keyword
let regexp right_kw = right_keyword | right_punctuator

(* Literal values *)
let regexp value_literal = "true" | "false" | "null" (*| "undefined" | "NaN" | "Infinity" *)

(* String literals *)
let regexp squote = '\''
let regexp dquote = '"'

(* Conservative identifier: actual checking is done with PCRE *)
(* Damnit why doesn't Ulex support class difference r1 # r2? This is awful. *)
let regexp identifier = ([^ '{' '}' '(' ')' '[' ']' '.' ';' ',' '<' '>' '+' '-' '*' '/' '%' '!' '&' '^' '|' '?' ':' '~' '=' '\'' "\"" '\t' '\x0B' '\x0C' ' ' '\xA0' 0x1680 0x180E 0x2000-0x200A 0x202F 0x205F 0x3000 0xFEFF '\010' '\013' 0x2028 0x2029])+

(* Token constructors *)
let k2c = function
  | "true" -> BOOL(true) | "false" -> BOOL(false) | "null" -> NULL (*| "undefined" -> UNDEFINED*)
  (* | "NaN" -> NUMBER(nan) | "Infinity" -> NUMBER(infinity) *)
  | "do" -> DO | "for" -> FOR | "while" -> WHILE | "break" -> BREAK | "continue" -> CONTINUE
  | "instanceof" -> INSTANCEOF | "typeof" -> TYPEOF | "enum" -> ENUM
  | "contract" -> CONTRACT | "mapping" -> MAPPING | "struct" -> STRUCT
  | "returns" -> RETURNS | "constant" -> CONSTANT | "modifier" -> MODIFIER
  | "new" -> NEW | "var" -> VAR | "const" -> CONST | "delete" -> DELETE
  | "switch" -> SWITCH | "case" -> CASE | "default" -> DEFAULT
  | "debugger" -> DEBUGGER | "event" -> EVENT | "public" -> PUBLIC
  | "private" -> PRIVATE | "internal" -> INTERNAL | "external" -> EXTERNAL
  | "function" -> FUNCTION | "this" -> THIS | "return" -> RETURN | "void" -> VOID
  | "with" -> WITH | "in" -> IN
  | "if" -> IF | "else" -> ELSE
  | "try" -> TRY | "throw" -> THROW | "catch" -> CATCH | "finally" -> FINALLY
  | "{" -> LC | "(" -> LP | "[" -> LB | "]" -> RB | ")" -> RP | "}" -> RC | "=>" -> MAPSTO
  | "." -> DOT | ";" -> SEMI | "," -> COMMA | "?" -> QM | ":" -> COLON | "!" -> LNOT | "~" -> BNOT
  | "<" -> LT | "<=" -> LE | ">" -> GT | ">=" -> GE | "==" -> EQ | "!=" -> NEQ | "===" -> SEQ | "!==" -> SNEQ
  | "+" -> PLUS | "-" -> MINUS | "*" -> TIMES | "%" -> MOD | "&" -> BAND | "|" -> BOR | "^" -> XOR
  | "++" -> INCR | "--" -> DECR | ">>" -> RSH | "<<" -> LSH | ">>>" -> ARSH | "&&" -> LAND | "||" -> LOR
  | "=" -> ASSIGN | "+=" -> PLUS_ASSIGN | "-=" -> MINUS_ASSIGN | "*=" -> TIMES_ASSIGN | "|=" -> OR_ASSIGN
  | "&=" -> AND_ASSIGN | "^=" -> XOR_ASSIGN | ">>=" -> RSH_ASSIGN | "<<=" -> LSH_ASSIGN | ">>>=" -> ARSH_ASSIGN
  | "%=" -> MOD_ASSIGN | "/" -> DIV | "/=" -> DIV_ASSIGN
  | "class" | "enum" | "extends" | "super" | "const" | "export" | "import" | "implements"
  | "let" | "yield" | "interface" | "package" | "protected" | "static" as s -> RESERVED(s)
  | _ as s -> KEYWORD(s)

(* Decoding of Unicode escape sequence in identifiers *)
let decode_unicode ?allowkw:(kw=false) =
(*  let irex = Pcre.regexp ~flags:[`UTF8] "^([$_]|\\p{Lu}|\\p{Ll}|\\p{Lt}|\\p{Lm}|\\p{Lo}|\\p{Nl})([$_]|\\p{Lu}|\\p{Ll}|\\p{Lt}|\\p{Lm}|\\p{Lo}|\\p{Nl}|\\p{Mn}|\\p{Mc}|\\p{Nd}|\\p{Pc}|\\x{200C}|\\x{200D})*$" in *)
  let rex = Str.regexp "^[a-zA-Z_$][a-zA-Z0-9_$]*$" in
  let rep s = String.set s 1 '0'; escape_unicode s in
(*  let is = Pcre.substitute ~rex:urex ~subst:rep is in *)
  fun s ->
  match Str.string_match rex s 0 with
  | true ->
    begin 
     match k2c s with
     | KEYWORD(_) -> s
     | _ -> if kw then s else lerr (sprintf "Can't use keyword or reserved word <%s> as identifier" s)
    end
  | false -> lerr (sprintf "Invalid identifier name <%s>" s)

let trim = BatString.trim

let expand_unit s =
  let (n, un) = BatString.split s " " in
  let n = float_of_string n in
  match un with
  | "minutes" -> 60. *. n
  | "hours" -> 3600. *. n
  | "days" -> 86400. *. n
  | "weeks" -> 604800. *. n
  | "years" -> 31536000. *. n
  | "finney" -> 1000. *. n
  | "szabo" -> 1000000. *. n
  | "ether" -> 1000000000000000000. *. n
  | _ -> n

let memory = ref None
let cut_right = ref false
let finished = ref false

(* The Tokenizer has a lookahead of 2 because of automatic semicolon insertion *)
let rec main lexbuf =  
  let res = match !memory with
		| Some RC -> memory := Some EOL; RC
    | Some t -> memory := None; t
    | None -> let t = token lexbuf in
      match !memory with Some EOL -> memory := Some t; EOL | _ -> t
  in res

and token = lexer
  | whitespace* | ("//" notnewline* ) -> c lexbuf; token lexbuf
  | "/*" -> c lexbuf; comment_scanner lexbuf; 
  | newline -> nl (); if not !cut_right then memory := Some EOL; token lexbuf
  | left_punctuator -> let s = utf8_lexeme lexbuf in c lexbuf; re := false; cut_right := false; memory := None; k2c (trim s)
  | '}' -> c lexbuf; re := true; memory := Some RC; cut_right := false; EOL
  | bi_kw blank* -> let s = utf8_lexeme lexbuf in c lexbuf; re := true; cut_right := true; memory := None; k2c (trim s)
  | '.' blank* -> c lexbuf; re := true; cut_right := true; memory := Some(dot_scanner lexbuf); DOT
  | right_kw blank* -> let s = utf8_lexeme lexbuf in c lexbuf; re := true; cut_right := true; k2c (trim s)
  | keyword -> let s = utf8_lexeme lexbuf in c lexbuf; re := true; cut_right := false; k2c s
  | value_literal -> let s = utf8_lexeme lexbuf in c lexbuf; re := false; cut_right := false; k2c s
  | reserved | future_reserved -> let s = utf8_lexeme lexbuf in c lexbuf; re := true; cut_right := false; RESERVED(s)
  | ['\'' "\""] -> let s = string_scanner (utf8_lexeme lexbuf) lexbuf in incr col; re := false; cut_right := false; STRING(s)
  | '/' '='? -> c lexbuf; let t = if !re then
      (re:=false; cut_right := false; REGEXP(regexp_scanner (subs (utf8_lexeme lexbuf) 1) lexbuf))
			else (memory := None; cut_right := true; re:=true; k2c (utf8_lexeme lexbuf)) in t
  | decimal_literal ' ' munit -> re := false; cut_right := false; NUMBER(expand_unit (utf8_lexeme lexbuf))
  | decimal_literal -> let i = float_of_string (utf8_lexeme lexbuf) in c lexbuf; re := false; cut_right := false; NUMBER(i)
  | hex_literal -> let i = int_of_string (utf8_lexeme lexbuf) in c lexbuf; re := false; cut_right := false; BYTE(i)
  | identifier -> let id = decode_unicode (utf8_lexeme lexbuf) in c lexbuf; re := false; cut_right := false; IDENTIFIER(id)
  | eof -> if !finished or !memory=Some EOL then EOF else (finished := true; EOL)
  | _ -> lerr (sprintf "Unexpected token: <%s>" (utf8_lexeme lexbuf))

and dot_scanner = lexer
  | whitespace* | ("//" notnewline* ) -> c lexbuf; dot_scanner lexbuf
  | "/*" -> c lexbuf; comment_scanner ~return:dot_scanner lexbuf;
  | identifier -> let id = decode_unicode ~allowkw:true (utf8_lexeme lexbuf) in
      c lexbuf; re := false; cut_right := false; IDENTIFIER(id)
	| _ -> lerr (sprintf "Invalid property for dot notation: <%s>" (utf8_lexeme lexbuf))

and string_scanner quote = lexer
  | newline | eof -> lerr "Unexpected end of string literal"
  | ['\'' "\""] -> let q = utf8_lexeme lexbuf in incr col; if q=quote then "" else q^(string_scanner quote lexbuf)
  | '\\' -> incr col; string_escape_scanner quote lexbuf
  | [^ '\'' "\"" '\\' '\010' '\013' 0x2028 0x2029]+ -> let s = utf8_lexeme lexbuf in c lexbuf; s ^ (string_scanner quote lexbuf)   

and string_escape_scanner quote = lexer
  | newline -> nl (); string_scanner quote lexbuf
  | single_escape_seq -> let s = escape_single (utf8_lexeme lexbuf) in c lexbuf; s ^ (string_scanner quote lexbuf)
  | unicode_escape_seq -> let s = escape_unicode (utf8_lexeme lexbuf) in c lexbuf; s ^ (string_scanner quote lexbuf)
  | hex_escape_seq -> let s = escape_hex (utf8_lexeme lexbuf) in c lexbuf; s ^ (string_scanner quote lexbuf)
  | _ -> c lexbuf; let s = utf8_lexeme lexbuf in lwar (sprintf "Bad escape sequence: \\%s" s); s ^ (string_scanner quote lexbuf)  

and regexp_scanner acc = lexer
  | newline | eof -> lerr "Unexpectend end of regexp literal"
  | "\\" -> c lexbuf; regexp_escape_scanner acc false lexbuf
  | '[' -> c lexbuf; regexp_class_scanner (acc^"[") lexbuf
  | '/' ['a'-'z' 'A'-'Z']* -> c lexbuf; let s = utf8_lexeme lexbuf in (acc, subs s 1)
  | [^ '/' '\\'] -> c lexbuf; let s = acc^(utf8_lexeme lexbuf) in regexp_scanner s lexbuf

and regexp_escape_scanner = (
 fun acc cl -> let tk = (if cl then regexp_class_scanner else regexp_scanner) in lexer
  | newline | eof -> lerr "Unexpectend end of regexp literal"
  | unicode_escape_seq -> let s = escape_unicode (utf8_lexeme lexbuf) in c lexbuf; tk (acc^s) lexbuf
  | hex_escape_seq -> let s = escape_hex (utf8_lexeme lexbuf) in c lexbuf; tk (acc^s) lexbuf
  | ['/'] -> let s = acc^(utf8_lexeme lexbuf) in c lexbuf; tk s lexbuf
  | ['\\' '[' ']' '{' '}' '(' ')' '+' '.' '*' '?' '|' '^' '$' 'B' 'D' 'S' 'W' 'c' 'd' 's'-'x' '0'-'9' '-']
     -> let s = acc^"\\"^(utf8_lexeme lexbuf) in c lexbuf; tk s lexbuf
  | single_escape_seq -> let s = escape_single (utf8_lexeme lexbuf) in c lexbuf; tk (acc^s) lexbuf  
  | _ -> c lexbuf; let s = utf8_lexeme lexbuf in lwar (sprintf "Bad escape sequence in regexp: \\%s" s); tk (acc^s) lexbuf
 )

and regexp_class_scanner acc = lexer
  | newline | eof -> lerr "Unexpectend end of class in regexp literal"
	| "\\" -> c lexbuf; regexp_escape_scanner acc true lexbuf
  | ']' -> c lexbuf; regexp_scanner (acc^"]") lexbuf
	| _ -> let s = utf8_lexeme lexbuf in c lexbuf; regexp_class_scanner (acc^s) lexbuf

and comment_scanner ?return:(tk=token) = lexer
  | newline -> nl (); if not !cut_right then memory := Some EOL; comment_scanner lexbuf
  | "*/" -> c lexbuf; tk lexbuf
  | eof -> lerr "Unclosed multiline comment"
  | _ -> c lexbuf; comment_scanner lexbuf
