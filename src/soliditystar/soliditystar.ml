open Error
open Printf
open Pretty
open Globals

let basename s =
  try String.sub s 0 (String.rindex s '.')
  with Not_found -> s;;

let out = (fun s -> output := Unix.out_channel_of_descr (Unix.openfile s [Unix.O_WRONLY;Unix.O_CREAT] 0o644)) in
let inp = (fun s -> (ifiles := s :: !ifiles)) in 
  Arg.parse [
    ("-v", Arg.Unit (fun () -> verbose := true), "verbose output");
    ("-p", Arg.Unit (fun () -> mode := Pretty), "Pretty-print the source contract (default)");
    ("-c", Arg.Unit (fun () -> mode := Compile), "Compile contract into F*");
    ("--escape-unicode", Arg.Unit (fun ()->escape_unicode:=true), "escape all Unicode characters (ASCII output)");
    ("--indent", Arg.Int (fun n->pad_len:=abs n), "n: number of spaces per indent level");
    ("-o", Arg.String out, "<file>: output file (defaults to stdout)")
  ] inp "Parses Solidity contracts and compile them to F*.";;

let run fn =
  ifile := fn; col := 0; ln := 1;
  input := (match fn with "<stdio>" -> stdin | s -> Unix.in_channel_of_descr (Unix.openfile s [Unix.O_RDONLY] 0));
  let inbuf = Ulexing.from_utf8_channel !input in
  try
    let parsed = menhir_with_ulex Lexer.main Parser.main inbuf in
    match !mode with
    | Pretty -> 
      let str = pretty_print 0 parsed in
      fprintf !output "%s\n" str
    | Compile ->
      Compile.compile parsed
  with
    | LexingError (loc, msg) -> fprintf stderr "%s at %s\n%!" msg (format_position (lexpos_of_loc loc))
    | Parser.Error -> fprintf stderr "Unexpected token <%s> at %s\n%!" !lasttok (format_position (lexpos_of_loc (getloc ())))
    | Utf8.MalFormed -> fprintf stderr "Invalid UTF-8 input character at %s\n%!" (format_position (lexpos_of_loc (getloc ())))

let _ =
  let files = match !ifiles with [] -> ["<stdio>"] | l -> List.rev l in
  List.iter run files
