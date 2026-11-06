(* Driver of the `.s` parser: the ocamllex lexer (cheriot_lexer.mll) and
   the menhir grammar (cheriot_grammar.mly), which states the accepted
   subset. Errors are reported with file:line (Diag.Error). *)

let parse_lexbuf lexbuf =
  try Cheriot_grammar.file Cheriot_lexer.token lexbuf
  with Cheriot_grammar.Error ->
    let p = Lexing.lexeme_start_p lexbuf in
    let tok = Lexing.lexeme lexbuf in
    Diag.error
      { Diag.file = p.Lexing.pos_fname; line = p.Lexing.pos_lnum }
      "syntax error at %s (not in the accepted subset, see cheriot_grammar.mly)"
      (if tok = "\n" then "end of line" else Printf.sprintf "%S" tok)

let set_position lexbuf file line =
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with pos_fname = file; pos_lnum = line }

let read_lines file =
  let ic = open_in_bin file in
  let rec go acc =
    match input_line ic with
    | l -> go (l :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  go []

let parse_file file =
  let ic = open_in_bin file in
  let lexbuf = Lexing.from_channel ic in
  set_position lexbuf file 1;
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
      let lines = parse_lexbuf lexbuf in
      lines)

(* One line of [file], numbered [line]. *)
let parse_line ~file ~line s =
  let lexbuf = Lexing.from_string (s ^ "\n") in
  set_position lexbuf file line;
  parse_lexbuf lexbuf
