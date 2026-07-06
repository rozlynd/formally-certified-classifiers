open Parsing_utils


let report_error filename lexbuf msg =
  let (b,e) = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d: %s\n" filename b.pos_lnum fc lc msg


(* main : string -> valueType *)
(* Analyse le contenu d'un fichier passé en paramètre *)
(* Dans le cas où l'analyse syntaxique s'est bien passée, *)
(* draw the DT *)
let read_file filename =
  (* print_string "debug : parsing file..."; *)
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  try
    let fs, t, v = Parser.main Lexer.token filebuf in 
    (* print_endline "done."; *)
    fs, unname_tree t fs, v
    (* print_tree t;
    print_vector v *)
  with
  | Lexer.Error _ ->
      report_error filename filebuf "lexical error (unexpected character).";
      exit 2
  | Parser.Error ->
      report_error filename filebuf "syntax error.";
      exit 2






