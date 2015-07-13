let stdout = Format.std_formatter

let _ =
  ignore (Parsing.set_trace true) ;
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let phi = Parser.form Lexer.token lexbuf in
      Form.print_formula stdout phi ; Format.pp_print_newline stdout ()
    done
  with Lexer.Eof ->
    exit 0
