let stdout = Format.std_formatter

let cpt = ref 1

let _ =
  ignore (Parsing.set_trace false) ;
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let phi = Parser.form Lexer.token lexbuf in
      Form.print_formula stdout phi ; Format.pp_print_newline stdout () ;
(*
      Form.print_formula stdout (Form.unchoice phi) ; Format.pp_print_newline stdout () ;
*)
      Format.pp_print_int stdout !cpt ; cpt := !cpt + 1 ;
      Format.pp_print_string stdout
        (if Tab.resolve phi then " sat" else " unsat") ;
      Format.pp_print_newline stdout () ; Format.pp_print_flush stdout ()
    done
  with Lexer.Eof ->
    exit 0
