type prog =
  | Atom of string
  | Seq of prog * prog
  | Test of form
  | Choice of prog * prog
  | Iter of prog
  | CPar of prog * prog
and form =
  | Var of string
  | Bot
  | Neg of form
  | Box of prog * form

let neg = function
  | Neg phi -> phi
  | Box (Test phi, Bot) -> phi
  | phi -> Neg phi

let top = neg Bot

let diam alpha phi = neg (Box (alpha, neg phi))

let imp phi psi = Box (Test phi, psi)

let disj phi psi = imp (neg phi) psi

let conj phi psi = diam (Test phi) psi

open Format

let rec print_formula pp = function
  | Var v -> pp_print_string pp v
  | Bot -> pp_print_string pp "⊥"
  | t when t = top -> pp_print_string pp "⊤"
  | Neg (Box (alpha, psi)) -> 
      pp_print_char pp '<';
      print_program pp alpha;
      pp_print_char pp '>';
      print_formula pp (neg psi)
  | Neg phi ->
      pp_print_string pp "¬";
      print_formula pp phi
  | Box (alpha, phi) ->
      pp_print_char pp '[';
      print_program pp alpha;
      pp_print_char pp ']';
      print_formula pp phi
and print_program pp = function
  | Atom a -> pp_print_string pp a
  | Seq (Seq (_,_) as alpha, beta) ->
      print_program pp alpha;
      pp_print_char pp ';';
      print_program pp beta
  | Seq (alpha, (Seq (_,_) as beta)) ->
      print_program pp alpha;
      pp_print_char pp ';';
      print_program pp beta
  | Seq (alpha, beta) ->
      print_progpar pp alpha;
      pp_print_char pp ';';
      print_progpar pp beta
  | Test phi ->
      print_formula pp phi;
      pp_print_char pp '?'
  | Choice (Choice (_,_) as alpha, beta) ->
      print_program pp alpha;
      pp_print_string pp "∪";
      print_program pp beta
  | Choice (alpha, (Choice (_,_) as beta)) ->
      print_program pp alpha;
      pp_print_string pp "∪";
      print_program pp beta
  | Choice (alpha, beta) ->
      print_progpar pp alpha;
      pp_print_string pp "∪";
      print_progpar pp beta
  | Iter alpha ->
      print_progpar pp alpha;
      pp_print_char pp '*'
  | CPar (alpha, beta) ->
      print_progpar pp alpha;
      pp_print_string pp "||";
      print_progpar pp beta
and print_progpar pp prog = match prog with
  | Seq (_,_)
  | Choice (_,_)
  | CPar (_,_) ->
      pp_print_char pp '(';
      print_program pp prog;
      pp_print_char pp ')'
  | _ ->
      print_program pp prog
