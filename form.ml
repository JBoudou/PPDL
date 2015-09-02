(** The PPDL full language.

   This module implement the full PPDL language with iteration and
   non-deterministic choice.
  
   @author Joseph Boudou
*)

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

(** Implication. *)
let imp phi psi = Box (Test phi, psi)

(** Disjunction. *)
let disj phi psi = imp (neg phi) psi

(** Conjunction *)
let conj phi psi = diam (Test phi) psi

open More

let seq_list =
  List.fold_notnil (fun a b -> Seq (a,b)) (Test top)

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

(** @private *)
and print_progpar pp prog = match prog with
  | Seq (_,_)
  | Choice (_,_)
  | CPar (_,_) ->
      pp_print_char pp '(';
      print_program pp prog;
      pp_print_char pp ')'
  | _ ->
      print_program pp prog

(** @deprecated Should use same type as in TForm *)
let rec size = function
  | Test _ -> 0
  | Atom _ -> 1
  | Iter alpha ->
      if (size alpha) = 0 then 0 else 2
  | Seq (alpha, beta) ->
      (match (size alpha, size beta) with
        | (0,0) -> 0
        | (1,_) -> 1
        | (_,1) -> 1
        | _     -> 2 )
  | CPar (alpha, beta) ->
      (match (size alpha, size beta) with
        | (0,0) -> 0
        | (1,_) -> 1
        | (_,1) -> 1
        | _     -> 2 )
  | Choice (alpha, beta) ->
      (match (size alpha, size beta) with
        | (0,0) -> 0
        | (1,1) -> 1
        | _     -> 2 )

(** Produce an equivalent choice-free formula.
    The resulting formula may be exponentialy bigger.
*)
let rec unchoice phi = List.fold_notnil disj Bot (unchoice_list_form phi)

(** @private *)
and unchoice_list_prog = function
  | Atom _ as a -> [a]
  | Test phi -> List.rev_map (fun psi -> Test psi) (unchoice_list_form phi)
  | Choice (alpha,beta) ->
      List.rev_append (unchoice_list_prog alpha) (unchoice_list_prog beta)
  | Iter alpha ->
      let filtered =
        List.fold_left  (fun acc -> function
                          | beta when size beta = 0 -> acc
                          | Iter beta -> beta::acc
                          | beta -> (Iter beta)::acc)
                        [] (unchoice_list_prog alpha)
      in (
      match filtered with
        | [] -> [Test top]
        | beta::[] -> [beta]
        | beta::lst ->
            [Iter (List.fold_left (fun acc beta -> Seq (acc, beta))
                                  beta lst)]
      )
  | Seq (alpha, beta) ->
      List.product (fun a b -> Seq (a,b))  (unchoice_list_prog alpha)
                                      (unchoice_list_prog beta)
  | CPar (alpha, beta) ->
      List.product (fun a b -> CPar (a,b)) (unchoice_list_prog alpha)
                                      (unchoice_list_prog beta)

(** @private *)
and unchoice_list_form = function
  | Box (alpha, phi) ->
      let nphi = unchoice phi in
      List.rev_map (fun beta -> Box (beta, nphi)) (unchoice_list_prog alpha)
  | Neg phi -> List.rev_map (fun psi -> neg psi) (unchoice_list_form phi)
  | phi -> [phi]
