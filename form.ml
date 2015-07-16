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

(* Move it to More.List *)
let fold_notnil fct default = function
  | [] -> default
  | h::t -> List.fold_left fct h t

let product fct la lb =
  List.fold_left  (fun acc1 v1 ->
                    List.fold_left (fun acc2 v2 -> (fct v1 v2)::acc2) acc1 lb)
                  [] la

let rec unchoice_list_prog = function
  | Atom _ as a -> [a]
  | Test phi -> List.rev_map (fun psi -> Test psi) (unchoice_list_form phi)
  | Choice (alpha,beta) ->
      List.rev_append (unchoice_list_prog alpha) (unchoice_list_prog beta)
  | Iter alpha ->
      let filtered =
        List.fold_left  (fun acc beta ->
                          if (size beta) = 0 then acc else (Iter beta)::acc)
                        [] (unchoice_list_prog alpha)
      in
      [Iter (fold_notnil (fun acc beta -> Seq (acc, beta)) (Test top) filtered)]
  | Seq (alpha, beta) ->
      product (fun a b -> Seq (a,b))  (unchoice_list_prog alpha)
                                      (unchoice_list_prog beta)
  | CPar (alpha, beta) ->
      product (fun a b -> CPar (a,b)) (unchoice_list_prog alpha)
                                      (unchoice_list_prog beta)
and unchoice_list_form = function
  | Box (alpha, phi) ->
      let nphi = unchoice phi in
      List.rev_map (fun beta -> Box (beta, nphi)) (unchoice_list_prog alpha)
  | Neg phi -> List.rev_map (fun psi -> neg psi) (unchoice_list_form phi)
  | phi -> [phi]
and unchoice phi = fold_notnil disj Bot (unchoice_list_form phi)
