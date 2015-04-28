module HForm
= struct

  type dir = L | R

  type loc = dir list

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
    | Diam of prog * form
    | PH of dir * int
    | Q of form

  type t = loc * form

  let neg = function
    | Neg phi -> phi
    | phi -> Neg phi

  let translate =
    let rec trans_form = function
      | Form.Var s -> Var s
      | Form.Bot -> Bot
      | Form.Neg phi -> neg (trans_form phi)
      | Form.Box (alpha, phi) -> neg (Diam (trans_prog alpha, neg (trans_form phi)))
    and trans_prog = function
      | Form.Atom s -> Atom s
      | Form.Seq (alpha, beta) -> Seq (trans_prog alpha, trans_prog beta)
      | Form.Test phi -> Test (trans_form phi)
      | Form.Choice (alpha, beta) -> Choice (trans_prog alpha, trans_prog beta)
      | Form.Iter alpha -> Iter (trans_prog alpha)
      | Form.CPar (alpha, beta) -> CPar (trans_prog alpha, trans_prog beta)
    in trans_form

  let compare (m1, phi1) (m2, phi2) =
    let rec comp_loc l1 l2 = match (l1, l2) with 
      | ([], []) -> 0
      | ([], _) -> -1
      | (_, []) ->  1
      | (h1::t1, h2::t2) when h1 = h2 -> comp_loc t1 t2
      | (L::_, _) -> -1
      | (R::_, _) ->  1
    in
    let rec comp_form phi psi = match (phi, psi) with
      | (phi, psi) when phi = psi -> 0
      | (Bot, _) -> -1
      | (_, Bot) ->  1
      | (Var a, Var b) -> String.compare a b
      | (Var _, _) -> -1
      | (_, Var _) ->  1
      | (PH (L, a), PH (L, b)) -> a - b
      | (PH (L, _), _) -> -1
      | (_, PH (L, _)) ->  1
      | (PH (R, a), PH (R, b)) -> a - b
      | (PH (R, _), _) -> -1
      | (_, PH (R, _)) ->  1
      | (Q phi, Q psi) -> comp_form phi psi
      | (Q _, _) -> -1
      | (_, Q _) ->  1
      | (Neg a, Neg b) -> comp_form a b
      | (Neg _, _) ->  1
      | (_, Neg _) -> -1
      | (Diam (alpha, phi), Diam (beta, psi)) ->
          let cprog = comp_prog alpha beta in
          if cprog != 0 then cprog
          else comp_form phi psi
    and comp_prog alpha beta = match (alpha, beta) with
      | (alpha, beta) when alpha = beta -> 0
      | (Atom a, Atom b) -> String.compare a b
      | (Atom _, _) -> -1
      | (_, Atom _) ->  1
      | (Test phi, Test psi) -> comp_form phi psi
      | (Test _, _) -> -1
      | (_, Test _) ->  1
      | (Iter a, Iter b) -> comp_prog a b
      | (Iter _, _) -> -1
      | (_, Iter _) ->  1
      | (Seq (a,b), Seq (c,d)) ->
          let cprog = comp_prog a c in
          if cprog != 0 then cprog
          else comp_prog b d
      | (Seq (_,_), _) -> -1
      | (_, Seq (_,_)) ->  1
      | (Choice (a,b), Choice (c,d)) ->
          let cprog = comp_prog a c in
          if cprog != 0 then cprog
          else comp_prog b d
      | (Choice (_,_), _) -> -1
      | (_, Choice (_,_)) ->  1
      | (CPar (a,b), CPar (c,d)) ->
          let cprog = comp_prog a c in
          if cprog != 0 then cprog
          else comp_prog b d
      | (CPar (_,_), _) -> -1
      | (_, CPar (_,_)) ->  1
    in
    let cloc = comp_loc m1 m2 in
    if cloc != 0 then cloc
    else comp_form phi1 phi2

end


module Hintikka
= struct
  open HForm

  include Set.Make (HForm)

  let fischer_ladner lf =
    let rec aux acc = function
      | [] -> acc
      | ((m, Diam (Atom _, phi)) as h)::t ->
          aux (add h acc) ((m, phi)::t)
      | ((m, Neg phi) as h)::t ->
          aux (add h acc) ((m, phi)::t)
      | ((m, Diam (Test phi, psi)) as h)::t ->
          aux (add h acc) ((m, phi)::(m, psi)::t)
      | ((m, Diam (Seq (alpha, beta), phi)) as h)::t ->
          aux (add h acc) ((m, Diam (alpha, Diam (beta, phi)))::t)
      | ((m, Diam (Choice (alpha, beta), phi)) as h)::t ->
          aux (add h acc) ((m, Diam (alpha, Q phi))::(m, Diam (beta, Q phi))::(m, phi)::t)
      | ((m, Diam (Iter alpha, phi)) as h)::t ->
          aux (add h acc) ((m, Diam (alpha, Q (Diam (Iter alpha, phi))))::(m, phi)::t)
      | ((m, Diam (CPar (alpha, beta), phi)) as h)::t ->
          aux (add h acc) ((L::m, Diam (alpha, PH (L, 1)))::(L::m, Diam (alpha, PH (L, 2)))::
                           (R::m, Diam (beta, PH (R, 1)))::(R::m, Diam (beta, PH (R, 2)))::(m, phi)::t)
      | h::t -> aux (add h acc) t
    in aux empty [lf]

end

module HStates
= struct

  include Set.Make (Hintikka)

  let all_subsets =
    let rec aux acc hin =
      if Hintikka.is_empty hin then acc else
      let 
