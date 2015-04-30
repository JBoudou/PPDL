open More

open Loc

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

type t = Loc.t * form

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

let rec compare_form phi psi = match (phi, psi) with
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
  | (Neg a, Neg b) -> compare_form a b
  | (Neg _, _) ->  1
  | (_, Neg _) -> -1
  | (Diam (alpha, phi), Diam (beta, psi)) ->
      let cprog = compare_prog alpha beta in
      if cprog != 0 then cprog
      else compare_form phi psi
and compare_prog alpha beta = match (alpha, beta) with
  | (alpha, beta) when alpha = beta -> 0
  | (Atom a, Atom b) -> String.compare a b
  | (Atom _, _) -> -1
  | (_, Atom _) ->  1
  | (Test phi, Test psi) -> compare_form phi psi
  | (Test _, _) -> -1
  | (_, Test _) ->  1
  | (Iter a, Iter b) -> compare_prog a b
  | (Iter _, _) -> -1
  | (_, Iter _) ->  1
  | (Seq (a,b), Seq (c,d)) ->
      let cprog = compare_prog a c in
      if cprog != 0 then cprog
      else compare_prog b d
  | (Seq (_,_), _) -> -1
  | (_, Seq (_,_)) ->  1
  | (Choice (a,b), Choice (c,d)) ->
      let cprog = compare_prog a c in
      if cprog != 0 then cprog
      else compare_prog b d
  | (Choice (_,_), _) -> -1
  | (_, Choice (_,_)) ->  1
  | (CPar (a,b), CPar (c,d)) ->
      let cprog = compare_prog a c in
      if cprog != 0 then cprog
      else compare_prog b d

let compare (m1, phi1) (m2, phi2) =
  let cloc = Loc.compare m1 m2 in
  if cloc != 0 then cloc
  else compare_form phi1 phi2

module Prog
= struct
  type t = prog
  let compare = compare_prog
end
