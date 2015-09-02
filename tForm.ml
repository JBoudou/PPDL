(** The extended PPDL language for the tableaux method,
    with indices and placeholders.

    There is no choice for now.

    @author Joseph Boudou
*)

open More

type prog =
  | Atom of string
  | Seq of prog * prog
  | Test of form
  | Iter of prog
  | CPar of prog * int * prog
and form =
  | Var of string
  | Bot
  | Neg of form
  | Diam of prog * form
  | PH of Dir.t * int

let neg = function
  | Neg phi -> phi
  | phi -> Neg phi

let top = neg Bot

let conj phi psi = Diam (Test phi, psi)
let disj phi psi = neg (conj (neg phi) (neg psi))

(** Translate a choice-free {!Form} formula into a TForm one. *)
let translate f =
  let rec trans_form i = function
    | Form.Var s -> (i, Var s)
    | Form.Bot -> (i, Bot)
    | Form.Neg phi ->
        let ni, nphi = trans_form i phi in
        ni, neg nphi
    | Form.Box (alpha, phi) ->
        let (ti, nalpha) = trans_prog i alpha in
        let (ni, nphi)   = trans_form ti phi in
        (ni, neg (Diam (nalpha, neg nphi)))
  and trans_prog i = function
    | Form.Atom s -> (i, Atom s)
    | Form.Seq (alpha, beta) ->
        let (ti, nalpha) = trans_prog i alpha in
        let (ni, nbeta)  = trans_prog ti beta in
        ni, Seq (nalpha, nbeta)
    | Form.Test phi ->
        let ni, nphi = trans_form i phi in
        ni, Test nphi
    | Form.Iter alpha ->
        let ni, nalpha = trans_prog i alpha in
        ni, Iter nalpha
    | Form.CPar (alpha, beta) ->
        let (ti, nalpha) = trans_prog i alpha in
        let (ni, nbeta)  = trans_prog ti beta in
        (ni + 1), CPar (nalpha, ni, nbeta)
    | Form.Choice (alpha, beta) -> failwith "TForm.translate"
  in snd (trans_form 0 (Form.unchoice f))

module Prog = struct
  type t = prog
  let compare = Pervasives.compare
end

module Formula = struct
  type t = form
  let compare = Pervasives.compare
end

type t_size = Zero | One | More

let rec size =
  let size_max alpha beta =
    match (size alpha, size beta) with
      | (One, _) -> One
      | (_, One) -> One
      | (Zero, Zero) -> Zero
      | _ -> More
  in function
  | Test _ -> Zero
  | Atom _ -> One
  | Seq (alpha, beta) ->      size_max alpha beta
  | CPar (alpha, _, beta) ->  size_max alpha beta
  | Iter alpha ->
      if (size alpha) = Zero then Zero else More

(* A program is direct if it can not add a formula to the current state *)
let rec direct = function
  | Test _ -> false
  | Seq (alpha, _)  -> direct alpha
  | Iter alpha      -> direct alpha
  | _ -> true

(** Replace each occurence of programs of the form [Iter alpha] by [Test top].
*)
let rec desiter = function
  | Iter _ -> Test top
  | Seq (alpha, beta)  -> Seq (desiter alpha, desiter beta)
  | CPar (alpha, i, beta) -> CPar (desiter alpha, i, desiter beta)
  | alpha -> alpha
