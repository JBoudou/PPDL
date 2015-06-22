open More
open TForm

type separation = Forw | Back

type judgment =
  | Node of int * TForm.form
  | Edge of int * int * TForm.prog
  | Sepa of int * int * int * separation

module IntString = struct
  type t = int * string
  let compare = Pervasives.compare
end

module IntStringSet = Set.Make (IntString)
module IntStringMap = Map.Make (IntString)

module TripleInt = struct
  type t = int * int * int
  let compare = Pervasives.compare
end

module TripleIntSet = Set.Make (TripleInt)

type tableau = {
  (* active judgments *)
  todo      : judgment list;
  branching : judgment list;
  successor : judgment list;
  waiting   : judgment list;
  (* var prop *)
  var_pos : IntStringSet.t;
  var_neg : IntStringSet.t;
  (* universals *)
  box_atom_form : TForm.form list IntStringMap.t;
  box_atom_prog :        int list IntStringMap.t;
  box_cpar_forw : (TForm.prog * int * TForm.prog * TForm.form) IntMap.t;
  box_sep_forw : TripleIntSet.t;
  box_sep_back : TripleIntSet.t;
  box_cpar_left   : int IntMap.t;
  box_cpar_right  : int IntMap.t;
  (* state *)
  current : int;
  fresh : int;
  terminated : IntSet.t;
}

let init phi = {
  todo      = [Node (0, phi)];
  branching = [];
  successor = [];
  waiting   = [];
  var_pos = IntStringSet.empty;
  var_neg = IntStringSet.empty;
  box_atom_form = IntStringMap.empty;
  box_atom_prog = IntStringMap.empty;
  box_cpar_forw = IntMap.empty;
  box_sep_forw = TripleIntSet.empty;
  box_sep_back = TripleIntSet.empty;
  box_cpar_left  = IntMap.empty;
  box_cpar_right = IntMap.empty;
  current = 0;
  fresh = 1;
  terminated = IntSet.empty;
}

exception Nothing_Todo

(*
let proceed rl_list tab =
  let rec aux tab = function
    | [] -> tab
    | h::t ->
        try aux (h tab) rl_list
        with Nothing_Todo -> aux t
  in aux
  *)

let rec proceed_todo tab =
  match tab.todo with
    | [] -> raise Nothing_Todo

    (* apply conjunctive non-successor rules *)

    (* diam 0 *)
    | (Node (x, Diam (alpha, phi)))::t when (size alpha) = Zero ->
        proceed_todo {tab with
          todo = (Edge (x,x, alpha))::(Node (x, phi))::t}
    (* diam ? *) 
    | (Edge (x, y, Test phi))::t when x = y ->
        proceed_todo {tab with todo = (Node (x, phi))::t}
    (* box ; *)
    | (Node (x, Neg (Diam (Seq (alpha, beta), phi))))::t ->
        proceed_todo {tab with
          todo = (Node (x, Neg (Diam (alpha, Neg (Diam (beta, phi))))))::t}
    (* diam ;00 *)
    | (Edge (x,y, Seq (alpha, beta)))::t when x = y ->
        proceed_todo {tab with
          todo = (Edge (x,x, alpha))::(Edge (x,x, beta))::t}
    (* diam ;0. *)
    | (Edge (x,y, Seq (alpha, beta)))::t when (size alpha) = Zero ->
        proceed_todo {tab with
          todo = (Edge (x,x, alpha))::(Edge (x,y, beta))::t}
    (* diam ;.0 *)
    | (Edge (x,y, Seq (alpha, beta)))::t when (size beta) = Zero ->
        proceed_todo {tab with
          todo = (Edge (x,y, alpha))::(Edge (y,y, beta))::t}
    (* box star *)
    | (Node (x, (Neg (Diam (Iter alpha, phi)) as psi)))::t ->
        proceed_todo {tab with
          todo = (Node (x, phi))::(Node (x, Neg (Diam (alpha, psi))))::t}

    (* check inconsistency *)

    | (Node (_, Bot))::_ -> false
    | (Node (x, Var v))::t ->
        if IntStringSet.mem (x,v) tab.var_neg then false else
        proceed_todo {tab with
          todo = t;
          var_neg = IntStringSet.add (x,v) tab.var_neg}
    | (Node (x, Neg (Var v)))::t ->
        if IntStringSet.mem (x,v) tab.var_pos then false else
        proceed_todo {tab with
          todo = t;
          var_pos = IntStringSet.add (x,v) tab.var_pos}

    (* TODO *)
    (* move branching *)
    (* move waiting *)
    (* Universals *)
    (* move successor *)

    | _ -> failwith "todo"
