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

module DoubleInt = struct
  type t = int * int
  let compare = Pervasives.compare
end

module DoubleIntSet = Set.Make (DoubleInt)

module ForwardCPar = struct
  type t = TForm.prog * int * TForm.prog * TForm.form
  let compare = Pervasives.compare
end

module ForwardCParSet = Set.Make (ForwardCPar)

module DoubleProg = struct 
  type t = TForm.prog * TForm.prog
  let compare = Pervasives.compare
end

module DoubleProgSet = Set.Make (DoubleProg)

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
  box_atom_form : TForm.form list StringMap.t;
  box_atom_succ :        int list StringMap.t;
  box_cpar_forw : ForwardCParSet.t;
  box_cpar_back :  DoubleProgSet.t;
  box_sep_forw : (int * int) list;
  box_sep_back : (int * int) list;
  box_cpar_left   : IntSet.t IntMap.t;
  box_cpar_right  : IntSet.t IntMap.t;
  g_par_form : TForm.form IntMap.t;
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
  box_atom_form = StringMap.empty;
  box_atom_succ = StringMap.empty;
  box_cpar_forw = ForwardCParSet.empty;
  box_cpar_back =  DoubleProgSet.empty;
  box_sep_forw = [];
  box_sep_back = [];
  box_cpar_left  = IntMap.empty;
  box_cpar_right = IntMap.empty;
  g_par_form = IntMap.empty;
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
    (* diam ;11 *)
    | (Edge (x,y, Seq (alpha, beta)))::t
        when x = tab.current && size alpha = One && size beta = One ->
        proceed_todo {tab with
          todo = (Edge (x, tab.fresh, alpha))::(Edge (tab.fresh, y, beta))::t ;
          fresh = tab.fresh + 1 }
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

    (* Universals (for all) *)

    | (Node (x, PH (Dir.L, i)))::t ->
        let aux acc (l,r) =
          if l = x &&
            ( try IntSet.mem i (IntMap.find r tab.box_cpar_right)
              with Not_found -> false )
          then (Node (tab.current, IntMap.find i tab.g_par_form))::acc
          else acc
        in
        proceed_todo {tab with
          todo = List.fold_left aux t tab.box_sep_back;
          box_cpar_left = IntMap.add x
            (IntSet.add i ( try IntMap.find x tab.box_cpar_left
                            with Not_found -> IntSet.empty))
            tab.box_cpar_left }
    | (Node (x, PH (Dir.R, i)))::t ->
        let aux acc (l,r) =
          if r = x &&
            ( try IntSet.mem i (IntMap.find l tab.box_cpar_left)
              with Not_found -> false )
          then (Node (tab.current, IntMap.find i tab.g_par_form))::acc
          else acc
        in
        proceed_todo {tab with
          todo = List.fold_left aux t tab.box_sep_back;
          box_cpar_right = IntMap.add x
            (IntSet.add i ( try IntMap.find x tab.box_cpar_right
                            with Not_found -> IntSet.empty))
            tab.box_cpar_right }

    (* move branching (for all) *)

    (* diam star *)
    | (Node (x, Diam (alpha, phi)) as n)::t when size alpha = More ->
        proceed_todo {tab with
          todo = t;
          branching = n::tab.branching}
    (* box ? *)
    | (Node (x, Neg (Diam (Test phi, psi))) as n)::t ->
        proceed_todo {tab with
          todo = t;
          branching = n::tab.branching}

    (* move waiting *)
    | (Node (x, _) as n)::t when x != tab.current ->
        proceed_todo {tab with
          todo = t;
          waiting = n::tab.waiting}
    | (Edge (x, _,_) as n)::t when x != tab.current ->
        proceed_todo {tab with
          todo = t;
          waiting = n::tab.waiting}
    | (Sepa (x,_,_,_) as n)::t when x != tab.current ->
        proceed_todo {tab with
          todo = t;
          waiting = n::tab.waiting}

    (* Universals (for current) *)

    (* Box *)
    | (Node (x, Neg (Diam (Atom a, phi))))::t ->
        let neg_phi = neg phi in
        proceed_todo {tab with
          todo = List.fold_left
                  (fun acc y -> (Node (y, neg_phi))::acc)
                  t ( try StringMap.find a tab.box_atom_succ
                      with Not_found -> [] ) ;
          box_atom_form = StringMap.add a
                  (neg_phi::( try StringMap.find a tab.box_atom_form
                          with Not_found -> []))
                  tab.box_atom_form }
    | (Edge (x,y, Atom a))::t ->
        proceed_todo {tab with
          todo = List.fold_left
                  (fun acc phi -> (Node (y, phi))::acc)
                  t ( try StringMap.find a tab.box_atom_form
                      with Not_found -> [] ) ;
          box_atom_succ = StringMap.add a
                  (y::( try StringMap.find a tab.box_atom_succ
                        with Not_found -> []))
                  tab.box_atom_succ }


    (* move branching (for current) *)

    | (Edge (x,y, Seq (alpha, beta)) as n)::t ->
        proceed_todo {tab with
          todo = t;
          branching = n::tab.branching}
    | (Edge (x,y, Iter alpha) as n)::t when x != y ->
        proceed_todo {tab with
          todo = t;
          branching = n::tab.branching}

    (* move successor *)

    | _ -> failwith "todo"
