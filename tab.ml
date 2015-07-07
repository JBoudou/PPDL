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

module DoubleProg = struct 
  type t = TForm.prog * TForm.prog
  let compare = Pervasives.compare
end

module DoubleProgSet = Set.Make (DoubleProg)

module FormSet = Set.Make (TForm.Form)
module FormSetSet = Set.Make (FormSet)

module IntProgMap = Map.Make (struct
  type t = int * TForm.prog
  let compare = Pervasives.compare
end)

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
  box_cpar_forw : (TForm.prog * int * TForm.prog) list;
  box_cpar_back :       (TForm.prog * TForm.prog) list;
  box_sep_forw : (int * int) list;
  box_sep_back : (int * int) list;
  box_cpar_left   : IntSet.t IntMap.t;
  box_cpar_right  : IntSet.t IntMap.t;
  g_par_form : TForm.form IntMap.t;
  (* state *)
  current : int;
  fresh : int;
  suspended: int IntMap.t;
  terminated : IntSet.t;
  (* loop check *)
  checked : bool;
  check_main : FormSetSet.t;
  check_iter : FormSetSet.t IntProgMap.t;
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
  box_cpar_forw = [];
  box_cpar_back = [];
  box_sep_forw = [];
  box_sep_back = [];
  box_cpar_left  = IntMap.empty;
  box_cpar_right = IntMap.empty;
  g_par_form = IntMap.empty;
  current = 0;
  fresh = 1;
  suspended  = IntMap.empty;
  terminated = IntSet.empty;
  checked = false;
  check_main = FormSetSet.empty;
  check_iter = IntProgMap.empty;
}

exception Nothing_Todo
exception No_rule of judgment

let select tab ncur =
  let partition = function
    | Node (x, _)     -> x = ncur
    | Edge (x,_,_)    -> x = ncur
    | Sepa (x,_,_,_)  -> x = ncur
  in
  let (ntodo, nwaiting) = List.partition partition tab.waiting
  in
  { tab with
      todo = ntodo;
      branching = [];
      successor = [];
      waiting = nwaiting;
      box_atom_form = StringMap.empty;
      box_atom_succ = StringMap.empty;
      box_cpar_forw = [];
      box_cpar_back = [];
      box_sep_forw = [];
      box_sep_back = [];
      box_cpar_left  = IntMap.empty;
      box_cpar_right = IntMap.empty;
      current = ncur;
      suspended = IntMap.remove ncur tab.suspended;
      checked = false;
  }

let make_formset tab =
  let add_form_list acc = function
    | Node (x, phi) when x = tab.current -> FormSet.add phi acc
    | _ -> acc
  in
  List.fold_left (fun acc f -> f acc) (FormSet.empty)
  [
    (fun acc -> List.fold_left add_form_list acc tab.todo );
    (fun acc -> List.fold_left add_form_list acc tab.branching );
    (fun acc -> List.fold_left add_form_list acc tab.successor );
    IntStringSet.fold
      (fun elt acc -> match elt with
        | (n, s) when n = tab.current -> FormSet.add (Var s) acc
        | _ -> acc)
      tab.var_pos ;
    IntStringSet.fold
      (fun elt acc -> match elt with
        | (n, s) when n = tab.current -> FormSet.add (Neg (Var s)) acc
        | _ -> acc)
      tab.var_neg ;
    StringMap.fold
      (fun alpha lst acc ->
        List.fold_left
          (fun acc phi -> FormSet.add (Neg (Diam (Atom alpha, neg phi))) acc)
          acc lst)
      tab.box_atom_form ;
    (fun acc ->
      List.fold_left
        (fun acc (alpha, i, beta) ->
          FormSet.add
            (Neg (Diam (CPar (alpha, i, beta),
                        neg (IntMap.find i tab.g_par_form))))
            acc)
        acc tab.box_cpar_forw );
    (fun acc ->
      List.fold_left
        (fun acc (alpha, beta) ->
          FormSet.add
            (Neg (Diam (CPar (alpha, 0, beta), top)))
            acc)
        acc tab.box_cpar_back );
  ]


(* TODO: remove this debuging exception *)
exception Argh of int list


(* TODO: factor size computation *)
let rec proceed_todo tab =
  match tab.todo with
    | [] -> proceed_branching tab

    (* remove garbage *)

    | (Edge (x,y, Iter _))::t when x = y ->
        proceed_todo {tab with todo = t}
    | (Node (_, Neg Bot))::t ->
        proceed_todo {tab with todo = t}

    (* conjunctive non-successor rules for all *)

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
          todo = (Node (x, neg phi))::(Node (x, Neg (Diam (alpha, neg psi))))::t}

    (* check inconsistency *)

    | (Node (_, Bot))::_ -> false
    | (Node (x, Var v))::t ->
        if IntStringSet.mem (x,v) tab.var_neg then false else
        proceed_todo {tab with
          todo = t;
          var_pos = IntStringSet.add (x,v) tab.var_pos}
    | (Node (x, Neg (Var v)))::t ->
        if IntStringSet.mem (x,v) tab.var_pos then false else
        proceed_todo {tab with
          todo = t;
          var_neg = IntStringSet.add (x,v) tab.var_neg}

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

    (* conjunctive non-successor rules for current *)

    (* diam ;11 *)
    | (Edge (x,y, Seq (alpha, beta)))::t
        when size alpha = One && size beta = One ->
        proceed_todo {tab with
          todo = (Edge (x, tab.fresh, alpha))::(Edge (tab.fresh, y, beta))::t ;
          fresh = tab.fresh + 1 }
    (* diam || 00 *)
    | (Edge (x,y, CPar (alpha, i, beta)))::t
        when x = y ->
        proceed_todo {tab with
          todo =
            (Sepa (x, tab.fresh, tab.fresh + 1, Forw))::
            (Edge (tab.fresh,     tab.fresh,    alpha))::
            (Edge (tab.fresh + 1, tab.fresh + 1, beta))::t;
          fresh = tab.fresh + 2}
    (* diam || 0. *)
    | (Edge (x,y, CPar (alpha, i, beta)))::t
        when size alpha = Zero ->
        proceed_todo {tab with
          todo =
            (Sepa (x, tab.fresh, tab.fresh + 1, Forw))::
            (Edge (tab.fresh,     tab.fresh,    alpha))::
            (Edge (tab.fresh + 1, tab.fresh + 2, beta))::
            (Sepa (y, tab.fresh, tab.fresh + 2, Back))::t;
          fresh = tab.fresh + 3}
    (* diam || 0. *)
    | (Edge (x,y, CPar (alpha, i, beta)))::t
        when size beta = Zero ->
        proceed_todo {tab with
          todo =
            (Sepa (x, tab.fresh, tab.fresh + 1, Forw))::
            (Edge (tab.fresh,     tab.fresh + 2, alpha))::
            (Edge (tab.fresh + 1, tab.fresh + 1,  beta))::
            (Sepa (y, tab.fresh + 2, tab.fresh + 1, Back))::t;
          fresh = tab.fresh + 3}
    (* diam || 11 *)
    | (Edge (x,y, CPar (alpha, i, beta)))::t
        when size alpha = One && size beta = One ->
        proceed_todo {tab with
          todo =
            (Sepa (x, tab.fresh, tab.fresh + 1, Forw))::
            (Edge (tab.fresh,     tab.fresh + 2, alpha))::
            (Edge (tab.fresh + 1, tab.fresh + 3,  beta))::
            (Sepa (y, tab.fresh + 2, tab.fresh + 3, Back))::t;
          fresh = tab.fresh + 4}


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
    (* Box || *)
    | (Node (x, Neg (Diam (CPar (alpha, i, beta) as gamma, phi))) as n)::t 
        when size gamma = Zero ->
        proceed_todo {tab with
          todo = t;
          branching = n::tab.branching}
    | (Node (x, Neg (Diam (CPar (alpha, i, beta) as gamma, phi))))::t 
        when size gamma = One ->
        proceed_boxpar1F x alpha i beta phi {tab with todo = t}
    | (Node (x, Neg (Diam (CPar (alpha, i, beta) as gamma, phi))) as j)::t 
        when size gamma = More ->
        proceed_boxpar1F x alpha i beta phi {tab with
          todo = t;
          branching = j::tab.branching}

    (* Sep *) (* We move them all to branching because of rule box||0bot *)
    | (Sepa (_,_,_,_) as j)::t ->
        proceed_todo {tab with
          todo = t;
          branching = j::tab.branching }


    (* move branching (for current) *)

    | (Edge (x,y, Seq (alpha, beta)) as n)::t ->
        proceed_todo {tab with
          todo = t;
          branching = n::tab.branching}

    (* move successor *)

    | (Node (x, Diam (_, _)) as j)::t ->
        proceed_todo {tab with
          todo = t;
          successor = j::tab.successor}
    | (Edge (x,y, Iter alpha) as n)::t when x != y ->
        proceed_todo {tab with
          todo = t;
          successor = n::tab.successor}

    (* error *)

    | j::_ -> raise (No_rule j)


and proceed_boxpar1F x alpha i beta phi tab =
  let aux acc (y,z) =
    (Node (y, Neg (Diam (alpha, Neg (PH (Dir.L, i))))))::
    (Node (y, Neg (Diam (beta,  Neg (PH (Dir.R, i))))))::acc
  in proceed_todo {tab with
    todo = List.fold_left aux tab.todo tab.box_sep_forw;
    box_cpar_forw = (alpha, i, beta)::tab.box_cpar_forw;
    g_par_form = IntMap.add i (neg phi) tab.g_par_form;
  }

and branch lst =
  List.exists proceed_todo lst

and proceed_branching tab =
  match tab.branching with
    | [] -> proceed_check tab

    (* diam star *)
    | (Node (x, Diam (alpha, phi)) as j)::t ->
        branch [
          {tab with
            branching = t;
            todo = (Edge (x,x, alpha))::(Node (x, phi))::tab.todo};
          {tab with
            branching = t;
            successor = j::tab.successor;}]
          
    (* box ? *)
    | (Node (x, Neg (Diam (Test phi, psi))))::t ->
        branch [
          {tab with
            branching = t;
            todo = (Node (x, neg phi))::tab.todo};
          {tab with
            branching = t;
            todo = (Node (x, neg psi))::tab.todo}]

    (* diam ; 1 star *)
    | (Edge (x,y, Seq (alpha, beta)))::t
        when size alpha = One ->
        (* assumed that size beta = More *)
        branch [
          {tab with
            branching = t;
            todo = (Edge (x,y, alpha))::(Edge (y,y, beta))::tab.todo};
          {tab with
            branching = t;
            todo =
              (Edge (x, tab.fresh, alpha))::(Edge (tab.fresh, y, beta))::tab.todo;
            fresh = tab.fresh + 1} ]

    (* diam ; star 1 *)
    | (Edge (x,y, Seq (alpha, beta)))::t
        when size beta = One ->
        (* assumed that size alpha = More *)
        branch [
          {tab with
            branching = t;
            todo = (Edge (x,x, alpha))::(Edge (x,y, beta))::tab.todo};
          {tab with
            branching = t;
            todo =
              (Edge (x, tab.fresh, alpha))::(Edge (tab.fresh, y, beta))::tab.todo;
            fresh = tab.fresh + 1} ]

    (* diam ; star star *)
    | (Edge (x,y, Seq (alpha, beta)))::t ->
        (* assumed that size alpha = More and size beta = More *)
        branch [
          {tab with
            branching = t;
            todo = (Edge (x,x, alpha))::(Edge (x,y, beta))::tab.todo};
          {tab with
            branching = t;
            todo = (Edge (x,y, alpha))::(Edge (y,y, beta))::tab.todo};
          {tab with
            branching = t;
            todo =
              (Edge (x, tab.fresh, alpha))::(Edge (tab.fresh, y, beta))::tab.todo;
            fresh = tab.fresh + 1} ]

    (* box || 1F (cpar forw) *)
    | (Sepa (x,y,z, Forw))::t ->
        proceed_boxpar0bot {tab with
          branching = t ;
          todo =
            List.fold_left
              (fun acc (alpha, i, beta) ->
                (Node (y, Neg (Diam (alpha, Neg (PH (Dir.L, i))))))::
                (Node (z, Neg (Diam (beta,  Neg (PH (Dir.R, i))))))::acc )
              tab.todo tab.box_cpar_forw ;
          box_sep_forw = (y,z)::tab.box_sep_forw ;
        } y z

    (* box || 1B (cpar back) *)
    | (Sepa (x,y,z, Back))::t ->
        let find_or_empty elt map = try IntMap.find elt map
                                    with Not_found -> IntSet.empty
        in
        proceed_boxpar0bot {tab with
          branching = t;
          todo =
            IntSet.fold
              (fun i acc -> (Node (x, IntMap.find i tab.g_par_form))::acc)
              (IntSet.inter (find_or_empty y tab.box_cpar_left)
                            (find_or_empty z tab.box_cpar_right))
              tab.todo;
          box_sep_forw = (y,z)::tab.box_sep_forw ;
        } y z
    
    (* box || 0 bot *)
    | (Node (x, Neg (Diam (CPar (alpha, i, beta) as gamma, Neg Bot))))::t
        when size gamma = Zero ->
        let add_todo = List.all_choices
          ( List.fold_left (fun acc (y,z) ->
                            ( Node (y, Neg (Diam (alpha, neg Bot))),
                              Node (z, Neg (Diam (beta,  neg Bot))) )::acc)
            [] (List.rev_append tab.box_sep_forw tab.box_sep_back)
          )
        in
        branch (List.map
                  (fun l -> {tab with
                    branching = t ;
                    todo = List.rev_append l tab.todo ;
                    box_cpar_back = (alpha,beta)::tab.box_cpar_back ;
                  })
                  add_todo)
    

    (* box || O top *)
    | (Node (x, Neg (Diam (CPar (alpha, i, beta) as gamma, phi))))::t ->
        (* asssumed that size gamma != One *)
        branch [
          {tab with
            branching = t;
            todo = (Node (x, neg phi))::tab.todo};
          {tab with
            branching = t;
            todo = (Node (x, Neg (Diam (desiter gamma, top))))::tab.todo} ]

    | j::_ -> raise (No_rule j)

and proceed_boxpar0bot tab y z =
  let todo_add = List.all_choices
    (List.map (fun (alpha, beta) -> Node (y, Neg (Diam (alpha, top))),
                                    Node (z, Neg (Diam (beta,  top))) )
              tab.box_cpar_back )
  in
  branch
    (List.map (fun to_add -> {tab with todo = List.rev_append tab.todo to_add})
              todo_add)

and proceed_check tab =
  if tab.checked then proceed_successor tab else
  let rec find_blocking = function
    | [] -> None
    | (Sepa (x,y,z,_))::_ when  (not (IntSet.mem x tab.terminated)) &&
                                ((y = tab.current) || (z = tab.current)) ->
          Some x
    | _::t -> find_blocking t
  in
  match find_blocking tab.waiting with
    | Some blocking ->
       proceed_waiting {tab with
          todo = [];
          branching = [];
          successor = [];
          waiting = List.fold_left List.rev_append
                    tab.waiting [tab.todo; tab.branching; tab.successor];
          suspended = IntMap.add tab.current blocking tab.suspended}
    | None -> (
  let check_set = make_formset tab in
  let rec find_iter_succ = function
    | [] ->
        if FormSetSet.mem check_set tab.check_main
        then proceed_waiting {tab with
          terminated = IntSet.add tab.current tab.terminated}
        else proceed_successor {tab with
          checked = true;
          check_main = FormSetSet.add check_set tab.check_main;
        }
    | (Edge (x, y, Iter alpha))::t ->
        let checksetset =
          try IntProgMap.find (y,alpha) tab.check_iter
          with Not_found -> FormSetSet.empty
        in
        if FormSetSet.mem check_set checksetset then false
        else proceed_successor {tab with
          checked = true;
          check_iter = IntProgMap.add (y,alpha)
                                      (FormSetSet.add check_set checksetset) 
                                      tab.check_iter
        }
    | _::t -> find_iter_succ t
  in find_iter_succ tab.successor
  )

and proceed_successor tab =
  match tab.successor with
    | [] -> proceed_waiting {tab with
              terminated = IntSet.add tab.current tab.terminated}

    (* diam 1 (or star) *)
    | (Node (x, Diam (alpha, phi)))::t ->
        (* assumed size alpha != Zero *)
        proceed_todo {tab with
          successor = t;
          todo = (Edge (x, tab.fresh, alpha))::(Node (tab.fresh, phi))::tab.todo;
          fresh = tab.fresh + 1}

    (* diam star diff *)
    | (Edge (x,y, Iter alpha))::t ->
        (* assumed size alpha != zero *)
        branch [
          {tab with
            successor = t;
            todo = (Edge (x,y, alpha))::tab.todo;
            check_iter = IntProgMap.remove (y, alpha) tab.check_iter;
          };
          {tab with
            successor = t;
            todo =  (Edge (x, tab.fresh, alpha))::
                    (Edge (tab.fresh, y, Iter alpha))::tab.todo;
            fresh = tab.fresh + 1} ]

    | j::_ -> raise (No_rule j)

and proceed_waiting tab =
  let rec make_candidate acc n =
    if n < 0 then acc else
    if (IntSet.mem n tab.terminated) ||
       ((IntMap.mem n tab.suspended) &&
        not (IntSet.mem (IntMap.find n tab.suspended) tab.terminated))
    then make_candidate               acc   (n - 1)
    else make_candidate (IntSet.add n acc)  (n - 1)
  in
  let eliminate acc = function
    | (Edge (x,y,_)) when x != y ->
        if IntSet.mem x tab.terminated
        then acc else IntSet.remove y acc
    | (Sepa (x,y,z, Back)) ->
        if (IntMap.mem y tab.suspended) && (IntMap.mem z tab.suspended)
        then acc else IntSet.remove x acc
    | _ -> acc
  in
  match tab.waiting with
    | [] -> true

    | lst ->
        let candidate = make_candidate IntSet.empty (tab.fresh - 1) in
        let selection = List.fold_left eliminate candidate tab.waiting in
        try
        proceed_todo (select tab (IntSet.choose selection))
        with Not_found -> raise (Argh (IntSet.elements tab.terminated))
