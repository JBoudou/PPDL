open More

module type HINTIKKA
= sig

  type t
  
  module HSet :
  sig
    type elt
    type t

    val empty : t
    val mem : elt -> t -> bool
    val sat : elt -> t -> bool
    val add : elt -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val compare : t -> t -> int

    val depth : t -> Dir.t

  end with
    type elt = HForm.t

  module SetHSet :
  sig
    type elt
    type t

    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val diff : t -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val choose : t -> elt

    val fold_product : ('a -> elt -> elt -> 'a) -> 'a -> t -> t -> 'a

  end with
    type elt = HSet.t

  val at_depth : t -> Dir.t -> SetHSet.t
  val fold_set : (HSet.t -> 'a -> 'a) -> t -> 'a -> 'a
  val forms_with_loc : t -> Dir.t -> HSet.t
end

module type S
= sig

  type model
  type hintikka

  val create_model : hintikka -> model
  val elimination : model -> (model * bool)
  val satisfies : HForm.form -> model -> bool

end

module Make (H : HINTIKKA) (* : S with type hintikka = H.t *)
= struct

  type hintikka = H.t


  (* Plugs *)

  module Plug
  = struct 

    type t = (H.HSet.t * H.HSet.t * H.HSet.t)

    let same_type l r =
      let simple_mem form set =
        H.HSet.sat (H.HSet.depth set, form) set
      in
      List.exists (fun t -> simple_mem (HForm.PH (Dir.L, t)) l && simple_mem (HForm.PH (Dir.R, t)) r)
                  [1;2]

    let type_list (s,l,r) =
      let loc = H.HSet.depth s in
      List.filter (fun t -> H.HSet.sat ((Dir.L::loc), HForm.PH (Dir.L, t)) l &&
                            H.HSet.sat ((Dir.R::loc), HForm.PH (Dir.R, t)) r ) [1;2]

    let all h =
      let aux s acc =
        let loc = H.HSet.depth s in
        H.SetHSet.fold_product (fun acc l r -> if same_type l r then (s,l,r)::acc else acc)
          acc (H.at_depth h (Dir.L::loc)) (H.at_depth h (Dir.R::loc))
      in H.fold_set aux h []

    let depth (b,_,_) = let base = H.HSet.depth b in [(Dir.L::base); (Dir.R::base)]

    let compare (s1,l1,r1) (s2,l2,r2) =
      chain_compare [ lazy (H.HSet.compare s1 s2);
                      lazy (H.HSet.compare l1 l2);
                      lazy (H.HSet.compare r1 r2) ]

  end

  (* Twines *)

  module DirSocket
  = struct

    type t =
      | Initial
      | Zero of Dir.dir * Plug.t
      | Nonzero of Dir.dir * Plug.t * Plug.t

    let compare = Pervasives.compare

    let compatible_plugs h (s1,l1,r1) (s2,l2,r2) =
      let s_loc = H.HSet.depth s1 in
      (s_loc = H.HSet.depth s2) &&
      let check s1 l1 r1 s2 t = function
        | (loc, HForm.Diam (HForm.CPar (alpha, beta), phi)) as lf ->
            (not (H.HSet.sat (loc, phi) s2 &&
                  H.HSet.sat (Dir.L::loc, HForm.Diam (alpha, HForm.PH (Dir.L, t))) l1 &&
                  H.HSet.sat (Dir.R::loc, HForm.Diam (beta,  HForm.PH (Dir.R, t))) r1 ))
            || H.HSet.sat lf s1
        | _ -> true
      in
      let forms = H.forms_with_loc h s_loc in
      List.for_all (fun t -> H.HSet.for_all (check s1 l1 r1 s2 t) forms) (Plug.type_list (s1,l1,r1))&&
      List.for_all (fun t -> H.HSet.for_all (check s2 l2 r2 s1 t) forms) (Plug.type_list (s2,l2,r2))

    let fold_all fct h acc =
      let acc = fct Initial acc in
      let plugs = Plug.all h in
      let acc =
        List.fold_left
          (fun acc elt -> fct (Zero (Dir.L,elt)) (fct (Zero (Dir.R,elt)) acc))
          acc plugs in
      let filt acc p1 p2 =

        if compatible_plugs h p1 p2
        then fct (Nonzero (Dir.L, p1,p2)) (fct (Nonzero (Dir.R, p1,p2)) acc)
        else acc
      in
      List.fold_unordered_distinct_pair filt acc plugs 

    let depth = function
      | Initial -> []
      | Zero    (d,(s,_,_))   -> d::(H.HSet.depth s)
      | Nonzero (d,(s,_,_),_) -> d::(H.HSet.depth s)

    let other_side = function
      | Initial -> Initial
      | Zero (d, p) -> Zero (Dir.other_dir d, p)
      | Nonzero (d, p1, p2) -> Nonzero (Dir.other_dir d, p1, p2)

  end
    

  (* Models *)

  module State
  = struct
    type t = H.HSet.t * (HForm.prog, H.SetHSet.t) Hashtbl.t
    let compare (s1, _) (s2, _) = H.HSet.compare s1 s2
  end

  module Thread
  = struct 
    include Set.Make (State)

    let filter_set fct thread =
      fold (fun (s,_) shs -> if fct s then H.SetHSet.add s shs else shs) thread H.SetHSet.empty
  end

  module Model = Map.Make (DirSocket)

  type model = H.t * Thread.t Model.t
 
  let create_model h =
    let construct dsock m =
      let add_set set acc = Thread.add (set, Hashtbl.create 4) acc in
      let add_loc acc loc = H.SetHSet.fold add_set (H.at_depth h loc) acc in 
      Model.add dsock (add_loc Thread.empty (DirSocket.depth dsock)) m
    in
    h, DirSocket.fold_all construct h Model.empty
  


  (* Reachability *)


  let rec reachable prog set hm thread =
    (* TODO: hash should be eventually provided *)
    let (set, hash) = Thread.find (set, Hashtbl.create 0) thread in
    let nreach =
      try
        let old_reach = Hashtbl.find hash prog in
        (* TODO: this is not very smart... *)
        Thread.filter_set (fun set -> H.SetHSet.mem set old_reach) thread
      with Not_found ->
        reach prog set hm thread
    in
    Hashtbl.replace hash prog nreach ;
    nreach

  and reach = function
    | HForm.Atom str              -> reach_prog str
    | HForm.Seq (alpha, beta)     -> reach_seq alpha beta
    | HForm.Test form             -> reach_test form
    | HForm.Choice (alpha, beta)  -> reach_choice alpha beta
    | HForm.Iter alpha            -> reach_iter alpha
    | HForm.CPar (alpha, beta)    -> reach_cpar alpha beta

  and reach_prog str set (h,m) thread =
    let loc = H.HSet.depth set in
    let filter_form lf acc = match lf with
      | (loc, HForm.Diam (HForm.Atom str2, phi)) as form
        when ((str2 = str) && (not (H.HSet.sat form set))) ->
          H.HSet.add (loc, phi) acc
      | _ -> acc
    in
    let forms = H.HSet.fold filter_form (H.forms_with_loc h loc) H.HSet.empty in
    let check dest =
      H.HSet.for_all (fun form -> not (H.HSet.sat form dest)) forms
    in
    Thread.filter_set check thread

  and reach_seq alpha beta cur hm thread =
    H.SetHSet.fold (fun z acc -> H.SetHSet.union acc  (reachable beta  z   hm thread))
                                                      (reachable alpha cur hm thread) H.SetHSet.empty

  and reach_test form set h thread =
    let loc = H.HSet.depth set in
    if H.HSet.sat (loc, form) set then H.SetHSet.singleton set else H.SetHSet.empty

  and reach_choice alpha beta cur hm thread =
    H.SetHSet.union (reachable alpha cur hm thread) (reachable beta cur hm thread)

  and reach_iter alpha cur hm thread =
    let rec aux acc todo =
      if H.SetHSet.is_empty todo then acc else
      let cur = H.SetHSet.choose todo in
      let ntodo = H.SetHSet.remove cur todo in
      let nreach = H.SetHSet.diff (reachable alpha cur hm thread) acc in
      aux (H.SetHSet.union nreach acc) (H.SetHSet.union nreach ntodo)
    in
    let initial = H.SetHSet.singleton cur in
    aux initial initial

  and reach_cpar alpha beta cur (h,m) thread =
    let check = function
      | DirSocket.Zero (Dir.L, (s,l,r)) as st
        when ((s = cur) &&
              (H.SetHSet.mem l (reachable alpha l (h,m) (Model.find st m))) &&
              (H.SetHSet.mem r (reachable alpha r (h,m) (Model.find (DirSocket.other_side st) m))))
        -> Some s
      | DirSocket.Nonzero (Dir.L, (s1,l1,r1), (s2,l2,r2)) as st
        when ((s1 = cur) && (Thread.mem (s2, Hashtbl.create 0) thread) &&
              (H.SetHSet.mem l2 (reachable alpha l1 (h,m) (Model.find st m))) &&
              (H.SetHSet.mem r2 (reachable alpha r1 (h,m) (Model.find (DirSocket.other_side st) m))))
        -> Some s2
      | DirSocket.Nonzero (Dir.L, (s2,l2,r2), (s1,l1,r1)) as st
        when ((s1 = cur) && (Thread.mem (s2, Hashtbl.create 0) thread) &&
              (H.SetHSet.mem l2 (reachable alpha l1 (h,m) (Model.find st m))) &&
              (H.SetHSet.mem r2 (reachable alpha r1 (h,m) (Model.find (DirSocket.other_side st) m))))
        -> Some s2
      | _ -> None
    in
    let aux dsock _ acc =
      match check dsock with
        | None -> acc
        | Some s -> H.SetHSet.add s acc
    in
    Model.fold aux m H.SetHSet.empty
      

  (* Elimination *)

  let elimination (h,m) =
    let aux dsocket thread ((h,m), modified) =
      let check_for_removal (set, hash) =
        let check_form = function
          | (loc, HForm.Diam (alpha, phi)) ->
              H.SetHSet.for_all (fun dest -> not (H.HSet.sat (loc, phi) dest))
                                (reachable alpha set (h,m) thread)
          | _ -> false
        in
        H.HSet.exists check_form set
      in
      let to_remove = Thread.filter check_for_removal thread in
      if Thread.is_empty to_remove then ((h,m), modified) else
      (* TODO: the update of memoized reachabilities should be updated here instead *)
      ((h, Model.add dsocket (Thread.diff thread to_remove) m), true)
    in
    Model.fold aux m ((h,m), false)


  let satisfies form (_,m) =
    Thread.exists (fun (set,_) -> H.HSet.sat ([], form) set) (Model.find DirSocket.Initial m)

end
