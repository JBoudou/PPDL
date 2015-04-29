open More

module type HINTIKKA
= sig

  type t
  
  module HSet :
  sig
    type elt
    type t

    val mem : elt -> t -> bool
    val for_all : (elt -> bool) -> t -> bool

    val depth : t -> Loc.t

    (* both have a type and the intersection of types is not empty (TODO: move it ?) *)
    val same_type : t -> t -> bool
    val compare : t -> t -> int
  end with
    type elt = HForm.t

  module SetHSet :
  sig
    type elt
    type t

    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_product : ('a -> elt -> elt -> 'a) -> 'a -> t -> t -> 'a

    (*
    let fold_product f acc t1 t2 =
      let second e1 acc =
        fold (fun e2 acc -> f acc e1 e2) t2 acc
      in fold second t1 acc 
    *)
  end with
    type elt = HSet.t

  val at_depth : t -> Loc.t -> SetHSet.t
  val fold_set : (HSet.t -> 'a -> 'a) -> t -> 'a -> 'a
  val forms_with_loc : t -> Loc.t -> HSet.t
end

module type S
= sig

  type model
  type hintikka

  val create_model : hintikka -> model
  val elimination : model -> (model * bool)
  val satisfies : HForm.form -> model -> bool

end

module Make (H : HINTIKKA) (* : S with hintikka = H.t *)
= struct

  type hintikka = H.t


  (* Plugs *)

  module Plug
  = struct 

    type t = (H.HSet.t * H.HSet.t * H.HSet.t)

    (*
    let all_plugs h =
      let with_head head l =
        let head_loc = H.HSet.depth head in
        let make_triple cur (plugs, left, right) =
          match H.HSet.depth cur with
            | Loc.L::t when t = head_loc ->
                let nplugs = List.fold_left
                              (fun p r -> if H.HSet.same_type cur r then (head, cur, r)::p else p)
                              plugs right
                in (nplugs, cur::left, right)
            | Loc.R::t when t = head_loc ->
                let nplugs = List.fold_left
                              (fun p l -> if H.HSet.same_type cur l then (head, l, cur)::p else p)
                              plugs left
                in (nplugs, left, cur::right)
            | _ -> (plugs, left, right)
        in
        let (plugs, _, _) = H.SetHSet.fold make_triple h (l, [], [])
        in plugs
      in H.SetHSet.fold with_head h []
    *)

    let all h =
      let aux s acc =
        let loc = H.HSet.depth s in
        H.SetHSet.fold_product (fun acc l r -> if H.HSet.same_type l r then (s,l,r)::acc else acc)
          acc (H.at_depth h (Loc.L::loc)) (H.at_depth h (Loc.R::loc))
      in H.fold_set aux h []

    let depth (b,_,_) = let base = H.HSet.depth b in [(Loc.L::base); (Loc.R::base)]

    let type_list (s,l,r) =
      let loc = H.HSet.depth s in
      List.filter (fun t -> H.HSet.mem ((Loc.L::loc), HForm.PH (Loc.L, t)) l &&
                            H.HSet.mem ((Loc.R::loc), HForm.PH (Loc.R, t)) r ) [1;2]

    let compare (s1,l1,r1) (s2,l2,r2) =
      chain_compare [ lazy (H.HSet.compare s1 s2);
                      lazy (H.HSet.compare l1 l2);
                      lazy (H.HSet.compare r1 r2) ]

  end

  (* Twines *)

  module Socket
  = struct

    type t = Plug.t list

    let belongs socket hset =
      let loc = H.HSet.depth hset in
      match socket with
      | [] -> loc = []
      | (_,l,r)::_ -> (loc = H.HSet.depth l) || (loc = H.HSet.depth r)

    let compare = List.compare Plug.compare

    let compatible_plugs h (s1,l1,r1) (s2,l2,r2) =
      let s_loc = H.HSet.depth s1 in
      (s_loc = H.HSet.depth s2) &&
      let check s1 l1 r1 s2 t = function
        | (loc, HForm.Diam (HForm.CPar (alpha, beta), phi)) as lf ->
            (not (H.HSet.mem (loc, phi) s2 &&
                  H.HSet.mem (Loc.L::loc, HForm.Diam (alpha, HForm.PH (Loc.L, t))) l1 &&
                  H.HSet.mem (Loc.R::loc, HForm.Diam (beta,  HForm.PH (Loc.R, t))) r1 ))
            || H.HSet.mem lf s1
        | _ -> true
      in
      let forms = H.forms_with_loc h s_loc in
      List.for_all (fun t -> H.HSet.for_all (check s1 l1 r1 s2 t) forms) (Plug.type_list (s1,l1,r1))&&
      List.for_all (fun t -> H.HSet.for_all (check s2 l2 r2 s1 t) forms) (Plug.type_list (s2,l2,r2))

    let fold_all fct h acc =
      let acc = fct [] acc in
      let plugs = Plug.all h in
      let acc = List.fold_left (fun acc elt -> fct [elt] acc) acc plugs in
      let filt acc p1 p2 =
        if compatible_plugs h p1 p2 then fct [p1;p2] acc else acc
      in
      List.fold_unordered_distinct_pair filt acc plugs 

    let depth = function
      | [] -> []
      | p::_ -> Plug.depth p

  end
    

  (* Models *)

  module State
  = struct
    type t = H.HSet.t * (HForm.prog, H.SetHSet.t) Hashtbl.t
    let compare (s1, _) (s2, _) = H.HSet.compare s1 s2
  end

  module Twine = Set.Make (State)

  module Model = Map.Make (Socket)

  type model = Twine.t Model.t

  let create_model h =
    let construct sock m =
      let add_set set acc = Twine.add (set, Hashtbl.create 4) acc in
      let add_loc acc loc = H.SetHSet.fold add_set (H.at_depth h loc) acc in 
      let twine = List.fold_left add_loc Twine.empty (Socket.depth sock) in
      Model.add sock twine m
    in
    Socket.fold_all construct h Model.empty
  

end
