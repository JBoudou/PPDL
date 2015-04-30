open More

module HSet
= struct 

  include Set.Make (HForm)
  
  open HForm
  open Loc

  let fischer_ladner lf =
    let rec aux acc = function
      | [] -> acc
      | (_, Bot)::t -> aux acc t
      | h::t when (mem h acc) -> aux acc t
      | ((m, Diam (Atom _, phi)) as h)::t ->
          aux (add h acc) ((m, phi)::t)
      | ((m, Neg phi) as h)::t ->
          aux acc ((m, phi)::t)
      | ((m, Diam (Test phi, psi)) as h)::t ->
          aux acc ((m, phi)::(m, psi)::t)
      | ((m, Diam (Seq (alpha, beta), phi)) as h)::t ->
          aux acc ((m, Diam (alpha, Diam (beta, phi)))::t)
      | ((m, Diam (Choice (alpha, beta), phi)) as h)::t ->
          aux acc ((m, Diam (alpha, phi))::(m, Diam (beta, phi))::t)
      | ((m, (Diam (Iter alpha, phi) as form)) as h)::t ->
          aux (add h acc) ((m, Diam (alpha, form))::(m, phi)::t)
      | ((m, Diam (CPar (alpha, beta), phi)) as h)::t ->
          aux (add h acc) ((L::m, Diam (alpha, PH (L, 1)))::(L::m, Diam (alpha, PH (L, 2)))::
                          (R::m, Diam (beta, PH (R, 1)))::(R::m, Diam (beta, PH (R, 2)))::(m, phi)::t)
      | h::t -> aux (add h acc) t
    in aux empty [lf]

  let sat (m, phi) set =
    let rec aux = function
      | Bot -> false
      | Neg phi -> not (aux phi)
      | Diam (Test phi, psi) -> (aux phi) && (aux psi)
      | Diam (Seq (alpha, beta), phi) -> aux (Diam (alpha, Diam (beta, phi)))
      | Diam (Choice (alpha, beta), phi) ->
         (aux (Diam (alpha, phi))) || (aux (Diam (beta, phi)))
      | phi -> mem (m, phi) set
    in
    aux phi

  let neg_closure set =
    fold (fun (loc, form) acc -> add (loc, neg form) acc) set set

  let depth s =
    try
      let (loc, _) = choose s in
      loc
    with Not_found -> []

  let is_Hintikka flc set = 
    let set_loc = depth set in
    let check_possible (loc, form) =
      loc = set_loc
    in
    let check_ok_forward (loc, form) =
      match form with
        | Diam (Iter alpha, phi) ->
            mem (loc, phi) set || mem (loc, Diam (alpha, form)) set
        | _ -> true
    in
    let check_ok_backward (loc, form) =
      loc != set_loc ||
      match form with
        | Diam (Iter alpha, phi) ->
            (mem (loc, phi) set || mem (loc, Diam (alpha, form)) set)
            --> (mem (loc, form) set)
        | _ -> true
    in
    if for_all check_possible set then
      if (not (is_empty set)) && (for_all check_ok_forward set)
                              && (for_all check_ok_backward flc)
      then SetSet.Ok else SetSet.Possible
    else SetSet.Wrong

end

module SetHSet
= struct

  include SetSet.Make (HSet)

  let fold_product f acc t1 t2 =
    let second e1 acc =
      fold (fun e2 acc -> f acc e1 e2) t2 acc
    in fold second t1 acc 

end

type t = HSet.t * SetHSet.t

let construct form =
  let flc = HSet.neg_closure (HSet.fischer_ladner ([], HForm.translate form)) in
  (flc, SetHSet.filtered_subsets (HSet.is_Hintikka flc) flc)

let at_depth (_,ss) loc =
  SetHSet.filter (fun s -> HSet.depth s = loc) ss

let fold_set fct (_,ss) = SetHSet.fold fct ss

let forms_with_loc (s,_) loc =
  HSet.filter (fun (l,_) -> l = loc) s
