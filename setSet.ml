type filter_status = Ok | Wrong | Possible

module Make (S : Set.S)
= struct

  include Set.Make (S)

  let filtered_subsets fct set =
    let fold_elt elt (ok1, possible1) =
      let fold_set set (ok, possible) =
        let nset = S.add elt set in
        match fct nset with
         | Ok -> (add nset ok, possible)
         | Possible -> (ok, add nset possible)
         | Wrong -> (ok, possible)
      in
      let (ok2, possible2) = fold fold_set ok1 (ok1, possible1) in
      fold fold_set possible1 (ok2, possible2)
    in
    let init = match fct S.empty with
     | Ok -> (singleton S.empty, empty)
     | _  -> (empty, singleton S.empty)
    in
    fst (S.fold fold_elt set init)

  let to_list_list ss =
    List.map S.elements (elements ss)

end
