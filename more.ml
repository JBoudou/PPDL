let rec chain_compare = function
  | [] -> 0
  | h::t ->
      let cmp = Lazy.force h in
      if cmp != 0 then cmp else chain_compare t

let ( --> ) a b = (not a) || b

module List
= struct
  include List

  let compare elt_cmp la lb =
    let rec aux la lb = match (la,lb) with
      | ([], []) -> 0
      | (h1::t1, h2::t2) -> chain_compare [lazy (elt_cmp h1 h2); lazy (aux t1 t2)]
      | _ -> failwith "More.List.compare impossible"
    in chain_compare [lazy (length la - length lb); lazy (aux la lb)]

  let rec fold_unordered_distinct_pair fct acc = function
    | [] -> acc
    | h::t -> fold_left (fun a v -> fct a v h) (fold_unordered_distinct_pair fct acc t) t

end
