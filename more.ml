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

  let all_choices chlst =
    let aux acc (a,b) =
      List.fold_left (fun acc lst -> (a::lst)::(b::lst)::acc) [] acc
    in
    List.fold_left aux [[]] chlst

end

module Format = struct
  include Format

  let pp_print_list print_elt fmt lst =
    let rec aux = function
      | [] -> ()
      | h::[] ->
        ( print_elt fmt h
        )
      | h::t ->
        ( print_elt fmt h ;
          pp_print_string fmt ";" ;
          pp_print_break fmt 1 1 ;
          aux t
        )
    in 
    pp_open_box fmt 0 ;
    pp_print_string fmt "[" ;
    aux lst ;
    pp_print_string fmt "]" ;
    pp_close_box fmt ()

end


module OrderedInt = struct
  type t = int
  let compare = (-)
end

module IntSet = Set.Make (OrderedInt)
module IntMap = Map.Make (OrderedInt)

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)
