(** Extension of the Pervasive module.
 
    @author Joseph Boudou
 *)

(** Return the first integer wich is not null.
    Usefull to build comparators.
    @deprecated
 *)
let rec chain_compare = function
  | [] -> 0
  | h::t ->
      let cmp = Lazy.force h in
      if cmp != 0 then cmp else chain_compare t

(** Implication boolean operator.
    The interpretation is sequential.
 *)
let ( --> ) a b = (not a) || b

(** Type identifying the side of a decomposition. *)
module Dir = struct
  type t = L | R

  let other_dir = function
    | L -> R
    | R -> L
end

module List
= struct
  include List

  (** Apply the function to all unordered non-identity pairs from the list.
      For instance,
      [fold_unordered_distinct_pair (fun acc a b -> (a,b)::acc) [] [1;2;3]]
      produces [ [(3, 1); (2, 1); (3, 2)] ].
    *)
  let rec fold_unordered_distinct_pair fct acc = function
    | [] -> acc
    | h::t -> fold_left (fun a v -> fct a v h) (fold_unordered_distinct_pair fct acc t) t

  (** Produce all the (reversed) lists constructed by selecting one side of each
      pair in the initial list.
   *)
  let all_choices chlst =
    let aux acc (a,b) =
      List.fold_left (fun acc lst -> (a::lst)::(b::lst)::acc) [] acc
    in
    List.fold_left aux [[]] chlst

  (** Fold without accumulator.
      If the list is empty, returns the second argument.
      For instance,
      [fold_notnil (+) 10 [1;2;3]] produces [6].
  *)
  let fold_notnil fct default = function
    | [] -> default
    | h::t -> List.fold_left fct h t

  (** Apply the given function to each element of
      the cartesian product of the two given lists,
      returning the list of results.
  *)
  let product fct la lb =
    List.fold_left  (fun acc1 v1 ->
                      List.fold_left (fun acc2 v2 -> (fct v1 v2)::acc2) acc1 lb)
                    [] la
end

module Format = struct
  include Format

  (** Print a list as in OCaml. *)
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
