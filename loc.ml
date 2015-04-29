type dir = L | R

type t = dir list

let rec compare l1 l2 = match (l1, l2) with 
  | ([], []) -> 0
  | ([], _) -> -1
  | (_, []) ->  1
  | (h1::t1, h2::t2) when h1 = h2 -> compare t1 t2
  | (L::_, _) -> -1
  | (R::_, _) ->  1
