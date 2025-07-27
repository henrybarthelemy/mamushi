open Printf
module NeighborSet = Set.Make (String)

type neighborst = NeighborSet.t

module Graph = Map.Make (String)

type grapht = neighborst Graph.t

module StringSet = Set.Make (String)

type livet = StringSet.t

let empty : grapht = Graph.empty

let add_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then
    g
  else
    Graph.add name NeighborSet.empty g
;;

let add_directed_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_node (add_node g n1) n2 in
  let curr_neighbors = Graph.find n1 g' in
  Graph.add n1 (NeighborSet.add n2 curr_neighbors) g'
;;

let add_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_directed_edge g n1 n2 in
  add_directed_edge g' n2 n1
;;

let get_neighbors (g : grapht) (name : string) : string list =
  if Graph.mem name g then
    NeighborSet.fold (fun n ns -> n :: ns) (Graph.find name g) []
  else
    []
;;

let get_vertices (g : grapht) : string list =
  let keys, _ = List.split (Graph.bindings g) in
  keys
;;

let smallest_degree_node (g : grapht) : string option =
  match get_vertices g with
  | [] -> None  
  | v :: vs ->
    let (min_degree, min_vertex) =
      List.fold_left
        (fun (cur_min, cur_min_v) v ->
          let degree = (List.length (get_neighbors g v)) in
          if degree < cur_min then (degree, v) else (cur_min, cur_min_v))
        ((List.length (get_neighbors g v)), v)
        vs
    in
    Some min_vertex
;;

let remove_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then 
    let g' = Graph.remove name g in  
    Graph.map (fun neighbors -> NeighborSet.remove name neighbors) g'  
  else
    g
;;

let graph_merge (g1 : grapht) (g2 : grapht) : grapht =
  Graph.union (fun _ n1 n2 -> Some (NeighborSet.union n1 n2)) g1 g2
;;

let string_of_graph (g : grapht) : string =
  let string_of_neighbors (n : string) : string = ExtString.String.join ", " (get_neighbors g n) in
  ExtString.String.join "\n"
    (List.map (fun k -> sprintf "%s: %s" k (string_of_neighbors k)) (get_vertices g))
;;
