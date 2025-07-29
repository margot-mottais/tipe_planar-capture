(*
  Copyright (c) 2025 Margot Mottais
  Licensed under CC BY-NC-SA 4.0 (https://creativecommons.org/licenses/by-nc-sa/4.0/)

  You are free to:
  - Share — copy and redistribute the material in any medium or format
  - Adapt — remix, transform, and build upon the material

  Under the following terms:
  - Attribution — You must give appropriate credit, provide a link to the license,
    and indicate if changes were made. You may do so in any reasonable manner,
    but not in any way that suggests the licensor endorses you or your use.
  - NonCommercial — You may not use the material for commercial purposes.
  - ShareAlike — If you remix, transform, or build upon the material,
    you must distribute your contributions under the same license.

  See the full license at: https://creativecommons.org/licenses/by-nc-sa/4.0/
*)

(* IMPLEMENTATION DE DIJKSTRA PAR FILE DE PRIORITE **************************)

type graph = int list array

type couple =
  { key: int
  ; mutable prio: int }

type heap =
  { arr: couple array
  ; pos: int array
  ; mutable size: int }

type prioQ = heap
type matrix = int array array

type adj_matrix = bool array array


(* Implementation du tas *)

let up (i : int) = (i - 1) / 2
let left (i : int) = (2 * i) + 1
let right (i : int) = (2 * i) + 2
let pd (i : int) (h : heap) = h.arr.(i).prio

let swap (t : 'a array) (i : int) (j : int) =
  let tmp = t.(i) in
  t.(i) <- t.(j);
  t.(j) <- tmp

let full_swap (h : heap) (i : int) (j : int) =
  swap h.pos h.arr.(i).key h.arr.(j).key ;
  swap h.arr i j

let rec sift_down (h : heap) (i : int) =
  let prio m = pd m h in
  let n = h.size in
  let l = left i in
  let r = right i in
  let smallest = ref i in
  if l < n && prio l < prio i then 
    smallest := l;
  if r < n && prio r < prio !smallest then
    smallest := r;
  if !smallest <> i then begin
    full_swap h i !smallest;
    sift_down h !smallest
  end

let rec sift_up (h : heap) (i : int) =
  if i = 0 then ()
  else
    let p = up i in
    if pd i h < pd p h then (full_swap h i p ; sift_up h p)

let insert (c : couple) (h : heap) =
  if h.pos.(c.key) <> -1 then failwith "clé déjà présente"
  else if Array.length h.arr = h.size then failwith "le tas est plein"
  else
    let n = h.size in
    h.arr.(n) <- c ;
    h.pos.(c.key) <- n ;
    h.size <- h.size + 1 ;
    sift_up h n

let pop (h : heap) : couple =
  if h.size = 0 then failwith "tas vide"
  else
    let n = h.size in
    let res = h.arr.(0) in
    full_swap h 0 (n - 1) ;
    h.pos.(res.key) <- -1 ;
    h.size <- h.size - 1 ;
    if h.size > 0 then sift_down h 0 ;
    res

(** Interface de la file de priorite *)

let file_prio_vide (n : int) : prioQ =
  let data = Array.make n {key= -1; prio= max_int} in
  {arr= data; pos= Array.make n (-1); size= 0}

let est_vide (f : prioQ) : bool = f.size = 0
let extraire_min (f : prioQ) : couple = pop f
let inserer (f : prioQ) (c : int) (p : int) : unit = insert {key= c; prio= p} f

let diminuer_prio_dij (f : prioQ) (c : int) (p' : int) : unit =
  let n = Array.length f.pos in
  if c >= n then failwith "pas un sommet du graphe"
  else if f.pos.(c) = -1 then failwith "pas dans le tas"
  else
    let i = f.pos.(c) in
    let p = f.arr.(i).prio in
    if p' > p then failwith "ce n'est pas une diminution" ;
    f.arr.(i).prio <- p' ;
    sift_up f i

(** Dijkstra qui renconstruit les chemins *)

let dij_recons (g : graph) (s : int) : int array =
  (* renvoie le père dans le chemin le plus court de tous les sommets vers s*)
  let n = Array.length g in
  if s >= n then failwith "ce sommet ne fait pas partie du graphe" ;
  let dist = Array.make n max_int in
  dist.(s) <- 0 ;
  let pere = Array.make n (-1) in
  pere.(s) <- s ;
  let ouverts = file_prio_vide n in
  inserer ouverts s 0 ;
  while not (est_vide ouverts) do
    let c = extraire_min ouverts in
    let j, dj = (c.key, c.prio) in
    let traite (k : int) : unit =
      (* si les arrêtes ne sont pas pondérées, rho(j->k) = 1*)
      let d = dj + 1 in
      if d < dist.(k) then (
        if dist.(k) < max_int then diminuer_prio_dij ouverts k d
        else inserer ouverts k d ;
        dist.(k) <- d ;
        pere.(k) <- j ) in
    List.iter traite g.(j)
  done ;
  pere

(* si on veut en une seule matrice le suivant pour aller d'un sommet s à p du graphe on a O(n * (n+p) * log n) <= O(n3) avec Floyd-Warshall*)

(* attention la matrice n'est pas symétrique !! s -> p != p -> s même si graphe non orienté*)

let dij_next (g : graph) (s : int) : int array =
  let n = Array.length g in
  let next = Array.make n (-1) in
  let pere = dij_recons g s in
  for i = 0 to n - 1 do
    let curr = ref i in
    while pere.(!curr) <> s do
      curr := pere.(!curr)
    done ;
    next.(i) <- !curr
  done ;
  next

let dij_next_matrix (g : graph) : matrix =
  let n = Array.length g in
  let m_next = Array.make_matrix n n (-1) in
  for i = 0 to n - 1 do
    m_next.(i) <- dij_next g i
  done ;
  m_next

(****************************************************************************)