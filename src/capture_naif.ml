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

(* IMPLEMENTATION DE L'ALGORITHME NAIF *)

open Printf

(*structures *****************************************************************)

type graph = int list array

type game_state =
  { nb_tour: int
  ; pos_cop: int array
  ; mutable pos_x: int }

type classes_disjointes =
  { lien: int array
  ; rang: int array }

type couple =
  { key: int
  ; mutable prio: int }


type matrix = int array array

type adj_matrix = bool array array

type g_nature =
  | Tree of ((int * int) option)
  | Grid of ((int * int) option)
  | Planar_square of ((int * int) option)
  | Planar_hexa of ((int * int) option)
  | Planar_sq_full of ((int * int) option)
  | Planar_read of int option

type settings = {g : graph ; nb_cop : int; t_max: int}

(* CONSTRUCTION DUNE GRILLE ************************************************)
(* p lignes, q colonnes, (0, 0) en haut à gauche, (0, 1) directement à droite*)

let make_grid (p : int) (q : int) : graph =
  let g = Array.make (p * q) [] in
  let indice i j = i * q + j in
  for i = 0 to p - 1 do
    for j = 0 to q - 1 do
      let ajoute x y = g.(indice i j) <- indice x y :: g.(indice i j) in
      if i > 0 then ajoute (i - 1) j;
      if i < p - 1 then ajoute (i + 1) j;
      if j > 0 then ajoute i (j - 1);
      if j < q - 1 then ajoute i (j + 1) 
    done
  done ;
  g


(* CONSTRUCTION DUN ARBRE DE ELLER ******************************************)

let cd_trouve (cd : classes_disjointes) (i : int) =
  let k = ref i in
  while !k <> cd.lien.(!k) do
    k := cd.lien.(!k)
  done ;
  !k

let cd_union (cd : classes_disjointes) (i : int) (j : int) : unit =
  let repi = cd_trouve cd i in
  let repj = cd_trouve cd j in
  if repi <> repj then
    let rangi = cd.rang.(repi) in
    let rangj = cd.rang.(repj) in
    if rangj >= rangi then begin
      cd.lien.(repi) <- repj ;
      if rangj = rangi then cd.rang.(j) <- cd.rang.(j) + 1
    end
    else cd.lien.(repj) <- repi

let cd_init (n : int) : classes_disjointes =
  let cd = {lien= Array.make n (-1); rang= Array.make n 0} in
  for i = 0 to n - 1 do
    cd.lien.(i) <- i
  done ;
  cd

let connect (g : graph) (i : int) (j : int) (cd : classes_disjointes) : unit =
  g.(i) <- j :: g.(i) ;
  g.(j) <- i :: g.(j) ;
  cd_union cd i j

let knuth_shuffle (t : int array) : unit =
  for i = 0 to Array.length t - 1 do
    let j = Random.int (i + 1) in
    let tmp = t.(i) in
    t.(i) <- t.(j) ;
    t.(j) <- tmp
  done

let edges_line (i : int) (q : int) : int array =
  let line = Array.make (q - 1) (-1) in
  for j = 0 to q - 2 do
    line.(j) <- (i * q) + j
  done ;
  knuth_shuffle line ;
  line

let vertices_line (i : int) (q : int) : int array =
  let vert = Array.make q (-1) in
  for j = 0 to q - 1 do
    vert.(j) <- (i * q) + j
  done ;
  knuth_shuffle vert ;
  vert

let rec already_reped (m : int) (cd : classes_disjointes) (reps : int list) :
    bool =
  match reps with
  | [] -> false
  | x :: xs ->
      if cd_trouve cd x = cd_trouve cd m then true else already_reped m cd xs

let make_tree_eller (p : int) (q : int) : graph =
  let t = Array.make (p * q) [] in
  let cd = cd_init (p * q) in
  for i = 0 to p - 2 do
    let line = edges_line i q in
    for j = 0 to Array.length line - 1 do
      let v = line.(j) in
      if cd_trouve cd v <> cd_trouve cd (v + 1) then
        if Random.bool () then connect t v (v + 1) cd
    done ;
    let vertices = vertices_line i q in
    let reps = ref [] in
    for k = 0 to Array.length vertices - 1 do
      if not (already_reped vertices.(k) cd !reps) then
        reps := vertices.(k) :: !reps
    done ;
    List.iter (fun x -> connect t x (x + q) cd) !reps
  done ;
  let last_line = edges_line (p - 1) q in
  for j = 0 to Array.length last_line - 1 do
    let v = last_line.(j) in
    if cd_trouve cd v <> cd_trouve cd (v + 1) then connect t v (v + 1) cd
  done ;
  t

(****************************************************************************)


(* CONSTRUCTION DE GO_NEXT_MATRIX par parcours en largeur *)

let bfs (g : graph) (s : int) : int array =
  (* précondition : g est connexe *)
  (* parcours en largeur en partant de s, renvoie le tableau tq parent.(i) =
      sommet adjacent à i à emprunter pour aller en s par le plus court chemin*)
  let q = Queue.create () in
  let n = Array.length g in
  let parent = Array.make n (-1) in
  let vu = Array.make n false in
  Queue.push (s, s) q;
  while not (Queue.is_empty q) do
    let x, p = Queue.pop q in
    (* sommet, pere dans le bfs *)
    if not vu.(x) then begin 
      vu.(x) <- true;
      parent.(x) <- p;
      List.iter (fun y -> Queue.push (y, x) q) g.(x);
    end
  done;
  parent

let go_next_matrix (g : graph) : matrix =
  (* renvoie m tq m.(i).(j) = sommet adjacent à i à emprunter pour aller en j par le plus court chemin,
     ou lui-même cas échéant *)
  let n = Array.length g in
  let m = Array.make_matrix n n (-1) in
  for j = 0 to (n-1) do 
    let tj = bfs g j in
    for i = 0 to (n-1) do
      m.(i).(j) <- tj.(i)
    done;
  done;
  m
    

(****************************************************************************)

(* SELECTION ALEATOIRE D'UN GRAPHE PLANAIRE *********************************)

exception Found

let select_random_graph  (filename : string) : adj_matrix =
  let f = open_in filename in
  let first_line = input_line f in
  (* on ne gère pas l'exception mais precondition : le fichier contient bien cette premiere ligne*)
  let n, max = Scanf.sscanf first_line "n = %d, max = %d" (fun x y -> (x, y)) in
  let matrix = Array.make_matrix n n false in
  let rand_i = (Random.int max) + 1 in
  let get_graph () : unit =
    (* precondition : on vient de lire "Graph ... "*)
    for i = 0 to (n -1) do
      let s = input_line f in
      for j = 0 to (n-1) do
        let b =
          (if s.[j] = '0' then false
          else if s.[j] = '1' then true
          else failwith "get_graph" ) in
        matrix.(i).(j) <- b ;
      done
    done; 
  in
  let rec loop () =
    try
      let s = input_line f in
      if s <> "" && s.[0] = 'G' then begin
        let i = Scanf.sscanf s "Graph %d, order %d." (fun x y -> x) in
        if i = rand_i then raise Found ;
      end;
      loop ()
    with
    | End_of_file -> () 
    | Found -> get_graph () in
  loop ();
  matrix

let matrix_to_graph (m : adj_matrix) : graph =
  let n = Array.length m in
  let g = Array.make n [] in
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      if m.(i).(j) then g.(i) <- j :: g.(i)
        (* peu importe car les graphes sont non orientés *)
    done
  done;
  g

let get_random_graph_size (n : int)  : graph =
  if n <= 0 || n >= 9 then failwith "choisir une autre taille"
    (* ordre 9 disponible mais fichier txt trop gros -> stack overflow *)
    (* les autres ordres s'executent instantanément*)
  else begin
    let tmp = String.cat "planar" (string_of_int n) in
    let filename = String.cat tmp ".txt" in
    let m = select_random_graph filename in
    let g = matrix_to_graph m in
    g
  end



(*******************************)


(* GENERATION ALEATOIRE D'UN GRAPHE PLANAIRE *********************************)

let make_grid_hexa (p : int) (q : int) : graph =
  (* nb lignes : p *)
  (* nb sommets sur premiere ligne : q *)
  (* nb de sommets : q * (psup (p /. 2)) + (q-1) * (p/2)  = p * q - (p/2)*)
  let n = p * q - (p/2) in
  let g = Array.make n [] in
  let indice i j = i * q - (i/2) + j in
  (* on compte d'abord le pavage rempli aux lignes d'avant i : correspond bien au nb de lignes au dessus*)
  for i = 0 to p - 1 do 
    for j = 0 to q - 1 - (i mod 2) do
      let ajoute x y = g.(indice i j) <- indice x y :: g.(indice i j) in
      if (i mod 2 = 0) then begin
        if  j > 0 then begin
          ajoute i (j-1);
          if i > 0 then ajoute (i - 1) (j - 1);
          if i < (p-1) then ajoute (i + 1) (j - 1);
        end;
        if j < (q - 1) then begin
          ajoute i (j+1);
          if i > 0 then ajoute (i - 1) j;
          if i < (p-1) then ajoute (i + 1) j;
        end;
      end
      else begin
        ajoute (i-1) j;
        ajoute (i-1) (j+1);
        if j > 0 then ajoute i (j-1);
        if j < (q - 2) then ajoute i (j+1);
        if i < (p-1) then begin
          ajoute (i+1) j;
          ajoute (i+1) (j+1);
        end
      end
    done
  done ;
  g

let make_grid_full (p :int) (q : int)  : graph =
  (* pavage carré avec les diagonales tracées aléatoirement *)
  let g = make_grid p q in
  let indice i j = i * q + j in
  let trace_arrete i1 j1 i2 j2 = begin
    g.(indice i1 j1) <- indice i2 j2 :: g.(indice i1 j1);
    g.(indice i2 j2) <- indice i1 j1 :: g.(indice i2 j2)
  end in
  for i = 0 to (p - 2) do
    for j = 0 to (q - 2) do
      let diag = Random.bool () in
      if diag then trace_arrete i j (i + 1) (j + 1)
      (* on trace une diagonale pour remplir le carré*)
      else trace_arrete i (j+1) (i+1) j
      (* on trace une antidiagonale *)
    done
  done;
  g


let rec remove (x : 'a) (l : 'a list) : 'a list =
  (* precondition : x est present au plus une fois dans l*)
  match l with 
  | [] -> []
  | y :: ys when x = y -> ys
  | y :: ys -> y :: (remove x ys)

exception Cycle

let make_planar (p : int) (q : int) (graph_nature : g_nature): graph =
  let g, grid_edges, tree_edges = match graph_nature with
  | Planar_square _ -> (make_grid p q), (p * (q-1) + (p-1) * q), ((p * q) - 1)
  | Planar_hexa _ -> (make_grid_hexa p q), ((q - 1) * (3 * p - 2) - (p / 2)), (p * q - (p/2) - 1) 
  | Planar_sq_full _ -> (make_grid_full p q), (p * (q-1) + (p-1) * q + p * q), ((p * q) - 1)
  | _ -> failwith "make_planar"
  in
  let rec dfs (pere : int) (vu : bool array) (s : int) : unit =
    if vu.(s) then begin
      g.(pere) <- remove s g.(pere);
      g.(s) <- remove pere g.(s);
      raise Cycle
    end
    else begin
      vu.(s) <- true;
      List.iter (dfs s vu) (remove pere g.(s))
      (* ne modifie pas le graphe ni la correction de l'algorithme car pere a deja été vu parmi les voisins de s
         et evite qu'on ne supprime une arrête sur laquelle on vient juste de passer, qui n'est pas une vraie "back edge"*)
    end
  in
  let max = (grid_edges - tree_edges) in
  let edges_to_remove = match graph_nature with 
    | Planar_sq_full _ -> (Random.int (max/2)) + (max/4) + 1
    | _ -> (Random.int (max/2)) + (max/2) + 1 
  in
  (* donne (floor(max/2)) + 1 <= e_to_move <= max *)
  (* ATTENTION : argument de Random.int doit être non nul*)
  for i = 1 to edges_to_remove do
    try
    let vu = Array.make (p * q) false in
    let s = Random.int p*q in
    dfs s vu s
    with 
    | Cycle -> ()
  done;
  g
(* post-condition : g est connexe *)

(*******************************)

(*** Actions de jeu *)


exception XHere


let set_cop_fair (g : graph) (s : game_state) : unit =
  for i = 0 to Array.length s.pos_cop - 1 do
    s.pos_cop.(i) <- Random.int (Array.length g)
  done


let x_start (g : graph) (e0 : int) : int array =
  (*effectue un parcours en largeur pour trouver un des sommets le plus loin*)
  let n = Array.length g in
  let ouverts = Queue.create () in
  Queue.push (e0, 0) ouverts;
  let dist = Array.make n (-1) in
  let vus = Array.make n false in
  vus.(e0) <- true;
  dist.(e0) <- 0;
  while not (Queue.is_empty ouverts) do
    let x, d = Queue.pop ouverts in
    List.iter (fun y ->
      if not vus.(y) then begin
        Queue.push (y,d+1)  ouverts;
        dist.(y) <- d+1;
        vus.(y) <- true
      end) g.(x);
  done;
  dist

exception CopHere


let rand_max_dist (t : int array) (num_cop : int) (s : game_state): int = 
  let l_max = ref [] in
  let max = ref (- max_int) in
  let n = Array.length t in
  for i = 0 to n-1 do
    if t.(i) > !max then begin
      max := t.(i);
      l_max := [i]
    end
    else if t.(i) = !max then l_max := i :: !l_max;
  done;
  let rec filter (l : int list) =
    match l with 
    | [] -> []
    | x :: xs -> begin
      let stay = ref true in
      for i = 0 to num_cop - 1 do
        if s.pos_cop.(i) = x then stay := false
      done;
      if !stay then x :: (filter xs)
      else filter xs
    end
  in
  let l_new = filter !l_max in
  match l_new with 
    | [] -> Random.int n
    | _ -> begin
      let len = List.length l_new in
      let k = Random.int len in
      List.nth l_new k
    end



let set_x_fair (g : graph) (s : game_state) : bool =
  try
    let n = Array.length g in
    let num_cop = Array.length s.pos_cop in
    let dist_tot = Array.make n 0 in
    for i = 0 to (num_cop -1) do
      let ti = x_start g s.pos_cop.(i) in
      for j = 0 to (n-1) do
        dist_tot.(j) <- ti.(j) + dist_tot.(j) 
      done;
    done;
    let u = rand_max_dist dist_tot num_cop s in
    s.pos_x <- u;
    for i = 0 to num_cop - 1 do
      if s.pos_cop.(i) = u then raise CopHere
    done;
    true
  with 
  | CopHere ->false 



let move_x (g : graph) (s : game_state) : bool =
  (*renvoie false si m_x a perdu (ne peut se déplacer que sur une position compromettante, true sinon et bouge m_x a une telle position au hasard)*)
  let next_pos = g.(s.pos_x) in
  (* on suppose que la taille est raisonnable pour la convertir en liste*)
  let rec aux (u : int list) : int list =
    match u with
    | [] -> []
    | x :: xs -> (
      try
        for i = 0 to Array.length s.pos_cop - 1 do
          if x = s.pos_cop.(i) then raise CopHere
        done ;
        x :: aux xs
      with
      | CopHere -> aux xs ) in
  let list_next = aux next_pos in
  match list_next with
  | [] -> false
  | _ ->
      let tab_next = Array.of_list list_next in
      let n = Array.length tab_next in
      s.pos_x <- tab_next.(Random.int n) ;
      true

let move_cop (g : graph) (nmc : matrix) (s : game_state) : bool =
  try 
    for i = 0 to Array.length s.pos_cop - 1 do
      let next_pos = nmc.(s.pos_cop.(i)).(s.pos_x) in
      let move = ref true in
      for j = 0 to (i - 1) do
        if s.pos_cop.(j) = next_pos then move := false 
      done;
      if !move then s.pos_cop.(i) <- next_pos;
      if s.pos_cop.(i) = s.pos_x then raise XHere
    done;
    true 
  with
  | XHere -> false 


let show (s : game_state) : unit =
  let n = Array.length s.pos_cop in
  printf "Position X : %d \n" s.pos_x;
  for i = 0 to n - 1 do
    printf "Position cop n° %d : %d \n" i s.pos_cop.(i)
  done


let play_fair (g : graph) (nmc : matrix) (s : game_state) (t_max : int) : int =
  set_cop_fair g s;
  let cop_ok = ref (set_x_fair g s) in
  let t = ref 0 in
  while move_x g s && !cop_ok && !t <= t_max do
    cop_ok := move_cop g nmc s ;
    incr t;
  done ;
  if !t > t_max then t := -1 ;
  !t


let tests (nb_tests : int) (nb_cop : int) (t_max : int) : int array * int =
  let g = make_tree_eller (Random.int 8 + 1) (Random.int 8 + 1) in
  (* /!\ 1 <= _ <= 8, ne doit surtout pas être 0, cd_init raises "index out of bounds" sinon !*)
  let next_move_cop = go_next_matrix g in
  let tab_res = Array.make nb_tests (-1) in
  let nb_success = ref 0 in
  for i = 0 to nb_tests - 1 do
    let s = {nb_tour= 0; pos_cop= Array.make nb_cop (-1); pos_x= -1} in
    let res_i = play_fair g next_move_cop s t_max in
    (* -1 si echec / t : temps de succès > 1 *)
    tab_res.(i) <- res_i ;
    if res_i <> -1 then incr nb_success
  done ;
  (tab_res, !nb_success)



let set_options (graph_nature : g_nature) (nb_cop : int option) (t_max : int option) =
  let p, q = match graph_nature with
  | Tree (Some (h, w)) | Grid (Some (h, w))-> h, w
  | Planar_square (Some (h, w)) when (h >= 2 && w >2) || (h > 2 && w >=2) -> h, w
  (* cf explications dans create_planar : il faut (h, w) > (2, 2) pour lexico sinon max = 0 ou 1 *)
  | Planar_square _ -> (Random.int 7 + 2), (Random.int 6 + 3) 
  | Planar_hexa (Some (h, w)) when (h >= 3 && w >= h) -> h, w
  | Planar_hexa _ -> begin
    let h = (Random.int 6 + 3) in
    let w = (Random.int 6 + h) in
  (* attention on ne peut pas vraiment borner la valeur de w*)
    h, w
  end
  | Planar_sq_full (Some (h, w)) when (1, 1) < (h, w) -> h, w
  | Planar_sq_full _ -> (Random.int 8 + 1), (Random.int 7 + 2)
  | _ -> (Random.int 8 + 1), (Random.int 8 + 1)
  in
  (* /!\ 1 <= _ <= 8, ne doit surtout pas être 0, cd_init raises "index out of bounds sinon !!"*)
  match graph_nature with
  | Tree _ -> begin
    let g = make_tree_eller p q in
    let cops = match nb_cop with 
    | None -> 1
    | Some n -> n in
    let time = match t_max with 
    | None -> (p * q - 3)
    | Some t -> t in
    {g = g; nb_cop = cops ; t_max = time}
  end
  | Grid _ -> begin
    let g = make_grid p q in
    let cops = match nb_cop with
    | None -> 2
    | Some n -> n in
    let time = match t_max with
    | None -> ((p + q) / 2) - 1 
    | Some t -> t in
    {g = g; nb_cop = cops ; t_max = time}
   end
  | Planar_read opt -> begin
    let m = match opt with 
    | Some i -> i
    | None -> (Random.int 8) + 1 in
    let g = get_random_graph_size m in
    let cops = match nb_cop with
    | None -> 3
    | Some n -> n in
    let time = match t_max with
    | None -> 2 * m
    (* résultat optimal mais, peut aussi faire (diam(G) + 1) * n , à calculer mais toujours <= 64 *)
    | Some t -> t in
    {g = g; nb_cop = cops ; t_max = time}
  end
  | Planar_square _ | Planar_sq_full _ -> begin 
    let g = make_planar p q graph_nature in
    let cops = match nb_cop with
    | None -> 3
    | Some n -> n in
    let time = match t_max with
    | None -> (p * q) / 10
    (* résultat optimal mais, peut aussi faire (diam(G) + 1) * n , à calculer mais toujours <= 64 *)
    | Some t -> t in
    {g = g; nb_cop = cops ; t_max = time}
  end
  | Planar_hexa _ -> begin
    let g = make_planar p q graph_nature in
    let cops = match nb_cop with
    | None -> 3
    | Some n -> n in
    let time = match t_max with 
    | None -> (p * q - (p/2)) / 10
    | Some t -> t in
    {g = g; nb_cop = cops ; t_max = time}
  end



let test_options (nb_tests : int) (graph_nature : g_nature) (nb_cop : int option) (t_max : int option) (show : bool): int array * int =
  (* effectue nb_tests tests sur un même graphe selon les options demandées *)
  
  let tab_res = Array.make nb_tests (-1) in
  let nb_success = ref 0 in
  for i = 0 to nb_tests - 1 do

    let settings = set_options graph_nature nb_cop t_max in
    let next_move_cop = go_next_matrix settings.g in

    let s = {nb_tour= 0; pos_cop= Array.make settings.nb_cop (-1); pos_x= -1} in
    let res_i = play_fair settings.g next_move_cop s settings.t_max in
    (* -1 si echec / t : temps de succès > 1 *)
    tab_res.(i) <- res_i ;
    if res_i <> -1 then incr nb_success
  done ;
  (tab_res, !nb_success)
  

let get_data () : (int*int) array  =
  (* 100 tests, même graphe, 10 tests identiques pour chaque temps imposé*)
  let p, q = 10, 10 in
  let nb_abs = 20 in
  let cops = None in
  let nat = Planar_hexa (Some (p, q)) in
  let t0 = 1 in
  let coeffs = [|2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 16; 18; 20; 25; 30; 35; 40|] in
  let res = Array.make nb_abs (-1, -1) in
  for i = 0 to nb_abs - 1 do
    let t = t0 * coeffs.(i) in
    let s  = ref 0 in
    for j = 0 to 9 do
      let _, succes = test_options 100 nat cops (Some t) false in
      s := !s + succes;
    done;
    res.(i) <- (!s, t)
  done;
  res

let get_data_grid () : int array  =
  (* 775 tests pour 775 graphes différents, renvoie le tableau de répartition des temps de réussite*)
  let p, q = 7, 7 in
  let cops = None in
  let nat = Grid (Some (p, q)) in
  (* déterminé en pratique précédemment : t_max_th = (p * q - (p/2) / 10 *)
  let res = Array.make 109 0 in
  let t = 108 in
  for i = 0 to 775 do
    let tab, succes = test_options 1 nat cops (Some t) false in
    if succes = 0 then failwith "un test n'a pas marché ";
    res.(tab.(0)) <- res.(tab.(0)) + 1
    done;
  res

let file = "test_grid_naif_twocops.csv"

let print_data () : unit =
  let res = get_data () in
  let out_file = open_out file in
  let n = Array.length res in
  for i = 0 to (n-1) do
    let succes, time = res.(i) in
    fprintf out_file "%d; %d \n" time succes
  done;
  close_out out_file


let print_data_grid () : unit =
  let res = get_data_grid () in
  let out_file = open_out file in
  let n = Array.length res in
  for i = 0 to (n-1) do
    fprintf out_file "%d \n" res.(i)
  done;
  close_out out_file

