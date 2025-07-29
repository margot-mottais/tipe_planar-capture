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

(* IMPLEMENTATION DE L'ALGORITHME DE PISANTECHAKOOL ET TAN *)

open Printf

let pi = acos(-1.)

type graph = int list array

type set = bool array

type chemin = int list

type job = Free | Go_guard of chemin * chemin | Guard of chemin | CatchTree | Go of chemin
(* pour go_guard : chemin1 = trajet à faire pour aller garder chemin2; chemin2 = chemin à garder*)
(* pour guard : chemin à garder, copie de chemin2 quand transition de Go_guard à Guard *)
(* pour Go : chemin est le plus court chemin à suivre jusqu'à la position désirée*)

type g_nature =
  | Tree of ((int * int) option)
  | Grid of ((int * int) option)
  | Planar_square of ((int * int) option)
  | Planar_hexa of ((int * int) option)
  | Planar_sq_full of ((int * int) option)
  | Planar_read of int option

type player = X | Cop of int

type point = int * int

type embedded_graph = {g : graph; coord : point array; card : int; pres : set}
(* g est un sous graph du graph initial avc seulement les arêtes effectivement présentes, 
   coord est invariant de coord initial,
   card est mis à jour tq card = nb de cases de g <> [],
   pres est mis a jour tq g.(i) = [] ssi pres.(i) = false *)

type edge = int * int

exception GameOver

exception TooLate

type matrix = int array array

type adj_matrix = bool array array

type game_state =
  { mutable nb_tour : int
  (* 1 tour = 1 mvt de chaque perso*)
  ; mutable step : int
  (* 1 step = le robber territory a été strictement réduit*)
  ; pos_cop: int array
  (* de taille 4 : cops numérotés de 1 à 3, case 0 non significative *)
  ; job_cop: job array
  ; mutable pos_x: int 
  ; e_g : embedded_graph
  (* mutable important meme si c'est un tableau, évite des recopies *)
  ; mutable eg_ri : embedded_graph
  (* sous graph de e_g.g initial avec seulement les sommets du set r_i*) 
  (* RQ : s.eg_ri.pres = c'est le set r_i *)
  ; m_cop : matrix
  (* résultat de go_next_matrix e_g.g : matrice de parcours en largeur de déplacement pour les cops*)
   }


(* Graphe de test spécifique*)
let g_dodeca = {g = [|[1; 4; 9;]; [0; 2; 3]; [1; 5; 6]; [1; 7; 8]; [0; 5; 18]; [2; 4; 10]; [2; 7; 11]; [3; 6; 13];
        [3; 9; 14]; [0; 8; 19]; [5; 11; 15]; [6; 10; 12]; [11; 13; 16]; [7; 12; 14]; [8; 13; 17]; [10; 16; 18];
        [12; 15; 17]; [14; 16; 19]; [4; 15; 19]; [9; 17; 18] |];
              coord = [|(3, 6); (3, 5); (2, 4); (4, 4); (0, 3); (1, 3); (2, 3); (4, 3); (5, 3); (6, 3);
              (1, 2); (2, 2); (3, 2); (4, 2); (5, 2); (1, 1); (3, 1); (5, 1); (1, 0); (5, 0)|];
              card = 20 ;
              pres = [|true; true; true; true; true; true; true; true; true; true; true; true; true; true;
               true; true; true; true; true; true; |]
}


let r_i (s : game_state) : set = s.eg_ri.pres


let get_starting_point (coord : point array) (pres : set): int =
  let n = Array.length coord in
  let s = ref 0 in
  let x_min = ref max_int in
  let y_max = ref (- max_int ) in
  for i = 0 to (n-1) do
    if pres.(i) then begin
      let x, y = coord.(i) in
      if (x < !x_min) || (x = !x_min && y > !y_max) then begin
        x_min := x;
        y_max := y;
        s := i
      end
    end
  done;
  !s


let dist2 ((x1, y1) : point) ((x2, y2) : point) : int = ((x1 - x2) * (x1 - x2)) + ((y1 - y2) * (y1 - y2)) 
  (*distance euclidienne au carré entre deux points*)


let theta ((xp, yp) : point) ((xu, yu) : point) ((xv, yv): point) : float =
  let phi = (yv - yp)*(xu - xp) - (xv - xp)*(yu - yp) in
  let d_uv = float_of_int (dist2 (xu, yu) (xv, yv)) in
  let d_up = float_of_int (dist2 (xu, yu) (xp, yp)) in
  let d_vp = float_of_int (dist2 (xv, yv) (xp, yp)) in
  let theta_0 = acos((d_uv +. d_up -. d_vp) /. (2. *. sqrt(d_uv)  *. sqrt(d_up) )) in
  if phi > 0 then theta_0
  else if phi < 0 then ((2. *. pi ) -. theta_0)
  else pi


let voisin_plus_petit_angle (u : point) (p : point) (num_pere : int) (voisins : int list) (e_g : embedded_graph)=
  (* voisins : liste des voisins de u dans G' sans p (père) *)
  let v_min = ref num_pere in
  let theta_min = ref (2. *. pi) in
  let rec aux (voisins : int list) =
    match voisins with 
    | [] -> !v_min
    | v :: vs -> begin
      let v_coord = e_g.coord.(v) in
      let theta_v = theta p u v_coord in
      if theta_v < !theta_min then begin
        v_min := v;
        theta_min := theta_v
      end;
      aux vs
    end
  in aux voisins


let rec remove (x : 'a) (l : 'a list) =
  (* enlève x de l, erreur si il n'est pas présent *)
  match l with 
  | [] -> failwith "x n'est pas dans l "
  | y :: ys when y = x -> ys
  | y :: ys -> y :: (remove x ys)


let rec remove_not_member (x : 'a) (l : 'a list) =
  (* enlève x de l si il est présent, ne fait rien sinon *)
  match l with 
  | [] -> []
  | y :: ys when y = x -> ys
  | y :: ys -> y :: (remove_not_member x ys)


let remove_cut (l : int list) (n : int): edge list =
  let t = Hashtbl.create n in
  let rec add (l : int list) : unit =
    match l with 
    | [] | [_] -> ()
    | a :: b :: bs -> begin
      if Hashtbl.mem t (b, a) then Hashtbl.remove t (b, a)
      else Hashtbl.add t (a, b) 1 ;
      add (b :: bs)
    end
  in 
  add l ;
  let res = ref [] in
  Hashtbl.iter (fun k _ -> res := k :: !res) t;
  !res


let border_cycles_c (e_g : embedded_graph) : edge list = 
  (*détermine la bordure cyclique d'un graphe g *)
  (* fonction C(V) définie dans l'article*)
  let g, coord, card, pres = e_g.g, e_g.coord, e_g.card, e_g.pres in
  if card <= 2 then []
  else begin
    (***** étape 1*)
    let d = get_starting_point coord pres in
    let l_exec = ref [d] in
    let x, y = coord.(d) in
    let curr = ref (voisin_plus_petit_angle (x, y) (x, y + 1) (-1) g.(d) e_g ) in
    (* initialisation avec un faux pere de numéro -1 *)
    let pere = ref d in
    l_exec := !curr :: !l_exec;
    while !curr <> d do
      let v_curr = remove !pere g.(!curr) in
      let next = voisin_plus_petit_angle coord.(!curr) coord.(!pere) !pere v_curr e_g in
      l_exec := next :: !l_exec ;
      pere := !curr;
      curr := next
    done;
    (***** étape 2 *)
    let l_border = List.rev !l_exec in
    let res = remove_cut l_border card in
    res
  end


let select_random_vertex (b : graph) : int =
  (* renvoie un sommet au hasard effectivement présent dans b un sous graphe de g initial*)
  let urne = ref [] in
  let n = Array.length b in
  for i = 0 to (n-1) do
    if b.(i) <> [] then urne := i :: !urne
  done;
  let i = Random.int (List.length !urne) in
  List.nth !urne i


let select_random_vertex_cycle (l : edge list) : int =
  (* renvoie un sommet au hasard dans un cycle *)
  let i = Random.int (List.length l) in
  fst (List.nth l i)


let select_random_vertex_set (esb :set) : int =
  (* renvoie un sommet au hasard effectivement présent dans esb un sous ensemble de sommets de g initial*)
  let urne = ref [] in
  let n = Array.length esb in
  for i = 0 to (n-1) do
    if esb.(i) then urne := i :: !urne
  done;
  let i = Random.int (List.length !urne) in
  List.nth !urne i


let incr_time (s : game_state) : unit =
  (* un tour a été effectué, ie. un déplacement de chaque cop et de x*)
  s.nb_tour <- s.nb_tour + 1
  

let move_cop (i : int) (v : int) (s : game_state) (max_time : int): unit =
  (* déplace le cop n° k sur le sommet v*)
  if v <> s.pos_cop.(i) then incr_time s;
  if s.nb_tour > max_time then raise TooLate;
  (* RQ : on augmente le temps à chaque déplacement d'un policier car c'est la borne proposée par l'article :
     <= 2n déplacement de policier *)
  s.pos_cop.(i) <- v;
  if v = s.pos_x then raise GameOver


let move_all_cops (v : int) (s : game_state) (max_time : int) : unit =
  (*déplace tous les cops sur le sommet v*)
  for k = 1 to 3 do
    move_cop k v s max_time
  done


let move_x (v : int) (s : game_state) : unit =
  (* déplace x sur le sommet v*)
  s.pos_x <- v;
  for i = 1 to 3 do
    if s.pos_cop.(i) = v then raise GameOver
  done


let decide_move_x (s : game_state) : int =
  (* renvoie v tq déplacer x sur v ne compromet pas x, raise GameOver sinon*)
  let voisins = ref s.eg_ri.g.(s.pos_x) in
  (* cases accessibles par x dans r_i*)
  for i = 1 to 3 do
    voisins := remove_not_member s.pos_cop.(i) !voisins
  done;
  if !voisins = [] then raise GameOver
  else begin
    let j = Random.int (List.length !voisins) in
    List.nth !voisins j
  end 


let edge_list_to_set (lv : int list) (s : game_state): set =
  (* attention edge = vertex ici erreur*)
  (* convertit une liste de sommets en un tableau de présence de la forme de l'ensemble des sommets de g initial *)
  let g = s.e_g.g in
  let n = Array.length g in
  let new_set = Array.make n false in
  List.iter (fun i -> new_set.(i) <- true) lv;
  new_set


let extract (esb : set) (ss_esb : set) : set = 
  (* calcule le sous graphe de esb obtenu en lui retirant ss_esb, qui est un sous ensemble de esb *)
  (* exemple : extract [|1; 0; 1; 1|] [|1; 0; 0; 1|] = [|0; 0; 1; 0|]*)
  let n = Array.length esb in
  let new_esb = Array.copy esb in
  for i = 0 to (n-1) do
    if ss_esb.(i) then new_esb.(i) <- false
  done;
  new_esb


let set_to_list (esb : set) : int list =
  (* renvoie la liste des sommets contenus dans le set *)
  let n = Array.length esb in
  let res = ref [] in
  for i = 0 to n-1 do
    if esb.(i) then 
      res := i :: !res
  done;
  !res


let graphify (esb : set) (s : game_state) : graph =
  (* renvoie le sous graphe de g initial contenant seulement les sommets de esb *)
  let g = s.e_g.g in
  let n = Array.length g in
  let new_g = Array.make n [] in
  for i = 0 to (n-1) do
    if esb.(i) then begin
      List.iter (fun y -> if esb.(y) then new_g.(i) <- y :: new_g.(i)) g.(i)
    end
  done;
  new_g


let set_to_eg (r_i : set) (s : game_state) : embedded_graph =
  (* renvoie un embedded_graph respectant les conditions en commentaire de la déclaration de type*)
  (* cad de la meme taille que e_g mais contenant seulement les sommets du set r_i *)
  let coord = s.e_g.coord in
  let n = Array.length r_i in
  let g_new = graphify r_i s in
  let cnt = ref 0 in
  for i = 0 to (n-1) do
    if r_i.(i) then incr cnt
  done;
  {g = g_new; coord = coord; card = !cnt; pres = r_i}


let border (s : game_state) : edge list = 
  (*détermine la bordure cyclique d'un graphe g *)
  (* Nouvelle version qui prend en compte Pi1 et Pi2 *)
  (* on calcule l'embedded graph avec Pi1 et Pi2 puis on applique l'ancienne fonction border *)
  let esb = s.eg_ri.pres in
  let chemins_gardes = ref [] in
  for i = 1 to 3 do
    match s.job_cop.(i) with
    | Guard c -> chemins_gardes := c @ !chemins_gardes
    | _ -> ()
  done;
  List.iter (fun x -> esb.(x) <- true) !chemins_gardes;
  let eg = set_to_eg esb s in
  border_cycles_c eg


let composante_x (esb : set) (s : game_state) : set = 
(* parcours en profondeur : prend en argument le set des sommets accessibles par X 
   et retroune un set = la composante connexe où est X (= r_i+1)*)
  let ss_eg = set_to_eg esb s in
  let ss_g = ss_eg.g in
  let x0 = s.pos_x in
  let curr_comp = ref [] in
  let found = ref false in
  let vu = Array.make s.e_g.card false in
  let sommets = set_to_list esb in
  let rec dfs (x : int) =
    if not vu.(x) then begin
      vu.(x) <- true;
      curr_comp := x :: !curr_comp;
      if x = x0 then found := true;
      List.iter (fun y -> dfs y) ss_g.(x);
    end
  in 
  let rec trouve_comp (l : int list) : int list =
    match l with 
    | [] -> failwith "x0 n'est pas dans le territoire de X  \n"
    | x :: xs -> begin
      dfs x;
      if !found = true then !curr_comp
      else begin
        curr_comp := [];
        trouve_comp xs
      end
    end
  in
  let comp_x_list = trouve_comp sommets in
  let res_set = edge_list_to_set comp_x_list s in
  res_set


let is_member (x : int) (l : edge list list) : edge list list =
  (* renvoie la liste des cycles qui contiennent le sommet x*)
  let res = ref [] in
  let rec mem (u : edge list) : bool =
    match u with
    | [] -> false
    | (a, b) :: us when a = x -> true
    | _ :: us -> mem us
  in
  List.iter (fun u -> if mem u then res := u :: !res) l;
  !res
 

let mem_head (x : int) (l : edge list) : bool =
  (* teste si la tête d'une liste d'arête a x en deuxième coordonée *)
  match l with 
  | [] -> failwith " l est vide  \n"
  | (_, b) :: ls -> x = b


let cycles (l : edge list) : edge list list =
  (* renvoie les cycles d'une liste d'arêtes sans séparer les boucles accolées*)
  let res = ref [] in
  let rec aux (u : edge list) =
    match u with
    | [] -> ()
    | (a, b) :: us -> begin
      let chgt = ref false in
      res := List.map (fun v -> if mem_head a v then (chgt := true; (a, b) :: v) else v) !res;
      if not !chgt then res := [(a, b)] :: !res;
      aux us;
    end
  in aux l;
  res := List.map (fun u -> List.rev u) !res;
  !res


let rec find_match (x: int) (vu : edge list) (a_voir  :edge list) : (edge * (edge list)) option =
  (* prend un entier b et une liste d'arêtes l = vu @ a_voir*)
  (* renvoie une arête e tq b est une des coord de e est l privée de e, si trouvé, None sinon*)
  match a_voir with 
  | [] -> None
  | (a, b) :: ls -> begin
    if a = x then Some ((a, b), vu @ ls)
    else if b = x then Some ((b, a), vu @ ls)
      (* on tourne le domino*)
    else find_match x ((a, b) :: vu) ls
  end


let domino_sort (l : edge list) : edge list =
  (* prend en entrée un liste d'arrêtes qui constitue en ensemble de cycles non nécessairement reliés*)
  (* renvoie la liste en mode "domino" , on fait [(a, b); (b, c); (c, d); (e, f)] autant que possible 
     pour coller ensemble et mettre dans l'ordre les arêtes des mêmes cycles*)
  let res = ref [] in
  let last = ref (-1) in
  let a_voir =
    match l with 
    | [] -> failwith "liste vide domino_sort"
    | x :: xs -> begin
      res := [x];
      last := snd x;
      xs
    end
  in
  let rec aux (l : edge list) : unit =
    match l with 
    | [] -> ()
    | (a, b) :: ls -> begin
      let d = find_match !last [] l in
      match d with 
      (* on a pas trouvé de domino pour compléter le cycle, on en prend un autre au hasard*)
      | None -> begin
        last := b;
        res := (a, b) :: !res;
        aux ls
      end
      (* on continue un cycle*)
      | Some ((c, d), lreste) -> begin
        if c <> !last then failwith "erreur domino_sort";
        last := d;
        res := (c, d) :: !res;
        aux lreste
      end
    end
  in
  aux a_voir;
  List.rev(!res)


let break_crossing_points_one_list (l : edge list) (e_g : embedded_graph): edge list list =
  (* sépare les boucles accolées dans une liste d'arêtes*)
  let cross_points = ref [] in
  let res = ref [] in
  let dico = Hashtbl.create (Array.length e_g.g) in
  let rec aux (u : edge list) :unit =
    match u with 
    | [] -> ()
    | (a, b) :: us -> begin
      if Hashtbl.mem dico a then begin
        let val_a = Hashtbl.find dico a in
        Hashtbl.replace dico a (val_a + 1)
      end
      else Hashtbl.add dico a 1 ;
      if Hashtbl.mem dico b then begin
        let val_b = Hashtbl.find dico b in
        Hashtbl.replace dico b (val_b + 1)
      end 
      else Hashtbl.add dico b 1;
      aux us
    end
  in aux l;
  Hashtbl.iter (fun k v -> if v > 2 then cross_points := k :: !cross_points) dico;
  if !cross_points = [] then [l]
  else begin
    let tmp_cycle = ref [] in
    let rec recons (l : edge list) (l_curr : edge list) (start_flag : bool) (end_flag : bool) (x : int) : unit =
      (* si start_flag = true : on cherche un endroit ou commencer un cycle avec x*)
      (* sinon on cherche un endroit ou finir un cycle avec x*)
      (* si end_flag = true : ca veut dire qu'on a déjà recommencé la liste du début
        et qu'il faut s'arrêter définitivement à la fin du prochain cycle*)
      match l_curr with 
      | [] -> recons l l start_flag true x
      | (a, b) :: us -> begin
        if start_flag then begin 
          (* on veut commencer*)
          if a = x then begin
            tmp_cycle :=  [(a, b)] ; 
            recons l us false false x
          end
          else recons l us true false x
        end
        else begin
          (* on veut finir*)
          if b = x then begin
            res := ((a, b) :: !tmp_cycle) :: !res ;
            tmp_cycle := [];
            if (not end_flag) then recons l us true false x
              (* on continue *)
          end
          else begin
            tmp_cycle := (a, b) :: !tmp_cycle;
            recons l us false false x
          end 
        end
      end
    in
    List.iter (fun x -> recons l l true false x) !cross_points;
    res := List.map (fun u -> List.rev u) !res;
    !res
  end


let all_minimal_cycles (l : edge list) (e_g : embedded_graph) :edge list list =
  let l_sort = domino_sort l in
  let l_c = cycles l_sort in
  let res = ref [] in
  List.iter (fun u -> res := (break_crossing_points_one_list u e_g) @ !res)  l_c;
  !res


let cycle_contenant (l : edge list) (v : int) (e_g : embedded_graph) : edge list =
  (* renvoie le sous cycle c_min minimal de c (ie. le sous graph de g et c) tq c_min contient v *)
  let l_cycles = all_minimal_cycles l e_g in
  let cycles_avec_v = is_member v l_cycles in
  match cycles_avec_v with
  | [] -> failwith "pas de cycle contenant v  \n"
  | [c] -> c
  | c :: cs -> begin
    c
  end


let two_cops_start (c : edge list) (u : int) (s : game_state) : int * int = 
  (* Précondition : c est un cycle *)
  let n = List.length c in
  let r_i = r_i s in
  let x = ref u in
  let y = ref u in
  (* floor (n / 3)*)
  let len = (n + 2) / 3 in
  let start_flag = ref true in
  let stop_flag = ref false in
  let rec set_pointer (p : int ref) (l : edge list) (i : int) : unit =
    (* si start_flag = true : on cherche le pointeur pour la premiere fois*)
    (* si stop_flag = true : on a déjà fait le tour une fois de la liste *)
    (* invariant : on a déjà regardé i sommet du cycle après u (u inclus)*)
    (* si x_or_y = true, on est en train de modifier x*)
    match l with 
    | [] ->
      if not !stop_flag then begin 
      stop_flag := true;
      set_pointer p c i
    end
    | (a, b) :: vs -> begin
      if !start_flag then begin
        (* on veut commencer*)
        if a = u then begin
          start_flag := false; 
          set_pointer p vs (i + 1)
        end
        else set_pointer p vs i
      end
      else 
        (* on a déjà commencé *)
        if i >= len then begin
          (* on commence à vérifier r_i*)
          if r_i.(a) then p := a
          (* on arrête le programme*)
          else set_pointer p vs (i + 1)
        end
        else set_pointer p vs (i + 1)
      end in
  set_pointer x c 0;
  start_flag := true;
  stop_flag := false;
  let c_rev = List.rev (List.map (fun (a, b) -> (b, a)) c) in
  set_pointer y c_rev 0;
  (!x, !y)



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


let pcc_g (u : int) (v : int) (s : game_state) : chemin =
  (* trouve le plus court chemin entre u et v dans ss_g un sous graphe de g*)
  (* pour un chemin u - u1 - ... - uk - v, renvoie [u; u1; ...; uk; v]*)
  let m = s.m_cop in
  let curr = ref u in
  let c = ref [u] in
  while !curr <> v do
    curr := m.(!curr).(v);
    c := !curr :: !c
  done;
  List.rev(!c)


let pcc_sub (u : int) (v : int) (ss_g : graph) : chemin =
  (* trouve le plus court chemin entre u et v dans ss_g un sous graphe de g*)
  (* pour un chemin u - u1 - ... - uk - v, renvoie [u; u1; ...; uk; v]*)
  let m = go_next_matrix ss_g in
  let curr = ref u in
  let c = ref [u] in
  while !curr <> v do
    curr := m.(!curr).(v);
    c := !curr :: !c
  done;
  List.rev(!c)


let go_guard (i : int) (p : chemin) (s : game_state) : chemin =
  (* renvoie le chemin pour aller garder le chemin p le plus vite possible depuis i
     càd aller le plus vite sur un sommet de p, càd le plus court chemin de i à tout sommet d p
     TOUJOURS DANS G INITIAL car les cops bougent comme ils veulent*)
     (* /!\ OU i est le NUMERO du COP pas un SOMMET*)
  (* RQ : on renvoie avec la tête même si pas optimal comme le cop i est deja sur cette case *)
  let u = s.pos_cop.(i) in
  let shortest_path = ref [] in
  let len = ref max_int in
  let rec aux (l : int list) : chemin  =
    match l with
    | [] -> !shortest_path
    | v :: vs -> begin
      let cx = pcc_g u v s in
      let n = List.length cx in
      if n < !len then begin
        shortest_path := cx;
        len := n
      end;
      aux vs
    end
  in aux p


let self_et_voisins (u : int) (p : chemin) : int list =
  (*renvoie une liste avec u élement du chemin p, et son éventuel voisins droit et gauche dans p*)
  if not (List.mem u p) then failwith "u n'est pas un sommet de p  \n";
  let rec aux (l : int list) : int list =
    match l with
    | [] -> [u]
    | x :: y :: ys when y = u -> x :: (aux (y :: ys))
    | x :: y :: ys when x = u -> y :: (aux ys)
    | x :: xs -> aux xs
  in aux p


let keep_guard (i : int) (s : game_state) (max_int : int): unit =
  (* déplace le cop i à gauche ou à droite ou sur place dans son chemin à guarder*)
  match s.job_cop.(i) with
  | Guard p -> begin
    let v = s.pos_x in
    let u = s.pos_cop.(i) in
    let next = self_et_voisins u p in
    let chemin_next = List.map (fun x -> let c = pcc_g x v s in (x, c, List.length c) ) next in
    let best_next = ref (-1, max_int) in
    (* numéro du sommet, longueur du plus court chemin *)
    List.iter (fun (x, c, len) -> let (_, n) = !best_next in if (len < n || (len = n && x = u)) then best_next := (x, len) ) chemin_next;
    (* si on peut avoir la meilleure distance ex_equo sans bouger, on préfère ne pas bouger*)
    let (next_edge, _) = !best_next in
    move_cop i next_edge s max_int
  end
  | _ -> failwith "i doit garder un chemin  \n"  


let play_moves (s : game_state) (max_time : int) : unit =
  (* joue les coups dans les listes de tous les joueurs jusqu'à ce
     qu'ils soient tous en train de guarder un chemin ou libre*)
  try
    let cont = ref true in
    while !cont do
      let cont_cops = ref false in
      for i = 1 to 3 do
        match s.job_cop.(i) with
        | Go_guard (c, p) -> begin
          cont_cops := true;
          match c with 
          | [] -> begin
            s.job_cop.(i) <- Guard p;
            keep_guard i s max_time
          end
          | v :: vs -> begin
            move_cop i v s max_time ;
            s.job_cop.(i) <- Go_guard (vs, p)
          end
        end
        | Guard p -> keep_guard i s max_time
        | Go c -> begin
          match c with
          | [] -> s.job_cop.(i) <- Free
          | v :: vs -> begin
            move_cop i v s max_time;
            s.job_cop.(i) <- Go vs
          end
        end
        | Free -> ()
        | CatchTree -> failwith "erreur, pas de CatchTree en cours  \n"
      done;
      cont := !cont_cops;
      let v = decide_move_x s in
      move_x v s;
    done
  with 
  | GameOver -> raise GameOver


let chase_on_path (s : game_state) (max_time : int)  : unit =
  (* X est sur un sommet d'un du(des) nouveaux chemins établis, on l'attrape*)
  try
    let flag = 2 * (Array.length s.e_g.g) in
    (* borne arbitraire <= 2n *)
    let k = ref 0 in
    while !k < flag do
      for i = 1 to 3 do
        match s.job_cop.(i) with
        | Guard p -> keep_guard i s max_time
        | _ -> ()
      done;
      let v = decide_move_x s in
      move_x v s;
    incr k
    done;
    raise TooLate
  with 
  | GameOver -> raise GameOver
  (* l'excpetion TooLate est directement renvoyée et gérée par la fonction test *)


let move_down_tree (i : int) (s : game_state) (max_time : int) : unit =
  match s.job_cop.(i) with
  | CatchTree -> begin
    let u = s.pos_cop.(i) in
    let x = s.pos_x in
    let v = s.m_cop.(u).(x) in
    move_cop i v s max_time;
  end
  | _ -> failwith "i devrait être en train d'attraper X dans l'arbre"


let solution_naive_arbre (s : game_state) (max_time : int) : unit = 
  (* déplace un policier de telle sorte à piéger X dans le cas où s.r_i est un arbre*)
  (* trouver le policier qui est free, ne pas toucher aux autres qui sont en guard,
     et lui faire faire la solution arbre*)
  let free_cop = ref 0 in
  for i = 1 to 3 do
    if s.job_cop.(i) = Free then free_cop := i
  done;
  if !free_cop = 0 then failwith "il n'y a pas de cop libre  \n"
  else begin
    try
      s.job_cop.(!free_cop) <- CatchTree; 
      let safeguard = ref 0 in
      while !safeguard < 50 do
        for i = 1 to 3 do
          match s.job_cop.(i) with
          | Go_guard _ | Go _ -> failwith "Les cops devraient être libres ou garder un chemin  \n"
          | Guard p -> keep_guard i s max_time
          | CatchTree -> move_down_tree i s max_time
          | Free -> ()
        done;
        incr safeguard;
        let v = decide_move_x s in
        move_x v s;
      done
    with 
    | GameOver ->  raise GameOver 
  end
(* on joue les coups des 3 cops et x tour à tour jusqu'a ce que les listes de tous les cops soient vides*)


let guarded_paths (s : game_state) : (int * chemin) array =
  let res = ref [] in
  for i = 1 to 3 do
    match s.job_cop.(i) with
    | Guard p -> res := (i, p) :: !res
    | _ -> ()
  done;
  let n = List.length !res in
  let t_res = Array.make n (-1, []) in
  for i = 0 to (n-1) do
    t_res.(i) <- List.nth !res i
  done;
  t_res


let vertices_of (l : edge list) : int list =
  (* renvoie la liste SANS DOUBLON  des sommets d'une liste d'arêtes*)
  let res = ref [] in
  let rec aux (l : edge list) : chemin  =
    match l with 
    | [] -> !res
    | (a, b) :: ls -> begin
      if not (List.mem a !res) then res := a :: !res;
      if not (List.mem b !res) then res := b :: !res;
      aux ls
    end
  in aux l


let rec intersect (u : 'a list) (v : 'a list) : 'a list =
  (*renvoie l'intersection des listes u et v SANS DOUBLON *)
  match u with 
  | [] -> []
  | x :: xs -> if List.mem x v then x :: (intersect xs v)
    else intersect xs v 


let rec union (u : 'a list) (v : 'a list) : 'a list =
  (* renvoie l'union des listes u et v SANS DOUBLON, où u et v ne contiennent pas de doublons *)
  match u with 
  | [] -> v
  | x :: xs -> begin
    if List.mem x v then union xs v
    else x :: (union xs v)
  end


let pcc_g_min_len (l1 : int list) (l2 : int list) (s : game_state): (int * int) =
  (* renvoie (x, w) tq longueur(pcc_g x w) est minimale avec x dans l1 et w dans l2  *) 
  (* RQ : on ne fait aucun test d'unicité *)
  let min_len = ref max_int in
  let xw_best = ref (-1, -1) in
  let maj_min x w = begin
    let c = pcc_g x w s in
    let len = List.length c in
    if len < !min_len then begin
      xw_best := (x, w);
      min_len := len
    end
  end
  in List.iter (fun x -> List.iter (fun w -> maj_min x w) l2 ) l1;
  !xw_best


let send_all_cops (v : int) (s : game_state) =
  (* met tous les cops à Go c tq c est le plus court chemin de leur position à x*)
  (* attention, on ne bouge pas les cops *)
  for i = 1 to 3 do
    let c = pcc_g s.pos_cop.(i) v s in
    s.job_cop.(i) <- Go c
  done


let deb (l : 'a list) : 'a  =
(* renvoie la tête de la liste l, lève un exception si l vide *)
  match l with 
  | [] -> failwith "deb : l est vide  \n"
  | x :: xs -> x


let rec fin (l : 'a list) : 'a =
  (* renvoie le dernier élément de la liste l, lève un exception si l vide *)
  match l with 
  | [] -> failwith "fin : l est vide  \n"
  | [x] -> x
  | x :: xs -> fin xs
  

(* N(s) = liste des sommets u de G ENTIER tel que u est voisin de v pour v dans r_i*)
let neighbours(s : game_state) : int list = 
  let pres = s.eg_ri.pres in
  (* le tableau de présence des sommets de r_i*)
  let g_tot = s.e_g.g in
  let n = Array.length g_tot in
  let res = ref [] in
  for i = 0 to (n-1) do
    if pres.(i) then res := union g_tot.(i) !res
    done;
  !res


let compute_m (e : int) (f : int) (l : int list) (s : game_state) : int =
  (* renvoie m élément de l tq len(ppc_g m f) - len (pcc_g e m) est >= 0 ET minimal *)
  let m = ref (-1) in
  let min_len = ref max_int in
  let rec aux (l : int list) =
    match l with 
    | [] -> begin
      if !m = -1 then failwith " erreur : compute_m  \n"
      else !m
    end 
    | n :: ns -> begin
      let pe = pcc_g e n s in
      let pf = pcc_g f n s in
      let len =  (List.length pf) - (List.length pe) in 
      if len >= 0 && len < !min_len then begin
        m := n;
        min_len := len
      end;
      aux ns
      end
    in aux l


let autre_bout (p : chemin) (e : int) : int =
  (* renvoie deb si fin p = e, fin si deb p = e, lève une exception sinon*)
  let d = deb p in
  let f = fin p in
  if d = e && f <> e then f
  else if d <> e && f = e then d
  else failwith "erreur : autre bout  \n"


(*si X est SUR un sommet d'un nouveau chemin établi, on fait jouer keep_guard jusqu'a la capture*)
let incr_step (l : int list) (s : game_state) (max_time : int) : unit =
  (* l est une liste de sommets à enlever de r_i *)
  (* les cops ont réussi a réduire le robber_territory, on passe à l'étape suivante*)
  (* et met à jour le robber territory pour cette nouvelle étape*)
  s.step <- s.step + 1;
  if List.mem s.pos_x l then begin
    chase_on_path s max_time
  end
  else begin
    let g_ei = edge_list_to_set l s in
    let r_i_new_whole = extract (r_i s) g_ei in
    let r_i_new = composante_x r_i_new_whole s in
    let eg_ri_new = set_to_eg r_i_new s in
    s.eg_ri <- eg_ri_new
  end 


let rec recursion (s : game_state) (max_time : int) : unit = 
  if s.nb_tour > max_time then raise TooLate
  else begin 
  let c_ri = border_cycles_c s.eg_ri in
  if c_ri = [] then solution_naive_arbre s max_time
    (* ie. g est un arbre*)
  else begin
    let b_ri = border s in
    let g_paths = guarded_paths s in
    let n = Array.length g_paths in
    if (n <> 1 && n<>2) then failwith "problème de nombre de chemins gardés  \n";
    let cop1, p1 = g_paths.(0) in
    let cop2_guarding = n = 2 in
    let v_b_ri = vertices_of b_ri in
    let bri_int_p1 = intersect v_b_ri p1 in
    
    (*PREMIER CAS*)
    if List.length bri_int_p1 <= 1 then begin
      let w = match bri_int_p1 with 
        | [] -> begin
          if cop2_guarding then begin
            let cop2, p2 = g_paths.(1) in
            if p2 <> [] then raise TooLate
          end;
          let _, w = pcc_g_min_len v_b_ri p1 s in
          w
        end
        | [a] -> a
        | _ -> failwith "impossible  \n"
      in
      send_all_cops w s;
      play_moves s max_time;

      let c_i = cycle_contenant b_ri w s.e_g in
      let v1, v2 = two_cops_start c_i w s in
      let cop_territory = begin
        let esb = Array.copy (r_i s) in
        esb.(w) <- true;
        esb
      end
      in
      let cop_graph = graphify cop_territory s in
      let p = pcc_sub w v1 cop_graph in
      let q = pcc_sub w v2 cop_graph in
      s.job_cop.(1) <- Go_guard ((go_guard 1 p s), p) ;
      s.job_cop.(2) <- Go_guard ((go_guard 2 q s), q) ;
      s.job_cop.(3) <- Free;
      (* 3 reste sur w pour le garder *)

      play_moves s max_time;
      incr_step (p @ q) s max_time;
    end 

    else begin

      (* DEUXIEME CAS *)
      if (not cop2_guarding) || (cop2_guarding && (snd g_paths.(1) = [] )) then begin
        let e, f = deb p1, fin p1 in
        let n_ri = neighbours s in
        let nri_inter_p1 = intersect n_ri p1 in
        let m = compute_m e f nri_inter_p1 s in
        let c_i = cycle_contenant b_ri m s.e_g in
        let v1, v2 = two_cops_start c_i m s in
        let cop_territory = begin
          let esb = Array.copy (r_i s) in
          esb.(m) <- true;
          esb
        end
        in
        let cop_graph = graphify cop_territory s in
        let p = pcc_sub m v1 cop_graph in
        let q = pcc_sub m v2 cop_graph in
        let free_cops = remove cop1 [1; 2; 3] in
        let i2 = List.nth free_cops 0 in
        let i3 = List.nth free_cops 1 in
        s.job_cop.(i2) <- Go_guard ((go_guard i2 p s), p) ;
        s.job_cop.(i3) <- Go_guard ((go_guard i3 q s), q) ;

        play_moves s max_time;
        incr_step (p @ q) s max_time;
      end 

      (* TROISIEME CAS *)
      else begin
        let cop2, p2 = g_paths.(1) in
        let e = match intersect p1 p2 with 
          | e :: es -> e
          | _ -> failwith "erreur : intersection de p1 et p2  \n"
        in
        let f = autre_bout p1 e in
        let nri = neighbours s in
        let v_b_ri = vertices_of b_ri in
        let nri_inter_p2 = intersect nri p2 in
        let bri_inter_p1 = intersect v_b_ri p1 in
        let _, x = pcc_g_min_len [e] nri_inter_p2 s in
        let _, y = pcc_g_min_len [f] bri_inter_p1 s in
        let cop_territory = begin
          let esb = Array.copy (r_i s) in
          esb.(x) <- true;
          esb.(y) <- true;
          esb
        end
        in
        let cop_graph = graphify cop_territory s in
        let p = pcc_sub x y cop_graph in
        let i3 = 
          match remove cop1 (remove cop2 [1; 2; 3]) with 
          | [i3] -> i3
          | _ -> failwith "impossible : deux cops sont guarding  \n"
        in
        s.job_cop.(i3) <- Go_guard ((go_guard i3 p s), p) ;
        (* rajout non mentionné dans le papier : il faut libérer un cop ! *)
        (* on libère cop2 car x est choisi dans P2, mieux selon le schéma*)
        s.job_cop.(cop2) <- Free;
        play_moves s max_time;
        incr_step p s max_time;
      end 
    end;

  recursion s max_time 
  end
end
  


let x_start (g : graph) (e0 : int) : int =
  (*effectue un parcours en largeur pour trouver un des sommets le plus loin*)
  let n = Array.length g in
  let ouverts = Queue.create () in
  Queue.push e0 ouverts;
  let vus = Array.make n false in
  vus.(e0) <- true;
  let last  = ref e0 in
  while not (Queue.is_empty ouverts) do
    let x = Queue.pop ouverts in
    last := x;
    List.iter (fun y ->
      if not vus.(y) then begin
        Queue.push y ouverts;
        vus.(y) <- true
      end) g.(x);
  done;
  !last


let tarjan (g : graph) : set =
  (* AP = articulation point = cut vertex *)
  (* renvoie l'ensemble des sommets qui ne sont pas des AP*)
  let n = Array.length g in
  let disc = Array.make n 0 in
  let low = Array.make n (-1) in
  let visited = Array.make n false in
  let isAP = Array.make n false in
  let time = ref 0 in
  let par = ref (-1) in
  let rec aux (x : int) (p : int): unit =
    (* p = parent dans le DFS*)
    let children = ref 0 in
    visited.(x) <- true;
    incr time;
    disc.(x) <- !time;
    low.(x) <- !time;
    List.iter (fun y ->
      if not visited.(y) then begin
      incr children;
      aux y x;
      low.(x) <- min low.(x) low.(y);
      if p <> -1 && low.(y) >= disc.(x) then isAP.(x) <- true;
      end
      else if y <> p then low.(x) <- min low.(x) disc.(y); 
    ) g.(x);
    if p = -1 && !children > 1 then isAP.(x) <- true
  in
  aux 0 !par;
  let res = Array.init n (fun i -> not isAP.(i)) in
  res



let intersect_esb (t1 : set) (t2 : set) : set =
  (* intersection de deux ensembles*)
  let n, m = Array.length t1, Array.length t2 in
  if n <> m then failwith "intersect_esb";
  let inter = Array.init n (fun i -> t1.(i) && t2.(i)) in
  inter


let is_empty_set (t : set) : bool =
  (* vrai si t est l'ensemble vide*)
  let n = Array.length t in 
  let res = ref false in
  for i = 0 to n-1 do
    res := !res || t.(i)
  done;
  not !res


let init (s : game_state) (max_time : int) : unit =
  (* precondition : r_i du graphe initial est toujours tout G càd un set avec que des true*)
  (* phase initiale*)
  let e_g = s.e_g in
  let b_r0 =  border_cycles_c e_g in
  (* r0 = tout G : graph passé en entrée *)
  if b_r0 = []
    (* ie. g est un arbre*)
    then begin 
      let n = Array.length e_g.g in
      let c0 = Random.int n in
      move_all_cops c0 s max_time;
      let pos_r = x_start e_g.g c0 in
      move_x pos_r s;
      solution_naive_arbre s max_time
  end
  else begin 
    (* Attention : e0 ne doit pas être un cut vertex !*)
    (* on va supposer que c'est possible de le choisir ansi même si c'est faux dans le cas général :
       facilite la construction de R1, expection sinon  *)
    let not_AP = tarjan s.e_g.g in
    let t_r0 = edge_list_to_set (vertices_of b_r0) s in
    let b_r0_uncut = intersect_esb not_AP t_r0 in
    if is_empty_set b_r0_uncut then failwith "pas de e0 qui ne soit pas un cut vertex";
    let e0 = select_random_vertex_set b_r0_uncut in
    move_all_cops e0 s max_time;

    let pos_r = x_start e_g.g e0 in
    move_x pos_r s;
    incr_step [e0] s max_time;

    s.job_cop.(1) <- Guard [e0] ;

    (* r_1 est dans s.eg_ri.pres *)
    let b_r1 = border s in

    if b_r1 = [] then begin
      solution_naive_arbre s max_time
    end
    else begin  
      let c_1 = cycle_contenant b_r1 e0 e_g in
      let v1, v2 = two_cops_start c_1 e0 s in
      
      (* à cette étape on fait le plus court chemin dans tout G *)
      let p = pcc_g e0 v1 s in
      let q = pcc_g e0 v2 s in  

      s.job_cop.(1) <- Go_guard ((go_guard 1 p s), p) ;
      s.job_cop.(2) <- Go_guard ((go_guard 2 q s), q) ;
      s.job_cop.(3) <- Free;
 
      play_moves s max_time;
      incr_step (p @ q) s max_time;
      recursion s max_time 
    end
  end 


let catch_within (s : game_state) (max_time : int) : int =
  (* renvoie le nb_tour nécessaires à la capture si il est < max_time, -1 sinon *)
  try 
  init s max_time;
  raise TooLate
  with
  | GameOver -> s.nb_tour   
  | TooLate -> -1



(* FABRICATION DE LA REPRESENTATION DANS LE PLAN **)

let get_graph (nat : g_nature) (p : int) (q : int) : (graph * point array) =
  (* renvoie le graphe correspondant à la nature demandée*)
  (* paramètres à modifier p et q de taille *)
  (* renvoie le tableau des coordonnées de chaque point dans le plan, attention aux numéros *)
  let g = 
    match nat with 
    | Planar_square _ | Planar_sq_full _ | Planar_hexa _ -> make_planar p q nat
    | Grid _ -> make_grid p q
    | _ -> failwith "erreur type graphe get_graph"
   in
  let t_emb = 
  match nat with 
  | Planar_square _ | Planar_sq_full _ | Grid _ -> begin
    let t = Array.make (p*q) (-1, -1) in
    for i = 0 to (p-1) do
      for j = 0 to (q-1) do
        t.(q * i + j) <- (j, p - i - 1)
      done;
    done;
    t
  end
  | Planar_hexa _ -> begin
    let n = p * q - p / 2 in
    let t = Array.make n (-1, -1) in
    let k = ref 0 in
    for i = 0 to (p-1) do
      if i mod 2 = 0 then begin
        for j = 0 to (q - 1) do
          t.(!k) <- (2*j, p - i - 1);
          incr k;
        done;
      end
      else begin
        for j = 0 to (q - 2) do
          t.(!k) <- (2*j + 1, p - i - 1);
          incr k;
        done;
      end
    done;
    t
  end
  | _ -> failwith "erreur type graphe get_graph \n"
  in 
  (g, t_emb)




let init_s (nat : g_nature ) (p : int) (q : int) : game_state = 
  let g, coord_init = get_graph nat p q in
  let card_init = Array.length g in
  let n = Array.length g in
  let pres_init = Array.make n true in
  (* car pour tout i, g.(i) <> [] comme i est connexe initialement *)
  let eg_init = {g = g; coord = coord_init; card = card_init ; pres = pres_init } in
  let m_init = go_next_matrix g in
  {nb_tour = 0; step = 0; pos_cop = Array.make 4 (-1); job_cop =  Array.make 4 Free; pos_x = -1; 
  e_g = eg_init;
  eg_ri = eg_init;
  (* precondition demandée par init*)
  m_cop = m_init
   }
(* codé seulement pour les types hexa, sq_full, square*)



let test (nb_tests : int) (p : int) (q : int) (time : int option) =
  let nb_cop_win = ref 0 in
  let nat = Grid None in
  let max_time = 200 in
  let t = Array.make (max_time + 1) 0 in
  for i = 0 to (nb_tests - 1) do
    let s = init_s nat p q in
    let res = catch_within s max_time in
    if res <> -1 then begin
      incr nb_cop_win;
      t.(res) <- t.(res) + 1
    end
  done;
  printf "Nb de wins de cops : %d sur %d tests \n" !nb_cop_win nb_tests;
  t


let file = "test_grid.csv"

let get_data () : unit =
  let t = test 1000 7 7 (Some 200) in
  let out_file = open_out file in
  let n = Array.length t in
  for i = 0 to (n-1) do
    fprintf out_file "%d \n" t.(i);
  done;
  close_out out_file
