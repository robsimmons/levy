(** Transitive closure *)

module SetS =
  Set.Make(struct type t = string let compare = String.compare end)

type vertex = string
type edge = vertex * vertex

type graph = 
  { fwdedges: (vertex, SetS.t) Hashtbl.t ;
    fwdpaths: (vertex, SetS.t) Hashtbl.t ;
    bwdedges: (vertex, SetS.t) Hashtbl.t ;
    bwdpaths: (vertex, SetS.t) Hashtbl.t }

(** [create ()] makes a new graph. *)
let create n: graph = 
  { fwdedges = Hashtbl.create n ;  
    fwdpaths = Hashtbl.create n ; 
    bwdedges = Hashtbl.create n ; 
    bwdpaths = Hashtbl.create n }

(** [edge graph (s, t)] checks whether there is an edge [(s, t)] in
    the graph [graph]. *)
let edge ({fwdedges}: graph) ((s, t): edge) = 
  Hashtbl.mem fwdedges s && SetS.mem t (Hashtbl.find fwdedges s)

(** [path graph (s, t)] checks whether there is a path [(s, t)] in 
    the graph [graph]. *)
let path ({fwdpaths}: graph) ((s, t): edge) = 
  Hashtbl.mem fwdpaths s && SetS.mem t (Hashtbl.find fwdpaths s)

(** [imm_succ graph s] returns the set of vertices [t] such that
    [edge graph (s, t)] holds. *)
let imm_succ ({fwdedges}: graph) (s: vertex) =
  if not (Hashtbl.mem fwdedges s)
  then SetS.empty
  else Hashtbl.find fwdedges s

(** [succ graph s] returns the set of vertices [t] such that
    [path graph (s, t)] holds. *)
let succ ({fwdpaths}: graph) (s: vertex) = 
  if not (Hashtbl.mem fwdpaths s)
  then SetS.empty
  else Hashtbl.find fwdpaths s

(** [imm_pred graph t] returns the set of vertices [s] such that
    [edge graph (s, t)] holds. *)
let imm_pred ({bwdedges}: graph) (s: vertex) = 
  if not (Hashtbl.mem bwdedges s)
  then SetS.empty
  else Hashtbl.find bwdedges s

(** [pred graph t] returns the set of vertices [s] such that
    [path graph (s, t)] holds. *)
let pred ({bwdpaths}: graph) (s: vertex) = 
  if not (Hashtbl.mem bwdpaths s)
  then SetS.empty
  else Hashtbl.find bwdpaths s

(** [is_final graph s] returns true iff [s] has no successors. *)
let is_final graph s = SetS.is_empty (succ graph s)

(** [is_initial graph s] returns true iff [s] has no predecessors. *)
let is_initial graph s = SetS.is_empty (pred graph s)

(** [iter_paths graph f] runs [f (s, t)] for every path [(s, t)] in the graph
    [graph]. *)
let iter_paths ({fwdpaths}: graph) f = 
  Hashtbl.iter 
    (fun s ts -> 
       SetS.fold (fun t () -> f s t) ts ())
    fwdpaths

let prim_augment tbl s t = 
  if not (Hashtbl.mem tbl s)
  then Hashtbl.add tbl s (SetS.singleton t)
  else (let set = Hashtbl.find tbl s in 
        Hashtbl.remove tbl s ;  
        Hashtbl.add tbl s (SetS.add t set))

let prim_insert_edge ({fwdedges; bwdedges}: graph) ((s, t): edge) = 
  prim_augment fwdedges s t ;
  prim_augment bwdedges t s

let prim_insert_path ({fwdpaths; bwdpaths}: graph) ((s, t): edge) = 
  prim_augment fwdpaths s t ;
  prim_augment bwdpaths t s

(** Worklist implementation for adding an edge to a graph *)
let add_edge (graph: graph) ((s, t): edge) = 
  (* Filter; we only want to add to the path queue non-extant paths *)
  let fwdmem (s, t) = 
    if path graph (s, t) then ([])
    else (prim_insert_path graph (s, t) ; [ (s, t) ]) in

  (* McAllester loop *)
  let rec paths = function
    | [] -> ()
    | (t, u) :: old_worklist -> 
        let new_worklist = 
          SetS.fold (fun s es -> fwdmem (s, u) @ es)
            (imm_pred graph t)
            old_worklist in
        paths new_worklist in

  if edge graph (s, t) then ()
  else (prim_insert_edge graph (s, t) ; 
        let worklist = 
          SetS.fold (fun u es -> fwdmem (s, u) @ es)
            (succ graph t)
            (fwdmem (s, t)) in
        paths worklist)

