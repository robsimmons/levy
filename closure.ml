(** Transitive closure *)

module SetS =
  Set.Make(struct type t = string let compare = String.compare end)

type vertex = string
type edge = vertex * vertex

type graph = (vertex, SetS.t) Hashtbl.t * (vertex, SetS.t) Hashtbl.t

let new_graph (): graph = (Hashtbl.create 5, Hashtbl.create 5)

let check_path ((bwdedges, fwdpaths): graph) ((s, t): edge) = 
  Hashtbl.mem fwdpaths s && SetS.mem t (Hashtbl.find fwdpaths s)

let is_final ((_, fwdpaths): graph) = Hashtbl.mem fwdpaths

let iter_paths f ((_, fwdpaths): graph) = 
  Hashtbl.iter 
    (fun s ts -> 
       SetS.fold (fun t () -> f s t) ts ())
    fwdpaths

let add_edge ((bwdedges, fwdpaths): graph) ((s, t): edge) = 

  (* Filter; we only want to add to the path queue non-extant paths *)
  let fwdmem (s, t) = 
    (* print_string ("fwdmem(" ^ s ^ ", " ^ t ^ ")... ") ; *)
    if not (Hashtbl.mem fwdpaths s)
    then ((* print_endline (s ^ " not in paths") ; *)
          Hashtbl.add fwdpaths s (SetS.singleton t) ;
          [ (s, t) ])
    else if SetS.mem t (Hashtbl.find fwdpaths s)
    then ((* print_endline ("duplicate") ; *)
          [])
    else (let nexts = Hashtbl.find fwdpaths s in
          (* print_endline (t ^ " not in successors") ; *)
          Hashtbl.remove fwdpaths s ; 
          Hashtbl.add fwdpaths s (SetS.add t nexts) ;
          [ (s, t) ]) in
 
  (* Query the previous paths to an edge *)
  let prevs t = 
    if not (Hashtbl.mem bwdedges t)
    then SetS.empty
    else Hashtbl.find bwdedges t in
 
  (* McAllester loop *)
  let rec paths = function
    | [] -> ()
    | (t, u) :: es -> 
        print_endline ("Dequeing " ^ t ^ ", " ^ u) ; 
        paths (SetS.fold (fun s es -> fwdmem (s, u) @ es) (prevs t) es) in

  if not (Hashtbl.mem bwdedges t)
  then (Hashtbl.add bwdedges t (SetS.singleton s) ; paths (fwdmem (s, t)))
  else 
    let prevs = Hashtbl.find bwdedges t in
    if not (SetS.mem s prevs) 
    then (Hashtbl.add bwdedges t (SetS.add s prevs) ; paths (fwdmem (s, t)))
