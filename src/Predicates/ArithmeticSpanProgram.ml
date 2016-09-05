open Abbrevs
open Util
open MakeAlgebra
open NonMonotonicBF
open Matrix

type weight =
  | Weight_Var of int
  | Weight_Const of Zp.t
type node =
  | Node of int
type edge  = {
    edge_end_node : node;
    edge_weight : weight
  }
type graph = (node * edge list) list

let create_graph_from_formula (f : arithmetic_formula_normal_form) =
  let find_node i (n,_) = match n with Node(i') -> i' = i in
  let rec add_term graph origin k = function
    | [] -> graph, origin
    | v :: rest ->
       let (_, origin_edges) = L.find_exn graph ~f:(find_node origin) in
       let rest_graph = L.filter graph ~f:(fun a -> not (find_node origin a)) in
       let new_node = (Node(origin), origin_edges @ [{edge_end_node = Node(k); edge_weight = Weight_Var v}]) in
       add_term ((Node(k), []) :: new_node :: rest_graph) k (k+1) rest
  in
  let rec aux graph k = function
    | [] -> graph
    | (coeff, vars) :: rest_f ->
       let updated_graph, k' = add_term graph 0 k vars in
       let new_node, new_k =
         if k' = 0 then
           let (_, origin_edges) = L.find_exn graph ~f:(find_node 0) in
           (Node(0), origin_edges @ [{edge_end_node = Node(1); edge_weight = Weight_Const(coeff)}]), k
         else
           (Node(k'), [{edge_end_node = Node(1); edge_weight = Weight_Const(coeff)}]), (k'+1)
       in
       let new_graph = (L.tl_exn updated_graph) @ [new_node] in
       aux new_graph new_k rest_f
  in
  let initial_graph = [ (Node(0), []); (Node(1), []) ] in
  aux initial_graph 2 f

let adjacency_matrix (g : graph) =
  let g = L.sort g ~cmp:(fun (Node(i),_) (Node(j),_) -> I.compare i j) in
  let n = L.length g in
  let rec create_row row k edges =
    if k >= n then row
    else
      let w = match L.find edges ~f:(fun e -> e.edge_end_node = Node(k)) with
        | None -> Weight_Const Zp.zero
        | Some e -> e.edge_weight
      in
      create_row (row @ [w]) (k+1) edges
  in
  let rec create_matrix rows k =
    if k >= n then rows
    else
      let row = match L.find g ~f:(fun (Node(i),_) -> i = k) with
        | None -> create_row [] 0 []
        | Some (_,edges) -> create_row [] 0 edges
      in
      create_matrix (rows @ [row]) (k+1)
  in
  (* Move the second row to the last one *)
  let second_to_last = function
    | a :: b :: rest -> (a :: rest) @ [b]
    | _ -> assert false
  in
  let m = create_matrix [] 0 in
  L.map m ~f:second_to_last |> second_to_last


type arithmetic_span_program = {
    asp_yj : Zp.t list list;
    asp_zj : Zp.t list list;
    asp_rep : int; (* Number of vectors representing a single attribute *)
  }

let pp_asp _fmp asp =
  F.printf "rep = %d\ny =\n%a\nz=\n%a" asp.asp_rep (pp_matrix Zp.pp) asp.asp_yj (pp_matrix Zp.pp) asp.asp_zj

let create_asp_from_formula (f : arithmetic_formula_normal_form) (n : int) (rep : int) (equality : bool) =
  let matrix = adjacency_matrix (create_graph_from_formula f) in
  let extended =
    (L.hd_exn matrix) ::
      (L.map (list_range 1 (L.length matrix))
        ~f:(fun i ->
          L.fold_left (list_range 0 (L.length (L.hd_exn matrix)))
            ~init:[]
            ~f:(fun row j -> if j = (i-1) then row @ [Weight_Const (Zp.neg Zp.one)]
                             else row @ [L.nth_exn (L.nth_exn matrix i) j])
        )
      )
    |> L.map ~f:(fun row -> row @ [Weight_Const (Zp.zero)])
    |> fun m -> m @ [(mk_list (Weight_Const (Zp.zero)) ((L.length matrix)-1)) @ [Weight_Const(Zp.neg Zp.one); Weight_Const (Zp.one)]]
  in
  let yz =
    if equality then L.tl_exn (L.rev (transpose_matrix extended))
    else
      let first_row = L.hd_exn extended in
      let rev_tail = L.rev (L.tl_exn extended) in
      let last_row = L.hd_exn rev_tail in
      let middle = L.rev (L.tl_exn rev_tail) in
      [last_row] @ middle @ [first_row]
      |> transpose_matrix
  in
  let separated =
    L.map yz ~f:(fun row ->
      let is_var = function | Weight_Var(_) -> true | _ -> false in
      let variable = match L.find row ~f:is_var with
        | Some (Weight_Var(i)) -> i
        | _ -> 0
      in
      let y = L.fold_left row ~init:[] ~f:(fun y a -> match a with | Weight_Var(_) -> y @ [Zp.one] | _ -> y @ [Zp.zero]) in
      let z = L.fold_left row ~init:[] ~f:(fun z a -> match a with | Weight_Const(c) -> z @ [c] | _ -> z @ [Zp.zero]) in
      (variable, y, z)
    )
  in
  let error = "The formula is too big for the parameters" in
  let rec aux output without_variable k =
    if k > n then
      match without_variable with
      | [] -> output
      | _ -> failwith error
    else
      let variable_k = L.filter separated ~f:(fun (i,_,_) -> i = k) in
      if (L.length variable_k) > rep then failwith error
      else
        let some_wo_variable, rest_wo_variable = L.split_n without_variable (rep-(L.length variable_k)) in
        let rest_with_zeros =
          let zero_list = mk_list Zp.zero (L.length (L.hd_exn yz)) in
          mk_list (0, zero_list, zero_list) (rep - (L.length variable_k) - (L.length some_wo_variable))
        in
        aux (output @ variable_k @ some_wo_variable @ rest_with_zeros) rest_wo_variable (k+1)
  in

  let without_variable = L.filter separated ~f:(fun (i,_,_) -> i = 0) in
  L.fold_left (aux [] without_variable 1)
    ~init:{ asp_yj = []; asp_zj = []; asp_rep = rep}
    ~f:(fun asp (_,y,z) -> { asp with asp_yj = asp.asp_yj @ [y]; asp_zj = asp.asp_zj @ [z]})

let pp_weight _fmt = function
  | Weight_Var (i) -> F.printf "x%d" i
  | Weight_Const (a) -> F.printf "%a" Zp.pp a

let test () =
  let formula = OR (OR (LEAF 1, AND (LEAF 3, LEAF 4)), OR( AND(LEAF 2, NEG(LEAF 3)), NEG(AND(LEAF 4, LEAF 5)))) in
  let arithmetic_f = non_monotonic_bf_to_arithmetic_formula formula in
  let afn = af_to_af_normal_form arithmetic_f in
  F.printf "%a" pp_arithmetic_formula_nf afn;
  F.print_flush();
  let asp = create_asp_from_formula afn 5 3 false in
  F.printf "%a" pp_asp asp;
  F.print_flush();
  ()
