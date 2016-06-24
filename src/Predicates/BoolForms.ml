open Abbrevs
open Util

(* * Functions for boolean formulas *)

type attribute = Att of int

type bool_formula =
  | Or   of bool_formula * bool_formula
  | And  of bool_formula * bool_formula
  | Leaf of attribute

let matrix_of_formula bf =
  let c = ref 1 in
  let add_zeros v = v @ (mk_list 0 (!c - (L.length v))) in
  let rec aux v = function
    | Or(bf1, bf2)  -> (aux v bf1) @ (aux v bf2)
    | And(bf1, bf2) ->
       let v1 = (add_zeros v) @ [1] in
       let v2 = (mk_list 0 !c) @ [-1] in
       c := !c + 1;
       (aux v1 bf1) @ (aux v2 bf2)
    | Leaf(a) -> [(v, a)]
  in
  L.map (aux [1] bf) ~f:(fun (v,a) ->  (add_zeros v, a))

(* ** Predicate Encodings Matrix Adjustments *)

let sort_matrix ?(rep = 1) matrix n_attrs =
  let empty_row =
    let (r,_) = L.hd_exn matrix in
    mk_list 0 (L.length r)
  in
  let rec aux matrix k =
    if k > n_attrs then matrix
    else
      let k_rows = L.count matrix ~f:(function | (_,Att(i)) -> k = i) in
      if k_rows > rep then
        failwith ("This matrix needs more than " ^ (string_of_int rep) ^ " repetitions")
      else
        let matrix' = matrix @ (mk_list (empty_row, Att(k)) (rep - k_rows)) in
        aux matrix' (k+1)
  in
  L.sort (aux matrix 1)
    ~cmp:(fun (_r1,a1) (_r2,a2) -> match a1,a2 with | Att(i1), Att(i2) -> i1 - i2)

let pred_enc_matrix_from_policy ~nattrs ~rep ~t_of_int p =
  sort_matrix ~rep (matrix_of_formula p) nattrs
  |> unzip1
  |> L.map ~f:(L.map ~f:t_of_int)
  
let pred_enc_set_attributes ~one ~zero ~nattrs ~rep attrs =
  let rec repeat output = function
    | [] -> output
    | a :: rest -> repeat (output @ (mk_list a rep)) rest
  in
  let rec mk_bit_vector output k =
    if k > nattrs then output
    else
      if L.exists attrs ~f:(function | Leaf(Att(i)) -> i = k | _ -> assert false) then
        mk_bit_vector (output @ [ one ]) (k+1)
      else
        mk_bit_vector (output @ [ zero ]) (k+1)
  in
  repeat [] (mk_bit_vector [] 1)

(* ** Pair Encodings Matrix Ajustments *)

let pair_enc_expand_matrix ~n1 ~n2 matrix labels =
  let rows = L.length matrix in
  let cols = L.length (L.hd_exn matrix) in
  if      rows > n1   then failwith ("The number of Leaf nodes must be at most " ^ (string_of_int n1))
  else if cols-1 > n2 then failwith ("The number of AND gates must be at most " ^ (string_of_int n2))
  else
    let empty_row = mk_list 0 n2 in
    let extended_cols = L.map matrix ~f:(fun row -> row @ (mk_list 0 (n2 - cols + 1))) in
    let matrix' = extended_cols @ (mk_list empty_row (n1 - rows)) in
    let extended_labels = labels @ (mk_list (Att(0)) (n1 - rows)) in
    matrix', extended_labels
                                           
let pair_enc_matrix_of_policy ~n1 ~n2 ~t_of_int p =
  let matrix, labels = L.unzip (matrix_of_formula p) in
  let matrix', labels' = pair_enc_expand_matrix ~n1 ~n2 matrix labels in
  L.map ~f:(L.map ~f:t_of_int) matrix',
  (fun i -> match L.nth_exn labels' (i-1) with | Att(n) -> t_of_int n)

let pair_enc_set_attributes ~t_of_int attributes =
  L.map attributes ~f:(function Leaf(Att(i)) -> t_of_int i | _ -> failwith "Invalid attribute")

(* ** Short operators *)

let (&.) a b = And(a,b)
let (|.) a b = Or(a,b)
