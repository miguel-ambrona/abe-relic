open Abbrevs
open LinAlg
open Util
open Zp
module R = Relic

(* ** Functions for boolean formulas *)

module GaussElim = LinAlg(struct
  type t = R.bn
  let pp fmt a = F.fprintf fmt "%s" (R.bn_write_str a ~radix:10)
  let add = bn_add_mod
  let neg = bn_neg_mod
  let mul = bn_mul_mod
  let inv = zp_inverse
  let one = R.bn_one ()
  let zero = R.bn_zero ()
  let is_zero = bn_is_zero_mod
end)  

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



(* ** Util *)

let matrix_from_policy ~nattrs ~rep p =
  sort_matrix ~rep (matrix_of_formula p) nattrs
  |> unzip1
  |> L.map ~f:(L.map ~f:(fun i -> bn_read_str_mod (string_of_int i)))
  
let set_attributes ~nattrs ~rep attrs =
  let rec repeat output = function
    | [] -> output
    | a :: rest -> repeat (output @ (mk_list a rep)) rest
  in
  let rec mk_bit_vector output k =
    if k > nattrs then output
    else
      if L.exists attrs ~f:(function | Leaf(Att(i)) -> i = k | _ -> assert false) then
        mk_bit_vector (output @ [ R.bn_one () ]) (k+1)
      else
        mk_bit_vector (output @ [ R.bn_zero () ]) (k+1)
  in
  repeat [] (mk_bit_vector [] 1)

let (&.) a b = And(a,b)
let (|.) a b = Or(a,b)
