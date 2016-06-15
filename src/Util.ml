open Core_kernel.Std
open Abbrevs

let sample_list ~f k =
  let rec aux list k = 
    if k = 0 then list
    else aux (list @ [f ()]) (k-1)
  in
  aux [] k

let sample_matrix ~f m n =
  let rec aux matrix m = 
    if m = 0 then matrix
    else aux (matrix @ [sample_list ~f n]) (m-1)
  in
  aux [] m
    
let transpose_matrix list =
  L.fold_left list
    ~init:(L.map (L.hd_exn list) ~f:(fun _ -> []))
    ~f:(fun l_output l -> L.map2_exn l_output l ~f:(fun li e -> li @ [e]))
    
let vector_times_vector ~add ~mul v1 v2 =
  let prods = L.map2_exn v1 v2 ~f:mul in
  L.fold_left (L.tl_exn prods)
    ~init:(L.hd_exn prods)
    ~f:add
    
let matrix_times_vector ~add ~mul m v = L.map m ~f:(fun row -> vector_times_vector ~add ~mul row v)

let matrix_times_matrix ~add ~mul m1 m2 =
  L.map (transpose_matrix m2) ~f:(fun col -> matrix_times_vector ~add ~mul m1 col)
  |> transpose_matrix
    
let matrix_map ~f m = L.map m ~f:(L.map ~f)


let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_int fmt i = F.fprintf fmt "%i" i

let mk_list el n =
  let rec aux output n =
    if n = 0 then output
    else aux (el :: output) (n-1)
  in
  aux [] n

let unzip1 list =
  let (list1,_) = L.unzip list in
  list1

let unzip2 list =
  let (_,list2) = L.unzip list in
  list2

let position_in_list el list =
  let rec aux k =
    if k >= (L.length list) then None
    else if L.nth_exn list k = el then Some k
    else aux (k+1)
  in
  aux 0

let list_to_string list =
  let del = ", " in
  let rec aux output = function
    | [] -> output
    | s :: [] -> output ^ s
    | s :: rest -> aux (output ^ s ^ del) rest
  in
  "[" ^ (aux "" list) ^ "]"

let list_list_to_string list =
  let del = ", " in
  let rec aux output = function
    | [] -> output
    | l :: [] -> output ^ (list_to_string l)
    | l :: rest -> aux (output ^ (list_to_string l) ^ del) rest
  in
  "[" ^ (aux "" list) ^ "]"

let list_list_list_to_string list =
  let del = ", " in
  let rec aux output = function
    | [] -> output
    | l :: [] -> output ^ (list_list_to_string l)
    | l :: rest -> aux (output ^ (list_list_to_string l) ^ del) rest
  in
  "[" ^ (aux "" list) ^ "]"

let to_base64 ?(split = false) string =
  let string64 = B64.encode string in
  let n = String.length string64 in
  let rec go output k =
    if (n - k < 64) then
      output ^ (String.slice string64 k n)
    else
      go (output ^ (String.slice string64 k (k+64)) ^ "\n") (k+64)
  in
  if not split then string64
  else go "" 0

let from_base64 string64 =
  let string = String.strip string64 in
  B64.decode string
