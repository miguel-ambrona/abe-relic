open Core_kernel.Std
open Abbrevs
open Util
open Matrix
open MakeAlgebra
open AlgStructures


(* ** Dual System Group proposed by Hoeteck *)

module Hoeteck's_DSG (B : BilinearGroup) = struct

  let k = L.length (B.G1.to_list B.G1.one) - 1
  let () = assert (L.length (B.G2.to_list B.G2.one) = k + 1)

  type pp = B.G1.t list * B.G1.t list list *
            B.G2.t list * B.G2.t list list
  type sp = R.bn list * R.bn list * R.bn list list list
  type img_mu = B.Gt.t list

  let samp_Dk n =
    let diagonal = sample_list ~f:Zp.samp n in
    let rec make_matrix matrix counter = function
      | [] -> matrix
      | a :: rest ->
         let new_row = (mk_list (R.bn_zero ()) counter) @ [a] @ (mk_list (R.bn_zero ()) (n - counter - 1)) in
         make_matrix (matrix @ [new_row]) (counter + 1) rest
    in
    (make_matrix [] 0 diagonal) @ [ mk_list (R.bn_one ()) n],
    (L.map diagonal ~f:Zp.inv) @ [Zp.neg (Zp.one)]
      
  let sampP n =
    let a_matrix, a_orth = samp_Dk k in
    let b_matrix, b_orth = samp_Dk k in


    let list_W = sample_list ~f:(fun () -> sample_matrix ~f:Zp.samp (k+1) (k+1)) n in
    let g1_A = matrix_map a_matrix ~f:B.G1.atom_from_dlog |> transpose_matrix |> L.map ~f:B.G1.from_list in
    let mu h = L.map g1_A ~f:(fun g -> B.e g h) in
    let g2_B = matrix_map b_matrix ~f:B.G2.atom_from_dlog |> transpose_matrix |> L.map ~f:B.G2.from_list in
    let list_WA = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:Zp.add ~mul:Zp.mul (transpose_matrix w) a_matrix) in
    let list_WB = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:Zp.add ~mul:Zp.mul w b_matrix) in
    let g1_WA =
      L.map list_WA ~f:(fun wa -> matrix_map wa ~f:B.G1.atom_from_dlog)
      |> L.map ~f:(fun m -> transpose_matrix m |> L.map ~f:B.G1.from_list)
    in
    let g2_WB =
      L.map list_WB ~f:(fun wb -> matrix_map wb ~f:B.G2.atom_from_dlog)
      |> L.map ~f:(fun m -> transpose_matrix m |> L.map ~f:B.G2.from_list)
    in
    mu, ((g1_A, g1_WA, g2_B, g2_WB), (a_orth, b_orth, list_W))


  let sampGT ?(randomness = None) p_list =
    let s_list =
      match randomness with
      | None        -> sample_list ~f:Zp.samp k
      | Some s_list -> s_list
    in
    let l = L.map2_exn s_list p_list ~f:(fun s p -> B.Gt.mul p s) in
    L.fold_left (L.tl_exn l) ~init:(L.hd_exn l) ~f:B.Gt.add


  let sampG ?(randomness = None) pp =
    let (g1_A, g1_WA, _, _) = pp in
    let s_list =
      match randomness with
      | None        -> sample_list ~f:Zp.samp k
      | Some s_list -> s_list
    in
    let prod_As = vector_times_vector ~add:B.G1.add ~mul:B.G1.mul g1_A s_list in
    let prod_WAs = L.map g1_WA ~f:(fun wa -> vector_times_vector ~add:B.G1.add ~mul:B.G1.mul wa s_list) in
    prod_As :: prod_WAs


  let sampH ?(randomness = None) pp =
    let r_list =
      match randomness with
      | None        -> sample_list ~f:Zp.samp k
      | Some r_list -> r_list
    in
    let (_, _, g2_B, g2_WB) = pp in
    let prod_Br = vector_times_vector ~add:B.G2.add ~mul:B.G2.mul g2_B r_list in
    let prod_WBr = L.map g2_WB ~f:(fun wb -> vector_times_vector ~add:B.G2.add ~mul:B.G2.mul wb r_list) in
    prod_Br :: prod_WBr

      
  (* *** String conversions *)
    
  let sep0 = "@"
  let sep1 = "#"
  let sep2 = ";"

  let string_of_pp pp =
    let (g1_A, g1_WA, g2_B, g2_WB) = pp in
    let g1_A_str  = L.map g1_A            ~f:(fun g -> B.G1.to_string g)  in
    let g1_WA_str = L.map g1_WA ~f:(L.map ~f:(fun g -> B.G1.to_string g)) in
    let g2_B_str  = L.map g2_B            ~f:(fun g -> B.G2.to_string g)  in
    let g2_WB_str = L.map g2_WB ~f:(L.map ~f:(fun g -> B.G2.to_string g)) in
    
    (list_to_string ~sep:sep2 g1_A_str) ^ sep0 ^ (list_list_to_string ~sep1 ~sep2 g1_WA_str) ^ sep0 ^
      (list_to_string ~sep:sep2 g2_B_str) ^ sep0 ^ (list_list_to_string ~sep1 ~sep2 g2_WB_str)

  let string_of_img_mu img_mu =
    list_to_string ~sep:sep2 (L.map img_mu ~f:(fun g -> B.Gt.to_string g))

  let csep0 = Char.of_string sep0
  let csep1 = Char.of_string sep1
  let csep2 = Char.of_string sep2

  let pp_of_string str =
    match String.split ~on:csep0 str with
    | g1_A_str :: g1_WA_str :: g2_B_str :: g2_WB_str :: [] ->
       (L.map (String.split ~on:csep2 g1_A_str) ~f:B.G1.of_string,
        L.map (String.split ~on:csep1 g1_WA_str) ~f:(fun s -> L.map (String.split ~on:csep2 s) ~f:B.G1.of_string),
        L.map (String.split ~on:csep2 g2_B_str) ~f:B.G2.of_string,
        L.map (String.split ~on:csep1 g2_WB_str) ~f:(fun s -> L.map (String.split ~on:csep2 s) ~f:B.G2.of_string)
       )
    | _ -> failwith "invalid string"

  let img_mu_of_string str =
    L.map (String.split ~on:csep2 str) ~f:B.Gt.of_string

end
