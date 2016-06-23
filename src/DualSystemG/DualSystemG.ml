open Abbrevs
open Util
open Algebra
open AlgebraInterfaces

(* ** Dual System Group proposed by Hoeteck *)

module Hoeteck's_DSG (B : BilinearGroup) = struct

  let k = 10 (* G1.k*)

(*  let dual_system_pairing g h =
    let gt_list = L.map2_exn g h ~f:R.e_pairing in
    L.fold_left (L.tl_exn gt_list) ~init:(L.hd_exn gt_list) ~f:R.gt_mul
    *)
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

    let g1 = B.G1.atom_gen in
    let g2 = B.G2.atom_gen in

    let list_W = sample_list ~f:(fun () -> sample_matrix ~f:Zp.samp (k+1) (k+1)) n in
    let g1_A = matrix_map a_matrix ~f:(B.G1.atom_mul g1) |> transpose_matrix |> L.map ~f:B.G1.from_list in
    let g2_B = matrix_map b_matrix ~f:(B.G2.atom_mul g2) |> transpose_matrix |> L.map ~f:B.G2.from_list in
    let list_WA = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:Zp.add ~mul:Zp.mul (transpose_matrix w) a_matrix) in
    let list_WB = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:Zp.add ~mul:Zp.mul w b_matrix) in
    let g1_WA =
      L.map list_WA ~f:(fun wa -> matrix_map wa ~f:(B.G1.atom_mul g1))
      |> L.map ~f:(fun m -> transpose_matrix m |> L.map ~f:B.G1.from_list)
    in
    let g2_WB =
      L.map list_WB ~f:(fun wb -> matrix_map wb ~f:(B.G2.atom_mul g2))
      |> L.map ~f:(fun m -> transpose_matrix m |> L.map ~f:B.G2.from_list)
    in
    (g1_A, g1_WA, g2_B, g2_WB), (a_orth, b_orth, list_W)


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


  let sampH pp =
    let (_, _, g2_B, g2_WB) = pp in
    let r_list = sample_list ~f:Zp.samp k in
    let prod_Br = vector_times_vector ~add:B.G2.add ~mul:B.G2.mul g2_B r_list in
    let prod_WBr = L.map g2_WB ~f:(fun wb -> vector_times_vector ~add:B.G2.add ~mul:B.G2.mul wb r_list) in
    prod_Br :: prod_WBr

end
