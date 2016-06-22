open Abbrevs
open Util
open Algebra

(* ** Dual System Group proposed by Hoeteck *)

module Hoeteck's_DSG = struct

  let k = 10 (* G1.k*)

  let dual_system_pairing l1 l2 =
    let gt_list = L.map2_exn l1 l2 ~f:R.e_pairing in
    L.fold_left (L.tl_exn gt_list) ~init:(L.hd_exn gt_list) ~f:R.gt_mul
      
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

    let g1 = R.g1_gen () in
    let g2 = R.g2_gen () in
    
    let list_W = sample_list ~f:(fun () -> sample_matrix ~f:Zp.samp (k+1) (k+1)) n in
    let g1_A = matrix_map a_matrix ~f:(R.g1_mul g1) in
    let g2_B = matrix_map b_matrix ~f:(R.g2_mul g2) in
    let list_WA = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:Zp.add ~mul:Zp.mul (transpose_matrix w) a_matrix) in
    let list_WB = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:Zp.add ~mul:Zp.mul w b_matrix) in
    let g1_WA = L.map list_WA ~f:(fun wa -> matrix_map wa ~f:(R.g1_mul g1)) in
    let g2_WB = L.map list_WB ~f:(fun wb -> matrix_map wb ~f:(R.g2_mul g2)) in
    (g1_A, g1_WA, g2_B, g2_WB), (a_orth, b_orth, list_W)


  let sampGT ?(randomness = None) p_list =
    let s_list =
      match randomness with
      | None        -> sample_list ~f:Zp.samp k
      | Some s_list -> s_list
    in
    let l = L.map2_exn s_list p_list ~f:(fun s p -> R.gt_exp p s) in
    L.fold_left (L.tl_exn l) ~init:(L.hd_exn l) ~f:R.gt_mul


  let sampG ?(randomness = None) pp =
    let (g1_A, g1_WA, _, _) = pp in
    let s_list =
      match randomness with
      | None        -> sample_list ~f:Zp.samp k
      | Some s_list -> s_list
    in
    let prod_As = matrix_times_vector ~add:R.g1_add ~mul:R.g1_mul g1_A s_list in
    let prod_WAs = L.map g1_WA ~f:(fun wa -> matrix_times_vector ~add:R.g1_add ~mul:R.g1_mul wa s_list) in
    prod_As :: prod_WAs


  let sampH pp =
    let (_, _, g2_B, g2_WB) = pp in
    let r_list = sample_list ~f:Zp.samp k in
    let prod_Br = matrix_times_vector ~add:R.g2_add ~mul:R.g2_mul g2_B r_list in
    let prod_WBr = L.map g2_WB ~f:(fun wb -> matrix_times_vector ~add:R.g2_add ~mul:R.g2_mul wb r_list) in
    prod_Br :: prod_WBr

end

