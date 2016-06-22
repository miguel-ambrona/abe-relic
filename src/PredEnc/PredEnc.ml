open Abbrevs
open Util
open BoolForms
open Algebra

(* ** Predicate Encodings *)

module type PredEnc = sig
  type x
  type y
  val sE : x -> G1.t list -> G1.t list
  val rE : y -> G2.t list -> G2.t list
  val kE : y -> G2.t -> G2.t list
  val sD : x -> y -> G1.t list -> G1.t
  val rD : x -> y -> G2.t list -> G2.t
end

module Boolean_Formula_PredEnc = struct

  (* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)

  type x = R.bn list list
  type y = R.bn list
  let head = L.hd_exn
  let tail = L.tl_exn
  let single v = if L.length v = 1 then head v else assert false
      
  let sE xM w_u_u0 =
    let ( +! ) = L.map2_exn ~f:G1.add in
    let l = L.length xM in
    let l' = L.length (L.hd_exn xM) in
    let w = L.slice w_u_u0 0 l in
    let u = L.slice w_u_u0 l (l+l'-1) in
    let u0 = L.hd_exn (L.tl_exn w_u_u0) in
    w +! (matrix_times_vector ~add:G1.add ~mul:(fun exp g -> G1.mul g exp) xM (u0 :: u))

  let rE y w_u_u0 =
    let l = L.length y in
    let w = L.slice w_u_u0 0 l in
    let u0 = L.hd_exn (L.tl_exn w_u_u0) in
    u0 :: (L.map2_exn ~f:G2.mul w y)
      
  let kE y alpha =
    alpha :: (mk_list G2.zero (L.length y))
      
  let sD xM y c =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
    if filtered = [] then G1.zero (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
      | None -> G1.zero (* Decryption failed *)
      | Some a ->
         let y_c = L.filter (L.zip_exn c y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
         let a_y_c = L.map2_exn ~f:G1.mul y_c a in
         L.fold_left (L.tl_exn a_y_c)
           ~init:(L.hd_exn a_y_c)
           ~f:G1.add
           
  let rD xM y d_d' =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
    if filtered = [] then G2.zero (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
      | None -> G2.zero (* Decryption failed *)
      | Some a ->
         let d' = L.hd_exn d_d' in
         let d = L.tl_exn d_d' in
         let d = L.filter (L.zip_exn d y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
         let a_d = L.map2_exn ~f:G2.mul d a in
         G2.add
           d'
           (L.fold_left (L.tl_exn a_d)
              ~init:(L.hd_exn a_d)
              ~f:G2.add)
end
