open Abbrevs
open Util
open LinAlg
open AlgStructures
open MakeAlgebra
open BoolForms

(* ** Predicate Encodings *)

module type PredEnc =
  functor (B : BilinearGroup) ->
    sig
      type x
      type y
      val sE : x -> B.G1.t list -> B.G1.t list
      val rE : y -> B.G2.t list -> B.G2.t list
      val kE : y -> B.G2.t -> B.G2.t list
      val sD : x -> y -> B.G1.t list -> B.G1.t
      val rD : x -> y -> B.G2.t list -> B.G2.t

      type x_input
      type y_input
      val set_x : x_input -> x
      val set_y : y_input -> y
    end

module Boolean_Formula_PredEnc (B : BilinearGroup) = struct

  (* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)

  module GaussElim = LinAlg(Zp)

  type x = R.bn list list
  type y = R.bn list
  let head = L.hd_exn
  let tail = L.tl_exn
  let single v = if L.length v = 1 then head v else assert false
      
  let sE xM w_u_u0 =
    let ( +! ) = L.map2_exn ~f:B.G1.add in
    let l = L.length xM in
    let l' = L.length (L.hd_exn xM) in
    let w = L.slice w_u_u0 0 l in
    let u = L.slice w_u_u0 l (l+l'-1) in
    let u0 = L.hd_exn (L.tl_exn w_u_u0) in
    w +! (matrix_times_vector ~add:B.G1.add ~mul:(fun exp g -> B.G1.mul g exp) xM (u0 :: u))

  let rE y w_u_u0 =
    let l = L.length y in
    let w = L.slice w_u_u0 0 l in
    let u0 = L.hd_exn (L.tl_exn w_u_u0) in
    u0 :: (L.map2_exn ~f:B.G2.mul w y)
      
  let kE y alpha =
    alpha :: (mk_list B.G2.zero (L.length y))
      
  let sD xM y c =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
    if filtered = [] then B.G1.zero (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
      | None -> B.G1.zero (* Decryption failed *)
      | Some a ->
         let y_c = L.filter (L.zip_exn c y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
         let a_y_c = L.map2_exn ~f:B.G1.mul y_c a in
         L.fold_left (L.tl_exn a_y_c)
           ~init:(L.hd_exn a_y_c)
           ~f:B.G1.add
           
  let rD xM y d_d' =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
    if filtered = [] then B.G2.zero (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
      | None -> B.G2.zero (* Decryption failed *)
      | Some a ->
         let d' = L.hd_exn d_d' in
         let d = L.tl_exn d_d' in
         let d = L.filter (L.zip_exn d y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
         let a_d = L.map2_exn ~f:B.G2.mul d a in
         B.G2.add
           d'
           (L.fold_left (L.tl_exn a_d)
              ~init:(L.hd_exn a_d)
              ~f:B.G2.add)

  type x_input = ~nattrs:int * int * bool_formula
  type y_input = int * int * bool_formula list

  let set_x (nattrs, rep, policy) =
    pred_enc_matrix_from_policy ~nattrs ~rep ~t_of_int:(fun i -> R.bn_read_str (string_of_int i) ~radix:10) policy
      
  let set_y (nattrs, rep, attrs) =
    pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs ~rep attrs

end
