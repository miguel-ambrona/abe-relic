open Abbrevs
open Util
open LinAlg
open AlgStructures
open MakeAlgebra
open BoolForms
open Predicates
open Matrix

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

      val set_x : generic_attribute -> x
      val set_y : generic_attribute -> y

      val string_of_x : x -> string
      val string_of_y : y -> string
      val x_of_string : string -> x
      val y_of_string : string -> y
    end


module type PredEnc_Characterization = sig
  type x
  type y
  val predicate : x -> y -> bool
    
  val sE_matrix : x -> int -> Zp.t list list  (* int corresponds to w_length *)
  val rE_matrix : y -> int -> Zp.t list list  (* int corresponds to w_length *)
  val kE_vector : y -> Zp.t list
  val sD_vector : x -> y -> Zp.t list
  val rD_vector : x -> y -> Zp.t list
    
  val set_x : generic_attribute -> x
  val set_y : generic_attribute -> y
    
  val string_of_x : x -> string
  val string_of_y : y -> string
  val x_of_string : string -> x
  val y_of_string : string -> y
end

module PredEnc_from_Characterization (C : PredEnc_Characterization) (B : BilinearGroup) = struct
    type x = C.x
    type y = C.y

    let sE x w = matrix_times_vector ~add:B.G1.add ~mul:(fun a g -> B.G1.mul g a) (C.sE_matrix x (L.length w)) w
    let rE y w = matrix_times_vector ~add:B.G2.add ~mul:(fun a g -> B.G2.mul g a) (C.rE_matrix y (L.length w)) w
    let kE y alpha = L.map (C.kE_vector y) ~f:(fun exp -> B.G2.mul alpha exp)
    let sD x y c = vector_times_vector ~add:B.G1.add ~mul:(fun a g -> B.G1.mul g a) (C.sD_vector x y) c
    let rD x y d = vector_times_vector ~add:B.G2.add ~mul:(fun a g -> B.G2.mul g a) (C.rD_vector x y) d

    let set_x = C.set_x
    let set_y = C.set_y

    let string_of_x = C.string_of_x
    let string_of_y = C.string_of_y
    let x_of_string = C.x_of_string
    let y_of_string = C.y_of_string
end

module Boolean_Formula_PredEnc (B : BilinearGroup) = struct

  (* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)

  module GaussElim = LinAlg(Zp)

  type x = Zp.t list list
  type y = Zp.t list
      
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
      
  let set_x = function
    | BoolForm_Policy (nattrs, rep, policy) ->
       pred_enc_matrix_from_policy ~nattrs ~rep ~t_of_int:Zp.from_int policy
    | _ -> failwith "wrong input"

  let set_y = function
    | BoolForm_Attrs (nattrs, rep, attrs) ->
       pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs ~rep (L.map attrs ~f:(fun a -> Leaf(a)))
    | _ -> failwith "wrong input"


  (* *** String converions *)

  let sep1 = "#"
  let sep2 = ";"

  let string_of_x x =
    list_list_to_string ~sep1 ~sep2 (L.map x ~f:(L.map ~f:Zp.write_str))

  let string_of_y y =
    list_to_string ~sep:sep2 (L.map y ~f:Zp.write_str)

  let x_of_string str =
    L.map (S.split ~on:(Char.of_string sep1) str)
      ~f:(fun row -> L.map (S.split ~on:(Char.of_string sep2) row) ~f:Zp.read_str)

  let y_of_string str =
    L.map (S.split ~on:(Char.of_string sep2) str) ~f:Zp.read_str
end


module BF_PredEnc_Characterization = struct

  (* Predicate Encoding Characterization for Ciphertet-Policy ABE for boolean formulas *)

  module GaussElim = LinAlg(Zp)

  let rec expand_a output a = function
    | [] -> if a = [] then output else assert false
    | yi :: rest_y ->
       if Zp.is_zero yi then expand_a (output @ [Zp.zero]) a rest_y
       else expand_a (output @ [L.hd_exn a]) (L.tl_exn a) rest_y

  let get_a xM y =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (Zp.is_zero yi)) |> unzip1 in
    if filtered = [] then None (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      GaussElim.solve matrix (Zp.one :: (mk_list Zp.zero (l'-1)))

  type x = Zp.t list list
  type y = Zp.t list

  let predicate xM y =
    match get_a xM y with
    | None -> false
    | Some _ -> true
      
  let sE_matrix xM _w_length =
    let id_n = identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:(L.length xM) in
    let xM_without_col1 = L.map xM ~f:(fun row -> L.tl_exn row) in
    let xM_col1 = L.map xM ~f:(fun row -> [L.hd_exn row]) in
    join_blocks [[id_n; xM_without_col1; xM_col1]]

  let rE_matrix y w_length =
    let l = L.length y in
    let l' = w_length - l in
    let diag_y = diagonal_matrix ~zero:Zp.zero y in
    join_blocks
      [[ create_matrix Zp.zero ~m:1 ~n:l; create_matrix Zp.zero ~m:1 ~n:(l'-1); create_matrix Zp.one ~m:1 ~n:1 ];
       [ diag_y; create_matrix Zp.zero ~m:l ~n:(l'-1); create_matrix Zp.zero ~m:l ~n:1 ]]
      
  let kE_vector y =
    Zp.one :: (mk_list Zp.zero (L.length y))

  let sD_vector xM y =
    let a = match get_a xM y with
      | None -> mk_list Zp.zero (L.length y) (* Decryption failed *)
      | Some a -> expand_a [] a y
    in
    L.map2_exn y a ~f:(fun yi ai -> Zp.mul yi ai)
               
  let rD_vector xM y =
    let a = match get_a xM y with
      | None -> mk_list Zp.zero (L.length y) (* Decryption failed *)
      | Some a -> expand_a [] a y
    in
    Zp.one :: a
      
  let set_x = function
    | BoolForm_Policy (nattrs, rep, policy) ->
       pred_enc_matrix_from_policy ~nattrs ~rep ~t_of_int:Zp.from_int policy
    | _ -> failwith "wrong input"

  let set_y = function
    | BoolForm_Attrs (nattrs, rep, attrs) ->
       pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs ~rep (L.map attrs ~f:(fun a -> Leaf(a)))
    | _ -> failwith "wrong input"


  (* *** String converions *)

  let sep1 = "#"
  let sep2 = ";"

  let string_of_x x =
    list_list_to_string ~sep1 ~sep2 (L.map x ~f:(L.map ~f:Zp.write_str))

  let string_of_y y =
    list_to_string ~sep:sep2 (L.map y ~f:Zp.write_str)

  let x_of_string str =
    L.map (S.split ~on:(Char.of_string sep1) str)
      ~f:(fun row -> L.map (S.split ~on:(Char.of_string sep2) row) ~f:Zp.read_str)

  let y_of_string str =
    L.map (S.split ~on:(Char.of_string sep2) str) ~f:Zp.read_str

end
