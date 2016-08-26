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
      val n : int

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
    
  val s : int
  val r : int
  val w : int

  val sE_matrix : x -> Zp.t list list
  val rE_matrix : y -> Zp.t list list
  val kE_vector : y -> Zp.t list
  val sD_vector : x -> y -> Zp.t list
  val rD_vector : x -> y -> Zp.t list

  val get_witness : x -> y -> Zp.t list
    
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

    let n = C.w

    let sE x w = matrix_times_vector ~add:B.G1.add ~mul:(fun a g -> B.G1.mul g a) (C.sE_matrix x) w
    let rE y w = matrix_times_vector ~add:B.G2.add ~mul:(fun a g -> B.G2.mul g a) (C.rE_matrix y) w
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

module Disjunction_Characterization (C1 : PredEnc_Characterization) (C2 : PredEnc_Characterization) = struct

  let diag_join m1 m2 =
    join_blocks [[ m1; create_matrix Zp.zero ~m:(L.length m1) ~n:(L.length (L.hd_exn m2))];
                 [ create_matrix Zp.zero ~m:(L.length m2) ~n:(L.length (L.hd_exn m1)); m2 ]];

  type x = C1.x * C2.x
  type y = C1.y * C2.y

  let predicate (x1,x2) (y1,y2) = (C1.predicate x1 y1) || (C2.predicate x2 y2)

  let s = C1.s + C2.s
  let r = C1.r + C2.r
  let w = C1.w + C2.w

  let sE_matrix (x1,x2) = diag_join (C1.sE_matrix x1) (C2.sE_matrix x2)
  let rE_matrix (y1,y2) = diag_join (C1.rE_matrix y1) (C2.rE_matrix y2)
  let kE_vector (y1,y2) = (C1.kE_vector y1) @ (C2.kE_vector y2)
  let sD_vector (x1,x2) (y1,y2) =
    if C1.predicate x1 y1 then
      let b1 = C1.sD_vector x1 y1 in
      b1 @ (mk_list Zp.zero C2.s)
    else
      let b2 = C2.sD_vector x2 y2 in
      (mk_list Zp.zero C1.s) @ b2
  let rD_vector (x1,x2) (y1,y2) =
    if C1.predicate x1 y1 then
      let b1 = C1.rD_vector x1 y1 in
      b1 @ (mk_list Zp.zero C2.r)
    else
      let b2 = C2.rD_vector x2 y2 in
      (mk_list Zp.zero C1.r) @ b2

  let get_witness (x1,x2) (y1,y2) =
    (C1.get_witness x1 y1) @ (C2.get_witness x2 y2)

  let set_x = function GenericAttPair(gx1, gx2) -> (C1.set_x gx1, C2.set_x gx2) | _ -> failwith "Pair of Generic Attributes expected"
  let set_y = function GenericAttPair(gy1, gy2) -> (C1.set_y gy1, C2.set_y gy2) | _ -> failwith "Pair of Generic Attributes expected"

  let sep = "!"
  let string_of_x (x1,x2) = (C1.string_of_x x1) ^ sep ^ (C2.string_of_x x2)
  let string_of_y (y1,y2) = (C1.string_of_y y1) ^ sep ^ (C2.string_of_y y2)
  let x_of_string str =
    match S.split str ~on:(Char.of_string sep) with
    | s1 :: s2 :: [] -> (C1.x_of_string s1, C2.x_of_string s2)
    | _ -> failwith "invalid string"
  let y_of_string str =
    match S.split str ~on:(Char.of_string sep) with
    | s1 :: s2 :: [] -> (C1.y_of_string s1, C2.y_of_string s2)
    | _ -> failwith "invalid string"

end

module Slow_Negation_Characterization (C : PredEnc_Characterization) = struct

  type x = C.x
  type y = C.y

  module M = MyGaussElim (Zp)
  module GaussElim = LinAlg(Zp)

  let predicate x y = not (C.predicate x y)
  
  let s = C.w
  let r = C.w + 1
  let w = C.r + C.w + C.s

  let sE_matrix x =
    join_blocks [[ create_matrix Zp.zero ~m:s ~n:C.r;
                   identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:s;
                   L.map (transpose_matrix (C.sE_matrix x)) ~f:(L.map ~f:Zp.neg) ]]
  let rE_matrix y =
    let mAr = C.rE_matrix y in
    let mAr' = M.pseudo_inverse mAr in
    let id_r = identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:C.w in
    let m12 =
      add_matrices ~add:(fun a b -> Zp.add a (Zp.neg b)) id_r
        (transpose_matrix (matrix_times_matrix ~add:Zp.add ~mul:Zp.mul mAr' mAr))
    in
    let k = C.kE_vector y in
    let m22 = matrix_times_matrix ~add:Zp.add ~mul:Zp.mul [k] (transpose_matrix mAr') in
    join_blocks [
      [ transpose_matrix mAr; m12; create_matrix Zp.zero ~m:C.w ~n:C.s ];
      [ [L.map k ~f:Zp.neg]; m22; create_matrix Zp.zero ~m:1 ~n:C.s];
    ]
  let kE_vector _y = 
    (mk_list Zp.zero C.w) @ [Zp.one]

  let sD_vector x y =
    C.get_witness x y
       
  let rD_vector x y =
    let w' = C.get_witness x y in
    w' @ [Zp.one]

  let get_witness x y =
    let mAs = C.sE_matrix x in
    let mAr = C.rE_matrix y in
    let mAr' = M.pseudo_inverse mAr in
    let bs = C.sD_vector x y in
    let br = C.rD_vector x y in
    let mAst_bs = matrix_times_vector ~add:Zp.add ~mul:Zp.mul (transpose_matrix mAs) bs in
    let aux = matrix_times_vector ~add:Zp.add ~mul:Zp.mul (transpose_matrix mAr') mAst_bs in
    (L.map2_exn aux br ~f:(fun a b -> Zp.add a (Zp.neg b))) @ mAst_bs @ bs

  let set_x = C.set_x
  let set_y = C.set_y

  let string_of_x = C.string_of_x
  let string_of_y = C.string_of_y
  let x_of_string = C.x_of_string
  let y_of_string = C.y_of_string
end

module Negation_Characterization (C : PredEnc_Characterization) = struct

  type x = C.x
  type y = C.y

  module GaussElim = LinAlg(Zp)

  let predicate x y = not (C.predicate x y)
  
  let s = C.w
  let r = C.w + 1
  let w = C.r + C.w + C.s

  let sE_matrix x =
    join_blocks [[ create_matrix Zp.zero ~m:s ~n:C.r;
                   identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:s;
                   L.map (transpose_matrix (C.sE_matrix x)) ~f:(L.map ~f:Zp.neg) ]]
  let rE_matrix y =
    let mAr = C.rE_matrix y in
    let id_r = identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:C.w in
    let k = C.kE_vector y in
    join_blocks [
      [ transpose_matrix mAr; id_r; create_matrix Zp.zero ~m:C.w ~n:C.s ];
      [ [L.map k ~f:Zp.neg]; create_matrix Zp.zero ~m:1 ~n:C.w; create_matrix Zp.zero ~m:1 ~n:C.s];
    ]
  let kE_vector _y = 
    (mk_list Zp.zero C.w) @ [Zp.one]

  let sD_vector x y =
    C.get_witness x y
       
  let rD_vector x y =
    let w' = C.get_witness x y in
    w' @ [Zp.one]

  let get_witness x y =
    let mAs = C.sE_matrix x in
    let bs = C.sD_vector x y in
    let br = C.rD_vector x y in
    bs @ (matrix_times_vector ~add:Zp.add ~mul:Zp.mul (transpose_matrix mAs) bs) @ (L.map br ~f:Zp.neg)

  let set_x = C.set_x
  let set_y = C.set_y

  let string_of_x = C.string_of_x
  let string_of_y = C.string_of_y
  let x_of_string = C.x_of_string
  let y_of_string = C.y_of_string
end

module Slow_Conjunction_Characterization  (C1 : PredEnc_Characterization) (C2 : PredEnc_Characterization) = struct
    module Neg1 = Negation_Characterization (C1)
    module Neg2 = Negation_Characterization (C2)
    module D = Disjunction_Characterization (Neg1) (Neg2)
    module C = Negation_Characterization (D)

    type x = C.x
    type y = C.y
    let predicate = C.predicate
    let s = C.s
    let r = C.r
    let w = C.w

    let sE_matrix = C.sE_matrix
    let rE_matrix = C.rE_matrix
    let kE_vector = C.kE_vector
    let sD_vector = C.sD_vector
    let rD_vector = C.rD_vector

    let get_witness = C.get_witness
      
    let set_x = C.set_x
    let set_y = C.set_y

    let string_of_x = C.string_of_x
    let string_of_y = C.string_of_y
    let x_of_string = C.x_of_string
    let y_of_string = C.y_of_string
end


module Conjunction_Characterization  (C1 : PredEnc_Characterization) (C2 : PredEnc_Characterization) = struct

  let diag_join m1 m2 =
    join_blocks [[ m1; create_matrix Zp.zero ~m:(L.length m1) ~n:(L.length (L.hd_exn m2))];
                 [ create_matrix Zp.zero ~m:(L.length m2) ~n:(L.length (L.hd_exn m1)); m2 ]];

  type x = C1.x * C2.x
  type y = C1.y * C2.y

  let predicate (x1,x2) (y1,y2) = (C1.predicate x1 y1) && (C2.predicate x2 y2)

  let s = C1.s + C2.s
  let r = C1.r + C2.r
  let w = C1.w + C2.w + 1

  let sE_matrix (x1,x2) =
    let big_block = diag_join (C1.sE_matrix x1) (C2.sE_matrix x2) in 
    join_blocks [ [big_block; create_matrix Zp.zero ~m:(L.length big_block) ~n:1 ]]                
  let rE_matrix (y1,y2) =
    let big_block = diag_join (C1.rE_matrix y1) (C2.rE_matrix y2) in
    let last_col  = transpose_matrix [(C1.kE_vector y1) @ (L.map (C2.kE_vector y2) ~f:Zp.neg)] in
    join_blocks [ [big_block; last_col]]                
  let kE_vector (y1,y2) = (C1.kE_vector y1) @ (C2.kE_vector y2)
  let sD_vector (x1,x2) (y1,y2) =
    let b1 = C1.sD_vector x1 y1 in
    let b2 = C2.sD_vector x2 y2 in
    let half = Zp.inv (Zp.add Zp.one Zp.one) in
    L.map (b1 @ b2) ~f:(Zp.mul half)
  let rD_vector (x1,x2) (y1,y2) =
    let b1 = C1.rD_vector x1 y1 in
    let b2 = C2.rD_vector x2 y2 in
    let half = Zp.inv (Zp.add Zp.one Zp.one) in
    L.map (b1 @ b2) ~f:(Zp.mul half)
          
  let get_witness (x1,x2) (y1,y2) =
    if not (C1.predicate x1 y1) then
      let w1 = C1.get_witness x1 y1 in
      let two = Zp.add Zp.one Zp.one in
      (L.map w1 ~f:(Zp.mul two))  @ (mk_list Zp.zero C2.w) @ [Zp.neg Zp.one]
    else
      let w2 = C2.get_witness x2 y2 in
      let two = Zp.add Zp.one Zp.one in
      (mk_list Zp.zero C1.w) @ (L.map w2 ~f:(Zp.mul two)) @ [Zp.one]

  let set_x = function GenericAttPair(gx1, gx2) -> (C1.set_x gx1, C2.set_x gx2) | _ -> failwith "Pair of Generic Attributes expected"
  let set_y = function GenericAttPair(gy1, gy2) -> (C1.set_y gy1, C2.set_y gy2) | _ -> failwith "Pair of Generic Attributes expected"

  let sep = "!"
  let string_of_x (x1,x2) = (C1.string_of_x x1) ^ sep ^ (C2.string_of_x x2)
  let string_of_y (y1,y2) = (C1.string_of_y y1) ^ sep ^ (C2.string_of_y y2)
  let x_of_string str =
    match S.split str ~on:(Char.of_string sep) with
    | s1 :: s2 :: [] -> (C1.x_of_string s1, C2.x_of_string s2)
    | _ -> failwith "invalid string"
  let y_of_string str =
    match S.split str ~on:(Char.of_string sep) with
    | s1 :: s2 :: [] -> (C1.y_of_string s1, C2.y_of_string s2)
    | _ -> failwith "invalid string"

end
    

module Dual_Characterization (C : PredEnc_Characterization) = struct

  type x = C.y
  type y = C.x

  let predicate x y = C.predicate y x
  
  let s = C.r
  let r = C.s + 1
  let w = C.w + 1

  let sE_matrix x = join_blocks [[ C.rE_matrix x; (L.map (C.kE_vector x) ~f:(fun a -> [a])) ]]
  let rE_matrix y =
    let mAs = C.sE_matrix y in
    join_blocks [[ mAs; L.map (list_range 0 (L.length mAs)) ~f:(fun _ -> [Zp.zero]) ];
                 [ [mk_list Zp.zero (L.length (L.hd_exn mAs))]; [[Zp.one]]  ]]
  let kE_vector y = (mk_list Zp.zero (L.length (C.sE_matrix y))) @ [Zp.one]
  let sD_vector x y = C.rD_vector y x
  let rD_vector x y = (C.sD_vector y x) @ [Zp.one]

  let get_witness x y = (L.map (C.get_witness y x) ~f:Zp.neg) @ [Zp.one]

  let set_x x = C.set_y x
  let set_y y = C.set_x y

  let string_of_x x = C.string_of_y x
  let string_of_y y = C.string_of_x y
  let x_of_string str = C.y_of_string str
  let y_of_string str = C.x_of_string str
end


let make_BF_PredEnc (n : int) =
  
  let module BF_PredEnc (B : BilinearGroup) = struct
      
    (* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)
      
    module GaussElim = LinAlg(Zp)
      
    type x = Zp.t list list
    type y = Zp.t list

    let n = n
      
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
      | BoolForm_Policy (nattrs, rep, and_gates, policy) ->
         pred_enc_matrix_from_policy ~nattrs ~rep ~and_gates ~t_of_int:Zp.from_int policy
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
  in
  (module BF_PredEnc : PredEnc)


let make_BF_PredEnc_Characterization (s : int) (r : int) (w : int) =

  let module Characterization = struct

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

    let s = s
    let r = r
    let w = w
         
    let sE_matrix xM =
      let id_n = identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:(L.length xM) in
      let xM_without_col1 = L.map xM ~f:(fun row -> L.tl_exn row) in
      let xM_col1 = L.map xM ~f:(fun row -> [L.hd_exn row]) in
      join_blocks [[id_n; xM_without_col1; xM_col1]]

    let rE_matrix y =
      let l = L.length y in
      let l' = w - l in
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

    let get_witness xM y =
      let matrix = join_blocks [[sE_matrix xM]; [rE_matrix y]] in
      let b = (mk_list Zp.zero s) @ (kE_vector y) in
      match GaussElim.solve matrix b with
      | None -> mk_list Zp.zero (L.length (L.hd_exn matrix)) (* Decryption failed *)
      | Some w' -> w'

    let set_x = function
      | BoolForm_Policy (nattrs, rep, and_gates, policy) ->
         pred_enc_matrix_from_policy ~nattrs ~rep ~and_gates ~t_of_int:Zp.from_int policy
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
  in
  (module Characterization : PredEnc_Characterization)


let make_ShareRoot_PredEnc_Characterization (s : int) (r : int) =

  let module Characterization = struct

    (* Predicate Encoding Characterization for the predicate P(x,y) defined as
         x(t) and y(t) are share a common factor in Zp[t]
     *)
      
    module M = Matrix.MyGaussElim(Zp)
    module GaussElim = LinAlg(Zp)
                             
    let half_discriminant v n =
      let rec aux output k =
        if k >= n then output
        else
          let new_row = (mk_list Zp.zero k) @ v @ (mk_list Zp.zero (n-k-1)) in
          aux (output @ [new_row]) (k+1)
      in
      aux [] 0
          
    let discriminant_matrix x y =
      (half_discriminant x r) @ (half_discriminant y s)

    type x = Zp.t list
    type y = Zp.t list

    let predicate x y =
      Zp.is_zero (M.determinant (discriminant_matrix x y))

    let s = s
    let r = r
    let w = s + r
         
    let sE_matrix x =
      half_discriminant x r

    let rE_matrix y =
      half_discriminant y s
                        
    let kE_vector _y =
      mk_list Zp.one s
                                  
    let dec_vector x y =
      let mX = half_discriminant x r |> transpose_matrix in
      let mY = L.map (half_discriminant y s) ~f:(L.map ~f:Zp.neg) |> transpose_matrix in
      let m = join_blocks [[mX; mY]; [[mk_list Zp.zero r]; [kE_vector y]]] in
      match GaussElim.solve m ((mk_list Zp.zero (s+r)) @ [Zp.one]) with
      | None -> mk_list Zp.zero (s+r) (* Decryption failed *)
      | Some a -> a

    let sD_vector x y =
      L.slice (dec_vector x y) 0 r

    let rD_vector x y =
      L.slice (dec_vector x y) r (s+r)

    let get_witness x y =
      match  GaussElim.solve (discriminant_matrix x y) ((mk_list Zp.zero (s+r-1)) @ [Zp.one]) with
      | None -> mk_list Zp.zero (s+r) (* Decryption failed *)
      | Some w' -> w'

    let poly_coeffs_from_roots roots =
      let rec aux coeffs = function
        | [] -> coeffs
        | a :: rest_roots ->  (* We multiply by (x-a) *)
           let neg_a = Zp.neg a in
           let first_list  = coeffs @ [Zp.zero] in             (* Multiplication by x  *)
           let second_list = L.map coeffs ~f:(Zp.mul neg_a) in (* Multiplication by -a *)
           let new_coeffs = L.map2_exn first_list (Zp.zero :: second_list) ~f:Zp.add in
           aux new_coeffs rest_roots
      in
      aux [Zp.one; Zp.neg (L.hd_exn roots)] (L.tl_exn roots)
                     
    let set_x = function   (* Reserved root for x is 0 *)
      | Discriminant (_,_,roots) ->
         if (L.length roots) > s then
           failwith ("Too many roots for a polynomial of degree " ^ (string_of_int s))
         else poly_coeffs_from_roots (roots @ (mk_list Zp.zero (s - (L.length roots))))
      | _ -> failwith "wrong input"

    let set_y = function   (* Reserved root for y is 1 *)
      | Discriminant (_,_,roots) ->
         if (L.length roots) > r then
           failwith ("Too many roots for a polynomial of degree " ^ (string_of_int r))
         else poly_coeffs_from_roots (roots @ (mk_list Zp.one (r - (L.length roots))))
      | _ -> failwith "wrong input"

(* *** String converions *)

    let sep = "#"

    let string_of_x x =
      list_to_string ~sep:sep (L.map x ~f:Zp.write_str)

    let string_of_y y =
      list_to_string ~sep:sep (L.map y ~f:Zp.write_str)

    let x_of_string str =
      L.map (S.split ~on:(Char.of_string sep) str) ~f:Zp.read_str
            
    let y_of_string str =
      L.map (S.split ~on:(Char.of_string sep) str) ~f:Zp.read_str
  end
  in
  (module Characterization : PredEnc_Characterization)


let make_InnerProduct_PredEnc (n : int) =
  
  let module ZIP_PredEnc (B : BilinearGroup) = struct
      
    (* Predicate Encoding for Ciphertet-Policy ABE for Zero Inner Product *)
            
    type x = Zp.t list
    type y = Zp.t list

    let n = n+2
      
    let sE x u0_u1_w = 
      let u1 = L.hd_exn (L.tl_exn u0_u1_w) in
      let w  = L.tl_exn (L.tl_exn u0_u1_w) in
      [B.G1.add u1 (vector_times_vector ~add:B.G1.add ~mul:B.G1.mul w x)]

    let rE y u0_u1_w =
      let u0 = L.hd_exn u0_u1_w in
      let u1 = L.hd_exn (L.tl_exn u0_u1_w) in
      let w  = L.tl_exn (L.tl_exn u0_u1_w) in
      (L.map2_exn (L.map y ~f:(B.G2.mul u0)) w ~f:B.G2.add) @ [u1]
        
    let kE y alpha =
      (mk_list B.G2.zero (L.length y)) @ [alpha]
                 
    let sD _x _y c =
      L.hd_exn c
             
    let rD x _y d_d' =
      let d' = L.hd_exn (L.rev d_d') in
      let d  = L.tl_exn (L.rev d_d') |> L.rev in
      B.G2.add (vector_times_vector ~add:B.G2.add ~mul:B.G2.mul d x) d'
             
    let set_x = function
      | InnerProduct (_,x) -> x
      | _ -> failwith "wrong input"
                      
    let set_y = function
      | InnerProduct (_,y) -> y
      | _ -> failwith "wrong input"
                      
  (* *** String converions *)

    let sep = "#"

    let string_of_x x =
      list_to_string ~sep:sep (L.map x ~f:Zp.write_str)

    let string_of_y y =
      list_to_string ~sep:sep (L.map y ~f:Zp.write_str)

    let x_of_string str =
      L.map (S.split ~on:(Char.of_string sep) str) ~f:Zp.read_str

    let y_of_string str =
      L.map (S.split ~on:(Char.of_string sep) str) ~f:Zp.read_str
  end
  in
  (module ZIP_PredEnc : PredEnc)


let make_BroadcastEnc_PredEnc (t1 : int) (t2 : int) =
  
  let module Broadcast_PredEnc (B : BilinearGroup) = struct
      
    (* Predicate Encoding for Ciphertet-Policy ABE for Broadcast Encryption *)
            
    type x = bool list
    type y = int * int
               
    let n = t1 + t2

    let bool_dot_prod ~add ~zero x v =
      L.fold_left (L.zip_exn x v)
       ~init:zero
       ~f:(fun result (xi,vi) -> if xi then add result vi else result)
       
    let sE x w_u =
      let w = L.slice w_u 0 t1 in
      let u = L.slice w_u t1 (t1+t2) in
      let xu = L.map (list_range 0 t1)
                ~f:(fun i -> bool_dot_prod ~add:B.G1.add ~zero:B.G1.zero (L.slice x (i*t2) ((i+1)*t2)) u)
      in
      L.map2_exn xu w ~f:B.G1.add

    let rE (i1,i2) w_u =
      let w = L.slice w_u 0 t1 in
      let u = L.slice w_u t1 (t1+t2) in
      L.map (list_range 0 t2) ~f:(fun i -> if i = i2 then B.G2.add (L.nth_exn u i) (L.nth_exn w i1)
                                           else L.nth_exn u i
                                 )     
        
    let kE (_,i2) alpha =
      L.map (list_range 0 t2) ~f:(fun i -> if i = i2 then alpha else B.G2.zero)
                 
    let sD _x (i1,_) c =
      L.nth_exn c i1
             
    let rD x (i1,_) d =
      bool_dot_prod ~add:B.G2.add ~zero:B.G2.zero (L.slice x (i1*t2) ((i1+1)*t2)) d
             
    let set_x = function
      | BroadcastEncVector (_,_,x) -> x
      | _ -> failwith "wrong input"
                      
    let set_y = function
      | BroadcastEncIndex (_,_,(i1,i2)) -> (i1,i2)
      | _ -> failwith "wrong input"
                      
  (* *** String converions *)

    let sep = "#"

    let string_of_x x =
      list_to_string ~sep:sep (L.map x ~f:(fun b -> if b then "1" else "0"))

    let string_of_y (i1,i2) =
      (string_of_int i1) ^ sep ^ (string_of_int i2)

    let x_of_string str =
      L.map (S.split ~on:(Char.of_string sep) str) ~f:(fun s -> if s = "1" then true else false)

    let y_of_string str =
      match S.split ~on:(Char.of_string sep) str with
      | s1 :: s2 :: [] -> (int_of_string s1), (int_of_string s2)
      | _ -> failwith "wrong input"
  end
  in
  (module Broadcast_PredEnc : PredEnc)
