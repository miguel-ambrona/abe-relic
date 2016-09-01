open Abbrevs
open Util
open LinAlg
open AlgStructures
open MakeAlgebra
open Matrix
open Predicates
open PredEnc

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
