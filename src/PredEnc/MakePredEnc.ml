open Abbrevs
open Util
open AlgStructures
open LinAlg
open Predicates
open BoolForms
open MakeAlgebra
open Matrix
open PredEnc
open ArithmeticSpanProgram
open NonMonotonicBF


(* ** Making Predicate Encodings *)

(* *** Monotonic Boolean Formulas *)

(* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)

let dec_vector_bf = ref None

let make_BF_PredEnc (n : int) =

  let module BF_PredEnc (B : BilinearGroup) = struct

    module GaussElim = LinAlg(Zp)

    type x = Zp.t list list
    type y = Zp.t list

    let n = n

    let sE xM w_u_u0 =
      dec_vector_bf := None;
      let ( +! ) = L.map2_exn ~f:B.G1.add in
      let l = L.length xM in
      let l' = L.length (L.hd_exn xM) in
      let w = L.slice w_u_u0 0 l in
      let u = L.slice w_u_u0 l (l+l'-1) in
      let u0 = L.hd_exn (L.tl_exn w_u_u0) in
      w +! (matrix_times_vector ~add:B.G1.add ~mul:(fun exp g -> B.G1.mul g exp) xM (u0 :: u))

    let rE y w_u_u0 =
      dec_vector_bf := None;
      let l = L.length y in
      let w = L.slice w_u_u0 0 l in
      let u0 = L.hd_exn (L.tl_exn w_u_u0) in
      u0 :: (L.map2_exn ~f:B.G2.mul w y)

    let kE y alpha =
      dec_vector_bf := None;
      alpha :: (mk_list B.G2.zero (L.length y))

    let sD xM y c =
      let l' = L.length (L.hd_exn xM) in
      let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
      if filtered = [] then B.G1.zero (* No attributes in the key *)
      else
        let matrix = transpose_matrix filtered in
        match !dec_vector_bf with
        | None ->
           begin match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
           | None -> B.G1.zero (* Decryption failed *)
           | Some a ->
              dec_vector_bf := Some a;
              let y_c = L.filter (L.zip_exn c y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
              let a_y_c = L.map2_exn ~f:B.G1.mul y_c a in
              L.fold_left (L.tl_exn a_y_c)
                          ~init:(L.hd_exn a_y_c)
                          ~f:B.G1.add
           end
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
        match !dec_vector_bf with
        | None ->
           begin match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
           | None -> B.G2.zero (* Decryption failed *)
           | Some a ->
              dec_vector_bf := Some a;
              let d' = L.hd_exn d_d' in
              let d = L.tl_exn d_d' in
              let d = L.filter (L.zip_exn d y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
              let a_d = L.map2_exn ~f:B.G2.mul d a in
              B.G2.add
                d'
                (L.fold_left (L.tl_exn a_d)
                             ~init:(L.hd_exn a_d)
                             ~f:B.G2.add)
           end
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


    (* String converions *)

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


(* *** Fast Monotonic Boolean Formulas *)

(* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)

let dec_vector = ref None

let make_Fast_BF_PredEnc (n : int) =

  let module BF_PredEnc (B : BilinearGroup) = struct

    module GaussElim = LinAlg(Zp)

    type x = Zp.t list list
    type y = Zp.t list

    let n = n+1

    let get_a xM y =
      match !dec_vector with
      | None ->
         let y_minus_one = diagonal_matrix ~zero:Zp.zero (L.map y ~f:(fun yi -> Zp.add yi (Zp.neg Zp.one))) in
         let n_zeros = [mk_list Zp.zero (L.length y)] in
         let block1 = join_blocks [ [ n_zeros; [[Zp.neg Zp.one]] ];
                                    [ y_minus_one; transpose_matrix n_zeros ];
                                    [ n_zeros; [[Zp.one]] ]
                                  ]
         in
         let one_zeros = [Zp.one :: (mk_list Zp.zero ((L.length (L.hd_exn xM))-1))] in
         let block2 = join_blocks [ [ one_zeros ];
                                    [ xM ];
                                    [ [mk_list Zp.zero (L.length (L.hd_exn xM))] ]
                                  ]
         in
         let matrix = join_blocks [ [block2 ; block1] ] in
         begin match GaussElim.solve matrix ((mk_list Zp.zero ((L.length matrix)-1)) @ [Zp.one]) with
         | None -> mk_list Zp.zero (L.length (L.hd_exn matrix)) (* Decryption failed *)
         | Some a ->
            dec_vector := Some a;
            a
         end
      | Some a -> a

    let sE xM w0_w =
      dec_vector := None;
      let xMw = matrix_times_vector ~add:B.G1.add ~mul:(fun exp g -> B.G1.mul g exp) (transpose_matrix xM) (L.tl_exn w0_w) in
      (B.G1.add (L.hd_exn w0_w) (L.hd_exn xMw)) :: (L.tl_exn xMw)

    let rE y w0_w =
      dec_vector := None;
      let one_minus_y = L.map y ~f:(fun yi -> Zp.add Zp.one (Zp.neg yi)) in
      (L.map2_exn ~f:B.G2.mul (L.tl_exn w0_w) one_minus_y) @ [L.hd_exn w0_w]

    let kE y alpha =
      dec_vector := None;
      (mk_list B.G2.zero (L.length y)) @ [alpha]

    let sD xM y c =
      let a = get_a xM y in
      vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c (L.slice a 0 ((L.length a)-(L.length y)-1))

    let rD xM y d =
      let a = get_a xM y in
      vector_times_vector ~add:B.G2.add ~mul:B.G2.mul d (L.slice a ((L.length a)-(L.length y)-1) (L.length a))

    let set_x = function
      | BoolForm_Policy (nattrs, rep, and_gates, policy) ->
         pred_enc_matrix_from_policy ~nattrs ~rep ~and_gates ~t_of_int:Zp.from_int policy
      | _ -> failwith "wrong input"

    let set_y = function
      | BoolForm_Attrs (nattrs, rep, attrs) ->
         pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs ~rep (L.map attrs ~f:(fun a -> Leaf(a)))
      | _ -> failwith "wrong input"


    (* String converions *)

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


(* *** Zero Inner Product *)

(* Predicate Encoding for Ciphertet-Policy ABE for Zero Inner Product *)

let make_InnerProduct_PredEnc (n : int) =

  let module ZIP_PredEnc (B : BilinearGroup) = struct

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

    (* String converions *)

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


(* *** Broadcast Encryption *)

(* Predicate Encoding for Ciphertet-Policy ABE for Broadcast Encryption *)

let make_BroadcastEnc_PredEnc (t1 : int) (t2 : int) =

  let module Broadcast_PredEnc (B : BilinearGroup) = struct

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

    (* String converions *)

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


(* *** Arithmetic Span Programs *)

(* Predicate Encoding for Arithmetic Span Programs *)

let make_ArithmeticSpanProgram_PredEnc (n_x : int) (rep : int) =

  let module ArithmeticSpanProgram_PredEnc (B : BilinearGroup) = struct

    module GaussElim = LinAlg(Zp)

    type x = Zp.t list
    type y = (Zp.t list list) * (Zp.t list list)

    let l = n_x * rep
    let l' = l
    let n = 2*l + (l'- 1)

    let computed = ref None

    let sE x w_v_u =
      computed := None;
      let ( +! ) = L.map2_exn ~f:B.G1.add in
      let w = L.slice w_v_u 0 l in
      let v = L.slice w_v_u l (2*l) in
      v +! (L.map2_exn ~f:B.G1.mul w x)

    let rE (y,z) w_v_u =
      computed := None;
      let ( +! ) = L.map2_exn ~f:B.G2.add in
      let w = L.slice w_v_u 0 l in
      let v = L.slice w_v_u l (2*l) in
      let u = L.slice w_v_u (2*l) (2*l+l'-1) in
      let y' = L.map y ~f:(fun row -> L.rev (L.tl_exn (L.rev row))) in
      let z' = L.map z ~f:(fun row -> L.rev (L.tl_exn (L.rev row))) in
      (w +! (matrix_times_vector ~add:B.G2.add ~mul:(fun exp g -> B.G2.mul g exp) y' u)) @
        (v +! (matrix_times_vector ~add:B.G2.add ~mul:(fun exp g -> B.G2.mul g exp) z' u))

    let kE (y,z) alpha =
      computed := None;
      (L.map y ~f:(fun row -> let last = L.hd_exn (L.rev row) in B.G2.mul alpha last)) @
        (L.map z ~f:(fun row -> let last = L.hd_exn (L.rev row) in B.G2.mul alpha last))

    let sD x (y,z) c =
      computed := None;
      let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
      let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
      let l = L.length (L.hd_exn xy_z) in
      let matrix = transpose_matrix xy_z in
      match !computed with
      | None ->
         begin match GaussElim.solve matrix ((mk_list Zp.zero (l-1)) @ [Zp.one]) with
         | None -> B.G1.zero (* Decryption failed *)
         | Some a ->
            computed := Some a;
            vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c a
         end
      | Some a ->
         vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c a

    let rD x (y,z) d =
      let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
      let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
      let l = L.length (L.hd_exn xy_z) in
      let matrix = transpose_matrix xy_z in
      match !computed with
      | None ->
         begin match GaussElim.solve matrix ((mk_list Zp.zero (l-1)) @ [Zp.one]) with
         | None -> B.G2.zero (* Decryption failed *)
         | Some a ->
            computed := Some a;
            let (d,d') = L.split_n d ((L.length d) / 2) in
            let xd = L.map2_exn x d ~f:(fun x_el d_el -> B.G2.mul d_el x_el) in
            let xd_d' = L.map2_exn xd d' ~f:B.G2.add in
            vector_times_vector ~add:B.G2.add ~mul:B.G2.mul xd_d' a
         end
      | Some a ->
         let (d,d') = L.split_n d ((L.length d) / 2) in
         let xd = L.map2_exn x d ~f:(fun x_el d_el -> B.G2.mul d_el x_el) in
         let xd_d' = L.map2_exn xd d' ~f:B.G2.add in
         vector_times_vector ~add:B.G2.add ~mul:B.G2.mul xd_d' a

    let set_x = function
      | BoolForm_Attrs (nattrs, rep', attrs) ->
         assert (rep = rep');
         pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs ~rep (L.map attrs ~f:(fun a -> Leaf(a)))
      | _ -> failwith "wrong input"

    let set_y = function
      | NonMonBoolForm (rep', formula) ->
         assert (rep = rep');
         let f row = (mk_list Zp.zero (n_x*rep-(L.length row))) @ row in
         let afn = af_to_af_normal_form (non_monotonic_bf_to_arithmetic_formula formula) in
         let asp = create_asp_from_formula afn n_x rep ~equality:false in
         (L.map asp.asp_yj ~f, L.map asp.asp_zj ~f)
      | _ -> failwith "wrong input"


    (* String converions *)

    let sep1 = "#"
    let sep2 = ";"

    let string_of_y (y,z) =
      list_list_to_string ~sep1 ~sep2 (L.map (y @ z) ~f:(L.map ~f:Zp.write_str))

    let string_of_x x =
      list_to_string ~sep:sep2 (L.map x ~f:Zp.write_str)

    let y_of_string str =
      let yz = L.map (S.split ~on:(Char.of_string sep1) str)
        ~f:(fun row -> L.map (S.split ~on:(Char.of_string sep2) row) ~f:Zp.read_str)
      in
      L.split_n yz ((L.length yz) / 2)

    let x_of_string str =
      L.map (S.split ~on:(Char.of_string sep2) str) ~f:Zp.read_str
  end
  in
  (module ArithmeticSpanProgram_PredEnc : PredEnc)


(* *** Fast Arithmetic Span Programs *)

(* Predicate Encoding for Arithmetic Span Programs *)

let computed_fast = ref None

let make_Fast_ArithmeticSpanProgram_PredEnc (n_x : int) (rep : int) =

  let module ArithmeticSpanProgram_PredEnc (B : BilinearGroup) = struct

    module GaussElim = LinAlg(Zp)

    type x = Zp.t list
    type y = (Zp.t list list) * (Zp.t list list)

    let l = n_x*rep
    let l' = l
    let n = 2*l

    let sE x w_v =
      computed_fast := None;
      let ( +! ) = L.map2_exn ~f:B.G1.add in
      let w = L.slice w_v 0 l in
      let v = L.slice w_v l (2*l) in
      (L.map v ~f:B.G1.neg) +! (L.map2_exn ~f:B.G1.mul w x)

    let rE (y,z) w_v =
      computed_fast := None;
      let ( +! ) = L.map2_exn ~f:B.G2.add in
      let w = L.slice w_v 0 l in
      let v = L.slice w_v l (2*l) in
      let mul exp g = B.G2.mul g exp in
      let wz = matrix_times_vector ~add:B.G2.add ~mul (transpose_matrix z) w in
      let vy = matrix_times_vector ~add:B.G2.add ~mul (transpose_matrix y) v in
      wz +! vy

    let kE _ alpha =
      computed_fast := None;
      (mk_list B.G2.zero (l'-1)) @ [alpha]

    let sD x (y,z) c =
      match !computed_fast with
      | None ->
         let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
         let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
         let l = L.length (L.hd_exn xy_z) in
         let matrix = xy_z @ [(mk_list Zp.zero (l'-1)) @ [Zp.one]] in
         begin match GaussElim.solve matrix ((mk_list Zp.zero l) @ [Zp.one]) with
         | None -> B.G1.zero (* Decryption failed *)
         | Some a ->
            computed_fast := Some a;
            let b = L.map ~f:Zp.neg (matrix_times_vector ~add:Zp.add ~mul:Zp.mul y a) in
            vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c b
         end
      | Some a ->
         let b = L.map ~f:Zp.neg (matrix_times_vector ~add:Zp.add ~mul:Zp.mul y a) in
         vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c b

    let rD x (y,z) d =
      match !computed_fast with
      | None ->
         let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
         let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
         let l = L.length (L.hd_exn xy_z) in
         let matrix = xy_z @ [(mk_list Zp.zero (l'-1)) @ [Zp.one]] in
         begin match GaussElim.solve matrix ((mk_list Zp.zero l) @ [Zp.one]) with
         | None -> B.G2.zero (* Decryption failed *)
         | Some a ->
            computed_fast := Some a;
            vector_times_vector ~add:B.G2.add ~mul:B.G2.mul d a
         end
      | Some a ->
         vector_times_vector ~add:B.G2.add ~mul:B.G2.mul d a

    let set_x = function
      | BoolForm_Attrs (nattrs, rep', attrs) ->
         assert (rep = rep');
         pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs ~rep (L.map attrs ~f:(fun a -> Leaf(a)))
      | _ -> failwith "wrong input"

    let set_y = function
      | NonMonBoolForm (rep', formula) ->
         assert (rep = rep');
         let f row = (mk_list Zp.zero (n_x*rep-(L.length row))) @ row in
         let afn = af_to_af_normal_form (non_monotonic_bf_to_arithmetic_formula formula) in
         let asp = create_asp_from_formula afn n_x rep ~equality:true in
         (L.map asp.asp_yj ~f, L.map asp.asp_zj ~f)
      | _ -> failwith "wrong input"


    (* String converions *)

    let sep1 = "#"
    let sep2 = ";"

    let string_of_y (y,z) =
      list_list_to_string ~sep1 ~sep2 (L.map (y @ z) ~f:(L.map ~f:Zp.write_str))

    let string_of_x x =
      list_to_string ~sep:sep2 (L.map x ~f:Zp.write_str)

    let y_of_string str =
      let yz = L.map (S.split ~on:(Char.of_string sep1) str)
        ~f:(fun row -> L.map (S.split ~on:(Char.of_string sep2) row) ~f:Zp.read_str)
      in
      L.split_n yz ((L.length yz) / 2)

    let x_of_string str =
      L.map (S.split ~on:(Char.of_string sep2) str) ~f:Zp.read_str
  end
  in
  (module ArithmeticSpanProgram_PredEnc : PredEnc)
