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


let make_ArithmeticSpanProgram_PredEnc (n_x : int) (rep : int) =

  let module ArithmeticSpanProgram_PredEnc (B : BilinearGroup) = struct

    (* Predicate Encoding for Arithmetic Span Programs *)

    module GaussElim = LinAlg(Zp)

    type x = Zp.t list
    type y = (Zp.t list list) * (Zp.t list list)

    let l = n_x * rep
    let l' = l
    let n = 2*l + (l'- 1)

    let sE x w_v_u =
      let ( +! ) = L.map2_exn ~f:B.G1.add in
      let w = L.slice w_v_u 0 l in
      let v = L.slice w_v_u l (2*l) in
      v +! (L.map2_exn ~f:B.G1.mul w x)

    let rE (y,z) w_v_u =
      let ( +! ) = L.map2_exn ~f:B.G2.add in
      let w = L.slice w_v_u 0 l in
      let v = L.slice w_v_u l (2*l) in
      let u = L.slice w_v_u (2*l) (2*l+l'-1) in
      let y' = L.map y ~f:(fun row -> L.rev (L.tl_exn (L.rev row))) in
      let z' = L.map z ~f:(fun row -> L.rev (L.tl_exn (L.rev row))) in
      (w +! (matrix_times_vector ~add:B.G2.add ~mul:(fun exp g -> B.G2.mul g exp) y' u)) @
        (v +! (matrix_times_vector ~add:B.G2.add ~mul:(fun exp g -> B.G2.mul g exp) z' u))

    let kE (y,z) alpha =
      (L.map y ~f:(fun row -> let last = L.hd_exn (L.rev row) in B.G2.mul alpha last)) @
        (L.map z ~f:(fun row -> let last = L.hd_exn (L.rev row) in B.G2.mul alpha last))

    let sD x (y,z) c =
      let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
      let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
      let l = L.length (L.hd_exn xy_z) in
      let matrix = transpose_matrix xy_z in
      match GaussElim.solve matrix ((mk_list Zp.zero (l-1)) @ [Zp.one]) with
      | None -> B.G1.zero (* Decryption failed *)
      | Some a ->
         vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c a

    let rD x (y,z) d =
      let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
      let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
      let l = L.length (L.hd_exn xy_z) in
      let matrix = transpose_matrix xy_z in
      match GaussElim.solve matrix ((mk_list Zp.zero (l-1)) @ [Zp.one]) with
      | None -> B.G2.zero (* Decryption failed *)
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


  (* *** String converions *)

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



let make_Fast_ArithmeticSpanProgram_PredEnc (n_x : int) (rep : int) =

  let module ArithmeticSpanProgram_PredEnc (B : BilinearGroup) = struct

    (* Predicate Encoding for Arithmetic Span Programs *)

    module GaussElim = LinAlg(Zp)

    type x = Zp.t list
    type y = (Zp.t list list) * (Zp.t list list)

    let l = n_x*rep
    let l' = l
    let n = 2*l

    let sE x w_v_u =
      let ( +! ) = L.map2_exn ~f:B.G1.add in
      let w = L.slice w_v_u 0 l in
      let v = L.slice w_v_u l (2*l) in
      (L.map v ~f:B.G1.neg) +! (L.map2_exn ~f:B.G1.mul w x)

    let rE (y,z) w_v_u =
      let ( +! ) = L.map2_exn ~f:B.G2.add in
      let w = L.slice w_v_u 0 l in
      let v = L.slice w_v_u l (2*l) in
      let mul exp g = B.G2.mul g exp in
      let wz = matrix_times_vector ~add:B.G2.add ~mul (transpose_matrix z) w in
      let vy = matrix_times_vector ~add:B.G2.add ~mul (transpose_matrix y) v in
      wz +! vy

    let kE _ alpha =
      (mk_list B.G2.zero (l'-1)) @ [alpha]

    let sD x (y,z) c =
      let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
      let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
      let l = L.length (L.hd_exn xy_z) in
      let matrix = xy_z @ [(mk_list Zp.zero (l'-1)) @ [Zp.one]] in
      match GaussElim.solve matrix ((mk_list Zp.zero l) @ [Zp.one]) with
      | None -> B.G1.zero (* Decryption failed *)
      | Some a ->
         let b = L.map ~f:Zp.neg (matrix_times_vector ~add:Zp.add ~mul:Zp.mul y a) in
         vector_times_vector ~add:B.G1.add ~mul:B.G1.mul c b

    let rD x (y,z) d =
      let xy = L.map2_exn x y ~f:(fun x_el yj -> L.map yj ~f:(fun y_el -> Zp.mul x_el y_el)) in
      let xy_z = L.map2_exn xy z ~f:(fun xyj zj -> L.map2_exn ~f:Zp.add xyj zj) in
      let l = L.length (L.hd_exn xy_z) in
      let matrix = xy_z @ [(mk_list Zp.zero (l'-1)) @ [Zp.one]] in
      match GaussElim.solve matrix ((mk_list Zp.zero l) @ [Zp.one]) with
      | None -> B.G2.zero (* Decryption failed *)
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


  (* *** String converions *)

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
