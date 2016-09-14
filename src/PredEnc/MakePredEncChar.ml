open Abbrevs
open Util
open LinAlg
open Predicates
open BoolForms
open MakeAlgebra
open Matrix
open PredEnc

(* ** Making characterizations of predicate encodings *)

(* *** Monotonic Boolean Formulas *)

(* Predicate Encoding Characterization for Ciphertet-Policy ABE for boolean formulas *)

let make_BF_PredEnc_Characterization (s : int) (r : int) (w : int) =

  let module Characterization = struct

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
  (module Characterization : PredEnc_Characterization)


(* *** Share Root *)

(* Predicate Encoding Characterization for the predicate P(x,y) defined as
       x(t) and y(t) are share a common factor in Zp[t]
 *)

let make_ShareRoot_PredEnc_Characterization (s : int) (r : int) =

  let module Characterization = struct

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
  (module Characterization : PredEnc_Characterization)


(* *** Broadcast Encryption *)

(* Predicate Encoding Characterization for Broadcast Encryption *)

let make_BroadcastEnc_Characterization (t1 : int) (t2 : int) =

  let module Characterization = struct

    type x = bool list
    type y = int * int

    let predicate x (i1,i2) =
      let x_i1 = L.slice x (i1*t2) ((i1+1)*t2) in
      L.nth_exn x_i1 i2

    let x_to_zp x = L.map x ~f:(fun xi -> if xi then Zp.one else Zp.zero)

    let s = t1
    let r = t2
    let w = s + r

    let sE_matrix x =
      let id_s = identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:s in
      let mX = L.map (list_range 0 t1) ~f:(fun i -> L.slice (x_to_zp x) (i*t2) ((i+1)*t2)) in
      join_blocks [[id_s; mX]]

    let rE_matrix (i1,i2) =
      let id_r = identity_matrix ~zero:Zp.zero ~one:Zp.one ~n:r in
      let mY = L.map (list_range 0 t2)
                 ~f:(fun i -> if i = i2 then (mk_list Zp.zero i1) @ [Zp.one] @ (mk_list Zp.zero (t1-i1-1))
                              else mk_list Zp.zero t1
                    )
      in
      join_blocks [[mY; id_r]]

    let kE_vector (_i1,i2) =
      (mk_list Zp.zero i2) @ [Zp.one] @ (mk_list Zp.zero (t2-i2-1))

    let sD_vector _x (i1,_i2) =
      (mk_list Zp.zero i1) @ [Zp.one] @ (mk_list Zp.zero (t1-i1-1))

    let rD_vector x (i1,_i2) =
      L.slice x (i1*t2) ((i1+1)*t2) |> x_to_zp

    let get_witness x (_i1,i2) =
      let e_i2 = (mk_list Zp.zero i2) @ [Zp.one] @ (mk_list Zp.zero (t2-i2-1)) in
      (L.map (list_range 0 t1) ~f:(fun i -> if (L.nth_exn x (i*t2+i2)) then Zp.neg Zp.one else Zp.zero)) @ e_i2

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
  (module Characterization : PredEnc_Characterization)
