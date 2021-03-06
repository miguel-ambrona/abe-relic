open Abbrevs
open LinAlg
open Util
open Matrix
open MakeAlgebra
open BoolForms
open Predicates
open PairEnc

(* ** Making Pair Encodings *)

(* *** Monotonic Boolean Formulas *)

let make_BF_PairEnc max_leaf_nodes and_gates n_attributes =

  let module BF_PairEnc = struct

      module Par = struct
        let par_n1 = max_leaf_nodes
        let par_n2 = and_gates+1
        let par_T  = n_attributes
      end

      module P = Zp_Poly
      module GaussElim = LinAlg(Zp)

      type x = (Zp.t list list) * (int -> Zp.t)
      type y = Zp.t list
      let to_mon = P.monom_of_monomPoly

      let mk_s = P.var "s"
      let mk_r i = P.var (F.sprintf "r_%d" i)
      let mk_v j = P.var (F.sprintf "v_%d" j)
      let mk_b i j = P.var (F.sprintf "b_{%d,%d}" i j)
      let mk_b' i t = P.var (F.sprintf "b'_{%d,%d}" i t)

      let monom_s = mk_s |> to_mon
      let monom_si = []
      let monom_alpha = mk_v 1 |> to_mon
      let monom_ri =
        (L.map (list_range 1 (Par.par_n1+1)) ~f:(fun i -> mk_r i |> to_mon)) @
          (L.map (list_range 2 (Par.par_n2+1)) ~f:(fun i -> mk_v i |> to_mon))
      let monom_bi =
        (L.map (list_range 1 (Par.par_n1+1))
               ~f:(fun i -> L.map (list_range 1 (Par.par_n2+1))
                                  ~f:(fun j -> mk_b i j |> to_mon)
                  )
         |> L.concat
        )
        @
          (L.map (list_range 1 (Par.par_n1+1))
                 ~f:(fun i -> L.map (list_range 0 (Par.par_T+1))
                                    ~f:(fun t -> mk_b' i t |> to_mon)
                    )
           |> L.concat
          )

      (* Pair Encoding for Ciphertext-Policy ABE for boolean formulas *)

      let param =
        Par.par_n1 * (Par.par_n2 + Par.par_T + 1)

      let encC (mA, pi) =
        let c1 = P.(var "s") in

        let rec aux p i j =
          if i > Par.par_n1 then p
          else
            if j > Par.par_n2 then aux p (i+1) 1
            else
              let a = P.(const (L.nth_exn (L.nth_exn mA (i-1)) (j-1))) in
              aux P.(p +@ (a *@ (mk_b i j))) i (j+1)
        in
        let rec aux' p i t =
          if i > Par.par_n1 then p
          else
            if t > Par.par_T then aux' p (i+1) 0
            else
              let a = P.(ring_exp (const (pi i)) t) in
              aux' P.(p +@ (a *@ (mk_b' i t))) i (t+1)
        in
        let c2 = P.((var "s") *@ ((aux zero 1 1) +@ (aux' zero 1 0))) in

        [c1; c2], 0 (* w2 = 0 *)


      let encK setS =
        let k1 = L.map (list_range 1 (Par.par_n1+1)) ~f:(fun i -> mk_r i) in
        let k2 =
          L.map (list_range 1 (Par.par_n1+1))
                ~f:(fun i ->
                  L.map (list_range 1 (Par.par_n2+1))
                        ~f:(fun j -> P.(((mk_r i) *@ (mk_b i j)) -@ (mk_v j)))
                )
          |> L.concat
        in
        let k3 =
          L.map (list_range 1 (Par.par_n1+1))
                ~f:(fun i ->
                  L.map (L.filter (list_range 1 (Par.par_n1+1)) ~f:(fun l -> not (i = l)))
                        ~f:(fun l ->
                          L.map (list_range 1 (Par.par_n2+1))
                                ~f:(fun j -> P.((mk_r i) *@ (mk_b l j)))
                        )
                  |> L.concat
                )
          |> L.concat
        in
        let k4 =
          L.map (list_range 1 (Par.par_n1+1))
                ~f:(fun i ->
                  L.map setS
                        ~f:(fun y ->
                          let sum = L.fold_left (list_range 0 (Par.par_T+1)) ~init:P.zero
                                                ~f:(fun p' t -> P.(p' +@ ((ring_exp (const y) t)  *@  (mk_b' i t)) )) in
                          P.((mk_r i) *@ sum)
                        )
                )
          |> L.concat
        in
        let k5 =
          L.map (list_range 1 (Par.par_n1+1))
                ~f:(fun i ->
                  L.map (L.filter (list_range 1 (Par.par_n1+1)) ~f:(fun l -> not (i = l)))
                        ~f:(fun l ->
                          L.map (list_range 0 (Par.par_T+1))
                                ~f:(fun t -> P.((mk_r i) *@ (mk_b' l t)))
                        )
                  |> L.concat
                )
          |> L.concat
        in

        k1 @ k2 @ k3 @ k4 @ k5, (Par.par_n1 + Par.par_n2 - 1)


(*      let genericPair (mA,pi) setS =
        let c, _ = encC (mA,pi) in
        let k, _ = encK setS in

        let module Alg = PolyAlg.PolyAlg (P) in
        let target = P.((mk_v 1) *@ mk_s) in

        let f monoms2 m1 = L.map monoms2 ~f:(fun m2 -> P.((from_mon m1) *@ (from_mon m2)) |> to_mon) in
        let ribj = L.map monom_ri ~f:(f monom_bi) |> L.concat in
        let sibj = L.map monom_si ~f:(f monom_bi) |> L.concat in
        let sbj = L.map monom_bi ~f:(fun m -> P.(mk_s *@ (from_mon m)) |> to_mon) in

        let ri_bj_s_bk = L.map ribj ~f:(f sbj) |> L.concat in
        let ri_bj_sk_bl = L.map ribj ~f:(f sibj) |> L.concat in
        let forbidden = ri_bj_s_bk @ ri_bj_sk_bl in

        let requirement p = list_empty_intersection ~equal:P.mon_equal (P.mons p) forbidden in

        try Some (Alg.find_matrix ~requirement k c target) with
        | Not_found -> None
 *)

      let ad_hocPair (mA,pi) setS =
        let cols = L.length (L.hd_exn mA) in
        let upsilon = L.filter (list_range 0 (L.length mA)) ~f:(fun i -> L.mem setS (pi (i+1)) ~equal:Zp.equal ) |> L.map ~f:Zp.from_int in
        let filtered = L.filter (L.zip_exn mA (list_range 0 (L.length mA))) ~f:(fun (_,i) -> L.mem upsilon (Zp.from_int i) ~equal:Zp.equal) |> unzip1 in
        if filtered = [] then None (* No relevant attributes in the key *)
        else
          let matrix = transpose_matrix filtered in
          match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (cols-1))) with
          | None -> None (* Decryption failed *)
          | Some epsilon ->

             let rec set_epsilon output epsilon i k =
               if i = k then output
               else
                 if L.mem upsilon (Zp.from_int i) ~equal:Zp.equal then set_epsilon (output @ [L.hd_exn epsilon]) (L.tl_exn epsilon) (i+1) k
                 else set_epsilon (output @ [Zp.zero]) epsilon (i+1) k
             in
             let epsilon = set_epsilon [] epsilon 0 (L.length mA) in

             let col1_k1 = mk_list Zp.zero (Par.par_n1) in
             let col1_k2 =
               L.map (list_range 1 (Par.par_n1+1))
                     ~f:(fun i ->
                       L.map (list_range 1 (Par.par_n2+1))
                             ~f:(fun j -> Zp.(mul (L.nth_exn epsilon (i-1)) ((L.nth_exn (L.nth_exn mA (i-1)) (j-1)))))
                     )
               |> L.concat
             in
             let col1_k3 =
               L.map (list_range 1 (Par.par_n1+1))
                     ~f:(fun i ->
                       L.map (L.filter (list_range 1 (Par.par_n1+1)) ~f:(fun l -> not (i = l)))
                             ~f:(fun l ->
                               L.map (list_range 1 (Par.par_n2+1))
                                     ~f:(fun j -> Zp.(mul (L.nth_exn epsilon (i-1)) ((L.nth_exn (L.nth_exn mA (l-1)) (j-1)))))
                             )
                       |> L.concat
                     )
               |> L.concat
             in
             let col1_k4 =
               L.map (list_range 1 (Par.par_n1+1))
                     ~f:(fun i ->
                       L.map setS
                             ~f:(fun y -> if Zp.equal y (pi i) then L.nth_exn epsilon (i-1) else Zp.zero)
                     )
               |> L.concat
             in
             let col1_k5 =
               L.map (list_range 1 (Par.par_n1+1))
                     ~f:(fun i ->
                       L.map (L.filter (list_range 1 (Par.par_n1+1)) ~f:(fun l -> not (i = l)))
                             ~f:(fun l ->
                               L.map (list_range 0 (Par.par_T+1))
                                     ~f:(fun t -> Zp.(mul (L.nth_exn epsilon (i-1)) (ring_exp (pi l) t) ))
                             )
                       |> L.concat
                     )
               |> L.concat
             in
             let monom_one = L.hd_exn (P.mons P.one) in
             let f x = let t = P.const x in P.(coeff_in_field t monom_one) in
             let col1 = L.map (col1_k1 @ col1_k2 @ col1_k3 @ col1_k4 @ col1_k5) ~f:Zp.(mul (neg one)) in
             let col2 = epsilon @ (mk_list Zp.zero ((L.length col1) - (L.length epsilon))) in
             Some (transpose_matrix [L.map col1 ~f; L.map col2 ~f])

      let pair (mA,pi) setS =
        (*
    let c, _ = encC (mA,pi) in
    let k, _ = encK setS in
    let mE = ad_hocPair (mA,pi) setS in
    let () =
      match mE with
      | Some matrix ->
         let matrix = L.map matrix ~f:(L.map ~f:(fun x -> P.(const (coeff_to_field x) ) )) in
         let v = matrix_times_vector ~add:P.add ~mul:P.mult matrix c in
         let p = vector_times_vector ~add:P.add ~mul:P.mult k v in
         F.printf "%a\n" P.pp p;
         ()
      | None -> ()
    in
         *)
        ad_hocPair (mA,pi) setS

      let set_x = function
        | BoolForm_Policy (n1, n2, _, policy) ->
           pair_enc_matrix_of_policy ~n1 ~n2 ~t_of_int:Zp.from_int policy
        | _ -> failwith "wrong input"

      let set_y = function
        | BoolForm_Attrs (_, _, attrs) ->
           pair_enc_set_attributes ~t_of_int:Zp.from_int (L.map attrs ~f:(fun a -> Leaf(a)))
        | _ -> failwith "wrong input"


      (* *** String converions *)

      let sep1 = "#"
      let sep2 = ";"

      let string_of_x x =
        let matrix, pi = x in
        (list_to_string ~sep:sep2 (L.map (Util.list_range 1 (Par.par_n1+1)) ~f:(fun i -> Zp.write_str (pi i))))
        ^ sep1 ^ (list_list_to_string ~sep1 ~sep2 (L.map matrix ~f:(L.map ~f:Zp.write_str)))

      let string_of_y y =
        list_to_string ~sep:sep2 (L.map y ~f:Zp.write_str)

      let x_of_string str =
        let list = S.split ~on:(Char.of_string sep1) str in
        let pi_list = S.split ~on:(Char.of_string sep2) (L.hd_exn list) in
        let pi i = L.nth_exn (L.map pi_list ~f:Zp.read_str) (i-1) in
        let matrix = L.map (L.tl_exn list) ~f:(fun row -> L.map (S.split ~on:(Char.of_string sep2) row) ~f:Zp.read_str) in
        matrix, pi

      let y_of_string str =
        L.map (S.split ~on:(Char.of_string sep2) str) ~f:Zp.read_str

  end
  in
  (module BF_PairEnc : PairEnc)
