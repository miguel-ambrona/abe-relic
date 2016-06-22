open Poly
open Core_kernel.Std
open Abbrevs
open Util
open Zp
open DualSystemGroup_Interface
open DualSystemGroup
open BoolForms
open PredicateEncodings

(* * ABE described in Improved Dual System ABE in Prime-Order Groups via Predicate Encodings *)

(* ** Attribute-Based Encryption *)
  
module PredEncABE (DSG: DualSystemGroup) (PE : PredEnc) = struct
    
  let setup n =
    let pp, _sp = DSG.sampP n in (* _sp is only used in the proof of security *)
    let (g1_A, _, _, _) = pp in
    let msk = sample_list ~f:R.g2_rand (DSG.k+1) in
    let mu_msk = matrix_times_vector ~add:R.gt_mul ~mul:R.e_pairing (transpose_matrix g1_A) msk in
    (pp, mu_msk), msk
      
  let enc mpk x m =
    let (pp, mu_msk) = mpk in
    let s_list = sample_list ~f:samp_zp DSG.k in
    let g_list = DSG.sampG ~randomness:(Some s_list) pp in
    let g'T = DSG.sampGT ~randomness:(Some s_list) mu_msk in
    let c0 = L.hd_exn g_list in
    let c1 = PE.sE x (L.tl_exn g_list) in
    let c' = R.gt_mul g'T m in
    (c0, c1, c'), x
  
  let keyGen mpk msk y =
    let (pp, _mu_msk) = mpk in
    let h_list = DSG.sampH pp in
    let k0 = L.hd_exn h_list in
    let k1 = L.map2_exn (PE.kE y msk) (PE.rE y (L.tl_exn h_list)) ~f:(L.map2_exn ~f:R.g2_add) in
    (k0, k1), y
  
  let dec _mpk sk_y ct_x =
    let (c0, c1, c'), x = ct_x in
    let (k0, k1), y = sk_y in
    let e_g0_msk = R.gt_mul (DSG.dual_system_pairing c0 (PE.rD x y k1)) (R.gt_inv (DSG.dual_system_pairing (PE.sD x y c1) k0)) in
    R.gt_mul c' (R.gt_inv e_g0_msk)        

end

(* ** Pair Encodings *)

module type PairEnc_Par = sig
  val par_n1 : int
  val par_n2 : int
  val par_T :  int
end

module MyField = struct
  type t = R.bn
  let pp fmt i = F.fprintf fmt "%s" (R.bn_write_str i ~radix:10)
  let add = bn_add_mod
  let neg = bn_neg_mod
  let mul = bn_mul_mod
  let inv = zp_inverse
  let one  = R.bn_one ()
  let zero = R.bn_zero ()
  let is_zero = bn_is_zero_mod
  let rec ring_exp m n =
    if n > 0 then mul m (ring_exp m (n-1))
    else if n = 0 then one
    else failwith "Negative exponent"
  let ladd cs = L.fold_left ~f:(fun acc c -> add c acc) ~init:zero cs
  let from_int i = R.bn_read_str (string_of_int i) ~radix:10
  let equal = R.bn_equal
  let compare = R.bn_cmp
  let use_parens = false
end

module P = MakePoly(
  struct
    type t = string
    let pp = pp_string
    let equal = (=)
    let compare = compare
  end) (MyField)

let monom_of_monomP p = L.hd_exn (P.mons p)

module Pair_Encoding (Par : PairEnc_Par) = struct

  let mk_s = P.var "s"
  let mk_r i = P.var (F.sprintf "r_%d" i)
  let mk_v j = P.var (F.sprintf "v_%d" j)
  let mk_b i j = P.var (F.sprintf "b_{%d,%d}" i j)
  let mk_b' i t = P.var (F.sprintf "b'_{%d,%d}" i t)

  let monom_s = mk_s |> monom_of_monomP
  let monom_si = []
  let monom_alpha = mk_v 1 |> monom_of_monomP
  let monom_ri =
    (L.map (list_range 1 (Par.par_n1+1)) ~f:(fun i -> mk_r i |> monom_of_monomP)) @
      (L.map (list_range 2 (Par.par_n2+1)) ~f:(fun i -> mk_v i |> monom_of_monomP))
  let monom_bi =
    (L.map (list_range 1 (Par.par_n1+1))
       ~f:(fun i -> L.map (list_range 1 (Par.par_n2+1))
         ~f:(fun j -> mk_b i j |> monom_of_monomP)
       )
       |> L.concat
    )
    @
    (L.map (list_range 1 (Par.par_n1+1))
       ~f:(fun i -> L.map (list_range 0 (Par.par_T+1))
         ~f:(fun t -> mk_b' i t |> monom_of_monomP)
       )
       |> L.concat
    )


  (* Pair Encoding for Ciphertet-Policy ABE for boolean formulas *)
                           
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


  let pair (mA,pi) setS =
    let c, _ = encC (mA,pi) in
    let k, _ = encK setS in

    let module Alg = PolyAlg.PolyAlg (P) in
    let target = P.((mk_v 1) *@ mk_s) in

    let f monoms2 m1 = L.map monoms2 ~f:(fun m2 -> P.((from_mon m1) *@ (from_mon m2)) |> monom_of_monomP) in
    let ribj = L.map monom_ri ~f:(f monom_bi) |> L.concat in
    let sibj = L.map monom_si ~f:(f monom_bi) |> L.concat in
    let sbj = L.map monom_bi ~f:(fun m -> P.(mk_s *@ (from_mon m)) |> monom_of_monomP) in

    let ri_bj_s_bk = L.map ribj ~f:(f sbj) |> L.concat in
    let ri_bj_sk_bl = L.map ribj ~f:(f sibj) |> L.concat in
    let forbidden = ri_bj_s_bk @ ri_bj_sk_bl in

    let requirement p = list_empty_intersection ~equal:P.mon_equal (P.mons p) forbidden in
    
    Alg.find_matrix ~requirement k c target

end


(* ** Pair-Encodings Attribute-Based Encryption *)
  
module PairEncABE (DSG : DualSystemGroup) (Par : PairEnc_Par) = struct

  let add_G1 = L.map2_exn ~f:R.g1_add
  let neg_G1 = L.map ~f:R.g1_neg
  let mul_G1 t a = L.map t ~f:(fun g -> R.g1_mul g a)
  let one_G1 = mk_list (R.g1_gen ()) (DSG.k+1)
  let zero_G1 = mk_list (R.g1_infty ()) (DSG.k+1)

  let add_G2 = L.map2_exn ~f:R.g2_add
  let neg_G2 = L.map ~f:R.g2_neg
  let mul_G2 t a = L.map t ~f:(fun g -> R.g2_mul g a)
  let one_G2 = mk_list (R.g2_gen ()) (DSG.k+1)
  let zero_G2 = mk_list (R.g2_infty ()) (DSG.k+1)

  module PairEnc = Pair_Encoding(Par)
  let n = PairEnc.param

  let setup =
    let pp, _sp = DSG.sampP n in (* _sp is only used in the proof of security *)
    let (g1_A, _, _, _) = pp in
    let msk = sample_list ~f:R.g2_rand (DSG.k+1) in
    let mu_msk = matrix_times_vector ~add:R.gt_mul ~mul:R.e_pairing (transpose_matrix g1_A) msk in
    (pp, mu_msk), msk

  let enc mpk x m =
    let (pp, mu_msk) = mpk in
    let c_polys, w2 = PairEnc.encC x in
    let alpha = sample_list ~f:samp_zp n in
    let g0 = DSG.sampG ~randomness:(Some alpha) pp in
    let g_list = sample_list ~f:(fun () -> DSG.sampG pp) w2 in

    let ct_list =
      L.map c_polys
        ~f:(fun c ->
          let zeta = P.coeff c PairEnc.monom_s in
          let ct = mul_G1 (L.nth_exn g0 0) zeta in
          let ct = 
            L.fold_left (list_range 1 (w2+1))
              ~init:ct
              ~f:(fun ct i ->
                let eta = P.coeff c (L.nth_exn PairEnc.monom_si (i-1)) in
                add_G1 ct (mul_G1 (L.nth_exn (L.nth_exn g_list (i-1)) 0) eta)
              )
          in
          let ct = 
            L.fold_left (list_range 1 (n+1))
              ~init:ct
              ~f:(fun ct j ->
                let monomial = P.((from_mon PairEnc.monom_s) *@ (from_mon (L.nth_exn PairEnc.monom_bi (j-1))))
                     |> monom_of_monomP
                in
                let theta = P.coeff c monomial in
                add_G1 ct (mul_G1 (L.nth_exn g0 (j-1)) theta)
              )
          in
          let ct =
            L.fold_left (list_range 1 (w2+1))
              ~init:ct
              ~f:(fun ct i ->
                L.fold_left (list_range 1 (n+1))
                  ~init:ct
                  ~f:(fun ct j ->
                    let monomial = P.((from_mon (L.nth_exn PairEnc.monom_si (i-1))) *@ (from_mon (L.nth_exn PairEnc.monom_bi (j-1))))
                         |> monom_of_monomP
                    in
                    let vartheta = P.coeff c monomial in
                    add_G1 ct (mul_G1 (L.nth_exn (L.nth_exn g_list (i-1)) (j-1)) vartheta)
                  )
              )
          in
          ct
        )
    in

    let ct' = R.gt_mul m (DSG.sampGT ~randomness:(Some alpha) mu_msk) in

    (ct_list, ct'), x
  
  let keyGen mpk msk y =
    let (pp, _mu_msk) = mpk in
    let k_polys, m2 = PairEnc.encK y in
    let h_list = sample_list ~f:(fun () -> DSG.sampH pp) m2 in
    
    let sk_list =
      L.map k_polys
        ~f:(fun k ->
          let tau = P.coeff k PairEnc.monom_alpha in
          let sk = mul_G2 msk tau in
          let sk =
            L.fold_left (list_range 1 (m2+1))
              ~init:sk
              ~f:(fun sk i -> 
                let upsilon = P.coeff k (L.nth_exn PairEnc.monom_ri (i-1)) in
                add_G2 sk (mul_G2 (L.nth_exn (L.nth_exn h_list (i-1)) 0) upsilon)
              )
          in
          let sk =
            L.fold_left (list_range 1 (m2+1))
              ~init:sk
              ~f:(fun sk i -> 
                L.fold_left (list_range 1 (n+1))
                  ~init:sk
                  ~f:(fun sk j ->
                    let monomial = P.((from_mon (L.nth_exn PairEnc.monom_ri (i-1))) *@ (from_mon (L.nth_exn PairEnc.monom_bi (j-1))))
                         |> monom_of_monomP
                    in
                    let phi = P.coeff k monomial in
                    add_G2 sk (mul_G2 (L.nth_exn (L.nth_exn h_list (i-1)) (j-1)) phi)
                  )
              )
          in
          sk
        )
    in
    sk_list, y
  
  let dec _mpk sk_y ct_x =
    let (ct_list, ct'), x = ct_x in
    let sk_list, y = sk_y in
    let w1 = L.length ct_list in
    let m1 = L.length sk_list in
    let mE = PairEnc.pair x y in
    let blinding_factor =
      L.fold_left (list_range 1 (m1+1))
        ~init:(R.gt_unity ())
        ~f:(fun bf t ->
          L.fold_left (list_range 1 (w1+1))
            ~init:bf
            ~f:(fun bf l ->
              let mE_tl = (L.nth_exn (L.nth_exn mE (t-1)) (l-1)) |> P.coeff_to_field in
              let sk_exp = mul_G2 (L.nth_exn sk_list (t-1)) mE_tl in
              R.gt_mul bf (DSG.dual_system_pairing (L.nth_exn ct_list (l-1)) sk_exp)
            )          
        )
    in
    R.gt_mul ct' (R.gt_inv blinding_factor)

end

(*
module G1_PE = Boolean_Formula_PE(struct
  type t = R.g1 list
  let add = L.map2_exn ~f:R.g1_add
  let neg = L.map ~f:R.g1_neg
  let mul t a = L.map t ~f:(fun g -> R.g1_mul g a)
  let one = mk_list (R.g1_gen ()) (DSG.k+1)
  let zero = mk_list (R.g1_infty ()) (DSG.k+1)
end)

module G2_PE = Boolean_Formula_PE(struct
  type t = R.g2 list
  let add = L.map2_exn ~f:R.g2_add
  let neg = L.map ~f:R.g2_neg
  let mul t a = L.map t ~f:(fun g -> R.g2_mul g a)
  let one = mk_list (R.g2_gen ()) (DSG.k+1)
  let zero = mk_list (R.g2_infty ()) (DSG.k+1)
end)
*)
(* ** Test *)

let test () =
  let tall     = Leaf(Att(1)) in
  let dark     = Leaf(Att(2)) in
  let handsome = Leaf(Att(3)) in
  let phd      = Leaf(Att(4)) in
  let cs       = Leaf(Att(5)) in
  let math     = Leaf(Att(6)) in

  let n_attrs = 6 in      (* Number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times an attribute can appear as a Leaf node *)
  let and_bound = 4 in    (* Bound on the number of AND gates *)

  
  let module DSG = DSG (G1) (G2) in
  let module PE = Boolean_Formula_PE (G1) (G2) in

  let module ABE = PredEncABE (DSG) (PE) in
  
  let mpk, msk = ABE.setup (n_attrs * repetitions + and_bound + 1)   in
  let policy = (tall &. dark &. handsome) |. (phd &. cs) in
  let xM = matrix_from_policy ~nattrs:n_attrs ~rep:repetitions policy in
  let msg = R.gt_rand () in

  let ct_x = ABE.enc mpk xM msg in

  let y = set_attributes ~nattrs:n_attrs ~rep:repetitions [ phd; cs ] in
  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = set_attributes ~nattrs:n_attrs ~rep:repetitions [ tall; dark; phd; math ] in
  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let module Par = struct
    let par_n1 = 2
    let par_n2 = 2
    let par_T = 2
  end
  in
  let mA = [[MyField.from_int 1; MyField.from_int 7]; [MyField.from_int 4; MyField.from_int 2]] in
  let pi i = MyField.from_int i in
  let setS = [MyField.from_int 1; MyField.from_int 2] in

  let module PairEncABE = PairEncABE (DSG) (Par) in

  let mpk, msk = PairEncABE.setup in
  let msg2 = R.gt_rand () in
  let ct_x = PairEncABE.enc mpk (mA,pi) msg2 in
  let sk_y = PairEncABE.keyGen mpk msk setS in
  let msg2' = PairEncABE.dec mpk sk_y ct_x in

  assert (R.gt_equal msg2 msg2');

  if (R.gt_equal msg msg') && not(R.gt_equal msg msg'') then F.printf "ABE test succedded!\n"
  else failwith "Test failed"
