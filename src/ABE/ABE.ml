open Core_kernel.Std
open Abbrevs
open Util
open AlgStructures
open MakeAlgebra
open DualSystemGInterface
open DualSystemG
open BoolForms
open PredEnc
open PairEnc

(* ** ABE described in 'Improved Dual System ABE in Prime-Order Groups via Predicate Encodings' *)

module PredEncABE (B : BilinearGroup) (DSG: DualSystemGroup) (PE : PredEnc) = struct
    
  module DSG = DSG (B)
  module PE = PE (B)

  let setup n =
    let pp, _sp = DSG.sampP n in (* _sp is only used in the proof of security *)
    let (g1_A, _, _, _) = pp in
    let msk = B.G2.samp () in
    let mu_msk = L.map g1_A ~f:(fun g -> B.e g msk) in
    (pp, mu_msk), msk
      
  let enc mpk x m =
    let (pp, mu_msk) = mpk in
    let k = (L.length (B.G1.to_list B.G1.one)) - 1 in
    let s_list = sample_list ~f:Zp.samp k in
    let g_list = DSG.sampG ~randomness:(Some s_list) pp in
    let g'T = DSG.sampGT ~randomness:(Some s_list) mu_msk in
    let c0 = L.hd_exn g_list in
    let c1 = PE.sE x (L.tl_exn g_list) in
    let c' = B.Gt.add g'T m in
    (c0, c1, c'), x
  
  let keyGen mpk msk y =
    let (pp, _mu_msk) = mpk in
    let h_list = DSG.sampH pp in
    let k0 = L.hd_exn h_list in
    let k1 = L.map2_exn (PE.kE y msk) (PE.rE y (L.tl_exn h_list)) ~f:B.G2.add in
    (k0, k1), y
  
  let dec _mpk sk_y ct_x =
    let (c0, c1, c'), x = ct_x in
    let (k0, k1), y = sk_y in
    let e_g0_msk = B.Gt.add (B.e c0 (PE.rD x y k1)) (B.Gt.neg (B.e (PE.sD x y c1) k0)) in
    B.Gt.add c' (B.Gt.neg e_g0_msk)        

end

(* ** ABE described in 'A Study of Pair Encodings: Predicate Encryption in Prime Order Groups' *)
  
module PairEncABE (B : BilinearGroup) (DSG : DualSystemGroup) (PE : PairEnc) = struct

  module DSG = DSG (B)
  let n = PE.param

  let setup =
    let pp, _sp = DSG.sampP n in (* _sp is only used in the proof of security *)
    let (g1_A, _, _, _) = pp in
    let msk = B.G2.samp () in
    let mu_msk = L.map g1_A ~f:(fun g -> B.e g msk) in
    (pp, mu_msk), msk

  let enc mpk x m =
    let (pp, mu_msk) = mpk in
    let c_polys, w2 = PE.encC x in
    let alpha = sample_list ~f:Zp.samp n in
    let g0 = DSG.sampG ~randomness:(Some alpha) pp in
    let g_list = sample_list ~f:(fun () -> DSG.sampG pp) w2 in

    let ct_list =
      L.map c_polys
        ~f:(fun c ->
          let zeta = P.coeff c PE.monom_s in
          let ct = B.G1.mul (L.nth_exn g0 0) zeta in
          let ct = 
            L.fold_left (list_range 1 (w2+1))
              ~init:ct
              ~f:(fun ct i ->
                let eta = P.coeff c (L.nth_exn PE.monom_si (i-1)) in
                B.G1.add ct (B.G1.mul (L.nth_exn (L.nth_exn g_list (i-1)) 0) eta)
              )
          in
          let ct = 
            L.fold_left (list_range 1 (n+1))
              ~init:ct
              ~f:(fun ct j ->
                let monomial = P.((from_mon PE.monom_s) *@ (from_mon (L.nth_exn PE.monom_bi (j-1))))
                     |> P.monom_of_monomPoly
                in
                let theta = P.coeff c monomial in
                B.G1.add ct (B.G1.mul (L.nth_exn g0 (j-1)) theta)
              )
          in
          let ct =
            L.fold_left (list_range 1 (w2+1))
              ~init:ct
              ~f:(fun ct i ->
                L.fold_left (list_range 1 (n+1))
                  ~init:ct
                  ~f:(fun ct j ->
                    let monomial = P.((from_mon (L.nth_exn PE.monom_si (i-1))) *@ (from_mon (L.nth_exn PE.monom_bi (j-1))))
                         |> P.monom_of_monomPoly
                    in
                    let vartheta = P.coeff c monomial in
                    B.G1.add ct (B.G1.mul (L.nth_exn (L.nth_exn g_list (i-1)) (j-1)) vartheta)
                  )
              )
          in
          ct
        )
    in

    let ct' = B.Gt.add m (DSG.sampGT ~randomness:(Some alpha) mu_msk) in

    (ct_list, ct'), x
  
  let keyGen mpk msk y =
    let (pp, _mu_msk) = mpk in
    let k_polys, m2 = PE.encK y in
    let h_list = sample_list ~f:(fun () -> DSG.sampH pp) m2 in
    
    let sk_list =
      L.map k_polys
        ~f:(fun k ->
          let tau = P.coeff k PE.monom_alpha in
          let sk = B.G2.mul msk tau in
          let sk =
            L.fold_left (list_range 1 (m2+1))
              ~init:sk
              ~f:(fun sk i -> 
                let upsilon = P.coeff k (L.nth_exn PE.monom_ri (i-1)) in
                B.G2.add sk (B.G2.mul (L.nth_exn (L.nth_exn h_list (i-1)) 0) upsilon)
              )
          in
          let sk =
            L.fold_left (list_range 1 (m2+1))
              ~init:sk
              ~f:(fun sk i -> 
                L.fold_left (list_range 1 (n+1))
                  ~init:sk
                  ~f:(fun sk j ->
                    let monomial = P.((from_mon (L.nth_exn PE.monom_ri (i-1))) *@ (from_mon (L.nth_exn PE.monom_bi (j-1))))
                         |> P.monom_of_monomPoly
                    in
                    let phi = P.coeff k monomial in
                    B.G2.add sk (B.G2.mul (L.nth_exn (L.nth_exn h_list (i-1)) (j-1)) phi)
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
    let mE = PE.pair x y in
    let blinding_factor =
      L.fold_left (list_range 1 (m1+1))
        ~init:(B.Gt.one)
        ~f:(fun bf t ->
          L.fold_left (list_range 1 (w1+1))
            ~init:bf
            ~f:(fun bf l ->
              let mE_tl = (L.nth_exn (L.nth_exn mE (t-1)) (l-1)) |> P.coeff_to_field in
              let sk_exp = B.G2.mul (L.nth_exn sk_list (t-1)) mE_tl in
              B.Gt.add bf (B.e (L.nth_exn ct_list (l-1)) sk_exp)
            )          
        )
    in
    B.Gt.add ct' (B.Gt.neg blinding_factor)

end

(* ** Test *)

let test_predEnc () =
  let tall     = Leaf(Att(1)) in
  let dark     = Leaf(Att(2)) in
  let handsome = Leaf(Att(3)) in
  let phd      = Leaf(Att(4)) in
  let cs       = Leaf(Att(5)) in
  let math     = Leaf(Att(6)) in

  let n_attrs = 6 in      (* Number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times an attribute can appear as a Leaf node *)
  let and_bound = 4 in    (* Bound on the number of AND gates *)

  let module DSG = Hoeteck's_DSG in
  let module PE = Boolean_Formula_PredEnc in
  let module B = (val make_BilinearGroup 2) in

  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  
  let mpk, msk = ABE.setup (n_attrs * repetitions + and_bound + 1)   in
  let policy = (tall &. dark &. handsome) |. (phd &. cs) in
  let xM = matrix_from_policy ~nattrs:n_attrs ~rep:repetitions policy in
  let msg = B.Gt.samp () in

  let ct_x = ABE.enc mpk xM msg in

  let y = set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs:n_attrs ~rep:repetitions [ phd; cs ] in
  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs:n_attrs ~rep:repetitions [ tall; dark; phd; math ] in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not(B.Gt.equal msg msg'') then
    F.printf "Predicate Encodings ABE test succedded!\n Time: %F seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings test failed"
    
let test_pairEnc () =
  
  let module DSG = Hoeteck's_DSG in

  let module Par = struct
    let par_n1 = 3
    let par_n2 = 2
    let par_T = 2
  end
  in

  let n = Zp.from_int in
  let mA = [[n 1; n 0]; [n 1; n 1]; [n 1; n 2]] in
  let pi i = n i in
  let setS = [n 2; n 3] in
  
  let module PE = Boolean_Formula_PairEnc (Par) in
  let module B = (val make_BilinearGroup PE.param) in

  let module ABE = PairEncABE (B) (DSG) (PE) in
  
  let t1 = Unix.gettimeofday() in

  let mpk, msk = ABE.setup in
  let msg = B.Gt.samp () in
  let ct_x = ABE.enc mpk (mA,pi) msg in
  let sk_y = ABE.keyGen mpk msk setS in
  let msg' = ABE.dec mpk sk_y ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') then
    F.printf "Pair Encodings ABE test succedded!\n Time: %F seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Pair Encodings test failed"
   
