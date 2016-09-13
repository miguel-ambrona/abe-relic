open Abbrevs
open Util
open Matrix
open AlgStructures
open MakeAlgebra
open DualSystemGInterface
open PredEnc
open PairEnc
open Predicates

(* ** Attribute-Based Encryption *)

module type ABE =
  sig
    type mpk
    type msk
    type x
    type y
    type msg
    type sk
    type ct

    val setup  : unit -> mpk * msk
    val enc    : mpk -> x -> msg -> ct
    val keyGen : mpk -> msk -> y -> sk
    val dec    : mpk -> sk -> ct -> msg

    val rand_msg : unit -> msg

    val set_x : generic_attribute -> x
    val set_y : generic_attribute -> y

    val string_of_mpk : mpk -> string
    val string_of_msk : msk -> string
    val string_of_sk  : sk  -> string
    val string_of_ct  : ct  -> string
    val string_of_msg : msg -> string

    val mpk_of_string : string -> mpk
    val msk_of_string : string -> msk
    val sk_of_string  : string -> sk
    val ct_of_string  : string -> ct
    val msg_of_string : string -> msg
end

(* ** ABE described in 'Improved Dual System ABE in Prime-Order Groups via Predicate Encodings' *)

module PredEncABE (B : BilinearGroup) (DSG: DualSystemGroup) (PE : PredEnc) = struct

  module DSG = DSG (B)
  module PE = PE (B)

  type mpk = DSG.pp * DSG.img_mu
  type msk = B.G2.t
  type x   = PE.x
  type y   = PE.y
  type msg = B.Gt.t
  type sk  = (B.G2.t * B.G2.t list) * y
  type ct  = (B.G1.t * B.G1.t list * B.Gt.t) * x

  let setup () =
    let mu, (pp, _sp) = DSG.sampP PE.n in (* _sp is only used in the proof of security *)
    let msk = B.G2.samp () in
    (pp, mu msk), msk

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

  let rand_msg = B.Gt.samp

  let set_x = PE.set_x
  let set_y = PE.set_y

  (* *** String conversions *)

  let sep = "&"
  let sep1 = "?"

  let string_of_mpk mpk =
    let (pp, img_mu) = mpk in
    (DSG.string_of_pp pp) ^ sep ^ (DSG.string_of_img_mu img_mu)

  let string_of_msk msk = B.G2.to_string msk

  let string_of_sk sk =
    let (k0, k1), y = sk in
    (B.G2.to_string k0) ^ sep ^ (list_to_string ~sep:sep1 (L.map k1 ~f:B.G2.to_string)) ^ sep ^ (PE.string_of_y y)

  let string_of_ct ct =
    let (c0, c1, c'), x = ct in
    (B.G1.to_string c0) ^ sep ^ (list_to_string ~sep:sep1 (L.map c1 ~f:B.G1.to_string)) ^ sep ^
      (B.Gt.to_string c') ^ sep ^ (PE.string_of_x x)

  let string_of_msg msg = B.Gt.to_string msg


  let mpk_of_string str =
    match S.split ~on:(Char.of_string sep) str with
    | str_pp :: str_img_mu :: [] ->
       (DSG.pp_of_string str_pp, DSG.img_mu_of_string str_img_mu)
    | _ -> failwith "invalid string"

  let msk_of_string str = B.G2.of_string str

  let sk_of_string str =
    match S.split ~on:(Char.of_string sep) str with
    | str_k0 :: str_k1 :: str_y :: [] ->
       (B.G2.of_string str_k0, L.map (S.split ~on:(Char.of_string sep1) str_k1) ~f:B.G2.of_string),
      PE.y_of_string str_y
    | _ -> failwith "invalid string"

  let ct_of_string str =
    match S.split ~on:(Char.of_string sep) str with
    | str_c0 :: str_c1 :: str_c' :: str_x :: [] ->
       (B.G1.of_string str_c0, L.map (S.split ~on:(Char.of_string sep1) str_c1) ~f:B.G1.of_string,
        B.Gt.of_string str_c'), PE.x_of_string str_x
    | _ -> failwith "invalide string"

  let msg_of_string str = B.Gt.of_string str
end

(* ** ABE described in 'A Study of Pair Encodings: Predicate Encryption in Prime Order Groups' *)

module PairEncABE (B : BilinearGroup) (DSG : DualSystemGroup) (PE : PairEnc) = struct

  module DSG = DSG (B)
  module P = Zp_Poly

  type mpk = DSG.pp * DSG.img_mu
  type msk = B.G2.t
  type x   = PE.x
  type y   = PE.y
  type msg = B.Gt.t
  type sk  = (B.G2.t list) * y
  type ct  = (B.G1.t list * B.Gt.t) * x

  let k = L.length (B.G1.to_list B.G1.one) - 1

  let setup () =
    let mu, (pp, _sp) = DSG.sampP PE.param in (* _sp is only used in the proof of security *)
    let msk = B.G2.samp () in
    (pp, mu msk), msk

  let enc mpk x m =
    let (pp, mu_msk) = mpk in
    let c_polys, w2 = PE.encC x in
    let alpha = sample_list ~f:Zp.samp k in
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
            L.fold_left (list_range 1 (PE.param+1))
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
                L.fold_left (list_range 1 (PE.param+1))
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
                L.fold_left (list_range 1 (PE.param+1))
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
    match mE with
    | None -> B.Gt.zero
    | Some mE ->
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


  let rand_msg = B.Gt.samp

  let set_x = PE.set_x
  let set_y = PE.set_y

  (* *** String conversions *)

  let sep = "&"
  let sep1 = "?"

  let string_of_mpk mpk =
    let (pp, img_mu) = mpk in
    (DSG.string_of_pp pp) ^ sep ^ (DSG.string_of_img_mu img_mu)

  let string_of_msk msk = B.G2.to_string msk

  let string_of_sk sk =
    let (k, y) = sk in
    (list_to_string ~sep:sep1 (L.map k ~f:B.G2.to_string)) ^ sep ^ (PE.string_of_y y)

  let string_of_ct ct =
    let (c, c'), x = ct in
    (list_to_string ~sep:sep1 (L.map c ~f:B.G1.to_string)) ^ sep ^ (B.Gt.to_string c') ^ sep ^ (PE.string_of_x x)

  let string_of_msg msg = B.Gt.to_string msg

  let mpk_of_string str =
    match S.split ~on:(Char.of_string sep) str with
    | str_pp :: str_img_mu :: [] ->
       (DSG.pp_of_string str_pp, DSG.img_mu_of_string str_img_mu)
    | _ -> failwith "invalid string"

  let msk_of_string str = B.G2.of_string str

  let sk_of_string str =
    match S.split ~on:(Char.of_string sep) str with
    | str_k :: str_y :: [] ->
      (L.map (S.split ~on:(Char.of_string sep1) str_k) ~f:B.G2.of_string, PE.y_of_string str_y)
    | _ -> failwith "invalid string"

  let ct_of_string str =
    match S.split ~on:(Char.of_string sep) str with
    | str_c :: str_c' :: str_x :: [] ->
       (L.map (S.split ~on:(Char.of_string sep1) str_c) ~f:B.G1.of_string, B.Gt.of_string str_c'), PE.x_of_string str_x
    | _ -> failwith "invalid string"

  let msg_of_string str = B.Gt.of_string str

end
