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

    val setup  : ?n:int -> unit -> mpk * msk
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

  let setup ?(n = -1) () =
    let n = if n <= 0 then failwith "ABE setup: wrong parameter or not provided" else n in
    let mu, (pp, _sp) = DSG.sampP n in (* _sp is only used in the proof of security *)
    let msk = B.G2.samp () in
    (pp, mu msk), msk
      
  let enc mpk x m =
    F.printf "%s\n" (PE.string_of_x x);
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
    match String.split ~on:(Char.of_string sep) str with
    | str_pp :: str_img_mu :: [] ->
       (DSG.pp_of_string str_pp, DSG.img_mu_of_string str_img_mu)
    | _ -> failwith "invalid string"

  let msk_of_string str = B.G2.of_string str

  let sk_of_string str =
    match String.split ~on:(Char.of_string sep) str with
    | str_k0 :: str_k1 :: str_y :: [] ->
       (B.G2.of_string str_k0, L.map (String.split ~on:(Char.of_string sep1) str_k1) ~f:B.G2.of_string),
      PE.y_of_string str_y
    | _ -> failwith "invalid string"
      
  let ct_of_string str =
    match String.split ~on:(Char.of_string sep) str with
    | str_c0 :: str_c1 :: str_c' :: str_x :: [] ->
       (B.G1.of_string str_c0, L.map (String.split ~on:(Char.of_string sep1) str_c1) ~f:B.G1.of_string,
        B.Gt.of_string str_c'), PE.x_of_string str_x
    | _ -> failwith "invalide string"

  let msg_of_string str = B.Gt.of_string str
end

(* ** ABE described in 'A Study of Pair Encodings: Predicate Encryption in Prime Order Groups' *)
  
module PairEncABE (B : BilinearGroup) (DSG : DualSystemGroup) (PE : PairEnc) = struct

  module DSG = DSG (B)

(*  type mpk = DSG.pp * DSG.img_mu
  type msk = B.G2.t
  type x   = PE.x
  type y   = PE.y
  type msg = B.Gt.t
  type sk  = (B.G2.t * B.G2.t list) * y
  type ct  = (B.G1.t * B.G1.t list * B.Gt.t) * x
*)

  let k = L.length (B.G1.to_list B.G1.one) - 1
  let n = PE.param

  let setup _ =
    let mu, (pp, _sp) = DSG.sampP n in (* _sp is only used in the proof of security *)
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

end

(* ** Test *)

let tall     = Leaf(Att(1))
let dark     = Leaf(Att(2))
let handsome = Leaf(Att(3))
let phd      = Leaf(Att(4))
let cs       = Leaf(Att(5))
let maths    = Leaf(Att(6))

let policy = (tall &. handsome &. dark) |. (phd &. cs)

module DSG = Hoeteck's_DSG
module B = (val make_BilinearGroup 2)

let bn_of_int i = Zp.read_str (string_of_int i)

let test_predEnc () =

  let n_attrs = 6 in      (* Global number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times the same attribute can appear as a Leaf node *)
  let and_bound = 3 in    (* Bound on the number of AND gates *)

  let module ABE = PredEncABE (B) (DSG) (Boolean_Formula_PredEnc) in

  let t1 = Unix.gettimeofday() in
  
  let mpk, msk = ABE.setup ~n:(n_attrs * repetitions + and_bound + 1) () in
  let xM = ABE.set_x (Predicates.BoolForm_Policy(n_attrs, repetitions, policy)) in
  let msg = ABE.rand_msg () in

  let ct_x = ABE.enc mpk xM msg in

  let y = pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs:n_attrs ~rep:repetitions [ phd; cs ] in
  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = pred_enc_set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs:n_attrs ~rep:repetitions [ tall; dark; phd; maths ] in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not(B.Gt.equal msg msg'') then
    F.printf "Predicate Encodings ABE test succedded!\n Time: %F seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings test failed"
    
let test_pairEnc () =
  
  let module Par = struct
    let par_n1 = 5    (* Bound on the number of Leaf nodes in the boolean formula*)
    let par_n2 = 3    (* Bound on the number of AND gates *)
    let par_T = 4     (* Bound on the number of attributes in a key *)
  end
  in  
  let module ABE = PairEncABE (B) (DSG) (Boolean_Formula_PairEnc (Par)) in
  
  let t1 = Unix.gettimeofday() in

  let mA, pi = pair_enc_matrix_of_policy ~n1:Par.par_n1 ~n2:Par.par_n2 ~t_of_int:bn_of_int policy in

  let mpk, msk = ABE.setup () in
  let msg = B.Gt.samp () in
  let ct_x = ABE.enc mpk (mA,pi) msg in

(*  let setS = pair_enc_set_attributes ~t_of_int:bn_of_int [ phd; cs ] in
  let sk_y = ABE.keyGen mpk msk setS in
  let msg' = ABE.dec mpk sk_y ct_x in*)

  let setS' = pair_enc_set_attributes ~t_of_int:bn_of_int [ tall; dark; maths; cs ] in

  let sk_y' = ABE.keyGen mpk msk setS' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

(*  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then*)
  if not (B.Gt.equal msg msg'') then
    F.printf "Pair Encodings ABE test succedded!\n Time: %F seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Pair Encodings test failed"
   
