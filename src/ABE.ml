open Core_kernel.Std
open Abbrevs
open LinAlg
open Util

module R = Relic

(* * ABE described in Improved Dual System ABE in Prime-Order Groups via Predicate Encodings *)

let init () =
  assert (R.core_init () = R.sts_ok);
  assert (R.pc_param_set_any () = R.sts_ok)

let _ = init ()

(* ** Public parameters *)

let g1 = R.g1_gen ()
let g2 = R.g2_gen ()
let p = R.g1_ord ()
let _ = assert ((R.bn_equal p (R.g2_ord ())) && (R.bn_equal p (R.gt_ord ())))
  
(* *** Functions depending on p *)

let samp_zp () = R.bn_rand_mod p
let zp_inverse a = 
  let (d,u,_v) = R.bn_gcd_ext a p in
  if R.bn_equal d (R.bn_one ()) then R.bn_mod u p
  else failwith ("Inverse of " ^ (R.bn_write_str a ~radix:10)  ^ 
                    " mod " ^ (R.bn_write_str p ~radix:10) ^ " does not exist")

let bn_add_mod a b = R.bn_mod (R.bn_add a b) p
let bn_mul_mod a b = R.bn_mod (R.bn_mul a b) p
let bn_neg_mod a = R.bn_mod (R.bn_neg a) p
let bn_is_zero_mod a = R.bn_is_zero (R.bn_mod a p)
let bn_read_str_mod str = R.bn_mod (R.bn_read_str str ~radix:10) p

(* ** Dual System Groups *)

module DSG = struct

  let k = 2  (* Security based on k-Lin assumption *)
  
  let dual_system_pairing l1 l2 =
    let gt_list = L.map2_exn l1 l2 ~f:R.e_pairing in
    L.fold_left (L.tl_exn gt_list) ~init:(L.hd_exn gt_list) ~f:R.gt_mul
  
  let samp_Dk k =
    let diagonal = sample_list ~f:samp_zp k in
    let rec make_matrix matrix counter = function
      | [] -> matrix
      | a :: rest ->
         let new_row = (mk_list (R.bn_zero ()) counter) @ [a] @ (mk_list (R.bn_zero ()) (k - counter - 1)) in
         make_matrix (matrix @ [new_row]) (counter + 1) rest
    in
    (make_matrix [] 0 diagonal) @ [ mk_list (R.bn_one ()) k],
    (L.map diagonal ~f:zp_inverse) @ [bn_neg_mod (R.bn_one ())]

  
  let sampP n =
    let a_matrix, a_orth = samp_Dk k in
    let b_matrix, b_orth = samp_Dk k in
    
    let list_W = sample_list ~f:(fun () -> sample_matrix ~f:samp_zp (k+1) (k+1)) n in
    let g1_A = matrix_map a_matrix ~f:(R.g1_mul g1) in
    let g2_B = matrix_map b_matrix ~f:(R.g2_mul g2) in
    let list_WA = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:bn_add_mod ~mul:bn_mul_mod (transpose_matrix w) a_matrix) in
    let list_WB = L.map list_W ~f:(fun w -> matrix_times_matrix ~add:bn_add_mod ~mul:bn_mul_mod w b_matrix) in
    let g1_WA = L.map list_WA ~f:(fun wa -> matrix_map wa ~f:(R.g1_mul g1)) in
    let g2_WB = L.map list_WB ~f:(fun wb -> matrix_map wb ~f:(R.g2_mul g2)) in
    (g1_A, g1_WA, g2_B, g2_WB), (a_orth, b_orth, list_W)


  let sampGT ?(randomness = None) p_list =
    let s_list =
      match randomness with
      | None        -> sample_list ~f:samp_zp k
      | Some s_list -> s_list
    in
    let l = L.map2_exn s_list p_list ~f:(fun s p -> R.gt_exp p s) in
    L.fold_left (L.tl_exn l) ~init:(L.hd_exn l) ~f:R.gt_mul


  let sampG ?(randomness = None) pp =
    let (g1_A, g1_WA, _, _) = pp in
    let s_list =
      match randomness with
      | None        -> sample_list ~f:samp_zp k
      | Some s_list -> s_list
    in
    let prod_As = matrix_times_vector ~add:R.g1_add ~mul:R.g1_mul g1_A s_list in
    let prod_WAs = L.map g1_WA ~f:(fun wa -> matrix_times_vector ~add:R.g1_add ~mul:R.g1_mul wa s_list) in
    prod_As :: prod_WAs


  let sampH pp =
    let (_, _, g2_B, g2_WB) = pp in
    let r_list = sample_list ~f:samp_zp k in
    let prod_Br = matrix_times_vector ~add:R.g2_add ~mul:R.g2_mul g2_B r_list in
    let prod_WBr = L.map g2_WB ~f:(fun wb -> matrix_times_vector ~add:R.g2_add ~mul:R.g2_mul wb r_list) in
    prod_Br :: prod_WBr

end

(* ** Functions for boolean formulas *)

module GaussElim = LinAlg(struct
  type t = R.bn
  let add = bn_add_mod
  let neg = bn_neg_mod
  let mul = bn_mul_mod
  let inv = zp_inverse
  let one = R.bn_one ()
  let zero = R.bn_zero ()
  let is_zero = bn_is_zero_mod
end)  

module type Group = sig
  type t
  val add  : t -> t -> t
  val neg  : t -> t
  val mul  : t -> R.bn -> t
  val one  : t
  val zero : t
end

type attribute = Att of int

type bool_formula =
  | Or   of bool_formula * bool_formula
  | And  of bool_formula * bool_formula
  | Leaf of attribute

let matrix_of_formula bf =
  let c = ref 1 in
  let add_zeros v = v @ (mk_list 0 (!c - (L.length v))) in
  let rec aux v = function
    | Or(bf1, bf2)  -> (aux v bf1) @ (aux v bf2)
    | And(bf1, bf2) ->
       let v1 = (add_zeros v) @ [1] in
       let v2 = (mk_list 0 !c) @ [-1] in
       c := !c + 1;
       (aux v1 bf1) @ (aux v2 bf2)
    | Leaf(a) -> [(v, a)]
  in
  L.map (aux [1] bf) ~f:(fun (v,a) ->  (add_zeros v, a))

let sort_matrix ?(rep = 1) matrix n_attrs =
  let empty_row =
    let (r,_) = L.hd_exn matrix in
    mk_list 0 (L.length r)
  in
  let rec aux matrix k =
    if k > n_attrs then matrix
    else
      let k_rows = L.count matrix ~f:(function | (_,Att(i)) -> k = i) in
      if k_rows > rep then
        failwith ("This matrix needs more than " ^ (string_of_int rep) ^ " repetitions")
      else
        let matrix' = matrix @ (mk_list (empty_row, Att(k)) (rep - k_rows)) in
        aux matrix' (k+1)
  in
  L.sort (aux matrix 1)
    ~cmp:(fun (_r1,a1) (_r2,a2) -> match a1,a2 with | Att(i1), Att(i2) -> i1 - i2)


let pp_attribute fmt = function
  | Att(i) -> F.fprintf fmt "%i" i

let pp_matrix _fmt =
 L.iter ~f:(fun (v,a) ->
    F.printf "[%a](%a)\n" (pp_list ", " pp_int) v pp_attribute a
  )

(* ** Predicate Encodings *)

module Boolean_Formula_PE(Group : Group) = struct

  (* Predicate Encoding for Ciphertet-Policy ABE for boolean formulas *)

  type t = Group.t list
  let ( +! ) = L.map2_exn ~f:Group.add                             (* Add two group vectors *)
  let ( *.!) g = L.map ~f:(Group.mul g)                            (* Mul group element by Zp vector *)
  let ( *!.) l n = L.map l ~f:(fun g -> Group.mul g n)             (* Mul group vector by Zp element *)
  let ( *..) = Group.mul                                           (* Mul group element by Zp element *)
  let ( *! ) = vector_times_vector ~add:Group.add ~mul:Group.mul   (* Mul group vector by Zp vector *)
  let one = Group.one
  let zero = Group.zero
  let head = L.hd_exn
  let tail = L.tl_exn
  let single v = if L.length v = 1 then head v else assert false
      
  let sE xM w_u_u0 =
    let l = L.length xM in
    let l' = L.length (L.hd_exn xM) in
    let w = L.slice w_u_u0 0 l in
    let u = L.slice w_u_u0 l (l+l'-1) in
    let u0 = L.hd_exn (L.tl_exn w_u_u0) in
    w +! (matrix_times_vector ~add:Group.add ~mul:(fun exp g -> Group.mul g exp) xM (u0 :: u))

  let rE y w_u_u0 =
    let l = L.length y in
    let w = L.slice w_u_u0 0 l in
    let u0 = L.hd_exn (L.tl_exn w_u_u0) in
    u0 :: (L.map2_exn ~f:Group.mul w y)
      
  let kE y alpha =
    alpha :: (mk_list zero (L.length y))
      
  let sD xM y c =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
    if filtered = [] then zero (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
      | None -> zero (* Decryption failed *)
      | Some a ->
         let y_c = L.filter (L.zip_exn c y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
         let a_y_c = L.map2_exn ~f:Group.mul y_c a in
         L.fold_left (L.tl_exn a_y_c)
           ~init:(L.hd_exn a_y_c)
           ~f:Group.add
           
  let rD xM y d_d' =
    let l' = L.length (L.hd_exn xM) in
    let filtered = L.filter (L.zip_exn xM y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
    if filtered = [] then zero (* No attributes in the key *)
    else
      let matrix = transpose_matrix filtered in
      match GaussElim.solve matrix ((R.bn_one ()) :: (mk_list (R.bn_zero ()) (l'-1))) with
      | None -> zero (* Decryption failed *)
      | Some a ->
         let d' = L.hd_exn d_d' in
         let d = L.tl_exn d_d' in
         let d = L.filter (L.zip_exn d y) ~f:(fun (_,yi) -> not (R.bn_is_zero yi)) |> unzip1 in
         let a_d = L.map2_exn ~f:Group.mul d a in
         Group.add
           d'
           (L.fold_left (L.tl_exn a_d)
              ~init:(L.hd_exn a_d)
              ~f:Group.add)
end

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

(* ** Attribute-Based Encryption *)
  
module ABE = struct
    
  let setup n =
    let pp, _sp = DSG.sampP n in
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
    let c1 = G1_PE.sE x (L.tl_exn g_list) in
    let c' = R.gt_mul g'T m in
    (c0, c1, c'), x
  
  let keyGen mpk msk y =
    let (pp, _mu_msk) = mpk in
    let h_list = DSG.sampH pp in
    let k0 = L.hd_exn h_list in
    let k1 = L.map2_exn (G2_PE.kE y msk) (G2_PE.rE y (L.tl_exn h_list)) ~f:(L.map2_exn ~f:R.g2_add) in
    (k0, k1), y
  
  let dec _mpk sk_y ct_x =
    let (c0, c1, c'), x = ct_x in
    let (k0, k1), y = sk_y in
    let e_g0_msk = R.gt_mul (DSG.dual_system_pairing c0 (G2_PE.rD x y k1)) (R.gt_inv (DSG.dual_system_pairing (G1_PE.sD x y c1) k0)) in
    R.gt_mul c' (R.gt_inv e_g0_msk)        

end


(* ** Util *)

let matrix_from_policy ~nattrs ~rep p =
  sort_matrix ~rep (matrix_of_formula p) nattrs
  |> unzip1
  |> L.map ~f:(L.map ~f:(fun i -> bn_read_str_mod (string_of_int i)))
  
let set_attributes ~nattrs ~rep attrs =
  let rec repeat output = function
    | [] -> output
    | a :: rest -> repeat (output @ (mk_list a rep)) rest
  in
  let rec mk_bit_vector output k =
    if k > nattrs then output
    else
      if L.exists attrs ~f:(function | Leaf(Att(i)) -> i = k | _ -> assert false) then
        mk_bit_vector (output @ [ R.bn_one () ]) (k+1)
      else
        mk_bit_vector (output @ [ R.bn_zero () ]) (k+1)
  in
  repeat [] (mk_bit_vector [] 1)

let (&.) a b = And(a,b)
let (|.) a b = Or(a,b)

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

  if (R.gt_equal msg msg') && not(R.gt_equal msg msg'') then F.printf "ABE test succedded!\n"
  else failwith "Test failed"
