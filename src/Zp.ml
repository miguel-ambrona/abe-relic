open Abbrevs
open Util
module R = Relic

let _ = Util.init_relic ()

let p = R.g1_ord ()
let _ = assert ((R.bn_equal p (R.g2_ord ())) && (R.bn_equal p (R.gt_ord ())))

(* *** Functions depending on p *)

let samp_zp () = R.bn_rand_mod p

let bn_add_mod a b = R.bn_mod (R.bn_add a b) p
let bn_mul_mod a b = R.bn_mod (R.bn_mul a b) p
let bn_neg_mod a = R.bn_mod (R.bn_neg a) p
let bn_is_zero_mod a = R.bn_is_zero (R.bn_mod a p)
let bn_read_str_mod str = R.bn_mod (R.bn_read_str str ~radix:10) p

let zp_inverse a =
  let (d,u,_v) = R.bn_gcd_ext a p in
  if R.bn_equal d (R.bn_one ()) then R.bn_mod u p
  else failwith ("Inverse of " ^ (R.bn_write_str a ~radix:10)  ^ 
                    " mod " ^ (R.bn_write_str p ~radix:10) ^ " does not exist")


module type Group = sig
  type t
  val k : int
  val add  : t -> t -> t
  val neg  : t -> t
  val mul  : t -> R.bn -> t
  val one  : t
  val zero : t
end

let k = 10

module G1 = struct
  type t = R.g1 list
  let k = k
  let add = L.map2_exn ~f:R.g1_add
  let neg = L.map ~f:R.g1_neg
  let mul t a = L.map t ~f:(fun g -> R.g1_mul g a)
  let one = mk_list (R.g1_gen ()) (k+1)
  let zero = mk_list (R.g1_infty ()) (k+1)
end

module G2 = struct
  type t = R.g2 list
  let k = k
  let add = L.map2_exn ~f:R.g2_add
  let neg = L.map ~f:R.g2_neg
  let mul t a = L.map t ~f:(fun g -> R.g2_mul g a)
  let one = mk_list (R.g2_gen ()) (k+1)
  let zero = mk_list (R.g2_infty ()) (k+1)
end
