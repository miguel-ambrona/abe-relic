
(* ** Imports *)

open Abbrevs
open Util

module R = Relic

let prime = ref None

let get_prime() =
  init_relic();
  match !prime with
  | None ->
     let p = R.g1_ord () in
     assert ((R.bn_equal p (R.g2_ord ())) && (R.bn_equal p (R.gt_ord ())));
     prime := Some p;
     p
  | Some p -> p
     
module Zp = struct
  type t = R.bn
  let p = get_prime()
  let pp fmt a = F.fprintf fmt "%s" (R.bn_write_str a ~radix:10)
  let add a b = R.bn_mod (R.bn_add a b) p
  let neg a = R.bn_mod (R.bn_neg a) p
  let mul a b = R.bn_mod (R.bn_mul a b) p    
  let inv a =
    let (d,u,_v) = R.bn_gcd_ext a p in
    if R.bn_equal d (R.bn_one ()) then R.bn_mod u p
    else failwith ("Inverse of " ^ (R.bn_write_str a ~radix:10)  ^ 
                      " mod " ^ (R.bn_write_str p ~radix:10) ^ " does not exist")
  let one = R.bn_one ()
  let zero = R.bn_zero ()
  let is_zero a = R.bn_is_zero (R.bn_mod a p)
    
  let samp () = R.bn_rand_mod p
  let read_str str = R.bn_mod (R.bn_read_str str ~radix:10) p

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
