open Abbrevs
open Util

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
  type atom = R.g1
  let atom_gen = R.g1_gen ()
  let atom_add = R.g1_add
  let atom_mul = R.g1_mul

  type t = atom list
  let add = L.map2_exn ~f:atom_add
  let neg = L.map ~f:R.g1_neg
  let mul t a = L.map t ~f:(fun g -> atom_mul g a)
  let one = mk_list (R.g1_gen ()) (k+1)
  let zero = mk_list (R.g1_infty ()) (k+1)
  let samp = (fun () -> sample_list ~f:R.g1_rand (k+1))
  let to_list g = g
  let from_list g = g

  let equal a b = Util.equal_lists ~equal:R.g1_equal (to_list a) (to_list b)
end

module G2 = struct
  type atom = R.g2
  let atom_gen = R.g2_gen ()
  let atom_add = R.g2_add
  let atom_mul = R.g2_mul

  type t = atom list
  let add = L.map2_exn ~f:atom_add
  let neg = L.map ~f:R.g2_neg
  let mul t a = L.map t ~f:(fun g -> atom_mul g a)
  let one = mk_list (R.g2_gen ()) (k+1)
  let zero = mk_list (R.g2_infty ()) (k+1)
  let samp = (fun () -> sample_list ~f:R.g2_rand (k+1))

  let to_list h = h
  let from_list h = h

  let equal a b = Util.equal_lists ~equal:R.g2_equal (to_list a) (to_list b)
end

module Gt = struct
  type t = R.gt
  let add = R.gt_mul
  let neg = R.gt_inv
  let mul = R.gt_exp
  let one = R.gt_unity ()
  let zero = R.gt_zero ()
  let samp = R.gt_rand

  let equal = R.gt_equal

  type atom = t
  let atom_gen = R.gt_gen ()
  let atom_add = add
  let atom_mul = mul
  let to_list h = [h]
  let from_list h = L.hd_exn h
end


module B = struct
  let p = R.g1_ord ()
  module G1 = G1
  module G2 = G2
  module Gt = Gt
  let e g1 g2 =
    let gt_list = L.map2_exn (G1.to_list g1) (G2.to_list g2) ~f:R.e_pairing in
    L.fold_left (L.tl_exn gt_list) ~init:(L.hd_exn gt_list) ~f:Gt.add
end
