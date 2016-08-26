open Core_kernel.Std
open Abbrevs
open Util
open Matrix
open AlgStructures

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
    
  let samp () = zp_samp_ref := !zp_samp_ref + 1; R.bn_rand_mod p
  let write_str t = R.bn_write_str (R.bn_mod t p) ~radix:10
  let read_str str = R.bn_mod (R.bn_read_str str ~radix:10) p

  let rec ring_exp m n =
    if n > 0 then mul m (ring_exp m (n-1))
    else if n = 0 then one
    else failwith "Negative exponent"

  let ladd cs = L.fold_left ~f:(fun acc c -> add c acc) ~init:zero cs
  let from_int i = R.bn_mod (R.bn_read_str (string_of_int i) ~radix:10) p
  let equal = R.bn_equal
  let compare = R.bn_cmp
  let use_parens = false
end


let make_BilinearGroup (k : int) =

  let module G1 = struct
    type atom = R.g1
      
    type t = atom list
                  
    let atom_add a a' =
      if R.g1_is_infty a then a'
      else if R.g1_is_infty a' then a
      else (g1_add_ref := !g1_add_ref + 1; R.g1_add a a')
    let add t t' = L.map2_exn ~f:atom_add t t'
    let neg t = L.map ~f:R.g1_neg t
    let one = mk_list (R.g1_gen ()) (k+1)
    let zero = mk_list (R.g1_infty ()) (k+1)
    let mul t a =
      if Zp.is_zero a then zero
      else (g1_mul_ref := !g1_mul_ref + k; L.map t ~f:(fun g -> R.g1_mul g a))
    let samp () =
      zp_samp_ref := !zp_samp_ref + k + 1;
      sample_list ~f:R.g1_rand (k+1)

    let atom_gen = R.g1_gen ()
    let atom_from_dlog = R.g1_mul atom_gen
    let to_list g = g
    let from_list g = g

    let sep = "|"
    let to_string g = list_to_string ~sep (L.map g ~f:(fun a -> R.g1_write_bin ~compress:false a |> to_base64))
    let of_string str = from_list (L.map (S.split ~on:(Char.of_string sep) str) ~f:(fun a -> R.g1_read_bin (from_base64 a)))

    let equal a b = Util.equal_lists ~equal:R.g1_equal (to_list a) (to_list b)
  end
  in

  let module G2 = struct
    type atom = R.g2

    type t = atom list
                  
    let atom_add a a' =
      if R.g2_is_infty a then a'
      else if R.g2_is_infty a' then a
      else (g2_add_ref := !g2_add_ref + 1; R.g2_add a a')
    let add t t' = L.map2_exn ~f:atom_add t t'
    let neg t = L.map ~f:R.g2_neg t
    let one = mk_list (R.g2_gen ()) (k+1)
    let zero = mk_list (R.g2_infty ()) (k+1)
    let mul t a =
      if Zp.is_zero a then zero
      else (g2_mul_ref := !g2_mul_ref + k; L.map t ~f:(fun g -> R.g2_mul g a))
    let samp () =
      zp_samp_ref := !zp_samp_ref + k + 1;
      sample_list ~f:R.g2_rand (k+1)

    let atom_gen = R.g2_gen ()
    let atom_from_dlog = R.g2_mul atom_gen
    let to_list h = h
    let from_list h = h

    let sep = "|"
    let to_string g = list_to_string ~sep (L.map g ~f:(fun a -> R.g2_write_bin ~compress:false a |> to_base64))
    let of_string str = from_list (L.map (S.split ~on:(Char.of_string sep) str) ~f:(fun a -> R.g2_read_bin (from_base64 a)))

    let equal a b = Util.equal_lists ~equal:R.g2_equal (to_list a) (to_list b)
  end
  in

  let module Gt = struct
    type t = R.gt
    let add t t' = gt_mul_ref := !gt_mul_ref + 1; R.gt_mul t t'
    let neg t = R.gt_inv t
    let mul t t' = gt_exp_ref := !gt_exp_ref + 1; R.gt_exp t t'
    let one = R.gt_unity ()
    let zero = R.gt_zero ()
    let samp () = zp_samp_ref := !zp_samp_ref + 1; R.gt_rand ()

    let equal = R.gt_equal

    type atom = t
                  
    let atom_gen = R.gt_gen ()
    let atom_from_dlog = R.gt_exp atom_gen
    let to_list h = [h]
    let from_list h = L.hd_exn h

    let to_string g = R.gt_write_bin ~compress:false g |> to_base64
    let of_string str = R.gt_read_bin (from_base64 str)

  end
  in

  (module struct
    let p = Zp.p
    module G1 = G1
    module G2 = G2
    module Gt = Gt
    let e g1 g2 =
      e_map_ref := !e_map_ref + 1;
      let gt_list = L.map2_exn (G1.to_list g1) (G2.to_list g2) ~f:R.e_pairing in
      L.fold_left (L.tl_exn gt_list) ~init:(L.hd_exn gt_list) ~f:Gt.add
  end : BilinearGroup)
