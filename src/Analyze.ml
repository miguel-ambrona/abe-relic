open Core_kernel.Std
open ABE
open Eval
open Abbrevs

let f = function
  | Some t -> t
  | None   -> assert false

let pp_setup pp =
  match pp.pp_scheme with
  | Some CP_ABE ->
     begin match pp.pp_predicate with
     | Some BoolForm(repetitions, and_bound) ->
        let n_attrs = L.length pp.pp_attributes in
        let mpk, msk = PredEncABE.setup (n_attrs * repetitions + and_bound + 1) in
        (mpk, msk)
     | _ -> assert false
     end
  | _ -> assert false
   
let mpk_setup mpk =
  mpk.mpk_pp, ((f mpk.mpk_A, f mpk.mpk_WA, f mpk.mpk_B, f mpk.mpk_WB), f mpk.mpk_mu)

let sk_setup pp sk =
  let y_list = sk.sk_attrs |> Eval.eval_sk_attrs pp.pp_attributes in
  let rep = 
    begin match pp.pp_predicate with
    | Some (BoolForm(n,_)) -> n
    | _ -> failwith "unknown predicate"
    end
  in
  let y = set_attributes ~nattrs:(L.length pp.pp_attributes) ~rep y_list in
  (f sk.sk_k0, f sk.sk_k1), y
  

let ct_setup pp ct =
  let nattrs = L.length pp.pp_attributes in
  let rep = 
    begin match pp.pp_predicate with
    | Some (BoolForm(n,_)) -> n
    | _ -> failwith "unknown predicate"
    end
  in
  let xM = matrix_from_policy ~nattrs ~rep (Eval.eval_policy pp.pp_attributes (f ct.ct_policy)) in
  (f ct.ct_c0, f ct.ct_c1, f ct.ct_c'), xM
