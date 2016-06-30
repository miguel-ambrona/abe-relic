open Core_kernel.Std
open ABE
open Eval
open Abbrevs
open DualSystemG
open MakeAlgebra
open PredEnc
open PairEnc
open Predicates

let abe_from_pp pp =
  let module B = (val make_BilinearGroup 2) in
  let module DSG = Hoeteck's_DSG in
  match pp.pp_scheme, pp.pp_encoding, pp.pp_predicate with
  | Some CP_ABE, Some PredicateEncoding, Some BoolForm(_,_,_) -> 
     (module PredEncABE (B) (DSG) (Boolean_Formula_PredEnc) : ABE)
  | Some CP_ABE, Some PairEncoding, Some BoolForm(n1,n2,t) ->
     let module Par = struct
         let par_n1 = n1
         let par_n2 = n2
         let par_T = t
     end
     in
     (module PairEncABE (B) (DSG) (Boolean_Formula_PairEnc (Par)) : ABE)
  | None, _, _ -> failwith "scheme not provided"
  | _, None, _ -> failwith "encoding not provided"
  | _, _, None -> failwith "predicate not provided"

let get_setup_size pp =
  match pp.pp_scheme, pp.pp_encoding, pp.pp_predicate with
  | Some CP_ABE, Some PredicateEncoding, Some BoolForm(rep, and_gates, _) -> 
     (L.length pp.pp_attributes) * rep * and_gates + 1

  | Some CP_ABE, Some PairEncoding, Some BoolForm(_, _, _) ->
     0 (* PairEncoding automatically allocates size *)

  | None, _, _ -> failwith "scheme not provided"
  | _, None, _ -> failwith "encoding not provided"
  | _, _, None -> failwith "predicate not provided"

let set_attributes pp attrs =
  match pp.pp_encoding, pp.pp_predicate with
  | Some PredicateEncoding, Some BoolForm(rep,_,_) ->
     BoolForm_Attrs(L.length pp.pp_attributes, rep, attrs)

  | Some PairEncoding, Some BoolForm(_,_,_) ->
     BoolForm_Attrs(0, 0, attrs)

  | None, _ -> failwith "encoding not provided"
  | _, None -> failwith "predicate not provided"

let set_policy pp policy =
  match pp.pp_encoding, pp.pp_predicate with
  | Some PredicateEncoding, Some BoolForm(rep,_,_) ->
     BoolForm_Policy(L.length pp.pp_attributes, rep, policy)

  | Some PairEncoding, Some BoolForm(n1,n2,_) ->
     BoolForm_Policy(n1, n2, policy)

  | None, _ -> failwith "encoding not provided"
  | _, None -> failwith "predicate not provided"


(*
let pp_setup pp =
  let module DSG = Hoeteck's_DSG in
  let module PE = Boolean_Formula_PredEnc in
  let module B = (val make_BilinearGroup 10) in

  let module ABE = PredEncABE (B) (DSG) (PE) in
  match pp.pp_scheme with
  | Some CP_ABE ->
     begin match pp.pp_predicate with
     | Some BoolForm(repetitions, and_bound) ->
        let n_attrs = L.length pp.pp_attributes in
        let mpk, msk = ABE.setup ~n:(n_attrs * repetitions + and_bound + 1) () in
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
  let y = set_attributes ~one:Zp.one ~zero:Zp.zero ~nattrs:(L.length pp.pp_attributes) ~rep y_list in
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
  *)
