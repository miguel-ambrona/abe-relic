open Core_kernel.Std
open ABE
open Eval
open Abbrevs
open DualSystemG
open MakeAlgebra
open MakePredEnc
open MakePairEnc
open Predicates

let abe_from_pp pp =
  let module B = (val make_BilinearGroup 2) in
  let module DSG = Hoeteck's_DSG in
  match pp.pp_scheme, pp.pp_encoding, pp.pp_predicate with
  | Some CP_ABE, Some PredicateEncoding, Some BoolForm(_,_,_) ->
     let module PE = (val make_BF_PredEnc 3) in
     (module PredEncABE (B) (DSG) (PE) : ABE)
  | Some CP_ABE, Some PairEncoding, Some BoolForm(n1,n2,t) ->
     let module PE = (val make_BF_PairEnc n1 (n2+1) t) in
     (module PairEncABE (B) (DSG) (PE) : ABE)
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
  | Some PredicateEncoding, Some BoolForm(rep,and_gates,_) ->
     BoolForm_Policy(L.length pp.pp_attributes, rep, and_gates, policy)

  | Some PairEncoding, Some BoolForm(n1,n2,_) ->
     BoolForm_Policy(n1, n2, 0, policy)

  | None, _ -> failwith "encoding not provided"
  | _, None -> failwith "predicate not provided"
