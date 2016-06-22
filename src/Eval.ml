open Core_kernel.Std
open Abbrevs
open Util
open BoolForms

module R = Relic

(* ** Interpret public parameters *)

type scheme_type =
  | CP_ABE

let string_of_scheme_type = function
  | CP_ABE -> "CP_ABE"

type predicate_type =
  | BoolForm of int * int

let string_of_predicate_type = function
  | BoolForm (n,b) ->
     "boolean_formula(" ^ (string_of_int n) ^ " repetitions, " ^ (string_of_int b) ^ " and-gates)"

type public_parameters = { 
  pp_scheme: scheme_type option;
  pp_predicate: predicate_type option;
  pp_attributes: string list;
}

let string_of_pp pp =
  match pp.pp_scheme with
  | None -> "undefined scheme"
  | Some scheme -> "scheme = " ^ (string_of_scheme_type scheme) ^ ".\n" ^
     begin match pp.pp_predicate with
     | None -> "undefined predicate"
     | Some predicate -> "predicate = " ^ (string_of_predicate_type predicate) ^ ".\n" ^
        ("attributes = " ^ (list_to_string pp.pp_attributes) ^ ".\n")
     end

let empty_pp = {
  pp_scheme = None;
  pp_predicate = None;
  pp_attributes = [];
}

type pp_cmd =
  | Scheme of string
  | Predicate of predicate_type
  | Attributes of string list

let eval_pp_cmd cmd pp =
  match cmd with
  | Scheme(s) ->
     begin match s with
     | "CP_ABE" -> { pp with pp_scheme = Some CP_ABE; }
     | _ -> failwith "Unknown scheme type"
     end

  | Predicate(p) ->
     { pp with pp_predicate = Some p; }

  | Attributes(l) ->
     { pp with pp_attributes = pp.pp_attributes @ l; }

let eval_pp_cmds cmds =
  let pp = L.fold_left cmds ~init:empty_pp ~f:(fun pp' cmd -> eval_pp_cmd cmd pp') in
  match pp.pp_scheme, pp.pp_predicate with
  | None, _ -> failwith "Unspecified scheme"
  | _, None -> failwith "Unspecified predicate"
  | _ -> pp

type mpk = { 
  mpk_pp: public_parameters;
  mpk_A:  (R.g1 list list) option;
  mpk_WA: (R.g1 list list list) option;
  mpk_B:  (R.g2 list list) option;
  mpk_WB: (R.g2 list list list) option;
  mpk_mu: (R.gt list) option;
}

let empty_mpk = {
  mpk_pp = empty_pp;
  mpk_A  = None;
  mpk_WA = None;
  mpk_B  = None;
  mpk_WB = None;
  mpk_mu = None;
}

type mpk_cmd =
  | A_matrix of string list list
  | WA_matrix of string list list list
  | B_matrix of string list list
  | WB_matrix of string list list list
  | Mu_msk of string list
  | PP of pp_cmd

let group_read ~r string = r (Util.from_base64 string)

let eval_mpk_cmd cmd mpk =
  match cmd with
  | A_matrix (l)  -> { mpk with mpk_A = Some (L.map l ~f:(L.map ~f:(group_read ~r:R.g1_read_bin))) }
  | WA_matrix (l) -> { mpk with mpk_WA = Some (L.map l ~f:(L.map ~f:(L.map ~f:(group_read ~r:R.g1_read_bin)))) }
  | B_matrix (l)  -> { mpk with mpk_B = Some (L.map l ~f:(L.map ~f:(group_read ~r:R.g2_read_bin))) }
  | WB_matrix (l) -> { mpk with mpk_WB = Some (L.map l ~f:(L.map ~f:(L.map ~f:(group_read ~r:R.g2_read_bin)))) }
  | Mu_msk (l)    -> { mpk with mpk_mu = Some (L.map l ~f:(group_read ~r:R.gt_read_bin)) }
  | PP (pp_cmd)   -> { mpk with mpk_pp = eval_pp_cmd pp_cmd mpk.mpk_pp }

let eval_mpk_cmds cmds =
  let mpk = L.fold_left cmds ~init:empty_mpk ~f:(fun mpk' cmd -> eval_mpk_cmd cmd mpk') in
  (match mpk.mpk_pp.pp_scheme, mpk.mpk_pp.pp_predicate with
  | None, _ -> failwith "Unspecified scheme"
  | _, None -> failwith "Unspecified predicate"
  | _ -> ()
  );
  match mpk.mpk_A, mpk.mpk_WA, mpk.mpk_B, mpk.mpk_WB, mpk.mpk_mu with
  | None, _, _, _, _ -> failwith "Unspecified A matrix"
  | _, None, _, _, _ -> failwith "Unspecified WA matrices"
  | _, _, None, _, _ -> failwith "Unspecified B matrix"
  | _, _, _, None, _ -> failwith "Unspecified WB matrices"
  | _, _, _, _, None -> failwith "Unspecified mu of msk"
  | _ -> mpk

type msk = {
  msk_key: (R.g2 list);
}

type msk_cmd =
  | Msk of string list

let eval_msk_cmd cmd =
  match cmd with
  | Msk (l) -> { msk_key = (L.map l ~f:(group_read ~r:R.g2_read_bin)) }

type eval_policy = 
  | Eval_OR of eval_policy * eval_policy
  | Eval_AND of eval_policy * eval_policy
  | Eval_leaf of string

let rec string_of_eval_policy = function
  | Eval_OR (p1,p2)  -> "(" ^ (string_of_eval_policy p1) ^ " or " ^ (string_of_eval_policy p2) ^ ")"
  | Eval_AND (p1,p2) -> "(" ^ (string_of_eval_policy p1) ^ " and " ^ (string_of_eval_policy p2) ^ ")"
  | Eval_leaf (s) -> s

let rec eval_policy attributes = function
  | Eval_OR  (p1,p2) ->  Or(eval_policy attributes p1, eval_policy attributes p2)
  | Eval_AND (p1,p2) -> And(eval_policy attributes p1, eval_policy attributes p2)
  | Eval_leaf (s) ->
     begin match Util.position_in_list s attributes with
     | None -> failwith ("undefined attribute " ^ s)
     | Some k -> Leaf(Att(k+1))
     end

let eval_sk_attrs attributes key_attrs =
  L.map key_attrs ~f:(fun s -> match Util.position_in_list s attributes with
  | Some i -> Leaf(Att(i+1))
  | _ -> failwith ("unknown attribute " ^ s))

type sk = {
  sk_attrs : string list;
  sk_k0 : (R.g2 list) option;
  sk_k1 : (R.g2 list list) option;
}

let empty_sk = {
  sk_attrs = [];
  sk_k0 = None;
  sk_k1 = None;
}

type sk_cmd =
  | SK_Attrs of string list
  | SK_K0 of string list
  | SK_K1 of string list list

let eval_sk_cmd cmd sk = 
  match cmd with
  | SK_Attrs (l) -> { sk with sk_attrs = l }
  | SK_K0 (l)    -> { sk with sk_k0 = Some (L.map l ~f:(group_read ~r:R.g2_read_bin)) }
  | SK_K1 (l)    -> { sk with sk_k1 = Some (L.map l ~f:(L.map ~f:(group_read ~r:R.g2_read_bin))) }

let eval_sk_cmds cmds =
  let sk = L.fold_left cmds ~init:empty_sk ~f:(fun sk' cmd -> eval_sk_cmd cmd sk') in
  match sk.sk_k0, sk.sk_k1 with
  | None, _ -> failwith "Unspecified k0"
  | _, None -> failwith "Unspecified k1"
  | _ -> sk


type ct = {
  ct_policy : eval_policy option;
  ct_c0 : (R.g1 list) option;
  ct_c1 : (R.g1 list list) option;
  ct_c' : R.gt option;
}

let empty_ct = {
  ct_policy = None;
  ct_c0 = None;
  ct_c1 = None;
  ct_c' = None
}

type ct_cmd =
  | CT_Policy of eval_policy
  | CT_C0 of string list
  | CT_C1 of string list list
  | CT_CT of string

let eval_ct_cmd cmd ct = 
  match cmd with
  | CT_Policy (p) -> { ct with ct_policy = Some p }
  | CT_C0 (l)     -> { ct with ct_c0 = Some (L.map l ~f:(group_read ~r:R.g1_read_bin)) }
  | CT_C1 (l)     -> { ct with ct_c1 = Some (L.map l ~f:(L.map ~f:(group_read ~r:R.g1_read_bin))) }
  | CT_CT (s)     -> { ct with ct_c' = Some (group_read s ~r:R.gt_read_bin) }

let eval_ct_cmds cmds =
  let ct = L.fold_left cmds ~init:empty_ct ~f:(fun ct' cmd -> eval_ct_cmd cmd ct') in
  match ct.ct_policy, ct.ct_c0, ct.ct_c1, ct.ct_c' with
  | None, _, _, _ -> failwith "Unspecified policy"
  | _, None, _, _ -> failwith "Unspecified c0"
  | _, _, None, _ -> failwith "Unspecified c1"
  | _, _, _, None -> failwith "Unspecified c'"
  | _ -> ct
