open Core_kernel.Std
open Abbrevs
open Util
open BoolForms

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

type encoding =
  | PredicateEncoding

let string_of_encoding = function
  | PredicateEncoding -> "PREDICATE_ENCODING"

type public_parameters = { 
  pp_scheme: scheme_type option;
  pp_encoding : encoding option;
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
        ("attributes = " ^ (list_to_string ~sep:"," pp.pp_attributes) ^ ".\n")
     end

let empty_pp = {
  pp_scheme = None;
  pp_encoding = None;
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
  mpk_key: string option;
}

let empty_mpk = {
  mpk_pp = empty_pp;
  mpk_key = None;
}

type mpk_cmd =
  | Pp of pp_cmd
  | Mpk of string

let eval_mpk_cmd cmd mpk =
  match cmd with
  | Pp (pp_cmd) -> { mpk with mpk_pp = eval_pp_cmd pp_cmd mpk.mpk_pp }
  | Mpk (s)     -> { mpk with mpk_key = Some s }

let eval_mpk_cmds cmds =
  let mpk = L.fold_left cmds ~init:empty_mpk ~f:(fun mpk' cmd -> eval_mpk_cmd cmd mpk') in
  (match mpk.mpk_pp.pp_scheme, mpk.mpk_pp.pp_predicate with
  | None, _ -> failwith "Unspecified scheme"
  | _, None -> failwith "Unspecified predicate"
  | _ -> ()
  );
  match mpk.mpk_key with
  | None -> failwith "Unspecified master public key data"
  | _ -> mpk

type msk = {
  msk_key: string option;
}

let empty_msk = {
  msk_key = None;
}

type msk_cmd =
  | Msk of string

let eval_msk_cmd cmd =
  match cmd with
  | Msk (s) -> { msk_key = Some s }

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
  sk_key : string option;
}

let empty_sk = {
  sk_attrs = [];
  sk_key = None;
}

type sk_cmd =
  | SK_Attrs of string list
  | SK_Key of string

let eval_sk_cmd cmd sk =
  match cmd with
  | SK_Attrs (l) -> { sk with sk_attrs = l }
  | SK_Key (s)   -> { sk with sk_key = Some s }

let eval_sk_cmds cmds =
  let sk = L.fold_left cmds ~init:empty_sk ~f:(fun sk' cmd -> eval_sk_cmd cmd sk') in
  match sk.sk_key with
  | None -> failwith "Unspecified secret key data"
  | _ -> sk


type ct = {
  ct_policy : eval_policy option;
  ct_cipher : string option;
}

let empty_ct = {
  ct_policy = None;
  ct_cipher = None;
}

type ct_cmd =
  | CT_Policy of eval_policy
  | CT_Cipher of string

let eval_ct_cmd cmd ct = 
  match cmd with
  | CT_Policy (p) -> { ct with ct_policy = Some p }
  | CT_Cipher (s) -> { ct with ct_cipher = Some s }

let eval_ct_cmds cmds =
  let ct = L.fold_left cmds ~init:empty_ct ~f:(fun ct' cmd -> eval_ct_cmd cmd ct') in
  match ct.ct_policy, ct.ct_cipher with
  | None, _ -> failwith "Unspecified policy"
  | _, None -> failwith "Unspecified ciphertext data"
  | _ -> ct
