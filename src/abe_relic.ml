(* Main function of the tool *)

open Core_kernel.Std
open Abbrevs
open Printf
open Util
open ABE
open Eval

let split_string_on_word string word =
  let n = String.length word in
  let rec aux k =
    if (k+n >= String.length string) then string, ""
    else if (String.sub string ~pos:k ~len:n) = word then
      (String.sub string ~pos:0 ~len:k),
      (String.sub string ~pos:(k+n) ~len:((String.length string)-(k+n)) )
    else aux (k+1)
  in
  aux 0    

let input_file filename =
  let in_channel = open_in filename in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat ~sep:"\n" (L.rev lines)
 
let search_argument a =
  let rec aux i =
    if Sys.argv.(i) = a then Sys.argv.(i+1)
    else aux (i+1)
  in
  try aux 1 with
  | _ -> raise Not_found

let main =
  let man = F.sprintf "usage: %s\n" Sys.argv.(0) in
  if Array.length Sys.argv = 1 then
    output_string stderr man
  else
    let compress = false in
    match Sys.argv.(1) with
    | "setup" ->
       let pp_file  = try search_argument "-pp"  with | Not_found -> failwith "missing argument -pp" in
       let mpk_file = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let msk_file = try search_argument "-msk" with | Not_found -> failwith "missing argument -msk" in
       let pp = MyParse.pp_cmds (input_file pp_file) |> Eval.eval_pp_cmds in
       let mpk, msk = Analyze.pp_setup pp in
              
       let (g1_A, g1_WA, g2_B, g2_WB), mu_msk = mpk in
       let g1_A_str = L.map g1_A ~f:(L.map ~f:(fun g -> R.g1_write_bin ~compress g |> to_base64)) in
       let g1_WA_str = L.map g1_WA ~f:(L.map ~f:(L.map ~f:(fun g -> R.g1_write_bin ~compress g |> to_base64)))in
       let g2_B_str = L.map g2_B ~f:(L.map ~f:(fun g -> R.g2_write_bin ~compress g |> to_base64)) in
       let g2_WB_str = L.map g2_WB ~f:(L.map ~f:(L.map ~f:(fun g -> R.g2_write_bin ~compress g |> to_base64)))in
       let mu_msk_str = L.map mu_msk ~f:(fun g -> R.gt_write_bin ~compress g |> to_base64) in

       let out_mpk_file = open_out mpk_file in
       fprintf out_mpk_file "%s\n" (Eval.string_of_pp pp);
       fprintf out_mpk_file "A = %s.\n\n" (list_list_to_string g1_A_str);
       fprintf out_mpk_file "WA = %s.\n\n" (list_list_list_to_string g1_WA_str);
       fprintf out_mpk_file "B = %s.\n\n" (list_list_to_string g2_B_str);
       fprintf out_mpk_file "WB = %s.\n\n" (list_list_list_to_string g2_WB_str);
       fprintf out_mpk_file "mu = %s.\n" (list_to_string mu_msk_str);
       let _ = close_out_noerr out_mpk_file in

       let msk_str = L.map msk ~f:(fun g -> R.g2_write_bin ~compress g |> to_base64) in
       let out_msk_file = open_out msk_file in
       fprintf out_msk_file "msk = %s.\n" (list_to_string msk_str);
       let _ = close_out_noerr out_msk_file in
       ()

    | "keygen" ->
       let mpk_file = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let msk_file = try search_argument "-msk" with | Not_found -> failwith "missing argument -msk" in
       let key_attrs = try search_argument "-attrs" with | Not_found -> failwith "missing argument -attrs" in
       let out_file   = try Some (search_argument "-out") with | Not_found -> None in

       let eval_mpk = MyParse.mpk_cmds (input_file mpk_file) |> Eval.eval_mpk_cmds in
       let pp, mpk = Analyze.mpk_setup eval_mpk in

       let eval_msk = MyParse.msk_cmd (input_file msk_file) |> Eval.eval_msk_cmd in
       let msk = eval_msk.msk_key in

       let y_list = MyParse.sk_attrs key_attrs |> Eval.eval_sk_attrs pp.pp_attributes in
       let rep = 
         begin match pp.pp_predicate with
         | Some (BoolForm(n,_)) -> n
         | _ -> failwith "unknown predicate"
         end
       in
       let y = set_attributes ~nattrs:(L.length pp.pp_attributes) ~rep y_list in
       let sk_y =  PredEncABE.keyGen mpk msk y in
       let (k0,k1), _ = sk_y in

       let k0_str = L.map k0 ~f:(fun g -> R.g2_write_bin ~compress g |> to_base64) in
       let k1_str = L.map k1 ~f:(L.map ~f:(fun g -> R.g2_write_bin ~compress g |> to_base64)) in

       let sk_y_str = 
         ("attributes = " ^ key_attrs ^ ".\n\n") ^
         (Format.sprintf "k0 = %s.\n\n" (list_to_string k0_str)) ^
         (Format.sprintf "k1 = %s.\n" (list_list_to_string k1_str))
       in

       begin match out_file with
       | None -> Format.printf "%s\n" sk_y_str
       | Some file -> 
          let out = open_out file in
          fprintf out "%s\n" sk_y_str
       end


    | "encrypt" ->
       let mpk_file   = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let msg_file   = try search_argument "-msg" with | Not_found -> failwith "missing argument -msg" in
       let policy_str = try search_argument "-policy" with | Not_found -> failwith "missing argument -policy" in
       let out_file   = try Some (search_argument "-out") with | Not_found -> None in

       let eval_mpk = MyParse.mpk_cmds (input_file mpk_file) |> Eval.eval_mpk_cmds in
       let pp, mpk = Analyze.mpk_setup eval_mpk in
       
       let ev_policy = MyParse.policy_cmd policy_str in
       let nattrs = L.length pp.pp_attributes in
       let rep = 
         begin match pp.pp_predicate with
         | Some (BoolForm(n,_)) -> n
         | _ -> failwith "unknown predicate"
         end
       in
       let xM = matrix_from_policy ~nattrs ~rep (Eval.eval_policy pp.pp_attributes ev_policy) in
       let gt_msg = R.gt_rand () in

       let ct_x = PredEncABE.enc mpk xM gt_msg in
       let (c0, c1, c), _ = ct_x in
       let password = SHA.sha256 (R.gt_write_bin ~compress gt_msg |> to_base64) in
       AES.encrypt ~key:password ~in_file:msg_file ~out_file;

       let c0_str = L.map c0 ~f:(fun g -> R.g1_write_bin ~compress g |> to_base64) in
       let c1_str = L.map c1 ~f:(L.map ~f:(fun g -> R.g1_write_bin ~compress g |> to_base64)) in
       let c_str = R.gt_write_bin ~compress c |> to_base64 in

       begin match out_file with
       | None -> ()
       | Some file ->
          let ciphertext_str =
            "___BEGIN_ABE_CIPHERTEXT___" ^
              (Format.sprintf "\npolicy = %s.\\n\\n" (Eval.string_of_eval_policy ev_policy)) ^
              (Format.sprintf "c0 = %s.\\n\\n" (list_to_string c0_str)) ^
              (Format.sprintf "c1 = %s.\\n\\n" (list_list_to_string c1_str)) ^
              (Format.sprintf "c* = %s.\\n"    (c_str)) ^
            "___END_ABE_CIPHERTEXT___"
          in

          let command = Format.sprintf "printf '%s' >> %s" ciphertext_str file in
          let _ = Unix.open_process command in
          ()
       end

    | "decrypt" ->
       let mpk_file = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let sk_file  = try search_argument "-sk" with | Not_found -> failwith "missing argument -sk" in
       let ct_file  = try search_argument "-ct" with | Not_found -> failwith "missing argument -ct" in
       let out_file = try Some (search_argument "-out") with | Not_found -> None in

       let sep = "___BEGIN_ABE_CIPHERTEXT___"  in

       let aes_ct, abe_ct = split_string_on_word (input_file ct_file) sep in
       
       let eval_mpk = MyParse.mpk_cmds (input_file mpk_file) |> Eval.eval_mpk_cmds in
       let pp, mpk = Analyze.mpk_setup eval_mpk in

       let eval_sk = MyParse.sk_cmds (input_file sk_file) |> Eval.eval_sk_cmds in
       let sk_y = Analyze.sk_setup pp eval_sk in

       let eval_ct = MyParse.ct_cmds (sep ^ abe_ct) |> Eval.eval_ct_cmds in
       let ct_x = Analyze.ct_setup pp eval_ct in

       let command = Format.sprintf "printf '%s' > %s" aes_ct "/tmp/aux.txt" in
       let _ = Unix.open_process command in

       let gt_msg = PredEncABE.dec mpk sk_y ct_x in
       let password = SHA.sha256 (R.gt_write_bin ~compress gt_msg |> to_base64) in
       AES.decrypt ~key:password ~in_file:"/tmp/aux.txt" ~out_file

    | _ -> output_string stderr man
