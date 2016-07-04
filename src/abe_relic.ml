(* Main function of the tool *)

open Core_kernel.Std
open Abbrevs
open Printf
open Util
open ABE
open Eval
open DualSystemG
open MakeAlgebra
open PredEnc

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
  let module DSG = Hoeteck's_DSG in
  let module PE = Boolean_Formula_PredEnc in
  let module B = (val make_BilinearGroup 2) in

  let module ABE = PredEncABE (B) (DSG) (PE) in

  let man = F.sprintf "usage: %s\n" Sys.argv.(0) in
  if Array.length Sys.argv = 1 then
    output_string stderr man
  else
    match Sys.argv.(1) with
    | "setup" ->
       let pp_file  = try search_argument "-pp"  with | Not_found -> failwith "missing argument -pp" in
       let mpk_file = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let msk_file = try search_argument "-msk" with | Not_found -> failwith "missing argument -msk" in
       let pp = Parse.pp_cmds (input_file pp_file) |> Eval.eval_pp_cmds in

       let module ABE = (val Analyze.abe_from_pp pp) in
       let n = Analyze.get_setup_size pp in
       let mpk, msk = ABE.setup ~n () in
              
       let out_mpk_file = open_out mpk_file in
       fprintf out_mpk_file "%s\nmpk = %s." (Eval.string_of_pp pp) (ABE.string_of_mpk mpk);
       let _ = close_out_noerr out_mpk_file in

       let out_msk_file = open_out msk_file in
       fprintf out_msk_file "msk = %s." (ABE.string_of_msk msk);
       let _ = close_out_noerr out_msk_file in
       ()

    | "keygen" ->
       let mpk_file = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let msk_file = try search_argument "-msk" with | Not_found -> failwith "missing argument -msk" in
       let out_file   = try Some (search_argument "-out") with | Not_found -> None in

       let eval_mpk = Parse.mpk_cmds (input_file mpk_file) |> Eval.eval_mpk_cmds in
       let eval_msk = Parse.msk_cmd (input_file msk_file) |> Eval.eval_msk_cmd in

       let pp = eval_mpk.mpk_pp in

       let module ABE = (val Analyze.abe_from_pp pp) in
       let mpk = ABE.mpk_of_string (get_option_exn eval_mpk.mpk_key) in
       let msk = ABE.msk_of_string (get_option_exn eval_msk.msk_key) in

       let y = match pp.pp_scheme with
         | Some CP_ABE ->
            let key_attrs = try search_argument "-attrs" with | Not_found -> failwith "missing argument -attrs" in
            let eval_sk = Parse.sk_attrs key_attrs |> Eval.eval_sk_attrs pp.pp_attributes in
            ABE.set_y (Analyze.set_attributes pp eval_sk)
         | None -> failwith "scheme not provided"
       in
       let sk_y = ABE.keyGen mpk msk y in
       let sk_y_str = "sk = " ^ (ABE.string_of_sk sk_y) ^ "." in

       begin match out_file with
       | None -> Format.printf "%s\n" sk_y_str
       | Some file -> 
          let out = open_out file in
          fprintf out "%s\n" sk_y_str;
          let _ = close_out_noerr out in
          ()
       end

    | "encrypt" ->
       let mpk_file   = try search_argument "-mpk" with | Not_found -> failwith "missing argument -mpk" in
       let msg_file   = try search_argument "-msg" with | Not_found -> failwith "missing argument -msg" in
       let out_file   = try Some (search_argument "-out") with | Not_found -> None in

       let eval_mpk = Parse.mpk_cmds (input_file mpk_file) |> Eval.eval_mpk_cmds in

       let pp = eval_mpk.mpk_pp in

       let module ABE = (val Analyze.abe_from_pp pp) in
       let mpk = ABE.mpk_of_string (get_option_exn eval_mpk.mpk_key) in
       
       let x = match pp.pp_scheme with
         | Some CP_ABE ->
            let policy_str = try search_argument "-policy" with | Not_found -> failwith "missing argument -policy" in
            let eval_policy = Parse.policy_cmd policy_str |> Eval.eval_policy pp.pp_attributes in
            ABE.set_x (Analyze.set_policy pp eval_policy)
         | None -> failwith "scheme not provided"
       in

       let gt_msg = ABE.rand_msg () in

       let ct_x = ABE.enc mpk x gt_msg in
       let ct_x_str = "ct = " ^ (ABE.string_of_ct ct_x) ^ "." in

       let password = SHA.sha256 (ABE.string_of_msg gt_msg) in
       AES.encrypt ~key:password ~in_file:msg_file ~out_file;

       begin match out_file with
       | None -> ()
       | Some file ->
          let ciphertext_str =
            "___BEGIN_ABE_CIPHERTEXT___" ^
            (Format.sprintf "\n%s\\n" ct_x_str) ^
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
       
       let eval_mpk = Parse.mpk_cmds (input_file mpk_file) |> Eval.eval_mpk_cmds in
       
       let pp = eval_mpk.mpk_pp in
       
       let module ABE = (val Analyze.abe_from_pp pp) in
       let mpk = ABE.mpk_of_string (get_option_exn eval_mpk.mpk_key) in
       
       let eval_sk = Parse.sk_cmds (input_file sk_file) |> Eval.eval_sk_cmd in
       let sk_y = ABE.sk_of_string (get_option_exn eval_sk.sk_key) in

       let eval_ct = Parse.ct_cmds (sep ^ abe_ct) |> Eval.eval_ct_cmd in
       let ct_x = ABE.ct_of_string (get_option_exn eval_ct.ct_cipher) in

       let command = Format.sprintf "printf '%s' > %s" aes_ct "/tmp/aux.txt" in
       let _ = Unix.open_process command in

       let gt_msg = ABE.dec mpk sk_y ct_x in
       let password = SHA.sha256 (ABE.string_of_msg gt_msg) in
       AES.decrypt ~key:password ~in_file:"/tmp/aux.txt" ~out_file

    | _ -> output_string stderr man
