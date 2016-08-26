open Abbrevs

let zp_samp_ref = ref 0
let g1_add_ref  = ref 0
let g2_add_ref  = ref 0
let gt_mul_ref  = ref 0
let g1_mul_ref  = ref 0
let g2_mul_ref  = ref 0
let gt_exp_ref  = ref 0
let e_map_ref   = ref 0

let empty_references () =
  zp_samp_ref := 0;
  g1_add_ref  := 0;
  g2_add_ref  := 0;
  gt_mul_ref  := 0;
  g1_mul_ref  := 0;
  g2_mul_ref  := 0;
  gt_exp_ref  := 0;
  e_map_ref   := 0;
  ()

let print_references () =
  F.printf "Zp_samp: %d,\tG1_add: %d,\tG2_add: %d,\tGt_mul: %d\t" !zp_samp_ref !g1_add_ref !g2_add_ref !gt_mul_ref;
  F.printf "G1_mul: %d,\tG2_mul: %d,\tGt_exp: %d,\te_map: %d\n\n" !g1_mul_ref !g2_mul_ref !gt_exp_ref !e_map_ref;
  F.print_flush ()
       
let rec equal_lists ~equal list1 list2 =
  match list1, list2 with
  | [], [] -> true
  | a1 :: rest1, a2 :: rest2 -> (equal a1 a2) && (equal_lists ~equal rest1 rest2)
  | _ -> false

let list_range i j =
  let rec aux output k =
    if k >= j then output
    else aux (output @ [k]) (k+1)
  in
  aux [] i

let g1_write = R.g1_write_bin ~compress:false
let g2_write = R.g2_write_bin ~compress:false
let gt_write = R.gt_write_bin ~compress:false  

let list_empty_intersection ~equal list1 list2 =
  let rec aux = function
    | [] -> true
    | a :: rest ->
       if L.mem ~equal list1 a then false
       else aux rest
  in
  aux list2

let get_positions_list ~predicate list =
  let rec aux output k = function
    | [] -> output
    | a :: rest ->
       if predicate a then aux (output @ [k]) (k+1) rest
       else aux output (k+1) rest
  in
  aux [] 0 list

let set_positions_list ~positions ~value list =
  let rec aux output k = function
    | [] -> output
    | a :: rest ->
       if L.mem positions k then aux (output @ [value]) (k+1) rest
       else aux (output @ [a]) (k+1) rest
  in
  aux [] 0 list

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_matrix pp_elt f m =
  L.iter m ~f:(F.fprintf f "[%a]\n" (pp_list ", " pp_elt))

let mk_list el n =
  let rec aux output n =
    if n = 0 then output
    else aux (el :: output) (n-1)
  in
  aux [] n

let unzip1 list =
  let (list1,_) = L.unzip list in
  list1

let unzip2 list =
  let (_,list2) = L.unzip list in
  list2

let position_in_list el list =
  let rec aux k =
    if k >= (L.length list) then None
    else if L.nth_exn list k = el then Some k
    else aux (k+1)
  in
  aux 0

let list_to_string ~sep list =
  let rec aux output = function
    | [] -> output
    | s :: [] -> output ^ s
    | s :: rest -> aux (output ^ s ^ sep) rest
  in
  aux "" list

let list_list_to_string ~sep1 ~sep2 list =
  let rec aux output = function
    | [] -> output
    | l :: [] -> output ^ (list_to_string ~sep:sep2 l)
    | l :: rest -> aux (output ^ (list_to_string ~sep:sep2 l) ^ sep1) rest
  in
  (aux "" list)

let get_option_exn = function
  | Some a -> a
  | None -> assert false

let to_base64 ?(split = false) string =
  let string64 = B64.encode string in
  let n = S.length string64 in
  let rec go output k =
    if (n - k < 64) then
      output ^ (S.slice string64 k n)
    else
      go (output ^ (S.slice string64 k (k+64)) ^ "\n") (k+64)
  in
  if not split then string64
  else go "" 0

let from_base64 string64 =
  let string = S.strip string64 in
  B64.decode string

let equal_list eq xs0 ys0 =
  let rec go xs ys =
    match xs,ys with
    | [], []       -> true
    | x::xs, y::ys -> eq x y && go xs ys
    | _            -> assert false
  in
  (L.length xs0 = L.length ys0) && go xs0 ys0

let compare_list cmp xs0 ys0 =
  let rec go xs ys =
    match xs, ys with
    | [], []       -> 0
    | x::xs, y::ys ->
      let d = cmp x y in
      if d <> 0 then d
      else go xs ys
    | _            -> assert false
  in
  let d = L.length xs0 - L.length ys0 in
  if d > 0 then 1
  else if d < 0 then -1
else go xs0 ys0

let equal_pair eq1 eq2 (x1,x2) (y1,y2) =
eq1 x1 y1 && eq2 x2 y2

let compare_pair cmp1 cmp2 (x1,x2) (y1,y2) =
  let r1 = cmp1 x1 y1 in
  if r1 <> 0 then r1
else cmp2 x2 y2


let list_sum ~zero ~add list = L.fold_left list ~init:zero ~f:add

let list_assoc a ab_list =
  L.find_exn ab_list ~f:(fun (a',_) -> a = a') |> snd

let conc_map f xs =
  L.concat (L.map ~f xs)

let cat_Some l =
  let rec go acc = function
    | Some(x)::xs  -> go (x::acc) xs
    | None::xs     -> go acc      xs
    | []           -> L.rev acc
  in
go [] l


let pp_string fmt s = F.fprintf fmt "%s" s

let pp_int fmt i = F.fprintf fmt "%i" i

let list_to_matrix list n =
  let rec aux matrix l =
    if L.length l <= n then matrix @ [l]
    else
      let l1 = L.slice l 0 n in
      let l2 = L.slice l n (L.length l) in
      aux (matrix @ [l1]) l2
  in
  aux [] list
    
let is_initialized = ref false

let init_relic () =
  if !is_initialized then ()
  else
    (assert (R.core_init () = R.sts_ok);
     assert (R.pc_param_set_any () = R.sts_ok);
     is_initialized := true
    )


let extract_random list =
  let rec extract output n = function
    | [] -> raise Not_found
    | a :: rest ->
       if n = 0 then (a, output @ rest)
       else extract (output @ [a]) (n-1) rest
  in
  extract [] (Rand.int (L.length list)) list

let random_permutation ~len list =
  let rec aux output list len =
    if len = 0 then output
    else
      let a, others = extract_random list in
      aux (output @ [a]) others (len-1)
  in
  aux [] list len
