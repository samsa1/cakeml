(*
Script for Huffman encodings.
*)

open preamble;
open listTheory  rich_listTheory;
open optionTheory;
open pairTheory;
open arithmeticTheory;
open ringBufferTheory;

val _ = new_theory"huffman";


(******************************************
               Frequencies
*******************************************)

Definition get_freq_def:
  get_freq []      ls = ls ∧
  get_freq (s::ss) ls =
  let
    ls' = (case ALOOKUP ls s of
             NONE => (s,1:num)::ls
           | SOME v => AFUPDKEY s (λ a. a + 1) ls)
  in
    get_freq ss ls'
End

Definition get_frequencies_def:
  get_frequencies input = get_freq input []
End

Definition sort_frequencies_def:
  sort_frequencies ls = QSORT (λ (_,(f1:num)) (_,(f2:num)). f1 < f2) ls
End

(******************************************
             Huffman tree
*******************************************)


Datatype:
  Tree = Empty | Leaf α | Node Tree Tree
End

Definition convert_frequencies_def:
  convert_frequencies ls = MAP (λ (c,(f:num)). (Leaf c, f)) ls
End

Definition create_tree_def:
  create_tree ((c,f)::[]) = [(c,f)] ∧
  create_tree ((c1,f1)::(c2,f2)::ls) =
  (let
     nn = (Node c1 c2, f1+f2)
   in
    create_tree (sort_frequencies (nn::ls)))
Termination
  WF_REL_TAC ‘measure $ λ ls. LENGTH ls’
  \\ rw[sort_frequencies_def]
End

Definition build_huffman_tree_def:
  build_huffman_tree s =
  (let
     freqs = sort_frequencies (convert_frequencies (get_frequencies s))
   in
     FST (HD (create_tree freqs)))
End

(******************************************
              Huffman encoding
*******************************************)

Definition get_huffman_codes_def:
    get_huffman_codes (Leaf c) code ls = (c,code)::ls ∧
    get_huffman_codes (Node ltr rtr) code ls =
    let
      left = get_huffman_codes ltr (code++[F]) ls;
      right = get_huffman_codes rtr (code++[T]) ls
    in
        (left++right)
End

Definition encode_def:
  encode [] ls = [] ∧
  encode (s::ss) ls =
  let
    res = ALOOKUP ls s
  in
    case res of
      NONE => []
    | SOME b => b++encode ss ls
End

Definition huff_enc_dyn_def:
  huff_enc_dyn l =
  let
    huff_tree = build_huffman_tree l;
    assoc_list = get_huffman_codes huff_tree [] [];
  in
    (huff_tree, assoc_list)
End

(*EVAL “huff_enc_dyn ( MAP encode_LZSS_len  [Lit #"a"; Lit #"a"; Lit #"b"; Lit #"c"; Lit #"c"; Lit #"c"; Lit #"d"])”;*)
EVAL “huff_enc_dyn (MAP ORD "aabcccd")”;



(******************************************
             Huffman decoding
*******************************************

Definition decode_char_def:
  decode_char Empty _ = NONE ∧
  decode_char (Leaf c) [] = SOME c ∧
  decode_char (Node ltr rtr) [] = NONE ∧
  decode_char (Node ltr rtr) (x::xs) =
  case x of
    T => decode_char ltr xs
  | F => decode_char rtr xs
End

Definition decode_def:
  decode tree ((b::bs) :bool list) ([]   :bool list) = (decode tree bs [b]) ∧
  decode tree ([]      :bool list) (code :bool list) = (
    let
      res = decode_char tree code
    in
      case res of
        NONE     => []
      | SOME (r) => [r]) ∧
  decode tree ((b::bs) :bool list) (code :bool list) = (
    let
      res = decode_char tree code
    in
      case res of
        NONE     => decode tree bs (code++[b])
      | SOME (r) => [r]++(decode tree bs [b]))
End

EVAL “let
        (tree, code) = huff_enc_dyn [Lit #"a"; Lit #"a"; Lit #"b"; Lit #"c"; Lit #"c"; Lit #"c"; Lit #"d"]
      in
     decode tree code []”;

Definition huffman_decoding_def:
  huffman_decoding (tree, code) =   decode tree code []
End

*)


(******************************************
         Canonical huffman codes
******************************************)


Definition gen_zero_codes_def:
  gen_zero_codes l 0 = APPEND [(0,[])] l ∧
  gen_zero_codes (l: (num # bool list) list) (n: num) =
  if (0 < n)
  then (gen_zero_codes (APPEND [(n,[])] l) (n-1))
  else (l)
End



Definition fill_assoc_list_def:
  fill_assoc_list gs [] = gs ∧
  fill_assoc_list [] ls = [] ∧
  fill_assoc_list ((n1,bl1)::gs) ((n2,bl2)::ls) =
  if (n1 = n2)
  then ([(n1, bl2)] ++ fill_assoc_list gs ls)
  else ([(n1, bl1)] ++ fill_assoc_list gs ((n2,bl2)::ls))
End

Definition complete_assoc_list_def:
  complete_assoc_list ls =
  let
    gs = gen_zero_codes [] 287;
    as = QSORT (λ (a,_) (b,_). a < b) ls;
  in
    fill_assoc_list gs as
End

Definition len_from_codes_def:
  len_from_codes [] = [] ∧
  len_from_codes ((n,bl)::ns) =
  LENGTH bl :: len_from_codes ns
End

Definition all_lens_def:
  all_lens as = len_from_codes (complete_assoc_list as)
End


Overload MAX_CODE_LENGTH = “16 :num”

Definition bl_count_aux_def:
  bl_count_aux [] (bl: num list) = LUPDATE 0 0 bl ∧
  bl_count_aux (x::xs) bl =
  let
val = EL x bl;
new_bl = LUPDATE (SUC val) x bl
  in
    bl_count_aux xs new_bl
End

Definition bl_count_def:
  bl_count l = bl_count_aux l (GENLIST (λ x. 0) MAX_CODE_LENGTH)
End

EVAL “bl_count [3;3;3;3;3;2;4;4]”;

Definition next_code_aux_def:
  next_code_aux max (n:num) (code:num) bl codes =
  if n < max
  then
      let
         code = (code + (EL (n-1) bl)) * 2
       in
         next_code_aux max (SUC n) code bl (SNOC code codes)
  else
      codes
Termination
  WF_REL_TAC ‘measure $ λ(max, s, _, _, _). max - s’
End

Definition index_largest_nonzero_def:
  index_largest_nonzero ([]: num list) (ci:num) (hi:num) = hi ∧
  index_largest_nonzero (x::xs) ci hi =
  let
    i = if x = 0 then hi else ci
  in
      index_largest_nonzero xs (1 + ci) i
End

Definition next_code_def:
  next_code (bl:num list) =
  let
    max = index_largest_nonzero bl 0 0
  in
    next_code_aux (max+1) 1 0 bl [0]
End

EVAL “next_code (bl_count [3;3;3;3;3;2;4;4])”;

(*  From kraft_ineq  *)
Definition inv_tbl2n_def:
  inv_tbl2n 0n = [] /\
  inv_tbl2n a = if EVEN a then [F]++(inv_tbl2n (a DIV 2))
                else [T]++(inv_tbl2n ((a-1) DIV 2 ))
Termination
  WF_REL_TAC‘$<’ >> rw[]>>
  irule LESS_EQ_LESS_TRANS >> qexists_tac‘v’ >> ‘0<2n’ by simp[] >>
  rw[DIV_LE_MONOTONE,DIV_LESS,DIV_LESS_EQ]
End

(* binary numbers in big-endian format *)
Overload TN2BL = “\n. REVERSE (inv_tbl2n n)”

Definition pad0_def:
  pad0 n bl = PAD_LEFT F n bl
End

Definition len_from_codes_inv_aux_def:
  len_from_codes_inv_aux  []     n nc = [] ∧
  len_from_codes_inv_aux (0::ls) n nc = len_from_codes_inv_aux ls (SUC n) nc ∧
  len_from_codes_inv_aux (l::ls) n nc =
  let
    code = EL l nc;
    nc = LUPDATE (SUC code) l nc;
  in
      (n, pad0 l (TN2BL code)) :: len_from_codes_inv_aux ls (SUC n) nc
End

Definition len_from_codes_inv_def:
  len_from_codes_inv ls =
  let
    nc = next_code (bl_count ls)
  in
    len_from_codes_inv_aux ls 0 nc
End

EVAL “
 let
   ls = [3;3;3;3;3;2;4;4];
 in
   len_from_codes_inv ls
    ”;


(* EVAL that tests whether the tree we create from length list is equal to original tree *)
EVAL “ let
   s = MAP ORD "abbbbd";
   (tree, as) = huff_enc_dyn s;
   ls = all_lens as;
   cs = len_from_codes_inv ls;
 in
   (as, cs)”;

(*****************************************
            Unique huff tree
*****************************************)

Definition unique_huff_codes_def:
  unique_huff_tree (l:num list)  =
  let
    huff_tree = build_huffman_tree l;
    assoc_list = get_huffman_codes huff_tree [] [];
    ls = all_lens assoc_list;
    cs = len_from_codes_inv ls;
  in
    cs
End

EVAL “unique_huff_tree (MAP ORD "aaaaccb")”;

val _ = export_theory();
