(*
Script for Huffman encodings.
*)

open preamble;

open listTheory  rich_listTheory;
open optionTheory;
open pairTheory;
open arithmeticTheory;
open ringBufferTheory;
open LZSSrbTheory;

val _ = new_theory"huffman";


Datatype:
  Tree = Leaf α | Node Tree Tree
End


(******************************************
               Frequencies
*******************************************)

Definition get_freq_def:
  get_freq [] ls = ls ∧
  get_freq (s::ss) ls =
  let
    ls' = (case ALOOKUP ls s of
             NONE => (s,1:num)::ls
           | SOME n => AFUPDKEY s (λ n. n + 1) ls)
  in
    get_freq ss ls'
End

Definition get_frequencies_def:
  get_frequencies (input:string) = get_freq input []
End

Definition convert_frequencies_def:
  convert_frequencies ls = MAP (λ (c,(f:num)). (Leaf c, f)) ls
End

Definition sort_frequencies_def:
  sort_frequencies ls = QSORT (λ (_,(f1:num)) (_,(f2:num)). f1 < f2) ls
End


(******************************************
             Huffman tree
*******************************************)

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
  build_huffman_tree (s:string) =
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
      left = get_huffman_codes ltr (T::code) ls;
      right = get_huffman_codes rtr (F::code) ls
    in
        (left++right)
End

Definition huffman_encoding_def:
  huffman_encoding s =
  let
    huff_tree = build_huffman_tree s
  in
    (huff_tree, get_huffman_codes huff_tree [] [])
End

(* EVAL “huffman_encoding "aaaaaaaaaaaabbcdddddddddddddddddddddddrrrrrrrrrrrrrrrrrrrrrrrrrrrr"”
   gives: [(#"r",[T]); (#"c",[T; T; T; F]); (#"b",[F; T; T; F]); (#"a",[F; T; F]); (#"d",[F; F])] *)


(******************************************
             Huffman decoding
*******************************************)

















val _ = export_theory();
