(*
  This compiler phase introduces the implementation of the share
  common data routine that reduces data duplication in the heap
*)
open preamble stackLangTheory data_to_wordTheory;

val _ = new_theory "stack_scdata";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(*
 0 -> length + 1
 1 -> first pointer
 2 -> snd pointer
writes in 3, 4, 5, 6

returns 0 or not 0 in reg 0 if values where equal
*)
val scd_equality_code_def = Define `
  scd_equality_code conf =
    list_Seq [
      move 3 0;

      (* computes addr of pointers *)
      right_shift_inst 1 (shift_length conf);
      left_shift_inst  1 (word_shift (:'a));
      right_shift_inst 2 (shift_length conf);
      left_shift_inst  2 (word_shift (:'a));
      Get 3 CurrHeap;
      add_inst 1 3;
      add_inst 2 3;

      (* test equality *)
      const_inst 6 1w;
      While NotEqual 0 (Imm 0w)
            (list_Seq [ load_inst 4 1;
                        load_inst 5 2;
                        add_bytes_in_word_inst 1;
                        add_bytes_in_word_inst 2;
                        sub_1_inst 0;
                        If Equal 4 (Reg 5) Skip (const_inst 6 0w)
                        ]);
      If NotTest 6 (Imm 1w)
        (list_Seq [
            (* compute the original header_addr *)
            move 0 3;
            left_shift_inst 0 (word_shift (:'a));
            sub_inst 1 0;
            sub_inst 2 0;

            (* write a pointer to 1 at pos 2 *)
            left_shift_inst 1 2;
            store_inst 1 2;

            const_inst 0 1w])
        Skip] : 'a stackLang$prog`;

val clear_top_inst_def = Define `
  clear_top_inst i n =
    Seq (left_shift_inst i (dimindex(:'a) - n - 1))
        (right_shift_inst i (dimindex(:'a) - n - 1)):'a stackLang$prog`;

(* receives data to update in register 0
and returns the result in register 0
 uses registers 1 and 2
*)
val scd_update_el_code_def = Define `
  scd_update_el_code conf =
    If Test 0 (Imm (1w: 'a word)) Skip
      (list_Seq
       [(*computes head_addr from pointer *)
        move 2 0;
        Get 1 CurrHeap;
        right_shift_inst 0 (shift_length conf);
        left_shift_inst 0 (word_shift (:'a));
        add_inst 0 1;
        load_inst 1 0;

        (* test if it is a forward pointer *)
        If Test 1 (Imm 3w)
           (* return the forwarded pointer *)
           (list_Seq [right_shift_inst 1 2;
                      left_shift_inst 1 (shift_length conf);
                      clear_top_inst 2 (small_shift_length conf - 1);
                      or_inst 2 1])
           (* else return the original pointer *)
           Skip;
        move 0 2]) : 'a stackLang$prog`;

(* given addr in reg 0 just before the first element
  and length in reg 1 return bool to say
 if can be processed *)
val scd_can_be_processed_list_code_def = Define `
  scd_can_be_processed_list_code conf = list_Seq [
    move 2 0;
    const_inst 0 1w;
    While NotEqual 1 (Imm 0w)
      (list_Seq [
          add_bytes_in_word_inst 2;
          load_inst 3 2;
          If Test 3 (Imm 1w) (sub_1_inst 1)
            (list_Seq [
              Get 4 CurrHeap;
              right_shift_inst 3 (shift_length conf);
              left_shift_inst 3 (word_shift (:'a));
              add_inst 3 4; (* here 0 is ptr_to_addr conf old w *)
              load_inst 3 3; (* here 1 is m (ptr_to_addr conf old w) *)
              If Test 3 (Imm 32w)
                (Seq (const_inst 0 0w) (const_inst 1 0w))
                (sub_1_inst 1)])
      ])] : 'a stackLang$prog`;

(*
arguments :
  reg 0 target addr
  reg 1 target length
  reg 2 ptr
  reg 3 hash
  reg 4 processing length + 1

assumes length is a power of 2

uses register up to 12
*)

val scd_store_in_target_code_def = Define `
  scd_store_in_target_code conf =
    list_Seq
     [move 7 0; (* target addr *)
      move 8 1; (* target length *)
      left_shift_inst 8 (1 + word_shift (:'a));
      move 9 2; (* ptr *)
      move 10 3; (* hash *)
      move 11 3; (* pos *)
      left_shift_inst 11 (1 + word_shift (:'a));
      const_inst 12 1w;
      move 13 4;
      While Equal 12 (Imm 1w)
        (list_Seq [
          move 0 7;
          add_inst 0 11;
          load_inst 2 0;
          If Test 2 (Imm 1w)
           (list_Seq [
            const_inst 12 0w;
            store_inst 9 0;
            add_bytes_in_word_inst 0;
            store_inst 10 0])
           (list_Seq [
            add_inst 1 0;
            If NotEqual 1 (Reg 10)
              (list_Seq [
                add_bytes_in_word_inst 11;
                add_bytes_in_word_inst 11;
                and_inst 11 8])
              (list_Seq [
                (* test equality *)
                move 0 13;
                move 2 9;
                scd_equality_code conf;

                If Equal 0 (Imm 1w)
                  Skip
                  (list_Seq [
                    add_bytes_in_word_inst 11;
                    add_bytes_in_word_inst 11;
                    and_inst 11 8])])])])] : 'a stackLang$prog`;


(* updates a pointer
arguments :
  reg 0 ptr

uses registers 0 -> 4
*)
val scd_updated_lookup_code_def = Define `
  scd_updated_lookup_code conf = list_Seq [
    (* computes head_addr *)
    Get 3 CurrHeap;
    right_shift_inst 0 (shift_length conf);
    left_shift_inst 0 (word_shift (:'a));
    add_inst 3 0;
    (* compute length *)
    load_inst 4 3;
    right_shift_inst 4 (dimindex (:'a) - conf.len_size);
    While NotEqual 4 (Imm 0w)
      (list_Seq [
        add_bytes_in_word_inst 3;
        load_inst 0 3;
        scd_update_el_code conf;
        store_inst 0 3;
        sub_1_inst 4])] : 'a stackLang$prog`;

(*

arguments :
  reg 0 list addr
  reg 1 list size
  reg 2 target addr
  reg 3 target size (assumes a power of 2)

returns new_list length in reg 0

uses 18 registers
*)
val scd_filter_list_code_def = Define `
  scd_filter_list_code conf = list_Seq [
    move 13 0; (* list addr *)
    move 14 1; (* list size *)
    move 15 0; (* new_list pos *)
    const_inst 16 0w; (* new_list length *)
    move 17 2; (* target addr *)
    move 18 3; (* target length *)
    While NotEqual 14 (Imm 0w)
      (list_Seq [
          load_inst 5 13;
          move 0 5;
          scd_updated_lookup_code conf;
          move 0 5;

          (* compute addr (reg 0) and length (reg 1) before call *)
          Get 1 CurrHeap;
          right_shift_inst 0 (shift_length conf);
          left_shift_inst 0 (word_shift (:'a));
          add_inst 0 1;
          load_inst 1 0;
          right_shift_inst 1 (dimindex (:'a) - conf.len_size);
          move 12 1;
          scd_can_be_processed_list_code conf;

          If Equal 0 (Imm 0w)
            (list_Seq [
              load_inst 0 13;
              store_inst 0 15;
              add_bytes_in_word_inst 15;
              add_1_inst 16])
            (list_Seq [
              move 0 17;
              move 1 18;
              load_inst 2 13;
              const_inst 3 0w; (* TODO compute hash *)
              move 4 12;
              add_1_inst 4;
              scd_store_in_target_code conf]);
          add_bytes_in_word_inst 13;
          sub_1_inst 14]);
    move 0 16] : 'a stackLang$prog`;


(* reg 0 ptr uses reg 1 and 2 *)
val scd_mark_as_processed_code_def = Define `
  scd_mark_as_processed_code conf = list_Seq [
    Get 1 CurrHeap;
    right_shift_inst 0 (shift_length conf);
    left_shift_inst 0 (word_shift (:'a));
    add_inst 0 1; (* here 0 is ptr_to_addr conf old w *)
    load_inst 1 0; (* here 1 is m (ptr_to_addr conf old w) *)

    (* marks as processed *)
    Inst (Arith (Binop Or 1 1 (Imm 32w)));

    store_inst 1 0] : 'a stackLang$prog`;

(*
arguments :
  reg 0 target addr
  reg 1 target size
*)
val scd_clean_hashmap_code_def = Define `
  scd_clean_hashmap_code conf = list_Seq [
    move 2 0;
    move 3 1;
    While NotEqual 3 (Imm 0w)
      (list_Seq [
        load_inst 0 2;
        If Test 0 (Imm 1w)
          Skip
          (list_Seq [
            scd_mark_as_processed_code conf;
            const_inst 0 0w;
            store_inst 0 2]);
        sub_1_inst 3;
        add_bytes_in_word_inst 2;
        add_bytes_in_word_inst 2
      ])]`;


(*
arguments :
  reg 0 array pos
  reg 1 max length
  reg 2 heap head
  reg 3 heap end
uses reg 4 to 6
*)
val scd_count_data_code_def = Define `
  scd_count_data_code conf = list_Seq [
    (* initialize the array with zeros *)
    move 4 0;
    move 5 1;
    const_inst 6 0w;
    While NotEqual 5 (Imm 0w)
      (list_Seq [store_inst 4 6; add_bytes_in_word_inst 4]);

    While NotEqual 2 (Reg 3)
      (list_Seq [
        load_inst 4 2;
        If Test 4 (Imm 4w)
          (list_Seq [
            move 5 4;
            right_shift_inst 4 (dimindex (:'a) - conf.len_size);
            If Less 4 (Reg 1)
              (list_Seq [
                (* test if isRef *)
                const_inst 6 28w;
                add_inst 5 6;
                If Equal 5 (Imm 8w)
                  (list_Seq [
                    move 5 4;
                    left_shift_inst 5 (word_shift (:'a));
                    add_inst 0 5;
                    load_inst 6 0;
                    add_1_inst 6;
                    store_inst 6 0;
                    sub_inst 0 5])
                  Skip])
              Skip;
            add_1_inst 4;
            left_shift_inst 4 (word_shift (:'a));
            add_inst 2 4])
          (list_Seq [
            right_shift_inst 4 (dimindex (:'a) - conf.len_size);
            add_1_inst 4;
            left_shift_inst 4 (word_shift (:'a));
            add_inst 2 4])])] : 'a stackLang$prog`;

(*
arguments :
  reg 0 address of address array
  reg 1 max length
  reg 2 heap head
  reg 3 heap end
uses reg 4
*)
val scd_separate_heap_code_def = Define `
  scd_separate_heap_code conf = list_Seq [
    While NotEqual 2 (Reg 3)
      (list_Seq [
        load_inst 4 2;
        If Test 4 (Imm 4w)
          (list_Seq [
            move 5 4;
            right_shift_inst 4 (dimindex (:'a) - conf.len_size);
            If Less 4 (Reg 1)
              (list_Seq [
                (* test if isRef *)
                move 6 5;
                Inst (Arith (Binop And 5 5 (Imm 28w)));
                If NotEqual 5 (Imm 8w) (* if not ref *)
                  (list_Seq [
                    (* set as uprocessed *)
                    Inst (Arith (Binop Or 6 6 (Imm 32w)));
                    Inst (Arith (Binop Xor 6 6 (Imm 32w)));
                    store_inst 6 2;

                    move 5 4;
                    left_shift_inst 5 (word_shift (:'a));
                    add_inst 5 0;

                    load_inst 6 5;
                    store_inst 2 6;
                    add_bytes_in_word_inst 6;
                    store_inst 6 5])
                  (list_Seq [
                    Inst (Arith (Binop Or 6 6 (Imm 32w)));
                    store_inst 6 2])])
              (list_Seq [
                Inst (Arith (Binop Or 5 5 (Imm 32w)));
                store_inst 5 2]);
            add_1_inst 4;
            left_shift_inst 4 (word_shift (:'a));
            add_inst 2 4])
          (list_Seq [
            right_shift_inst 4 (dimindex (:'a) - conf.len_size);
            add_1_inst 4;
            left_shift_inst 4 (word_shift (:'a));
            add_inst 2 4])])] : 'a stackLang$prog`;

(*
arguments
  reg 0 addr array
  reg 1 size array
  reg 2 max length
  reg 3 target addr
  reg 4 target length

uses registers 0 -> 21
*)
val scd_update_rows_code_def = Define `
  scd_update_rows_code conf = list_Seq [
    move 19 0; (* addr array *)
    move 20 1; (* size array *)
    move 21 2; (* max length *)
    move 22 3; (* target addr *)
    move 23 4; (* target length *)
    While NotEqual 21 (Imm 0w)
      (list_Seq [
        load_inst 0 19;
        load_inst 1 20;
        move 2 22;
        move 3 23;
        scd_filter_list_code conf;
        store_inst 0 20;

        move 0 22;
        move 1 23;
        scd_clean_hashmap_code conf;

        add_bytes_in_word_inst 19;
        add_bytes_in_word_inst 20;
        sub_1_inst 21])]`;

(*
arguments :
  reg 1 list hd
  reg 2 list size

returns sum in reg 0

uses reg 3
*)

val scd_compute_sum_code_def = Define `
  scd_compute_sum_code = list_Seq [
    const_inst 0 0w;
    While NotEqual 2 (Imm 0w)
      (list_Seq [
        load_inst 3 1;
        add_inst 0 3;
        add_bytes_in_word_inst 1;
        sub_1_inst 2])
]`;

(*
arguments :
  reg 0 max nb iter
  reg 1 addr array
  reg 2 size array
  reg 3 max length
  reg 4 target addr
  reg 5 target length

*)
val share_common_data_iter_code_def = Define `
  share_common_data_iter_code conf = list_Seq [
    move 30 0; (* max nb_iter *)
    move 31 1; (* addr array *)
    move 32 2; (* size array *)
    move 33 3; (* max length *)
    move 34 4; (* target addr *)
    move 35 5; (* target length *)

    move 1 32;
    move 2 33;
    scd_compute_sum_code;
    move 0 29;

    While NotEqual 30 (Imm 0w)
      (list_Seq [
        move 0 31;
        move 1 32;
        move 2 33;
        move 3 34;
        move 4 35;
        scd_update_rows_code conf;

        sub_1_inst 30;

        move 1 32;
        move 2 33;
        scd_compute_sum_code;
        If Equal 0 (Reg 29)
          (const_inst 30 0w)
          Skip;
        move 29 0])]`;

(*
arguments :
  reg 0 heap head
  reg 1 heap end
uses reg 0 -> 5
*)
val scd_update_heap_code_def = Define `
  scd_update_heap_code conf = list_Seq [
    move 3 0;
    move 4 1;
    While NotEqual 3 (Reg 4)
      (list_Seq [
        load_inst 5 3;
        If Test 5 (Imm 4w)
          (list_Seq [
            right_shift_inst 5 (dimindex (:'a) - conf.len_size);
            add_bytes_in_word_inst 3;
            While NotEqual 5 (Imm 0w)
              (list_Seq [
                load_inst 0 3;
                scd_update_el_code conf;
                store_inst 0 3;
                sub_1_inst 5;
                add_bytes_in_word_inst 3])])
          (list_Seq [
            right_shift_inst 5 (dimindex (:'a) - conf.len_size);
            add_1_inst 5;
            left_shift_inst 5 (word_shift (:'a));
            add_inst 3 5])])] : 'a stackLang$prog`;

(*
  reg 0 heap start
  reg 1 heap end
  reg 2 stack start
  reg 3 stack end
*)

val share_common_data_code_def = Define `
  share_common_data_code conf = let max_length = 5w in list_Seq [
    move 40 0; (* heap start *)
    move 41 1; (* heap end *)
    move 42 2; (* stack start *)
    move 43 3; (* stack end *)

    move 44 1; (* nb array *)
    move 45 44; (* addr array *)
    const_inst 50 max_length;
    left_shift_inst 50 (word_shift (:'a));
    add_inst 45 50;

    (* count data *)
    move 0 44;
    const_inst 1 max_length;
    move 2 40;
    move 3 41;
    scd_count_data_code conf;

    (* initialize address array *)
    move 46 45; (* working space *)
    move 0 44;
    move 1 45;
    const_inst 2 max_length;
    While NotEqual 2 (Imm 0w)
      (list_Seq [
        store_inst 46 1;
        load_inst 3 0;
        left_shift_inst 3 (word_shift (:'a));
        add_inst 46 3;
        add_bytes_in_word_inst 0;
        add_bytes_in_word_inst 1;
      ]);

    (* split the heap *)
    move 0 45;
    const_inst 1 max_length;
    move 2 40;
    move 3 41;
    scd_separate_heap_code conf;

    (* compute workspace size *)
    move 0 44;
    const_inst 1 max_length;
    const_inst 5 1w;
    While NotEqual 1 (Imm 0w)
      (list_Seq [
        load_inst 2 0;
        While Less 2 (Reg 5) (left_shift_inst 5 1);
        add_bytes_in_word_inst 0;
        sub_1_inst 1]);

    (* iterates share common data *)
    const_inst 0 100w;
    move 1 45;
    move 2 44;
    const_inst 3 max_length;
    move 4 46;
    share_common_data_iter_code conf;

    const_inst 3 0w;
    StackLoadAny 0 3;

    (* updates the stack *)
    While NotTest 0 (Reg 0)
      (list_Seq [
        scd_update_el_code conf;
        StackStoreAny 0 3;
        add_bytes_in_word_inst 3;
        StackLoadAny 0 3])] : 'a stackLang$prog`;

val _ = export_theory ();
