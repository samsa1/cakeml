(*
    An attempt to implement shareCommonData from PolyML in CakeML
    https://www.polyml.org/documentation/Reference/PolyMLStructure.html
    #shareCommonData
*)

open preamble wordsTheory wordsLib integer_wordTheory gc_sharedTheory;


val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "scData";

val _ = ParseExtras.temp_loose_equality();

val gc_state_component_equality = DB.fetch "gc_shared"
  "gc_state_component_equality";

val _ = Datatype `
  share_common_data_conf =
    <| limit : num
     ; isRef : 'b -> bool
     ; was_processed : 'b -> bool
     ; set_as_processed : 'b -> 'b
     ; set_as_unprocessed : 'b -> 'b
     ; hash : ('a heap_address) list -> num
     ; load : num -> 'a
     ; unload : 'a -> num
     ; max_length : num
     |>`;


val scd_equality_def = Define `
  scd_equality conf state ptr1 ptr2 d =
    case heap_lookup ptr1 state.heap of
      | SOME (DataElement xs1 l1 dd1) =>
        (case heap_lookup ptr2 state.heap of
          | SOME (DataElement xs2 l2 dd2) =>
            if ((l1 = l2) /\ (xs1 = xs2) /\ (dd1 = dd2))
            then
              let (heap, ok) = gc_forward_ptr ptr2 state.heap ptr1 d state.ok
              in (T, state with <| heap := heap; ok := ok |>)
            else
              (F, state)
          | _ => (F, state with <| ok := F |> ))
      | _ => (F, state with <| ok := F |> )`;

val update_el_def = Define `
    (update_el state (Data d) = Data d) /\
    (update_el state (Pointer ptr d) =
        case heap_lookup ptr state.heap of
            | SOME (ForwardPointer ptr _ l) => (Pointer ptr d)
            | _ => (Pointer ptr d))`;

val can_be_processed_list_def = Define `
    (can_be_processed_list conf state [] = T) /\
    (can_be_processed_list conf state (Data d::tl) =
        can_be_processed_list conf state tl) /\
    (can_be_processed_list conf state (Pointer ptr d::tl) =
        case heap_lookup ptr state.heap of
            | SOME (DataElement xs l dd) =>
                if conf.was_processed dd
                then can_be_processed_list conf state tl
                else F
            | _ => F)`;

val store_in_target_def = Define `
  (store_in_target 0 conf state target ptr1 d hash pos length =
        (target, state with <| ok := F |>)) /\
  (store_in_target (SUC m) conf state target ptr1 d hash pos length =
    case EL (2 * pos + 1) target of
      | Data hash2 =>
        (case EL (2 * pos) target of
          | Pointer ptr2 d2 =>
            if (hash = conf.unload hash2)
            then
              let (b, state) = scd_equality conf state ptr2 ptr1 d in
              if b
              then (target, state)
              else
                store_in_target m conf state target ptr1 d hash
                  ((pos + 1) MOD length) length
            else
              store_in_target m conf state target ptr1 d hash
                ((pos + 1) MOD length) length
          | Data d2 =>
            let target = LUPDATE (Data (conf.load hash)) (2 * pos + 1) target in
            let target = LUPDATE (Pointer ptr1 d) (2 * pos) target in
            (target, state))
      | Pointer ptr d => (target, state with <| ok := F |>))`;

val updated_lookup_list_def = Define `
  (updated_lookup_list a [] state = NONE) /\
  (updated_lookup_list a ((DataElement ys l d)::xs) state =
     if a = 0 then
       let ys = MAP (update_el state) ys in
         SOME (state with <| heap :=  (DataElement ys l d)::xs|>, DataElement
          ys l d)
     else
     if a < el_length (DataElement ys l d) then NONE else
       case updated_lookup_list (a - el_length (DataElement ys l d)) xs state
        of
         | NONE => NONE
         | SOME (state, eL) => SOME (state with
          <| heap := (DataElement ys l d)::state.heap|>, eL)) ∧
  (updated_lookup_list a (x::xs) state =
     if a < el_length x then NONE else
       case updated_lookup_list (a - el_length x) xs state of
         | NONE => NONE
         | SOME (state, eL) =>
          SOME (state with <| heap := x::state.heap|>, eL))`;

val updated_lookup_def = Define `
  updated_lookup ptr state = updated_lookup_list ptr state.heap state`;

val filter_list_def = Define `
  (filter_list conf state [] target new_list length =
    (target, new_list, state)) /\
  (filter_list conf state (x::tl) target new_list length =
    case x of
      | Data d => (target, new_list, state with <| ok := F |>)
      | Pointer ptr d =>
        (case updated_lookup ptr state of
         | SOME (state, DataElement xs l dd) =>
             if can_be_processed_list conf state xs
             then
               let hash = conf.hash xs in
               let length = LENGTH target DIV 2 in
               let pos = hash MOD length in
               let (target, state) = store_in_target length conf state target
                    ptr d hash pos length in
                 filter_list conf state tl target new_list length
             else
               filter_list conf state tl target (new_list ++ [x]) length
          | _ => (target, new_list, state with <| ok := F |>)))`;

val gc_update_addr_def = Define `
  (gc_update_addr conf a [] ok = ([], F)) /\
  (gc_update_addr conf 0 (DataElement dataL l dd::xs) ok =
    (DataElement dataL l (conf.set_as_processed dd)::xs, ok)) /\
  (gc_update_addr conf 0 xs ok =
    (xs, F)) /\
  (gc_update_addr conf a (x::xs) ok =
    if a < el_length x then (x::xs, F)
    else
      let (xs, ok) = gc_update_addr conf (a - el_length x) xs ok in
      (x::xs, ok))`;

val clean_hashmap_def = Define `
    (clean_hashmap conf state [] = ([], state)) /\
    (clean_hashmap conf state [x] = ([x], state with <| ok := F |>)) /\
    (clean_hashmap conf state (y::x::tl) =
      (case y of
        | Data d =>
            let (xs, state) = clean_hashmap conf state tl in
            (x::y::xs, state)
        | Pointer ptr d =>
            let (heap, ok) = gc_update_addr conf ptr state.heap state.ok in
            let (xs, state) = clean_hashmap conf
              (state with <| heap := heap; ok := ok |>) tl in
            ((Data d)::x::xs, state)))`;

val scd_count_data_el_def = Define `
    (scd_count_data_el conf (array : num list) (DataElement xs l dd) =
        if conf.isRef dd \/ l >= conf.max_length
        then array
        else LUPDATE (EL l array + 1) l array) /\
    (scd_count_data_el conf array _ = array)`;

val scd_count_data_list_def = Define `
    (scd_count_data_list conf array [] = array) /\
    (scd_count_data_list conf array (x::tl) =
        let array = scd_count_data_el conf array x in
        scd_count_data_list conf array tl)`;

val scd_count_data_def = Define `
    scd_count_data conf list =
        scd_count_data_list conf (GENLIST (K 0) conf.max_length) list`;

val scd_separate_heap_def = Define `
  (scd_separate_heap conf pos [] list default ok = ([], list, ok)) /\
  (scd_separate_heap conf pos (DataElement dataL l d::xs) list default ok =
    if conf.isRef d \/ l >= conf.max_length
    then
      let (xs, list, ok) = scd_separate_heap conf
        (pos + el_length (DataElement dataL l d)) xs list default ok in
      (DataElement dataL l (conf.set_as_processed d)::xs, list, ok)
    else
      let list = LUPDATE ((EL l list) ++ [Pointer pos default]) l list in
      let (xs, list, ok) = scd_separate_heap conf (pos + el_length
        (DataElement dataL l d)) xs list default ok in
      (DataElement dataL l (conf.set_as_unprocessed d)::xs, list, ok))`;

val update_rows_def = Define `
  (update_rows conf state [] workspace length = (state, [], workspace)) /\
  (update_rows conf state (hd::tl) workspace length =
    let (workspace, hd, state) = filter_list conf state hd workspace []
      length in
      let (workspace, state) = clean_hashmap conf state workspace in
        let (state, tl, workspace) = update_rows conf state tl workspace
          length in
          (state, hd::tl, workspace))`;

val share_common_data_iter_def = Define `
  (share_common_data_iter 0 conf state list workspace length = state) /\
  (share_common_data_iter (SUC k) conf state list workspace length =
   let tot_len = LENGTH $ FLAT list in
     let (state, list, workspace) = update_rows conf state list workspace
      length in
       if LENGTH (FLAT list) = tot_len
       then state
       else
         share_common_data_iter k conf state list workspace length)`;

val update_heap_def = Define `
  (update_heap [] state = []) ∧
  (update_heap (x::xs) state =
   case x of
   | DataElement ys l d =>
       (DataElement (MAP (update_el state) ys) l d)::update_heap xs state
   | x => (x::update_heap xs state))`;

val share_common_data_def = Define `
  (share_common_data (conf: (α, β) share_common_data_conf)
    (roots : α heap_address list)
     (state: (α, β) gc_state) (d : α) =
    let count = scd_count_data conf state.heap in
      let maxi = FOLDL MAX 0 count in
    let (heap, l, ok) = scd_separate_heap conf 0 state.heap
                                          (GENLIST (K []) conf.max_length)
                                          d state.ok in
    let state = state with <| heap := heap; ok := ok |> in
    let state = share_common_data_iter maxi conf state l
        (GENLIST (K $ Data d) (maxi * 2)) maxi in
    (state with <| heap := update_heap state.heap state |>,
      MAP (update_el state) roots))`;

(* Exemples and tests *)

Datatype:
  data_wrapper = Stored num
End

val default_conf_def = Define `
   default_conf =
   <| limit := 1000
      ; isRef := FST
      ; was_processed := SND
      ; set_as_processed := (λ(x,y). (x, T))
      ; set_as_unprocessed := (λ(x,y). (x, F))
      ; hash := (FOLDL (λx y. case y of
        | Data (Stored num) => x * 17 + num
        | Pointer ptr (Stored num) => x * 19 * 23 + 23 * ptr + num) 1)
      ; load := (λnum. Stored num)
      ; unload := (λx. case x of | Stored num => num)
      ; max_length := 5
   |>`;


val state_builder_def = Define `
    state_builder heap size =
    <| old := []
       ; h1 := []
       ; h2 := []
       ; r4 := []
       ; r3 := []
       ; r2 := []
       ; r1 := []
       ; a := heap_length heap
       ; n := size - heap_length heap
       ; ok := T
       ; heap := heap
       ; heap0 := []
    |>`;


(*

  roots = [Pointer 0 (Stored 0); Data (Stored 3);
    Pointer 1 (Stored 1); Pointer 2 (Stored 2)]
  heap = [DataElement [] 0 (F, F); DataElement [] 0 (F, T);
    DataElement [] 0 (T, F)]

*)


Theorem test1:
  ∀out.
    (share_common_data default_conf
            [Pointer 0 (Stored 0); Data (Stored 3);
              Pointer 1 (Stored 1); Pointer 2 (Stored 2)]
            (state_builder [DataElement [] 0 (F,F); DataElement [] 0 (F,T);
              DataElement [] 0 (T,F)] 100) (Stored 13)
    = out) ⇒
    (SND out = [Pointer 0 (Stored 0); Data (Stored 3); Pointer 0 (Stored 1);
      Pointer 2 (Stored 2)]) ∧
    ((FST out).heap = [DataElement [] 0 (F,T); ForwardPointer 0 (Stored 13) 0;
      DataElement [] 0 (T,T)])
Proof
  gvs [] \\ EVAL_TAC
QED

Theorem test2:
  ∀out.
    (share_common_data default_conf
         [Pointer 0 (Stored 0); Data (Stored 3); Pointer 2 (Stored 1);
          Pointer 4 (Stored 2);
              Pointer 5 (Stored 3); Pointer 7 (Stored 4)]
         (state_builder [DataElement [Pointer 4 (Stored 20)] 1 (F,F);
                         DataElement [Pointer 4 (Stored 20)] 1 (F,T);
                         DataElement [] 0 (T,F);
                         DataElement [Pointer 0 (Stored 21)] 1 (F, F);
                         DataElement [Pointer 2 (Stored 21)] 1 (F, F)
                        ] 100) (Stored 13)
    = out) ⇒
    (SND out = [Pointer 0 (Stored 0); Data (Stored 3); Pointer 0 (Stored 1);
                Pointer 4 (Stored 2); Pointer 5 (Stored 3);
                Pointer 5 (Stored 4)]) ∧
    ((FST out).heap = [DataElement [Pointer 4 (Stored 20)] 1 (F,T);
                       ForwardPointer 0 (Stored 13) 1;
                       DataElement [] 0 (T,T);
                       DataElement [Pointer 0 (Stored 21)] 1 (F,T);
                       ForwardPointer 5 (Stored 13) 1])
Proof
  gvs [] \\ EVAL_TAC
QED

Theorem test3:
  ∀out.
    (share_common_data default_conf
         [Pointer 0 (Stored 0); Data (Stored 3); Pointer 2 (Stored 1);
          Pointer 4 (Stored 2);
              Pointer 5 (Stored 3); Pointer 7 (Stored 4)]
         (state_builder [DataElement [Pointer 4 (Stored 20)] 1 (F,F);
                         DataElement [Pointer 4 (Stored 20)] 1 (F,T);
                         DataElement [] 0 (T,F);
                         DataElement [Pointer 0 (Stored 21)] 1 (F, F);
                         DataElement [Pointer 2 (Stored 21)] 1 (F, F);
                         DataElement [Pointer 5 (Stored 22)] 1 (T, F);
                         DataElement [Pointer 7 (Stored 22)] 1 (T, F)] 100)
                (Stored 13)
    = out) ⇒
    (SND out = [Pointer 0 (Stored 0); Data (Stored 3); Pointer 0 (Stored 1);
                Pointer 4 (Stored 2); Pointer 5 (Stored 3);
                Pointer 5 (Stored 4)]) ∧
    ((FST out).heap = [DataElement [Pointer 4 (Stored 20)] 1 (F,T);
                       ForwardPointer 0 (Stored 13) 1;
                       DataElement [] 0 (T,T);
                       DataElement [Pointer 0 (Stored 21)] 1 (F,T);
                       ForwardPointer 5 (Stored 13) 1;
                       DataElement [Pointer 5 (Stored 22)] 1 (T, T);
                       DataElement [Pointer 5 (Stored 22)] 1 (T, T)])
Proof
  gvs [] \\ EVAL_TAC
QED

val _ = export_theory ();
