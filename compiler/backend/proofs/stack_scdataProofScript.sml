
open preamble stackLangTheory data_to_wordTheory stackSemTheory stack_scdataTheory;

val _ = new_theory "stack_scdataProof";

val default_s_def = Define `
  default_s s = s with <|
    regs := FOLDL (λy x. y |+ (x, Word 0w)) FEMPTY (GENLIST (λx.x) 50);
    store := FEMPTY;
    stack := [];
    stack_space := 1000;
    memory := λx. Word 0w;
    mdomain := {};
    bitmaps := [];
    compile := λx y. NONE;
    use_stack := T;
    use_store := T;
    use_alloc := T;
    clock := 10;
    be := F |>`;

Theorem test1:
  T
Proof
  gvs []
QED

val _ = export_theory ();
