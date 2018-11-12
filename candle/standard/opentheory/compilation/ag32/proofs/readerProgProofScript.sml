open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     ag32_memoryTheory ag32_memoryProofTheory ag32_ffi_codeProofTheory
     ag32_machine_configTheory ag32_basis_ffiProofTheory
     readerProgTheory readerCompileTheory;

val _ = new_theory "readerProgProof";

val reader_io_events_def =
  new_specification ("reader_io_events_def", ["reader_io_events"],
  reader_semantics |> Q.GENL [`cl`,`fs`]
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM]
  |> SIMP_RULE std_ss [SKOLEM_THM]);

val (reader_sem,reader_output) = reader_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (reader_not_fail,reader_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail reader_sem |> CONJ_PAIR

val ffi_names =
  ``config.ffi_names``
  |> (REWRITE_CONV[readerCompileTheory.config_def] THENC EVAL)

val LENGTH_code =
  ``LENGTH code``
  |> (REWRITE_CONV[readerCompileTheory.code_def] THENC listLib.LENGTH_CONV)

val LENGTH_data =
  ``LENGTH data``
  |> (REWRITE_CONV[readerCompileTheory.data_def] THENC listLib.LENGTH_CONV)

val _ = overload_on("reader_machine_config",
    ``ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)``);

val target_state_rel_reader_start_asm_state = Q.store_thm("target_state_rel_reader_start_asm_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms ⇒
   ∃n. target_state_rel ag32_target (init_asm_state code data (THE config.ffi_names) (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  strip_tac
  \\ drule (GEN_ALL init_asm_state_RTC_asm_step)
  \\ disch_then drule
  \\ simp_tac std_ss []
  \\ disch_then(qspecl_then[`code`,`data`,`THE config.ffi_names`]mp_tac)
  \\ impl_tac >- ( EVAL_TAC>> fs[ffi_names,LENGTH_data,LENGTH_code])
  \\ strip_tac
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md).mem_domain``]);

val reader_startup_clock_def =
  new_specification("reader_startup_clock_def",["reader_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_reader_start_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val compile_correct_applied =
  MATCH_MP compile_correct reader_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP reader_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[reader_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_ag32_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`

val reader_installed = Q.store_thm("reader_installed",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms0 ⇒
   installed code 0 data 0 config.ffi_names (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (reader_machine_config) (FUNPOW Next (reader_startup_clock ms0 inp cl) ms0)`,
  rewrite_tac[ffi_names, THE_DEF]
  \\ strip_tac
  \\ irule ag32_installed
  \\ drule reader_startup_clock_def
  \\ disch_then drule
  \\ rewrite_tac[ffi_names, THE_DEF]
  \\ disch_then drule
  \\ strip_tac
  \\ simp[]
  \\ conj_tac >- (simp[LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- (simp[LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (EVAL_TAC)
  \\ asm_exists_tac
  \\ simp[]
  \\ fs[ffi_names]);

val reader_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (UNDISCH reader_installed)
  |> DISCH_ALL
  |> curry save_thm "reader_machine_sem";

val read_stdin_writes_def = Define `
  read_stdin_writes fs refs =
    case readLines (all_lines fs (IOStream (strlit "stdin"))) init_state refs of
      (Success (s, _), refs) => msg_success s refs.the_context
    | _ => strlit ""`;

val reader_extract_writes_stdout = Q.store_thm("reader_extract_writes_stdout",
  `wfcl cl /\
   (LENGTH cl = 1)
   ==>
   (extract_writes 1
     (MAP get_output_io_event (reader_io_events cl (stdin_fs inp))) =
     (case init_reader () init_refs of
        (Success _, refs) =>
           explode
             (case readLines
               (all_lines (stdin_fs inp) (IOStream (strlit "stdin")))
               init_state init_refs of
                (Success (s, _), refs) => msg_success s refs.the_context
              | _ => strlit "")
      | _ => ""))`,
  strip_tac \\ fs []
  \\ mp_tac (GEN_ALL (DISCH_ALL reader_output))
  \\ disch_then (qspecl_then [`stdin_fs inp`, `cl`] mp_tac)
  \\ fs [wfFS_stdin_fs, STD_streams_stdin_fs, LENGTH_EQ_NUM_compute]
  \\ impl_tac
  >- (qexists_tac `inp` \\ EVAL_TAC)
  \\ strip_tac
  \\ drule (GEN_ALL extract_fs_extract_writes)
  \\ simp [Once stdin_fs_def]
  \\ disch_then match_mp_tac
  \\ simp [Once stdin_fs_def]
  \\ conj_tac >- simp [stdin_fs_def]
  \\ conj_tac >- simp [stdin_fs_def, fsFFIPropsTheory.inFS_fname_def]
  \\ conj_tac
  >-
   (rpt gen_tac
    \\ simp [readerProofTheory.reader_main_def,
             readerProofTheory.read_stdin_def,
             fsFFIPropsTheory.inFS_fname_def]
    \\ rpt (PURE_CASE_TAC \\ fs [])
    \\ simp [TextIOProofTheory.add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ (conj_tac >- (qexists_tac `implode ""` \\ EVAL_TAC))
    \\ Cases
    \\ strip_tac
    \\ simp [fsFFIPropsTheory.fastForwardFD_def, libTheory.the_def, stdin_fs_def,
             TextIOProofTheory.stdo_def, TextIOProofTheory.up_stdo_def,
             ALIST_FUPDKEY_ALOOKUP, fsFFITheory.fsupdate_def,
             CaseEq "bool", CaseEq "option"]
    \\ rw [] \\ fs [])
  \\ conj_tac >- cheat (* TODO *)
  \\ conj_tac >- cheat (* TODO *)
  \\ conj_tac >- cheat (* TODO *)
  \\ simp [readerProofTheory.reader_main_def,
           readerProofTheory.read_stdin_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ simp [fsFFIPropsTheory.fastForwardFD_def, libTheory.the_def, stdin_fs_def,
           TextIOProofTheory.stdo_def, TextIOProofTheory.up_stdo_def,
           TextIOProofTheory.stdo_def, TextIOProofTheory.add_stdo_def,
           ALIST_FUPDKEY_ALOOKUP,
           fsFFITheory.fsupdate_def,
           CaseEq "bool", CaseEq "option"]
  \\ cheat (* TODO *)
  );

val reader_ag32_next = Q.store_thm("reader_ag32_next",
  `SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   wfcl cl /\
   (LENGTH cl = 1) /\
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms0
   ==>
   ?k1. !k. k1 <= k ==>
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (reader_machine_config).halt_pc) /\
       (get_mem_word ms.MEM ms.PC = Encode (Jump (fAdd,0w,Imm 0w))) /\
       outs ≼ MAP get_output_io_event (reader_io_events cl (stdin_fs inp)) /\
       ((ms.R (n2w (reader_machine_config).ptr_reg) = 0w) ==>
        (outs = MAP get_output_io_event (reader_io_events cl (stdin_fs inp))))`,
  strip_tac
  \\ mp_tac (GEN_ALL reader_machine_sem)
  \\ disch_then (mp_tac o CONV_RULE (RESORT_FORALL_CONV rev))
  \\ disch_then (qspec_then `cl` mp_tac)
  \\ fs [LENGTH_EQ_NUM_compute]
  \\ disch_then(qspec_then`stdin_fs inp`mp_tac)
  \\ disch_then (qspec_then `inp` mp_tac)
  \\ disch_then (qspec_then `ms0` mp_tac)
  \\ impl_tac
  >-
   (fs[STD_streams_stdin_fs, wfFS_stdin_fs]
    \\ qexists_tac `inp`
    \\ simp [stdin_fs_def, TextIOProofTheory.stdin_def])
  \\ simp []
  \\ strip_tac \\ rveq \\ rfs []
  \\ cheat (* TODO *)
  (*
  \\ irule ag32_next
  \\ conj_tac >- simp[ffi_names]
  \\ conj_tac >- (simp[ffi_names, LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (simp[ffi_names] \\ EVAL_TAC)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ drule reader_startup_clock_def
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ metis_tac[]);
  *)
  );

val _ = export_theory();
