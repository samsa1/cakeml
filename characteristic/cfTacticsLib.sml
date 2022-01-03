(*
  Various tactics for reasoning about CF-based goals in HOL.
*)
structure cfTacticsLib (*:> cfTacticsLib*) =
struct

open preamble
open ConseqConv
open set_sepTheory cfAppTheory cfHeapsTheory cfTheory cfTacticsTheory
open helperLib cfHeapsBaseLib cfHeapsLib cfTacticsBaseLib evarsConseqConvLib
open cfAppLib cfSyntax semanticPrimitivesSyntax

val ERR = mk_HOL_ERR "cfTacticsLib";

fun constant_printer s _ _ _ (ppfns:term_pp_types.ppstream_funs) _ _ _ =
  let
    open Portable term_pp_types smpp
    val str = #add_string ppfns
  in str s end

val ellipsis_pp = constant_printer "(…)"

(* TODO add types to these terms *)

val printers = [
  ("extend_env_ellipsis", ``extend_env _ _ _``, ellipsis_pp),
  ("extend_env_rec_ellipsis", ``extend_env_rec _ _ _ _ _``, ellipsis_pp),
  ("extend_env_with_ellipsis", ``extend_env _ _ _ with v := _``, ellipsis_pp),
  ("extend_env_rec_with_ellipsis", ``extend_env_rec _ _ _ _ _ with v := _``,
   ellipsis_pp),
  ("merge_env_ellipsis", ``merge_env _ _``, ellipsis_pp),
  ("merge_env_with_ellipsis", ``merge_env _ _ with v := _``, ellipsis_pp)
]

fun hide_environments b =
  if b then app temp_add_user_printer printers
  else app (ignore o temp_remove_user_printer) (map #1 printers)

val _ = hide_environments true

(* -------------------------------------------------------------------------
 * Restrictive compset for use with CF conversions in this file
 * ------------------------------------------------------------------------- *)

local
  val reduce_ss = reduceLib.num_compset ();
  val _ = computeLib.extend_compset [
    computeLib.Extenders [
      listLib.list_rws,
      basicComputeLib.add_basic_compset,
      semanticsComputeLib.add_semantics_compset,
      ml_progComputeLib.add_env_compset,
      cfComputeLib.add_cf_aux_compset
    ],
    computeLib.Defs [
      semanticPrimitivesTheory.find_recfun_def,
      cfTheory.cf_def
    ],
    computeLib.Convs [
      (“nsLookup”, 2, ml_progLib.nsLookup_conv),
      (“nsLookup_Short”, 2, ml_progLib.nsLookup_conv),
      (“nsLookup_Mod1”, 2, ml_progLib.nsLookup_conv)]
    ] reduce_ss;
in
  val cf_eval = computeLib.CBV_CONV reduce_ss;
  val cf_eval_pat = compute_pat reduce_ss
end

val _ = (max_print_depth := 15)

(*------------------------------------------------------------------*)

fun process_topdecs q = cfNormaliseLib.normalise_prog (parse_topdecs q)

(*------------------------------------------------------------------*)

fun head_unfold_conv thm =
  TRY_CONV hnf_conv THENC
  rewr_head_conv thm THENC
  TRY_CONV hnf_conv

fun head_unfold thm = CONV_TAC (head_unfold_conv thm)

val reducible_pats = [
  ``find_recfun _ _``,
  ``is_bound_Fun _ _``,
  ``dest_opapp _``,
  ``exp2v _ _``,
  ``exp2v_list _ _``,
  ``do_con_check _ _ _``,
  ``build_conv _ _ _``,
  ``nsLookup _ _``,
  ``nsLookup_Short _ _``,
  ``nsLookup_Mod1 _ _``,
  ``Fun_body _``
]

fun err_tac orig msg : tactic =
  fn _ => raise ERR orig msg

(* [xpull] *)

(* xx have a proper cfSyntax? *)
fun cf_get_precondition t = rand (rator t)

(* xx *)
val cf_defs =
  [cf_lit_def, cf_con_def, cf_var_def, cf_let_def, cf_opn_def, cf_opb_def,
   cf_app_def, cf_fun_def, cf_fun_rec_def, cf_ref_def, cf_assign_def,
   cf_deref_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def,
   cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
   cf_copyaw8aw8_def, cf_log_def, cf_if_def, cf_match_def, cf_ffi_def,
   cf_raise_def, cf_handle_def]

val cleanup_exn_side_cond =
  simp [cfHeapsBaseTheory.SEP_IMPPOSTv_POSTe_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_POSTf_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_POSTd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_POSTed_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTf_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_POSTvd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTe_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTve_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTvd_left,
        cfHeapsBaseTheory.SEP_IMPPOSTf_POSTed_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTe_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTf_left,
        cfHeapsBaseTheory.SEP_IMPPOSTd_POSTve_left,
        cfHeapsBaseTheory.SEP_IMPPOSTv_inv_POSTv_left,
        cfHeapsBaseTheory.SEP_IMPPOSTe_inv_POSTe_left
       ]

val xlocal =
  FIRST [
    first_assum MATCH_ACCEPT_TAC,
    (HO_MATCH_MP_TAC app_local \\ fs [] \\ NO_TAC),
    (HO_MATCH_ACCEPT_TAC cf_cases_local \\ NO_TAC),
    (fs (local_is_local :: cf_defs) \\ NO_TAC)
  ] (* todo: is_local_pred *)

fun xpull_check_not_needed (g as (_, w)) =
  let val H = cf_get_precondition w
  in hpullable_rec H; ALL_TAC g end

fun xpull_core (g as (_, w)) =
  if is_sep_imp w orelse is_sep_imppost w then
    hpull g
  else
    hclean g

val xpull =
  xpull_core \\ rpt strip_tac THEN1 (TRY xlocal)

(* [xsimpl] *)

val sep_imp_instantiate_tac =
  TRY hinst \\
  simp [SEP_IMP_REFL, cfHeapsBaseTheory.hsimpl_gc]

val xsimpl =
  simp [PULL_EXISTS,BOOL_T,BOOL_F] \\
  CHANGED_TAC (rpt (hsimpl \\ sep_imp_instantiate_tac))
  ORELSE sep_imp_instantiate_tac

(* [xcf] *)

fun naryFun_repack_conv tm =
  let
    val (base_case, rec_case) = CONJ_PAIR (GSYM naryFun_def)
    val Fun_pat = ``Fun _ _``
    val conv =
        if can (match_term Fun_pat) tm then
          (RAND_CONV naryFun_repack_conv) THENC
          (REWR_CONV rec_case)
        else
          REWR_CONV base_case
  in conv tm
  end

val naryClosure_repack_conv =
  (RAND_CONV naryFun_repack_conv) THENC (REWR_CONV (GSYM naryClosure_def))

(* -------------------------------------------------------------------------
 * Consequence conversion that instantiates a theorem which proves 'app'
 * from 'cf' (see the theorem app_rec_of_cf).
 * ------------------------------------------------------------------------- *)

local
  val cfth = SPEC_ALL app_rec_of_cf;
  val find_recfun_pat =
    cfth |> concl |> strip_imp |> #1 |> el 4 |> rator |> rand
  val app_pat = cfth |> concl |> strip_imp |> #2;
  val params_tm =
    mk_var ("params", listSyntax.mk_list_type stringSyntax.string_ty);
  val body_tm = mk_var ("body", astSyntax.exp_ty);
  fun prove_app app_tm =
    let
      val th = INST_TY_TERM (match_term app_pat app_tm) cfth
      (* Get results of find_recfun application *)
      val find_rf_tm = find_term (can (match_term find_recfun_pat)) (concl th)
      val find_rf_th = cf_eval find_rf_tm
      (* Instantiate theorem with params and body *)
      val (params, body) =
        concl find_rf_th |> rhs |> optionSyntax.dest_some |> pairSyntax.dest_pair
      val th1 = INST [params_tm|->params,body_tm|->body] th
      (* Prove list hyps *)
      fun prove_imp th = MP th (EQT_ELIM (cf_eval (#1 (dest_imp (concl th)))))
      val th2 = prove_imp th1
      val th3 = prove_imp th2
      val th3 = prove_imp th3
    in
      (* Remove find_recfun hyp *)
      MP th3 find_rf_th
    end;
in
  val prove_app_rec_of_cf = ConseqConv.STRENGTHEN_CONSEQ_CONV prove_app
end

(* -------------------------------------------------------------------------
 * [xcf]
 * ------------------------------------------------------------------------- *)

(* TODO The [name] argument is unused. *)

fun xcf_with_def name f_def =
  let
    val Closure_tac =
      CONV_TAC (DEPTH_CONV naryClosure_repack_conv) \\
      irule app_of_cf THEN
      CONJ_TAC THEN1 (CONV_TAC cf_eval) THEN
      CONJ_TAC THEN1 (CONV_TAC cf_eval) THEN simp [cf_def]
    val Recclosure_tac =
      PURE_ONCE_REWRITE_TAC [GSYM letrec_pull_params_repack] THEN
      ConseqConv.CONSEQ_CONV_TAC prove_app_rec_of_cf THEN
      PURE_ONCE_REWRITE_TAC [letrec_pull_params_repack]
  fun closure_tac (g as (_, w)) =
    let val (_, c, _, _, _) = cfAppSyntax.dest_app w in
        if is_Closure c then
          Closure_tac g
        else if is_Recclosure c then
          Recclosure_tac g
        else
          err_tac "xcf" "argument of app is not a closure" g
    end
    handle HOL_ERR _ => err_tac "xcf" "goal is not an app" g
in
  rpt strip_tac THEN
  rewrite_tac [f_def] THEN
  closure_tac THEN
  CONV_TAC cf_eval THEN
  rewrite_tac [GSYM f_def]
end;

fun xcf name st =
  let
    val f_def = fetch_def name st
  in
    xcf_with_def name f_def
  end;

(* [xlet] *)

fun xlet_core cont0 cont1 cont2 =
  xpull_check_not_needed \\
  head_unfold cf_let_def \\
  irule local_elim \\ hnf \\
  simp [namespaceTheory.nsOptBind_def] \\
  cont0 \\
  rpt CONJ_TAC THENL [
    all_tac,
    TRY (MATCH_ACCEPT_TAC cfHeapsBaseTheory.SEP_IMPPOSTv_inv_POSTv_left),
    cont1 \\ cont2
  ]

val res_CASE_tm =
  CONJ_PAIR cfHeapsBaseTheory.res_case_def
  |> fst |> SPEC_ALL |> concl
  |> lhs |> strip_comb |> fst

val POSTv_tm =
  cfHeapsBaseTheory.POSTv_def |> SPEC_ALL |> concl
  |> lhs |> strip_comb |> fst

val POST_tm =
  cfHeapsBaseTheory.POST_def |> SPEC_ALL |> concl
  |> lhs |> strip_comb |> fst

fun vname_of_post fallback Qtm = let
  val vname_lam = fst o dest_var o fst o dest_abs
  fun vname_res_CASE_lam tm = let
      val body = dest_abs tm |> snd
    in
      if body ~~ res_CASE_tm then
        List.nth (strip_comb body |> snd, 1)
        |> vname_lam
      else fail ()
    end
  fun vname_POSTv tm = let
      val (base, args) = strip_comb tm
    in if base ~~ POSTv_tm then vname_lam (List.hd args)
       else fail()
    end
  fun vname_POST tm = let
      val (base, args) = strip_comb tm
    in if base ~~ POST_tm then vname_lam (List.hd args)
       else fail()
    end
in
  vname_POSTv Qtm handle HOL_ERR _ =>
  vname_POST Qtm handle HOL_ERR _ =>
  vname_res_CASE_lam Qtm handle HOL_ERR _ =>
  fallback
end

(* temporary basic wrapper until evars *)
fun xlet Q (g as (asl, w)) = let
  val ctx = free_varsl (w :: asl)
  val name = vname_of_post "v" (Term Q)
  val name' = prim_variant ctx (mk_var (name, v_ty)) |> dest_var |> fst
  val qname = [QUOTE name']
in
  xlet_core
    (qexists_tac Q)
    (qx_gen_tac qname \\ simp [])
    (TRY xpull)
    g
end

(* [xfun] *)

(* FIXME srw_ss () *)

val reduce_spec_conv =
  STRIP_QUANT_CONV (LAND_CONV cf_eval) THENC
  SIMP_CONV (srw_ss()) [LENGTH_EQ_NUM_compute, PULL_EXISTS]

val reduce_curried_conv = RATOR_CONV (RAND_CONV cf_eval)

val fun_reduce_conv =
  QUANT_CONV (
    LAND_CONV (
      LAND_CONV reduce_curried_conv THENC
      RAND_CONV reduce_spec_conv
    )
  )

fun fun_rec_aux_unfold_conv tm = let
  val base_case = fst (CONJ_PAIR fun_rec_aux_def)
  val ind_case = fst (CONJ_PAIR (snd (CONJ_PAIR fun_rec_aux_def)))
  val base_conv = REWR_CONV base_case
  val ind_conv =
    REWR_CONV ind_case THENC
    LAND_CONV (
      LAND_CONV reduce_curried_conv THENC
      RAND_CONV reduce_spec_conv
    ) THENC
    RAND_CONV (
      fun_rec_aux_unfold_conv
    )
in (base_conv ORELSEC ind_conv) tm end

(* FIXME srw_ss () *)

val fun_rec_reduce_conv = let
  val reduce_length =
      cf_eval THENC
      SIMP_CONV (srw_ss()) [LENGTH_EQ_NUM_compute, PULL_EXISTS]
in
  SIMP_CONV (srw_ss()) [] THENC
  QUANT_CONV (
    LAND_CONV reduce_length THENC
    RAND_CONV (
      LAND_CONV cf_eval THENC
      RAND_CONV (
        DEPTH_CONV (cf_eval_pat ``letrec_pull_params _``)
      )
    )
  ) THENC
  SIMP_CONV (srw_ss()) [PULL_EXISTS] THENC
  QUANT_CONV fun_rec_aux_unfold_conv
end

val xfun_norec_core =
  head_unfold cf_fun_def \\
  irule local_elim \\ hnf \\
  CONV_TAC fun_reduce_conv

val xfun_rec_core =
  head_unfold cf_fun_rec_def \\
  irule local_elim \\ hnf \\
  CONV_TAC fun_rec_reduce_conv

fun xfun_core (g as (_, w)) =
  if is_cf_fun w then
    xfun_norec_core g
  else if is_cf_fun_rec w then
    xfun_rec_core g
  else
    err_tac "xfun" "goal is not a cf_fun or cf_fun_rec" g

val simp_spec = CONV_RULE (REPEATC (cf_eval THENC PURE_ONCE_REWRITE_CONV[cf_def]))

fun xfun qname =
  xpull_check_not_needed \\
  xfun_core \\
  qx_gen_tac qname \\
  disch_then (fn th => assume_tac (simp_spec th))

fun xfun_spec qname qspec =
  xfun_core \\
  qx_gen_tac qname \\
  disch_then (fn th =>
    let val (curried_th, spec_th) = CONJ_PAIR th
        val spec_th = simp_spec spec_th
    in assume_tac curried_th \\
       Tactical.REVERSE (qsuff_tac qspec) THENL [
         assume_tac spec_th,
         strip_tac
       ]
    end
  ) ORELSE FAIL_TAC "invalid spec"

(* [xapply] *)

fun xapply_core H cont1 cont2 =
  irule local_frame_gc THEN
    CONJ_TAC THEN1 xlocal THEN
    CONSEQ_CONV_TAC (K (
      ecc_conseq_conv (
        conj1_ecc (irule_ecc H)
      )
    )) \\
    CONV_TAC (DEPTH_CONV (REWR_CONV ConseqConvTheory.AND_CLAUSES_TX))

fun xapply H =
  xpull_check_not_needed \\
  xapply_core H all_tac all_tac
  ORELSE err_tac "xapply" "Failed to apply the given theorem"

(* [xspec] *)

datatype spec_kind =
    CF_spec
  | Translator_spec

fun spec_kind_toString CF_spec = "CF"
  | spec_kind_toString Translator_spec = "translator"

fun concl_tm tm =
  let
    val thm' = Drule.IRULE_CANON (ASSUME tm)
    val (_, body) = strip_forall (concl thm')
  in
    if is_imp body then
      (snd o dest_imp) body
    else
      body
  end

fun goal_app_infos tm : hol_type * term =
  let val (p, f_tm, _, _, _) = cfAppSyntax.dest_app tm
      val ffi_ty = cfHeapsBaseSyntax.dest_ffi_proj (type_of p)
  in (ffi_ty, f_tm) end
  handle HOL_ERR {message,...} => raise (ERR "goal_app_infos" "not an app")

fun is_cf_spec_for f tm =
  (concl_tm tm |> goal_app_infos |> snd) ~~ f
  handle HOL_ERR _ => false

fun is_arrow_spec_for f tm =
  let val tm = tm |> strip_imp |> #2 in
    ml_translatorSyntax.is_Arrow (tm |> rator |> rator) andalso
    (rand tm) ~~ f
  end handle HOL_ERR _ => false

fun spec_kind_for f tm : spec_kind option =
  if is_cf_spec_for f tm then SOME CF_spec
  else if is_arrow_spec_for f tm then SOME Translator_spec
  else NONE

fun is_spec_for f tm : bool =
  spec_kind_for f tm <> NONE

(*
  val asl = #1 (top_goal ())
  val tm = hd asl
 *)

fun xspec_in_asl f asl : (spec_kind * term) option =
  find_map (fn tm =>
    case spec_kind_for f tm of
        SOME k => SOME (k, tm)
      | NONE => NONE)
  asl

fun xspec_in_db f : (string * string * spec_kind * thm) option =
  case DB.matchp (fn thm => is_spec_for f (concl thm)) [] of
      ((thy, name), (thm, _)) :: _ =>
      (case spec_kind_for f (concl thm) of
           SOME k => SOME (thy, name, k, thm)
         | NONE => fail())
    | _ => NONE

fun cf_spec (ffi_ty : hol_type) (kind : spec_kind) (spec : thm) : thm =
  case kind of
      CF_spec => spec
    | Translator_spec => app_of_Arrow_rule ffi_ty spec

(* todo: variants *)
fun xspec ffi_ty f (ttac: thm_tactic) (g as (asl, w)) =
  case xspec_in_asl f asl of
      SOME (k, a) =>
      (print
         ("Using a " ^ (spec_kind_toString k) ^
          " specification from the assumptions\n");
       ttac (cf_spec ffi_ty k (ASSUME a)) g)
    | NONE =>
      case xspec_in_db f of
          SOME (thy, name, k, thm) =>
          (print ("Using " ^ (spec_kind_toString k) ^
                  " specification " ^ name ^
                  " from theory " ^ thy ^ "\n");
           ttac (cf_spec ffi_ty k thm) g)
        | NONE =>
          raise ERR "xspec" ("Could not find a specification for " ^
                             term_to_string f)

(* [xapp] *)

val unfolded_app_reduce_conv =
  let
    fun fail_if_F_conv msg tm =
      if Feq tm then raise ERR "xapp" msg
      else REFL tm

    val fname_lookup_reduce_conv =
      cf_eval THENC
      (fail_if_F_conv "Unbound function")

    val args_lookup_reduce_conv =
      cf_eval THENC
      (fail_if_F_conv "Unbound argument(s)")
  in
    STRIP_QUANT_CONV (
      FORK_CONV (
        fname_lookup_reduce_conv,
        (LAND_CONV args_lookup_reduce_conv)))
  end

(* TODO make this into a conversion (or tactic) that instantiates
 * more carefully *)

val unfold_cf_app =
  head_unfold cf_app_def \\
  irule local_elim \\ hnf \\
  CONV_TAC unfolded_app_reduce_conv \\
  irule_at (Pos hd) EQ_REFL \\
  irule_at (Pos hd) EQ_REFL \\
  CONV_TAC cf_eval

val xapp_prepare_goal =
  xpull_check_not_needed \\
  (fn (g as (_, w)) =>
    if is_cf_app w then unfold_cf_app g
    else if cfAppSyntax.is_app w then all_tac g
    else err_tac "xapp"
      "Goal is not of the right form (must be a cf_app or app)" g)

(* This tactical assumes the goal is of the form [app _ _ _ _ _].
   This is the case after calling [xapp_prepare_goal] (if it doesn't fail).
*)
fun app_f_tac tmtac (g as (_, w)) = tmtac (goal_app_infos w) g

fun xapp_common spec do_xapp =
  xapp_prepare_goal \\
  app_f_tac (fn (ffi_ty, f) =>
    case spec of
        SOME thm =>
        (case spec_kind_for f (concl thm) of
             SOME k => do_xapp (cf_spec ffi_ty k thm)
           | NONE => failwith "Invalid specification")
      | NONE => xspec ffi_ty f do_xapp)

fun xapp_xapply_no_simpl K =
  FIRST [irule K, xapply_core K all_tac all_tac] ORELSE
  err_tac "xapp" "Could not apply specification"

fun xapp_core spec =
  xapp_common spec xapp_xapply_no_simpl

val xapp = xapp_core NONE
fun xapp_spec spec = xapp_core (SOME spec)

(* [xret] *)

val xret_irule_lemma =
  FIRST [(* irule xret_lemma_unify,*)
         HO_MATCH_MP_TAC xret_lemma \\ conj_tac]

val xret_no_gc_core =
    FIRST [(*irule xret_lemma_unify,*)
           (* todo evars *) HO_MATCH_MP_TAC xret_no_gc_lemma \\ conj_tac]

val xlit_core =
  head_unfold cf_lit_def \\ cbv

val xcon_core =
  head_unfold cf_con_def \\ CONV_TAC cf_eval

val xvar_core =
  head_unfold cf_var_def \\ CONV_TAC cf_eval

fun xret_pre cont1 cont2 (g as (_, w)) =
  (xpull_check_not_needed \\
   (if is_cf_lit w then xlit_core
    else if is_cf_con w then xcon_core
    else if is_cf_var w then xvar_core
    else fail ()) \\
   cont1 \\
   cleanup_exn_side_cond
   ) g
  (* todo: also do stuff with lets *)

val xret = xret_pre xret_irule_lemma (TRY xpull)
val xlit = xret
val xcon = xret
val xvar = xret

(* todo: xrets *)

(* [xlog] *)

val xlog_base =
  xpull_check_not_needed \\
  head_unfold cf_log_def \\
  irule local_elim \\ hnf \\
  CONV_TAC cf_eval \\
  cleanup_exn_side_cond \\
  TRY (asm_exists_tac \\ simp [])

val xlog = xlog_base

(* [xif] *)

val xif_base =
  xpull_check_not_needed \\
  head_unfold cf_if_def \\
  irule local_elim \\ hnf \\
  CONV_TAC cf_eval \\
  TRY (asm_exists_tac \\ simp [] \\ conj_tac \\ DISCH_TAC)

val xif = xif_base

(* [xcases] *)

(* FIXME srw_ss () *)

fun clean_cases_conv tm = let
  val cond_conv =
      HO_REWR_CONV exists_v_of_pat_norest_length THENC
      STRIP_QUANT_CONV (LAND_CONV (RHS_CONV cf_eval)) THENC
      STRIP_QUANT_CONV (RAND_CONV (LAND_CONV (RHS_CONV cf_eval))) THENC
      SIMP_CONV (srw_ss()) [LENGTH_EQ_NUM_compute, PULL_EXISTS] THENC
      STRIP_QUANT_CONV
        (LHS_CONV cf_eval THENC SIMP_CONV (srw_ss()) [option_CLAUSES])
  val then_conv =
      HO_REWR_CONV forall_v_of_pat_norest_length THENC
      STRIP_QUANT_CONV (LAND_CONV (RHS_CONV cf_eval)) THENC
      STRIP_QUANT_CONV (RAND_CONV (LAND_CONV (RHS_CONV cf_eval))) THENC
      SIMP_CONV (srw_ss()) [LENGTH_EQ_NUM_compute, PULL_EXISTS] THENC
      STRIP_QUANT_CONV
        (LAND_CONV (LHS_CONV cf_eval) THENC
         SIMP_CONV (srw_ss()) [option_CLAUSES])
  val else_conv =
      TRY_CONV (LAND_CONV clean_cases_conv ORELSEC
                SIMP_CONV (srw_ss()) [cf_bottom_def])
in
  (RATOR_CONV (RATOR_CONV (RAND_CONV cond_conv)) THENC
   RATOR_CONV (RAND_CONV then_conv) THENC
   RAND_CONV else_conv) tm
end

val unfold_cases =
  simp [cf_cases_def] \\
  CONSEQ_CONV_TAC (CONSEQ_HO_REWRITE_CONV ([local_elim], [], [])) \\
  CONV_TAC (LAND_CONV clean_cases_conv) \\
  simp []

(* FIXME srw_ss () *)

fun validate_pat_conv tm = let
  val conv =
      REWR_CONV validate_pat_def THENC
      RAND_CONV cf_eval THENC
      LAND_CONV (REWR_CONV pat_typechecks_def) THENC
      cf_eval
  val conv' = (QUANT_CONV conv) THENC SIMP_CONV (srw_ss()) []
  val th = conv' tm
in if Teq (rhs (concl th)) then th else fail () end

val validate_pat_all_conv =
  REPEATC (
    RAND_CONV validate_pat_conv THENC RW.RW_CONV [boolTheory.AND_CLAUSES]
  )

(* FIXME srw_ss () *)

local
  val can_pmatch_all_tm =
    semanticPrimitivesTheory.can_pmatch_all_def
    |> CONJUNCT2 |> SPEC_ALL |> concl |> rand |> rand
  val c1 = SIMP_CONV (srw_ss()) [evaluatePropsTheory.can_pmatch_all_EVERY,
                                 evaluatePropsTheory.pmatch_not_type_error_EQ,
                                 semanticPrimitivesTheory.same_type_def]
  val c2 = cf_eval THENC SIMP_CONV (srw_ss()) [] THENC cf_eval
in
  fun can_pmatch_all_conv tm =
    if not (can (match_term can_pmatch_all_tm) tm)
    then NO_CONV tm else let
      val th1 = QCONV (c1 THENC c2) tm
      in if Teq (rhs (concl th1)) then th1 else QCONV c1 tm end
  val reduce_can_pmatch_all_tac =
    CONV_TAC (ONCE_DEPTH_CONV can_pmatch_all_conv)
    \\ PURE_REWRITE_TAC [boolTheory.AND_CLAUSES]
end

val xcases =
  xpull_check_not_needed \\
  unfold_cases \\
  CONV_TAC validate_pat_all_conv \\
  reduce_can_pmatch_all_tac

(* [xmatch] *)

val xmatch_base =
  xpull_check_not_needed \\
  head_unfold cf_match_def \\ irule local_elim \\
  CONV_TAC cf_eval \\
  xcases

val xmatch = xmatch_base

(* [xffi] *)

val xffi =
  xpull_check_not_needed \\
  head_unfold cf_ffi_def \\
  irule local_elim \\ hnf \\
  simp [app_ffi_def] \\ CONV_TAC cf_eval \\
  conj_tac \\ cleanup_exn_side_cond

(* [xraise] *)

val xraise =
  xpull_check_not_needed \\
  head_unfold cf_raise_def \\ CONV_TAC cf_eval \\
  HO_MATCH_MP_TAC xret_lemma \\
  cleanup_exn_side_cond

(* [xhandle] *)

fun xhandle_core cont0 cont1 =
  xpull_check_not_needed \\
  head_unfold cf_handle_def \\
  irule local_elim \\ hnf \\
  cont0 \\
  CONJ_TAC THENL [
    CONJ_TAC THENL [all_tac, cleanup_exn_side_cond],
    cont1
  ]

fun xhandle Q (g as (asl, w)) = let
  val ctx = free_varsl (w :: asl)
  val name = vname_of_post "e" (Term Q)
  val name' =
    prim_variant ctx (mk_var (name, v_ty))
    |> dest_var |> fst
  val qname = [QUOTE name']
in
  xhandle_core
    (qexists_tac Q)
    (qx_gen_tac qname \\
     CONV_TAC cf_eval \\
     TRY xpull)
    g
end

(* [xopb] *)
val xopb =
  xpull_check_not_needed \\
  head_unfold cf_opb_def \\
  CONV_TAC cf_eval \\
  irule local_elim \\ hnf \\
  simp[app_opb_def, semanticPrimitivesTheory.opb_lookup_def] \\
  cleanup_exn_side_cond

(* [xopn] *)
val xopn =
  xpull_check_not_needed \\
  head_unfold cf_opn_def \\
  CONV_TAC cf_eval \\
  irule local_elim \\ hnf \\
  simp[app_opn_def, semanticPrimitivesTheory.opn_lookup_def] \\
  cleanup_exn_side_cond

val xref = xpull_check_not_needed \\ head_unfold cf_ref_def \\
           irule local_elim \\ hnf \\ simp[app_ref_def] \\ CONV_TAC cf_eval

end
