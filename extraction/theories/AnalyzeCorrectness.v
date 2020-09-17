From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From Coq Require Import Arith.
From Coq Require Import Btauto.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Psatz.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Template Require Import utils.
Import ListNotations.
Import ExAst.
Open Scope bool.

Lemma get_mib_masks_eq kn mm im :
  get_mib_masks ((kn, mm) :: im) kn = Some mm.
Proof.
  unfold get_mib_masks.
  cbn.
  now rewrite eq_kername_refl.
Qed.

Lemma get_mib_masks_ne p im kn :
  fst p <> kn ->
  get_mib_masks (p :: im) kn = get_mib_masks im kn.
Proof.
  intros ne.
  unfold get_mib_masks.
  destruct p; cbn in *.
  unfold eq_kername.
  now destruct (kername_eq_dec _ _).
Qed.

Lemma get_const_mask_eq kn mask cm :
  get_const_mask ((kn, mask) :: cm) kn = mask.
Proof.
  unfold get_const_mask.
  cbn.
  now rewrite eq_kername_refl.
Qed.

Lemma valid_case_masks_add_new Σ kn brs im ind npars m :
  lookup_env Σ kn = None ->
  inductive_mind ind <> kn ->
  Forall (fun br => wfe_term Σ br.2) brs ->
  valid_case_masks im ind npars brs ->
  valid_case_masks ((kn, m) :: im) ind npars brs.
Proof.
  intros no_prev ne wf_brs valid_brs.
  unfold valid_case_masks in *.
  now rewrite get_mib_masks_ne.
Qed.

Lemma valid_proj_add_new Σ kn im ind npars arg m :
  lookup_env Σ kn = None ->
  inductive_mind ind <> kn ->
  valid_proj im ind npars arg ->
  valid_proj ((kn, m) :: im) ind npars arg.
Proof.
  intros no_prev ne valid_p.
  unfold valid_proj.
  now rewrite get_mib_masks_ne.
Qed.

Lemma valid_cases_add_new Σ kn t im m :
  lookup_env Σ kn = None ->
  wfe_term Σ t ->
  valid_cases im t ->
  valid_cases ((kn, m) :: im) t.
Proof.
  intros no_prev wf_t valid_t.
  induction t using term_forall_list_ind; cbn in *; propify; auto; try tauto.
  - induction H; [easy|].
    cbn in *.
    now propify.
  - destruct p.
    propify.
    apply and_assoc.
    split; [easy|].
    split; cycle 1.
    + unfold lookup_minductive in *.
      destruct (lookup_env Σ (inductive_mind i)) eqn:ind_found; [|easy].
      eapply valid_case_masks_add_new; [eassumption|congruence| |easy].
      now apply forallb_Forall.
    + destruct valid_t as ((_ & valid_brs) & _).
      destruct wf_t as (_ & wf_brs).
      induction X; [easy|].
      cbn in *.
      propify; split; [easy|].
      now apply IHX.
  - destruct s as ((ind & npars) & arg).
    propify; split; [easy|].
    unfold lookup_minductive in *.
    destruct (lookup_env Σ (inductive_mind ind)) eqn:ind_found; [|easy].
    now eapply valid_proj_add_new.
  - induction H; [easy|].
    cbn in *; propify.
    now rewrite H.
  - induction H; [easy|].
    cbn in *; propify.
    now rewrite H.
Qed.

Lemma valid_masks_decl_add_ind Σ kn im cm m :
  lookup_env Σ kn = None ->
  wfe_env Σ ->
  valid_masks_env im cm Σ ->
  forallb (valid_masks_decl ((kn, m) :: im) cm) Σ.
Proof.
  intros no_prev wfe valid.
  induction Σ as [|(kn', decl) Σ IH]; [easy|].
  cbn in *.
  unfold eq_kername in no_prev.
  destruct (kername_eq_dec _ _); [easy|].
  destruct decl; cbn in *; propify; [|easy|easy].
  destruct c.
  destruct cst_body; cbn in *; [|easy].
  propify.
  split; [|easy].
  split; [easy|].
  now eapply valid_cases_add_new.
Qed.

Lemma valid_masks_decl_add_const Σ kn im cm mask :
  lookup_env Σ kn = None ->
  wfe_env Σ ->
  valid_masks_env im cm Σ ->
  forallb (valid_masks_decl im ((kn, mask) :: cm)) Σ.
Proof.
  intros no_prev wfe valid.
  induction Σ as [|(kn', decl) Σ IH]; [easy|].
  cbn in *.
  unfold eq_kername in no_prev.
  destruct (kername_eq_dec _ _); [easy|].
  destruct decl; cbn in *; propify; [|easy|easy].
  destruct c.
  destruct cst_body; cbn in *; [|easy].
  propify.
  split; [|easy].
  split; [|easy].
  Admitted.

Lemma nth_clear_bit_eq k bs :
  nth k (clear_bit k bs) false = false.
Proof.
  revert bs.
  induction k as [|k IH]; intros bs; cbn in *.
  - now destruct bs.
  - now destruct bs.
Qed.

Lemma nth_clear_bit_neq k k' bs :
  k <> k' ->
  nth k (clear_bit k' bs) false = nth k bs false.
Proof.
  revert bs k'.
  induction k as [|k IH]; intros bs k' ne.
  - destruct k'; [easy|].
    now destruct bs.
  - destruct k'.
    + destruct bs; [|easy].
      now destruct k.
    + destruct bs; [easy|].
      cbn.
      now apply IH.
Qed.

Lemma hd_nth {A} d (l : list A) :
  hd d l = nth 0 l d.
Proof. now destruct l. Qed.

Lemma nth_tl {A} k (l : list A) d :
  nth k (tl l) d = nth (S k) l d.
Proof.
  destruct l.
  - now destruct k.
  - easy.
Qed.

Lemma analyze_top_level_analyze state n t :
  analyze_top_level analyze state n t =
  ((analyze_top_level analyze state n t).1, analyze state t).
Proof.
  induction t in state, n |- * using term_forall_list_ind; cbn in *; auto.
  - destruct n; [easy|].
    destruct analyze_top_level eqn:an.
    rewrite IHt in an.
    now noconf an.
  - destruct analyze_top_level eqn:an.
    rewrite IHt2 in an.
    now noconf an.
Qed.

Lemma analyze_case_branches_analyze ind c brs state cm :
  analyze_case_branches analyze ind c brs state cm =
  (fold_right (fun br state => analyze state br.2) state brs,
   (analyze_case_branches analyze ind c brs state cm).2).
Proof.
  induction brs in c, state, cm |- *; [easy|].
  cbn in *.
  destruct a.
  now rewrite IHbrs, analyze_top_level_analyze.
Qed.

Definition consistent_mib_mask (mm : mib_masks) (mib : mutual_inductive_body) : Prop :=
  (#|param_mask mm| = ind_npars mib) /\
  ∥Alli (fun ind oib =>
           Alli (fun c '(_, args) => #|get_branch_mask (ctor_masks mm) ind c| = #|args|)
                0
                (ind_ctors oib))
   0
   (ind_bodies mib)∥.

Definition consistent_mib_masks (Σ : global_env) (im : list (kername × mib_masks)) : Prop :=
  forall kn,
    match lookup_minductive Σ kn with
    | Some mib =>
      match get_mib_masks im kn with
      | Some mm => consistent_mib_mask mm mib
      | None => False
      end
    | None => True
    end.

Lemma get_mib_masks_update_eq im kn mm' mm :
  get_mib_masks im kn = Some mm' ->
  get_mib_masks (update_mib_masks kn mm im) kn = Some mm.
Proof.
  intros ex.
  induction im as [|(kn', mm'') im IH]; [easy|].
  cbn in *.
  unfold eq_kername.
  destruct (kername_eq_dec kn' kn) as [->|].
  - now rewrite get_mib_masks_eq.
  - now rewrite get_mib_masks_ne in * by easy.
Qed.

Lemma get_mib_masks_update_neq kn mm im kn' :
  kn' <> kn ->
  get_mib_masks (update_mib_masks kn mm im) kn' = get_mib_masks im kn'.
Proof.
  intros ne.
  induction im as [|(kn'', mm') im IH]; [easy|].
  cbn in *.
  unfold eq_kername.
  destruct (kername_eq_dec kn'' kn) as [->|].
  - now rewrite !get_mib_masks_ne in * by easy.
  - unfold get_mib_masks.
    cbn.
    unfold eq_kername.
    now destruct (kername_eq_dec kn'' kn'); [congruence|].
Qed.

Lemma consistent_mib_masks_update Σ im kn mm mib :
  consistent_mib_masks Σ im ->
  consistent_mib_mask mm mib ->
  lookup_minductive Σ kn = Some mib ->
  consistent_mib_masks Σ (update_mib_masks kn mm im).
Proof.
  intros cons_mms cons_mm found kn'.
  destruct (eq_dec kn kn') as [<-|].
  - specialize (cons_mms kn).
    rewrite found in *.
    destruct get_mib_masks eqn:mmeq in cons_mms; [|easy].
    now erewrite get_mib_masks_update_eq by eassumption.
  - specialize (cons_mms kn').
    destruct lookup_minductive; [|easy].
    now rewrite get_mib_masks_update_neq by easy.
Qed.

(*
Lemma mib_masks_consistent_analyze Σ t state :
  wfe_term Σ t ->
  consistent_mib_masks Σ state.2 ->
  consistent_mib_masks Σ (analyze state t).2.
Proof.
  intros wf_t cons_mm.
  induction t in state, wf_t, cons_mm |- * using term_forall_list_ind; cbn in *; auto.
  - induction H; [easy|].
    cbn in *.
    now propify.
  - propify.
    now apply IHt2, IHt1.
  - propify.
    now apply IHt2, IHt1.
  - destruct p.
    propify.
    destruct get_mib_masks eqn:mm; [|easy].
    destruct analyze_case_branches eqn:an.
    apply IHt in cons_mm; [|easy].
    specialize (cons_mm (inductive_mind i)) as cons.
    destruct lookup_minductive eqn:?; [|now propify].
    rewrite mm in *.
    cbn.
    eapply consistent_mib_masks_update.
    + admit.
    + now destruct m0.
    cbn.
    eapply consistent_mib_masks_update. [easy| |eassumption].
    induction X.
    + cbn.
      apply IHt in cons_mm; [|easy].
      specialize (cons_mm (inductive_mind i)) as cons.
      destruct lookup_minductive eqn:?; [|now propify].
      rewrite mm in *.
      eapply consistent_mib_masks_update; [easy| |eassumption].
      now destruct m.
    + cbn in *.
      * apply IHt.
      destruct get_mib_masks eqn:mm' in valid_im; [|easy].
      propify.
      destruct wf_t as ((<- & ?) & _).

    easy.
    easy.
    apply H in valid_im.
    easy.
*)

Lemma nth_skipn {A} i n (l : list A) a :
  nth i (skipn n l) a = nth (n + i) l a.
Proof. now rewrite !nth_nth_error, nth_error_skipn. Qed.

Lemma nth_app_left_eq {A} i n (l l' : list A) a :
  i = #|l| ->
  nth (i + n) (l ++ l') a = nth n l' a.
Proof.
  intros ->.
  now rewrite app_nth2, minus_plus by lia.
Qed.

Lemma nth_analyze k state t :
  nth k (analyze state t).1 false = nth k state.1 false && is_dead k t.
Proof.
  induction t in k, state |- * using term_forall_list_ind; cbn in *; propify.
  - now btauto.
  - destruct (Nat.eqb_spec n k) as [<-|];
      [rewrite nth_clear_bit_eq|rewrite nth_clear_bit_neq by easy];
      btauto.
  - now btauto.
  - induction H; cbn in *; [now btauto|].
    rewrite H, IHForall.
    now btauto.
  - rewrite nth_tl, IHt by easy.
    cbn.
    now btauto.
  - rewrite nth_tl, IHt2 by easy.
    cbn.
    rewrite IHt1 by easy.
    now btauto.
  - rewrite IHt2, IHt1 by easy.
    now btauto.
  - now btauto.
  - now btauto.
  - destruct p as (ind & npars).
    destruct get_mib_masks.
    + rewrite analyze_case_branches_analyze.
      cbn.
      induction X; cbn in *; [now rewrite IHt; btauto|].
      rewrite p, IHX.
      now btauto.
    + induction X; cbn in *; [now rewrite IHt; btauto|].
      rewrite p, IHX.
      now btauto.
  - destruct s as ((ind & npars) & arg).
    destruct get_mib_masks.
    + cbn.
      now rewrite IHt.
    + now rewrite IHt.
  - rewrite nth_skipn.
    generalize #|m|.
    induction H in k, m, H |- *; intros; cbn in *.
    + rewrite nth_app_left_eq by now rewrite repeat_length.
      now btauto.
    + rewrite H, IHForall.
      now btauto.
  - rewrite nth_skipn.
    generalize #|m|.
    induction H in k, m, H |- *; intros; cbn in *.
    + rewrite nth_app_left_eq by now rewrite repeat_length.
      now btauto.
    + rewrite H, IHForall.
      now btauto.
Qed.

Lemma valid_dearg_mask_analyze_top_level state n t :
  valid_dearg_mask (analyze_top_level analyze state n t).1 t.
Proof.
  induction t in state, n |- * using term_forall_list_ind; cbn in *; auto.
  - destruct n; [easy|].
    destruct analyze_top_level eqn:an.
    rewrite analyze_top_level_analyze in an.
    cbn in *.
    noconf an.
    rewrite hd_nth, nth_analyze.
    cbn.
    propify; split; [|now apply IHt].
    now btauto.
  - destruct analyze_top_level eqn:an.
    rewrite analyze_top_level_analyze in an.
    cbn in *.
    noconf an.
    apply IHt2.
Qed.

(*
Lemma valid_cases_update_mib_masks_branches im t kn ind c mm mm' i :
  valid_cases im t ->
  get_mib_masks im kn = Some mm ->
  ctor_masks mm' = analyze_case_branches analyze ind c brs  update_ind_ctor_mask ind c (ctor_masks mm) (clear_bit i) ->
  valid_cases (update_mib_masks kn mm' im) t.
Proof.
  Admitted.
*)

(*
Lemma valid_case_masks_update_mib_masks_one_additive im ind npars brs kn mm mm' ind' c i :
  valid_case_masks im ind npars brs ->
  get_mib_masks im kn = Some mm ->
  ctor_masks mm' = update_ind_ctor_mask ind' c (ctor_masks mm) (clear_bit i) ->
  valid_case_masks (update_mib_masks kn mm' im) ind npars brs.
Proof.
  Admitted.
*)

Definition additive_ctor_masks (mm_old mm_new : mib_masks) : Prop :=
  param_mask mm_new = param_mask mm_old /\
  forall ind c,
    Forall2 implb
            (get_branch_mask (ctor_masks mm_new) ind c)
            (get_branch_mask (ctor_masks mm_old) ind c).

Instance Reflexive_additive_ctor_masks : RelationClasses.Reflexive additive_ctor_masks.
Proof.
  intros x.
  split; [easy|].
  intros.
  apply Forall2_same.
  now intros [].
Qed.

Instance Transitive_additive_ctor_masks : RelationClasses.Transitive additive_ctor_masks.
Proof.
  intros x y z [] [].
  split; [congruence|].
  intros.
  specialize (H0 ind c).
  specialize (H2 ind c).
  enough (RelationClasses.Transitive (Forall2 implb)).
  { now specialize (H3 _ _ _ H2 H0). }
  apply Forall2_trans.
  clear.
  now intros [] [] [] ? ?.
Qed.

Lemma valid_dearg_mask_additive new old t :
  Forall2 implb new old ->
  valid_dearg_mask old t ->
  valid_dearg_mask new t.
Proof.
  intros all valid_old.
  induction t in new, old, all, valid_old |- *; cbn in *; auto; try solve [now destruct all].
  destruct all; [easy|].
  propify.
  now destruct x, y.
Qed.

Lemma valid_case_masks_update_mib_masks_additive im ind npars brs kn mm mm' :
  valid_case_masks im ind npars brs ->
  get_mib_masks im kn = Some mm ->
  additive_ctor_masks mm mm' ->
  valid_case_masks (update_mib_masks kn mm' im) ind npars brs.
Proof.
  intros valid mmeq add.
  unfold valid_case_masks in *.
  destruct (eq_dec kn (inductive_mind ind)) as [->|].
  - erewrite get_mib_masks_update_eq by easy.
    rewrite mmeq in *.
    unfold additive_ctor_masks in *.
    propify.
    split; [intuition auto; congruence|].
    destruct valid as (_ & valid).
    destruct add as (_ & add).
    revert valid.
    generalize 0 as c.
    induction brs as [|(ar & br) brs IH]; [easy|].
    intros c valid.
    cbn in *.
    propify.
    split; [|easy].
    clear IH.
    specialize (add (inductive_ind ind) c).
    split; [now apply Forall2_length in add as ->|].
    destruct valid as ((_ & valid) & _).
    now eapply valid_dearg_mask_additive.
  - now rewrite get_mib_masks_update_neq by easy.
Qed.

Lemma valid_cases_update_mib_masks_additive im t kn mm mm' :
  valid_cases im t ->
  get_mib_masks im kn = Some mm ->
  additive_ctor_masks mm mm' ->
  valid_cases (update_mib_masks kn mm' im) t.
Proof.
  intros valid_t mmeq add.
  induction t using term_forall_list_ind; cbn in *; auto.
  - induction H; [easy|].
    cbn in *.
    now propify.
  - propify.
    now rewrite IHt1, IHt2.
  - propify.
    now rewrite IHt1, IHt2.
  - destruct p.
    propify.
    rewrite IHt by easy.
    split.
    + split; [easy|].
      destruct valid_t as ((_ & valid_brs) & _).
      induction X; cbn in *; [easy|].
      now propify.
    + now eapply valid_case_masks_update_mib_masks_additive.
  - destruct s as ((ind' & npars) & arg).
    propify.
    split; [easy|].
    unfold valid_proj.
    destruct (eq_dec kn (inductive_mind ind')) as [->|].
    + erewrite get_mib_masks_update_eq by eassumption.
      unfold valid_proj in valid_t.
      rewrite mmeq in *.
      propify.
      destruct add as (param_masks & branch_masks).
      split; [intuition auto; congruence|].
      specialize (branch_masks (inductive_ind ind') 0).
      rewrite !nth_nth_error in *.
      destruct nth_error eqn:nth in |- *; [|easy].
      eapply Forall2_nth_error_Some in branch_masks as (? & eq & ?); [|eassumption].
      rewrite eq in *.
      now destruct b, x.
    + now erewrite get_mib_masks_update_neq by easy.
  - induction H; [easy|].
    cbn in *.
    now propify.
  - induction H; [easy|].
    cbn in *.
    now propify.
Qed.

Lemma analyze_top_level_same_max_lams s1 s2 max_lams t :
  (analyze_top_level analyze s1 max_lams t).1 =
  (analyze_top_level analyze s2 max_lams t).1.
Proof.
  induction t in s1, s2, max_lams |- * using term_forall_list_ind; cbn in *; auto.
  - destruct max_lams; [easy|].
    destruct analyze_top_level eqn:an.
    destruct analyze_top_level eqn:an' in |- *.
    cbn.
    rewrite analyze_top_level_analyze in an, an'.
    noconf an.
    noconf an'.
    f_equal; [|now apply IHt].
    now rewrite !hd_nth, !nth_analyze.
  - destruct analyze_top_level eqn:an.
    destruct analyze_top_level eqn:an' in |- *.
    cbn.
    rewrite analyze_top_level_analyze in an, an'.
    noconf an.
    noconf an'.
    apply IHt2.
Qed.

Lemma analyze_ind_masks_eq state1 state2 t :
  state1.2 = state2.2 ->
  (analyze state1 t).2 = (analyze state2 t).2.
Proof.
  intros eq.
  induction t in state1, state2, eq |- * using term_forall_list_ind; cbn in *; auto.
  - induction H; [easy|].
    now apply H, IHForall.
  - now apply IHt2, IHt1.
  - destruct p.
    erewrite IHt by eassumption.
    destruct get_mib_masks.
    + enough (
          forall state1 state2 ind n masks,
            state1.2 = state2.2 ->
            (analyze_case_branches analyze ind n l state1 masks).2 =
            (analyze_case_branches analyze ind n l state2 masks).2).
      { rewrite analyze_case_branches_analyze.
        symmetry.
        rewrite analyze_case_branches_analyze.
        cbn.
        f_equal; cycle 1.
        { clear -X eq IHt.
          induction X in |- *; [easy|].
          apply p, IHX. }
        f_equal.
        now apply H, IHt. }

      clear -X.
      intros state1 state2 ind n masks eq.
      induction X in state1, state2, n, eq |- ; [easy|].
      cbn in *.
      destruct x.
      rewrite analyze_case_branches_analyze.
      symmetry; rewrite analyze_case_branches_analyze.
      rewrite analyze_top_level_analyze.
      symmetry; rewrite analyze_top_level_analyze.
      cbn.
      rewrite (IHX state1 state2) by easy.
      now erewrite analyze_top_level_same_max_lams.
    + induction X; [easy|].
      now apply p, IHX.
  - destruct s as ((ind & npars) & arg).
    erewrite IHt by eassumption.
    destruct get_mib_masks; [|now apply IHt].
    cbn.
    f_equal.
    now apply IHt.
  - generalize #|m|.
    induction H; [easy|].
    intros.
    cbn in *.
    apply H, IHForall.
  - generalize #|m|.
    induction H; [easy|].
    intros.
    cbn in *.
    apply H, IHForall.
Qed.

Lemma analyze_additive_ctor_masks state kn mm_old t :
  get_mib_masks state.2 kn = Some mm_old ->
  exists mm_new,
    get_mib_masks (analyze state t).2 kn = Some mm_new /\
    additive_ctor_masks mm_old mm_new.
Proof.
  intros get_old.
  induction t in state, mm_old, get_old |- * using term_forall_list_ind; cbn in *;
    try solve [now exists mm_old].
  - induction H; cbn in *.
    + now exists mm_old.
    + destruct IHForall as (? & ? & ?).
      apply H in H1 as (? & ? & ?).
      exists x1.
      split; [easy|].
      now transitivity x0.
  - now apply IHt.
  - apply IHt2 in get_old as (? & ? & ?).
    apply IHt1 in H as (? & ? & ?).
    exists x0.
    unfold new_var.
    eexists; split; [eauto|].

      apply
      * easy.
      * eapply
      eapply IHForall in get_old; [|eassumption].

Lemma valid_cases_analyze_additive state t t' :
  valid_cases state.2 t ->
  valid_cases (analyze state t').2 t.
Proof.
  intros valid_t.
  induction t' in state, t, valid_t |- * using term_forall_list_ind; cbn in *; auto.
  - now induction H.
  - now apply IHt'2, IHt'1.
  - destruct p.
    destruct get_mib_masks eqn:mm.
    + rewrite analyze_case_branches_analyze.
      cbn in *.
      assert (exists m',
                 fold_right (fun br state => analyze state br.2) (analyze state t') brs

      destruct analyze_case_branches eqn:an.
      cbn.
      eapply valid_cases_update_mib_masks_additive.
      rewrite analyze_case_branches_analyze.
      cbn in *.
      eapply valid_cases_update_mib_masks_additive.
      * now induction X.
      *
      generalize l at 1.
      induction X; intros; cbn in *.
      * eapply valid_cases_update_mib_masks_additive; eauto.
        split; [easy|].
        cbn.
        admit.
      * eapply valid_cases_update_mib_masks_additive; eauto.
        unfold get_branch_mask.
        cbn.
        -- now apply IHt'.
        -- eassumption.
        now apply IHt'.
      * eapply valid_cases_update_mib_masks_branches_additive.
      *
      admit.
    + now induction X.*)
    admit.
  - destruct s as ((ind & npars) & arg).
    destruct get_mib_masks eqn:mm; [|now apply IHt'].
    cbn.
    eapply valid_cases_update_mib_masks_one; [easy|eassumption|].
    cbn.
    reflexivity.
  -

Lemma valid_cases_analyze state t :
  valid_cases (analyze state t).2 t.
Proof.
  induction t in state |- * using term_forall_list_ind; cbn in *; auto.
  - induction H; intros; cbn in *; [easy|].
    propify; split; [now apply H|].
    eapply forallb_impl; [|eassumption].
    intros.
    now apply valid_cases_analyze_additive.
    induction l; [easy|].
    cbn.
    rewrite valid_cases_analyze_additive.
    cbn.
    apply IHl.
    pose proof valid_cases_analyze_additive; unfold is_true in *.
    pattern(fold_right (fun (t : term) (state0 : analyze_state) => analyze state0 t) state l).
    rewrite H1.
pattern (valid_cases
       (analyze
          (fold_right (fun (t : term) (state0 : analyze_state) => analyze state0 t) state l) x).2).
rewrite H1.
    pattern valid_cases.
    rewrite H1.
    rewrite valid_cases_analyze_additive.
    cbn in *.
    rewrite H.
    rewrite IHForall.

Lemma analyze_env_correct Σ :
  wfe_env Σ ->
  let (consts, inds) := analyze_env Σ in
  valid_masks_env inds consts Σ.
Proof.
  intros wfe.
  induction Σ as [|(kn, decl) Σ IH]; [easy|].
  cbn in *.
  destruct lookup_env eqn:no_prev; [easy|].
  cbn in *; propify.
  specialize (IH (proj2 wfe)).
  destruct (analyze_env Σ).
  destruct decl; cycle 1; cbn.
  - now apply valid_masks_decl_add_ind.
  - easy.
  - destruct analyze_constant eqn:an.
    propify.
    split.
    + destruct c, cst_body; [|easy].
      rewrite get_const_mask_eq.
      propify.
      cbn in *.
      destruct analyze_top_level eqn:an'.
      destruct a.
      noconf an.
      rewrite analyze_top_level_analyze in an'.
      noconf an'.
      split; [now apply valid_dearg_mask_analyze_top_level|].
      destruct analyze_top_level eqn:an.
      destruct a.
      cbn in *.
      noconf an'.
Lemma analyze_correct :
    + apply valid_masks_decl_add_const; [easy|easy|].
      admit.
