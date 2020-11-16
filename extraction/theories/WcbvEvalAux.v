From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import ClosedAux.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Eqdep_dec.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import EInversion.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.
Set Equations Transparent.

Notation "Σ 'e⊢' s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Global Arguments eval_unique_sig {_ _ _ _ _}.
Global Arguments eval_deterministic {_ _ _ _ _}.
Global Arguments eval_unique {_ _ _ _}.

Lemma isBox_mkApps hd args :
  isBox (mkApps hd args) = isBox hd && (#|args| =? 0).
Proof.
  destruct args using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, app_length.
    cbn.
    rewrite Nat.add_comm.
    cbn.
    now rewrite Bool.andb_false_r.
Qed.

Lemma isLambda_mkApps hd args :
  isLambda (mkApps hd args) = isLambda hd && (#|args| =? 0).
Proof.
  destruct args using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, app_length.
    cbn.
    symmetry; propify.
    right; easy.
Qed.

Section fix_flags.
Context {wfl : WcbvFlags}.

Lemma eval_tApp_inv Σ hd arg v :
  Σ e⊢ tApp hd arg ▷ v ->
  ∑ hdv argv,
    Σ e⊢ hd ▷ hdv ×
    Σ e⊢ arg ▷ argv.
Proof.
  intros ev.
  depelim ev; try solve [eexists _, _; split; eauto].
  depelim i.
Qed.

Lemma eval_mkApps_inv Σ hd args v :
  Σ e⊢ mkApps hd args ▷ v ->
  ∑ hdv argsv,
    Σ e⊢ hd ▷ hdv ×
    All2 (eval Σ) args argsv.
Proof.
  revert hd v.
  induction args; intros hd v ev.
  - exists v, []; split; eauto.
  - cbn in *.
    apply IHargs in ev as (?&?&?&?).
    apply eval_tApp_inv in e as (?&?&?&?).
    eexists _, (_ :: _).
    split; eauto.
Qed.

Lemma eval_tApp_congr Σ hd hdv arg argv hd' arg' v :
  Σ e⊢ hd ▷ hdv ->
  Σ e⊢ arg ▷ argv ->
  Σ e⊢ hd' ▷ hdv ->
  Σ e⊢ arg' ▷ argv ->
  Σ e⊢ tApp hd' arg' ▷ v ->
  Σ e⊢ tApp hd arg ▷ v.
Proof.
  intros ev_hd ev_arg ev_hd' ev_arg' ev_app'.
  depind ev_app';
    repeat
      match goal with
      | [H: Σ e⊢ ?t ▷ ?v1, H': Σ e⊢ ?t ▷ ?v2 |- _] =>
        pose proof (eval_unique_sig H H') as eq; noconf eq
      end; try solve [econstructor; eauto].
  depelim i.
Qed.

Lemma eval_mkApps_congr Σ hd hdv args argsv hd' args' v :
  Σ e⊢ hd ▷ hdv ->
  All2 (eval Σ) args argsv ->
  Σ e⊢ hd' ▷ hdv ->
  All2 (eval Σ) args' argsv ->
  Σ e⊢ mkApps hd' args' ▷ v ->
  Σ e⊢ mkApps hd args ▷ v.
Proof.
  intros ev_hd ev_args ev_hd' ev_args' ev_apps.
  induction ev_args in
      hd, hdv, args, argsv, hd', args', v, ev_hd, ev_args, ev_hd', ev_args', ev_apps |- *;
    cbn in *.
  - depelim ev_args'.
    cbn in *.
    pose proof (eval_unique_sig ev_hd' ev_apps) as eq; noconf eq.
    auto.
  - depelim ev_args'.
    cbn in *.
    apply eval_mkApps_inv in ev_apps as H; destruct H as (?&_&?&_).
    eapply IHev_args.
    1: eapply eval_tApp_congr; eauto.
    all: eauto.
Qed.

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_tLetIn_inv Σ na val body res :
  Σ e⊢ tLetIn na val body ▷ res ->
  ∑ val_res,
    Σ e⊢ val ▷ val_res ×
    Σ e⊢ csubst val_res 0 body ▷ res.
Proof. intros ev; depelim ev; easy. Qed.

Lemma eval_tLambda_inv Σ na body v :
  Σ e⊢ tLambda na body ▷ v ->
  v = tLambda na body.
Proof. now intros ev; depelim ev. Qed.

Lemma eval_tApp_tLambda_inv Σ na body a v :
  Σ e⊢ tApp (tLambda na body) a ▷ v ->
  ∑ av,
    Σ e⊢ a ▷ av ×
    Σ e⊢ csubst av 0 body ▷ v.
Proof.
  intros ev.
  depelim ev.
  - now apply eval_tLambda_inv in ev1.
  - apply eval_tLambda_inv in ev1.
    inversion ev1; subst; clear ev1.
    easy.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - now apply eval_tLambda_inv in ev1 as ->.
  - easy.
Qed.

Lemma lookup_env_find Σ kn :
  ETyping.lookup_env Σ kn =
  option_map snd (find (fun '(kn', _) => if kername_eq_dec kn kn' then true else false) Σ).
Proof.
  induction Σ as [|(kn' & decl) Σ IH]; [easy|].
  cbn.
  now destruct (kername_eq_dec kn kn').
Qed.

Lemma closed_constant Σ kn cst body :
  env_closed Σ ->
  ETyping.declared_constant Σ kn cst ->
  EAst.cst_body cst = Some body ->
  closed body.
Proof.
  intros env_clos decl_const body_eq.
  unfold ETyping.declared_constant in decl_const.
  rewrite lookup_env_find in decl_const.
  destruct (find _ _) eqn:find; [|easy].
  apply find_some in find.
  eapply forallb_forall in env_clos; [|exact (proj1 find)].
  destruct p.
  cbn in *.
  noconf decl_const.
  cbn in *.
  now rewrite body_eq in env_clos.
Qed.

Lemma closedn_substl k s t :
  Forall (closedn k) s ->
  closedn (k + #|s|) t ->
  closedn k (substl s t).
Proof.
  intros all clos.
  unfold substl.
  induction s in t, all, clos |- *; cbn in *.
  - now rewrite Nat.add_0_r in clos.
  - depelim all.
    apply IHs; auto.
    apply (closedn_csubst _ (k + #|s|) 0).
    + eapply closed_upwards; eauto.
      lia.
    + cbn.
      now rewrite <- Nat.add_succ_r.
Qed.

Lemma closedn_fix_subst k mfix :
  forallb (test_def (closedn (#|mfix| + k))) mfix ->
  Forall (closedn k) (fix_subst mfix).
Proof.
  intros all.
  unfold fix_subst.
  now induction #|mfix| as [|n IH] at 1.
Qed.

Lemma closedn_cunfold_fix k mfix idx narg fn :
  closedn k (tFix mfix idx) ->
  cunfold_fix mfix idx = Some (narg, fn) ->
  closedn k fn.
Proof.
  cbn.
  intros clos fix_eq.
  unfold cunfold_fix in *.
  destruct nth_error eqn:nth; [|discriminate].
  noconf fix_eq.
  apply closedn_substl.
  - apply closedn_fix_subst; auto.
  - eapply nth_error_forallb in clos.
    rewrite nth in clos.
    now rewrite Nat.add_comm, fix_subst_length.
Qed.

Lemma closedn_cofix_subst k mfix :
  forallb (test_def (closedn (#|mfix| + k))) mfix ->
  Forall (closedn k) (cofix_subst mfix).
Proof.
  intros all.
  unfold cofix_subst.
  now induction #|mfix| as [|n IH] at 1.
Qed.

Lemma closedn_cunfold_cofix k mfix idx narg fn :
  closedn k (tCoFix mfix idx) ->
  cunfold_cofix mfix idx = Some (narg, fn) ->
  closedn k fn.
Proof.
  cbn.
  intros clos fix_eq.
  unfold cunfold_cofix in *.
  destruct nth_error eqn:nth; [|discriminate].
  noconf fix_eq.
  apply closedn_substl.
  - apply closedn_cofix_subst; auto.
  - eapply nth_error_forallb in clos.
    rewrite nth in clos.
    now rewrite Nat.add_comm, cofix_subst_length.
Qed.

Lemma closedn_iota_red k pars c args brs :
  Forall (closedn k) args ->
  Forall (fun t => closedn k t.2) brs ->
  closedn k (ETyping.iota_red pars c args brs).
Proof.
  intros clos_args clos_brs.
  unfold ETyping.iota_red.
  apply closedn_mkApps.
  - rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    now eapply nth_error_forall in nth; [|eassumption].
  - now apply Forall_skipn.
Qed.

Lemma eval_closedn Σ t v k :
  Σ e⊢ t ▷ v ->
  env_closed Σ ->
  closedn k t ->
  closedn k v.
Proof.
  intros ev env_clos clos.
  induction ev; cbn in *; propify.
  - easy.
  - apply IHev3.
    now apply closedn_csubst with (k' := 0).
  - apply IHev2.
    now apply closedn_csubst with (k' := 0).
  - apply IHev2.
    apply closedn_iota_red.
    + eapply proj2.
      now eapply closedn_mkApps_inv.
    + now apply forallb_Forall.
  - subst brs.
    cbn in *.
    propify.
    apply IHev2.
    apply closedn_mkApps; [easy|].
    now apply Forall_repeat.
  - apply IHev3.
    split; [|easy].
    destruct clos as (clos & _).
    specialize (IHev1 clos).
    apply closedn_mkApps_inv in IHev1 as (? & ?).
    apply closedn_mkApps; [|easy].
    eapply closedn_cunfold_fix; eauto.
  - easy.
  - apply IHev.
    split; [|easy].
    destruct clos as (clos & _).
    apply closedn_mkApps_inv in clos.
    cbn in *.
    apply closedn_mkApps; [|easy].
    now eapply closedn_cunfold_cofix.
  - apply IHev.
    apply closedn_mkApps_inv in clos.
    apply closedn_mkApps; [|easy].
    now eapply closedn_cunfold_cofix.
  - apply IHev.
    eapply closed_upwards.
    + eapply closed_constant; eauto.
    + lia.
  - apply IHev2.
    apply closedn_mkApps_inv in IHev1 as (_ & IHev1); [|easy].
    rewrite nth_nth_error in *.
    destruct (nth_error _ _) eqn:nth_eq.
    + apply nth_error_In in nth_eq.
      rewrite Forall_forall in IHev1.
      now apply IHev1.
    + easy.
  - easy.
  - easy.
  - easy.
Qed.

Lemma eval_closed Σ t v :
  Σ e⊢ t ▷ v ->
  env_closed Σ ->
  closed t ->
  closed v.
Proof.
  eapply eval_closedn.
Qed.

Fixpoint deriv_length {Σ t v} (ev : Σ e⊢ t ▷ v) : nat :=
  match ev with
  | eval_atom _ _ => 1
  | red_cofix_case _ _ _ _ _ _ _ _ _ ev
  | red_cofix_proj _ _ _ _ _ _ _ _ ev
  | eval_delta _ _ _ _ _ _ ev
  | eval_proj_prop _ _ _ _ _ ev _ => S (deriv_length ev)
  | eval_box _ _ _ ev1 ev2
  | eval_zeta _ _ _ _ _ ev1 ev2
  | eval_iota _ _ _ _ _ _ _ ev1 _ ev2
  | eval_iota_sing _ _ _ _ _ _ _ _ ev1 _ _ ev2
  | eval_fix_value _ _ _ _ _ _ _ _ ev1 ev2 _ _
  | eval_proj _ _ _ _ _ _ ev1 _ ev2
  | eval_app_cong _ _ _ _ ev1 _ ev2 => S (deriv_length ev1 + deriv_length ev2)
  | eval_beta _ _ _ _ _ _ ev1 ev2 ev3
  | eval_fix _ _ _ _ _ _ _ _ ev1 ev2 _ ev3 =>
    S (deriv_length ev1 + deriv_length ev2 + deriv_length ev3)
  end.

Lemma deriv_length_min {Σ t v} (ev : Σ e⊢ t ▷ v) :
  1 <= deriv_length ev.
Proof. destruct ev; cbn in *; lia. Qed.

Lemma eval_tApp_deriv {Σ hd arg v} (ev : Σ e⊢ tApp hd arg ▷ v) :
  ∑ hdv (ev_hd : Σ e⊢ hd ▷ hdv) argv (ev_arg : Σ e⊢ arg ▷ argv),
    S (deriv_length ev_hd + deriv_length ev_arg) <= deriv_length ev.
Proof.
  depelim ev; cbn in *;
    try now eexists _, ev1, _, ev2.
  easy.
Qed.

Fixpoint sum_deriv_lengths {Σ ts tsv} (a : All2 (eval Σ) ts tsv) : nat :=
  match a with
  | All2_nil => 0
  | All2_cons _ _ _ _ ev a => deriv_length ev + sum_deriv_lengths a
  end.

Fixpoint app_All2
         {A B}
         {T : A -> B -> Type}
         {la lb la' lb'}
         (a1 : All2 T la lb)
         (a2 : All2 T la' lb') : All2 T (la ++ la') (lb ++ lb').
Proof.
  destruct a1.
  - exact a2.
  - refine (All2_cons t _).
    exact (app_All2 _ _ _ _ _ _ _ a1 a2).
Defined.

Lemma eval_mkApps_deriv {Σ hd args v} (ev : Σ e⊢ mkApps hd args ▷ v) :
  ∑ hdv (ev_hd : Σ e⊢ hd ▷ hdv) argsv (ev_args : All2 (eval Σ) args argsv),
    deriv_length ev_hd + #|args| + sum_deriv_lengths ev_args <= deriv_length ev.
Proof.
  revert hd v ev.
  induction args; intros hd v ev; cbn in *.
  - exists _, ev, [], All2_nil.
    now cbn.
  - specialize (IHargs _ _ ev) as (hdv & ev_hd & argsv & ev_args & len).
    specialize (eval_tApp_deriv ev_hd) as (hdv' & ev_hdv' & argv & ev_argv & len').
    exists _, ev_hdv', (argv :: argsv).
    exists (All2_cons ev_argv ev_args).
    cbn in *.
    lia.
Qed.

Lemma All2_split_eq
      {X Y} {T : X -> Y -> Type}
      {xs ys xs' ys'}
      (a : All2 T (xs ++ xs') (ys ++ ys')) :
  #|xs| = #|ys| ->
  ∑ apref asuf, a = app_All2 apref asuf.
Proof.
  intros eq.
  induction xs in xs, ys, xs', ys', a, eq |- *.
  - destruct ys; [|easy].
    cbn in *.
    now exists All2_nil, a.
  - destruct ys; [easy|].
    cbn in *.
    depelim a.
    specialize (IHxs ys xs' ys' a ltac:(easy)) as (apref & asuf & ->).
    now exists (All2_cons t apref), asuf.
Qed.

Lemma All2_rev_rect X Y (T : X -> Y -> Type) (P : forall xs ys, All2 T xs ys -> Type) :
  P [] [] All2_nil ->
  (forall x y xs ys (t : T x y) (a : All2 T xs ys),
      P xs ys a -> P (xs ++ [x]) (ys ++ [y]) (app_All2 a (All2_cons t All2_nil))) ->
  forall xs ys (a : All2 T xs ys), P xs ys a.
Proof.
  intros nil_case snoc_case.
  induction xs using MCList.rev_ind; intros ys a.
  - now depelim a.
  - destruct ys as [|y ys _] using MCList.rev_ind.
    + apply All2_length in a as ?.
      rewrite app_length in *.
      now cbn in *.
    + unshelve epose proof (All2_split_eq a _) as (? & ? & ->).
      * apply All2_length in a.
        rewrite !app_length in a.
        now cbn in *.
      * depelim x1.
        depelim x3.
        apply snoc_case.
        apply IHxs.
Qed.

Inductive All2_eval_app_spec Σ : list term -> term ->
                                 list term -> term ->
                                 forall ts tsv, All2 (eval Σ) ts tsv -> Type :=
| All2_eval_app_intro {ts tsv} (a : All2 (eval Σ) ts tsv)
                      {x xv} (evx : Σ e⊢ x ▷ xv) :
    All2_eval_app_spec
      Σ ts x tsv xv
      (ts ++ [x])
      (tsv ++ [xv])
      (app_All2 a (All2_cons evx All2_nil)).

Derive Signature for All2.
Derive NoConfusionHom for All2.

Lemma All2_eval_snoc_elim
      {Σ ts tsv x xv} (a : All2 (eval Σ) (ts ++ [x]) (tsv ++ [xv])) :
  All2_eval_app_spec Σ ts x tsv xv _ _ a.
Proof.
  unshelve epose proof (All2_split_eq a _) as (? & ev & ->).
  - apply All2_length in a.
    rewrite !app_length in a.
    now cbn in *.
  - depelim ev.
    depelim ev.
    constructor.
Qed.

Lemma eval_tApp_heads_deriv {Σ hd hd' hdv arg v}
      (ev_hd : Σ e⊢ hd ▷ hdv)
      (ev_hd' : Σ e⊢ hd' ▷ hdv)
      (ev_app : Σ e⊢ tApp hd arg ▷ v) :
  ∑ (ev_app' : Σ e⊢ tApp hd' arg ▷ v),
    (deriv_length ev_app + deriv_length ev_hd' = deriv_length ev_app' + deriv_length ev_hd)%nat.
Proof.
  depind ev_app.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_box|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_beta|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix_value|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_app_cong|].
    cbn; lia.
  - easy.
Qed.

Lemma eval_mkApps_heads_deriv {Σ hd hd' hdv args v}
      (ev_hd : Σ e⊢ hd ▷ hdv)
      (ev_hd' : Σ e⊢ hd' ▷ hdv)
      (ev_apps : Σ e⊢ mkApps hd args ▷ v) :
  ∑ (ev_apps' : Σ e⊢ mkApps hd' args ▷ v),
  (deriv_length ev_apps + deriv_length ev_hd' = deriv_length ev_apps' + deriv_length ev_hd)%nat.
Proof.
  revert hd hd' hdv v ev_hd ev_hd' ev_apps.
  induction args using MCList.rev_ind; intros; cbn in *.
  - pose proof (eval_unique_sig ev_hd ev_apps) as H; noconf H.
    exists ev_hd'; lia.
  - revert ev_apps; rewrite !mkApps_app; intros.
    cbn in *.
    eapply eval_tApp_inv in ev_apps as ev_apps'.
    destruct ev_apps' as (?&_&ev_apps'&_).
    specialize (IHargs _ _ _ _ ev_hd ev_hd' ev_apps') as (ev_apps'' & ?).
    pose proof (eval_tApp_heads_deriv ev_apps' ev_apps'' ev_apps) as (ev & ?).
    exists ev.
    lia.
Qed.

End fix_flags.
