From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From Coq Require Import Arith.
From Coq Require Import Btauto.
From Coq Require Import Bool.
From Coq Require Import List.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Template Require Import utils.
Import ListNotations.
Import ExAst.
Open Scope bool.

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

Lemma valid_masks_decl_add_new Σ kn im cm m :
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

Lemma analyze_correct Σ :
  wfe_env Σ ->
  let (consts, inds) := analyze_env Σ in
  valid_masks_env inds consts Σ.
Proof.
  intros wfe.
  induction Σ as [|(kn, decl) Σ IH]; [easy|].
  cbn in *.
  propify.
  specialize (IH (proj2 wfe)).
  destruct (analyze_env Σ).
  destruct decl; cycle 1; cbn.
  - destruct lookup_env eqn:no_prev; [easy|].
    now apply valid_masks_decl_add_new.
  - easy.
  -
