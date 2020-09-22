From ConCert.Extraction Require Import Aux.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ErasureCorrectness.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import MetaCoqErasureCorrectnessStrong.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import WcbvEvalType.
From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import String.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require PCUICWcbvEval.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import utils.

Open Scope string.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ 'e⊢' s ▷ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma eval_const_construct_mask Σ kn ind c im cm :
  trans_env Σ e⊢ E.tConst kn ▷ E.tConstruct ind c ->
  valid_masks_env im cm Σ ->
  get_const_mask cm kn = [].
Proof.
  intros ev valid.
  depelim ev.
  unfold valid_masks_env in valid.
  apply forallb_Forall in valid.
  apply declared_constant_trans in isdecl as [(? & ? & nth)|(isbox & ? & ? & nth)]; cycle 1.
  { eapply nth_error_forall in nth; [|eassumption].
    cbn in *.
    now destruct get_const_mask. }
  eapply nth_error_forall in nth; [|eassumption].
  cbn in *.
  rewrite H in nth.
  propify.
  destruct nth as (valid_mask_body & _).
  clear -ev valid_mask_body.
  enough (#|get_const_mask cm kn| = 0) by (now destruct get_const_mask).
  apply valid_dearg_mask_spec in valid_mask_body as (Γ & inner & <- & <-).
  induction #|Γ| as [|Γlen IH] eqn:eq in Γ, inner, ev |- *.
  - now destruct Γ.
  - destruct Γ as [|[na [body|]] Γ]; cbn in *.
    + easy.
    + depelim ev.
      refold.
      rewrite subst_it_mkLambda_or_LetIn in ev2.
      erewrite <- vasses_subst_context.
      eapply IH; [eassumption|].
      now rewrite length_subst_context.
    + depelim ev.
Qed.

Theorem extract_correct (Σ : P.global_env_ext) kn ui ind c ui' (wfΣ : wf_ext Σ) exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ▷ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  extract_pcuic_env
    (pcuic_params check_masks_args)
    Σ (wf_ext_wf_squash wfΣ) [kn] (fun _ => false) = Ok exΣ ->
  trans_env exΣ e⊢ E.tConst kn ▷ E.tConstruct ind c.
Proof.
  intros ax [T wt] ev not_erasable ex.
  cbn in *.
  destruct erase_global_decls_deps_recursive as [Σex|] eqn:er; cbn in *; [|congruence].
  destruct env_closed eqn:closed; cbn in *; [|congruence].
  destruct analyze_env eqn:an; cbn in *.
  destruct is_expanded_env eqn:isexp; cbn in *; [|congruence].
  destruct valid_masks_env eqn:valid; cbn in *; [|congruence].
  inversion_clear ex.
  rewrite trans_env_debox_env_types.
  eapply erase_global_decls_deps_recursive_correct in er; eauto.
  3: left; reflexivity.
  2: intros.
  2: now eapply SafeErasureFunction.erases_erase.
  assert (ev' := ev).
  depelim ev'.
  unfold declared_constant in isdecl.
  rewrite isdecl in er.

  eapply erases_correct in er as (erv & erase_to & erev); eauto.
  2: now constructor.

  depelim erase_to; [|easy].

  eapply eval_const_construct_mask in erev as no_mask; eauto.
  apply eval_evalT in erev as [erev].
  assert (ctor_exp := erev).
  eapply eval_is_expanded_aux with (k := 0) in ctor_exp; eauto.
  2: now cbn; rewrite no_mask.
  cbn in *.
  eapply dearg_correct in erev; eauto.
  - cbn in *.
    rewrite no_mask in erev.
    destruct get_ctor_mask; [|easy].
    cbn in *.
    now apply evalT_eval.
  - cbn.
    now rewrite no_mask.
Qed.