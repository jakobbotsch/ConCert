From Coq Require Import List.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import WcbvEvalAux.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.

Import ListNotations.

Section env_eval.
  Context {wfl : WcbvFlags}.

  Reserved Notation "Σ ;;; σ 'e⊢' t ▷ v" (at level 50, σ, t, v at next level).

  Inductive env_eval (Σ : global_declarations) (σ : list term) : term -> term -> Type :=
  | env_eval_rel i v :
      nth_error σ i = Some v ->
      Σ ;;; σ e⊢ tRel i ▷ v
  | env_eval_box a t t' :
      Σ ;;; σ e⊢ a ▷ tBox ->
      Σ ;;; σ e⊢ t ▷ t' ->
      Σ ;;; σ e⊢ tApp a t ▷ tBox
  | env_eval_beta f na b a a' res :
      Σ ;;; σ e⊢ f ▷ tLambda na b ->
      Σ ;;; σ e⊢ a ▷ a' ->
      Σ ;;; (a' :: σ) e⊢ b ▷ res ->
      Σ ;;; σ e⊢ tApp f a ▷ res
  | env_eval_zeta na b0 b0' b1 res :
      Σ ;;; σ e⊢ b0 ▷ b0' ->
      Σ ;;; (b0' :: σ) e⊢ b1 ▷ res ->
      Σ ;;; σ e⊢ tLetIn na b0 b1 ▷ res
  | env_eval_iota ind pars discr c args brs res :
      Σ ;;; σ e⊢ discr ▷ mkApps (tConstruct ind c) args ->
      is_propositional Σ ind = Some false ->
      Σ ;;; σ e⊢ iota_red pars c args brs ▷ res ->
      Σ ;;; σ e⊢ tCase (ind, pars) discr brs ▷ res
  | env_eval_iota_sing ind pars discr brs n f res :
      with_prop_case ->
      Σ ;;; σ e⊢ discr ▷ tBox ->
      is_propositional Σ ind = Some true ->
      brs = [(n, f)] ->
      Σ ;;; σ e⊢ mkApps f (repeat tBox n) ▷ res ->
      Σ ;;; σ e⊢ tCase (ind, pars) discr brs ▷ res
  | env_eval_fix f mfix idx argsv a av def res :
      Σ ;;; σ e⊢ f ▷ mkApps (tFix mfix idx) argsv ->
      Σ ;;; σ e⊢ a ▷ av ->
      nth_error mfix idx = Some def ->
      #|argsv| = rarg def ->
      Σ ;;; (fix_subst mfix ++ σ) e⊢ tApp (mkApps (dbody def) argsv) av ▷ res ->
      Σ ;;; σ e⊢ tApp f a ▷ res
  | env_eval_fix_value f mfix idx argsv a av def :
      Σ ;;; σ e⊢ f ▷ mkApps (tFix mfix idx) argsv ->
      Σ ;;; σ e⊢ a ▷ av ->
      nth_error mfix idx = Some def ->
      #|argsv| < rarg def ->
      Σ ;;; σ e⊢ tApp f a ▷ tApp (mkApps (tFix mfix idx) argsv) av
  | env_eval_cofix_case ip mfix idx args def brs res :
      closedn #|σ| (tCoFix mfix idx) ->
      nth_error mfix idx = Some def ->
      Σ ;;; (cofix_subst mfix ++ σ) e⊢ tCase ip (mkApps (dbody def) args) brs ▷ res ->
      Σ ;;; σ e⊢ tCase ip (mkApps (tCoFix mfix idx) args) brs ▷ res
  | env_eval_cofix_proj p mfix idx args def res :
      closedn #|σ| (tCoFix mfix idx) ->
      nth_error mfix idx = Some def ->
      Σ ;;; (cofix_subst mfix ++ σ) e⊢ tProj p (mkApps (dbody def) args) ▷ res ->
      Σ ;;; σ e⊢ tProj p (mkApps (tCoFix mfix idx) args) ▷ res
  | env_eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
      cst_body decl = Some body ->
      closedn #|σ| body ->
      Σ ;;; σ e⊢ body ▷ res ->
      Σ ;;; σ e⊢ tConst c ▷ res
  | env_eval_proj i pars arg discr args res :
      Σ ;;; σ e⊢ discr ▷ mkApps (tConstruct i 0) args ->
      is_propositional Σ i = Some false ->
      Σ ;;; σ e⊢ nth (pars + arg) args tDummy ▷ res ->
      Σ ;;; σ e⊢ tProj (i, pars, arg) discr ▷ res
  | env_eval_proj_prop i pars arg discr :
      with_prop_case ->
      Σ ;;; σ e⊢ discr ▷ tBox ->
      is_propositional Σ i = Some true ->
      Σ ;;; σ e⊢ tProj (i, pars, arg) discr ▷ tBox
  | env_eval_app_cong f f' a a' :
      Σ ;;; σ e⊢ f ▷ f' ->
      negb (isLambda f' || isFixApp f' || isBox f') ->
      Σ ;;; σ e⊢ a ▷ a' ->
      Σ ;;; σ e⊢ tApp f a ▷ tApp f' a'
  | env_eval_atom t :
      atom t ->
      closedn #|σ| t ->
      Σ ;;; σ e⊢ t ▷ t
  where "Σ ;;; σ 'e⊢' t ▷ v" := (env_eval Σ σ t v) : type_scope.

Lemma env_eval_closedn Σ σ t v k :
  Σ ;;; σ e⊢ t ▷ v ->
  env_closed Σ ->
  Forall (closedn k) σ ->
  closedn (k + #|σ|) t ->
  closedn k v.
Proof.
  intros ev genv_clos env_clos clos.
  induction ev in |- *; cbn in *; propify.
  15: {
    destruct t; cbn in *; try congruence.
    }
  - eapply nth_error_forall in env_clos; [|eassumption].
    auto.
    (*cbn in *.
    eapply closed_upwards; eauto.
    apply nth_error_Some_length in e.
    lia.*)
  - easy.
  - destruct clos.
    eapply IHev3; auto.
    eapply closed_upwards; eauto.
    lia.
  - destruct clos.
    apply IHev2; auto.
    eapply closed_upwards; eauto.
    lia.
  - destruct clos.
    apply IHev2; auto.
    apply closedn_iota_red.
    + eapply Forall_impl.
      * eapply proj2.
        now eapply closedn_mkApps_inv.
      * cbn.
        intros.
        eapply closed_upwards; eauto.
        lia.
    + now apply forallb_Forall.
  - subst brs.
    cbn in *.
    propify.
    apply IHev2; auto.
    apply closedn_mkApps; [easy|].
    now apply Forall_repeat.
  - destruct clos as (clos_f & clos_a).
    intuition auto.
    apply closedn_mkApps_inv in H1 as (clos_fix&clos_argsv).
    apply IHev3.
    + apply app_Forall; auto.
      apply closedn_fix_subst; auto.
    + rewrite app_length, fix_subst_length.
      split; [|eapply closed_upwards; eauto; lia].
      apply closedn_mkApps.
      * eapply nth_error_forallb in clos_fix.
        rewrite e in clos_fix; cbn in *.
        eapply closed_upwards; eauto.
        lia.
      * eapply Forall_impl; eauto.
        cbn.
        intros.
        eapply closed_upwards; eauto.
        lia.
  - intuition auto.
  - intuition auto.
    apply closedn_mkApps_inv in H as (clos_cofix & clos_args).
    apply IHev.
    + apply app_Forall; auto.
      apply closedn_cofix_subst; auto.
      cbn in *.


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



Ltac facts :=
  repeat
    match goal with
    | [H: ?Σ e⊢ ?t ▷ ?v, H': closedn ?k ?t |- _] =>
      match goal with
      | [H'': is_true (closedn k v) |- _] => fail 1
      | _ => idtac
      end;
      assert (closedn k v) by (apply (eval_closedn _ _ _ _ H _ H'); trivial)
    end.

  Lemma env_eval_eval Σ σ t v :
    env_closed Σ ->
    closedn #|σ| t ->
    All value σ ->
    Σ;;; σ e⊢ t ▷ v ->
    Σ e⊢ subst σ 0 t ▷ v.
  Proof.
    intros env_clos clos vals ev.
    induction ev; cbn in *; propify.
    - rewrite Nat.sub_0_r, e, lift0_id.
      apply value_final.
      eapply nth_error_all in e; eauto.
    - destruct clos.
      eapply eval_box; eauto.
    - destruct clos.
      eapply eval_beta; eauto.
      facts.
      assert (closedn #|σ| (tLambda na b)).
      { eapply eval_closedn.
        eauto.
        eauto.
      apply eval_closed


End env_eval.

Notation "Σ ;;; σ 'e⊢' t ▷ v" :=
  (env_eval Σ σ t v) (at level 50, σ, t, v at next level) : type_scope.
