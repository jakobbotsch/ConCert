From Coq Require Import List.
From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import WcbvEvalAux.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require PCUICAstUtils.

Set Keyed Unification.

Import ListNotations.

Section env_eval.
  Reserved Notation "Σ ;;; σ 'e⊢' t , args ▷ v" (at level 50, σ, t, v at next level).

  Definition is_stuck_fix (defs : mfixpoint term) (i nargs : nat) :=
    match nth_error defs i with
    | Some def => nargs <=? rarg def
    | None => false
    end.

  (*
  Inductive ee_val : Type :=
  | vLambda (na : name) (body : term)
  | vFix (defs : mfixpoint term) (idx : nat

  Inductive ee_val : term -> Type :=
  | vLambda
      (na : name) (body : term)
      (σ : list term) (σv : All ee_val σ) : ee_val (tLambda na body)
  | vFix
      (defs : mfixpoint term)
      (idx : nat)
      (σ : list term) (σv : All ee_val σ)
      (args : list term) (argsv : All ee_val args)
      (is_stuck : is_stuck_fix defs idx #|args|) : ee_val (tFix defs idx)
  | vBox : ee_val tBox
  | vConstruct ind c args (argsv : All ee_val args) : ee_val (tConstruct ind c)
  | vCoFix defs i args (argsv : All ee_val args) : ee_val (tCoFix defs i).

  Definition ee_val_sig := ∑ t, ee_val t.
*)

  Inductive ee_val : Type :=
  | vLambda
      (na : name)
      (body : term)
      (σ : list ee_val)
  | vFix
      (mfix : mfixpoint term)
      (idx : nat)
      (σ : list ee_val)
      (args : list ee_val)
  | vCoFix
      (mfix : mfixpoint term)
      (idx : nat)
      (σ : list ee_val)
      (args : list ee_val)
  | vBox
  | vConstruct (ind : inductive) (c : nat) (args : list ee_val).

  Derive NoConfusion NoConfusionHom for ee_val.

  Definition env_fixes mfix σ :=
    let fix aux n :=
        match n with
        | 0 => []
        | S n => vFix mfix n σ [] :: aux n
        end in
    aux #|mfix|.

  Lemma env_fixes_length mfix σ :
    #|env_fixes mfix σ| = #|mfix|.
  Proof.
    unfold env_fixes.
    induction #|mfix|; auto.
    cbn.
    f_equal.
    auto.
  Qed.

  Definition fix_env (mfix : mfixpoint term) (σ : list ee_val) : list ee_val :=
    env_fixes mfix σ ++ σ.

  Definition env_cofixes mfix σ :=
    let fix aux n :=
        match n with
        | 0 => []
        | S n => vCoFix mfix n σ [] :: aux n
        end in
    aux #|mfix|.

  Definition cofix_env (mfix : mfixpoint term) (σ : list ee_val) : list ee_val :=
    env_cofixes mfix σ ++ σ.

  Lemma env_cofixes_length mfix σ :
    #|env_cofixes mfix σ| = #|mfix|.
  Proof.
    unfold env_cofixes.
    induction #|mfix|; auto.
    cbn.
    f_equal.
    auto.
  Qed.

  Hint Rewrite env_fixes_length env_cofixes_length : len.

  Inductive env_eval
            (Σ : global_declarations)
            (σ : list ee_val) : term -> list ee_val -> ee_val -> Type :=
  | env_eval_app a av t argsv v :
      Σ ;;; σ e⊢ a, [] ▷ av ->
      Σ ;;; σ e⊢ t, (av :: argsv) ▷ v ->
      Σ ;;; σ e⊢ tApp t a, argsv ▷ v
  | env_eval_rel i v :
      nth_error σ i = Some v ->
      Σ ;;; σ e⊢ tRel i, [] ▷ v
  | env_eval_box a argsv av :
      Σ ;;; σ e⊢ a, argsv ▷ vBox ->
      Σ ;;; σ e⊢ a, (argsv ++ [av]) ▷ vBox
  | env_eval_beta f argsv na b σ' av res :
      Σ ;;; σ e⊢ f, argsv ▷ vLambda na b σ' ->
      Σ ;;; (av :: σ') e⊢ b, [] ▷ res ->
      Σ ;;; σ e⊢ f, (argsv ++ [av]) ▷ res
  | env_eval_zeta na val valv body v :
      Σ ;;; σ e⊢ val, [] ▷ valv ->
      Σ ;;; (valv :: σ) e⊢ body, [] ▷ v ->
      Σ ;;; σ e⊢ tLetIn na val body, [] ▷ v
  | env_eval_iota discr ind pars c argsv brs v :
      Σ ;;; σ e⊢ discr, [] ▷ vConstruct ind c argsv ->
      is_propositional Σ ind = Some false ->
      Σ ;;; σ e⊢ (nth c brs (0, tDummy)).2, (skipn pars argsv) ▷ v ->
      Σ ;;; σ e⊢ tCase (ind, pars) discr brs, [] ▷ v
  | env_eval_fix f argsv mfix idx σ' fargsv a av def v :
      Σ ;;; σ e⊢ f, argsv ▷ vFix mfix idx σ' fargsv ->
      Σ ;;; σ e⊢ a, [] ▷ av ->
      nth_error mfix idx = Some def ->
      #|fargsv| = rarg def ->
      Σ ;;; (fix_env mfix σ') e⊢ dbody def, (fargsv ++ [av]) ▷ v ->
      Σ ;;; σ e⊢ f, (argsv ++ [av]) ▷ v
  | env_eval_fix_value f argsv mfix idx σ' fargsv a av def :
      Σ ;;; σ e⊢ f, argsv ▷ vFix mfix idx σ' fargsv ->
      Σ ;;; σ e⊢ a, [] ▷ av ->
      nth_error mfix idx = Some def ->
      #|fargsv| < rarg def ->
      Σ ;;; σ e⊢ f, (argsv ++ [av]) ▷ vFix mfix idx σ' (fargsv ++ [av])
  | env_eval_cofix_case mfix idx def ind pars args argsv c cargsv brs v :
      nth_error mfix idx = Some def ->
      All2 (fun t v => Σ ;;; σ e⊢ t, [] ▷ v) args argsv ->
      Σ ;;; (cofix_env mfix σ) e⊢ dbody def, argsv ▷ vConstruct ind c cargsv ->
      is_propositional Σ ind = Some false ->
      Σ ;;; σ e⊢ (nth c brs (0, tDummy)).2, (skipn pars cargsv) ▷ v ->
      Σ ;;; σ e⊢ tCase (ind, pars) (mkApps (tCoFix mfix idx) args) brs, [] ▷ v
  (*| env_eval_cofix_proj mfix idx def
      nth_error mfix idx = Some def ->
      Σ ;;; (cofix_subst mfix ++ σ) e⊢ tProj p (mkApps (dbody def) args) ▷ res ->
      Σ ;;; σ e⊢ tProj p (mkApps (tCoFix mfix idx) args) ▷ res*)
  | env_eval_delta c decl body (isdecl : declared_constant Σ c decl) v :
      cst_body decl = Some body ->
      Σ ;;; [] e⊢ body, [] ▷ v ->
      Σ ;;; σ e⊢ tConst c, [] ▷ v
  | env_eval_proj discr ind argsv pars arg av :
      Σ ;;; σ e⊢ discr, [] ▷ vConstruct ind 0 argsv ->
      is_propositional Σ ind = Some false ->
      nth_error argsv (pars + arg) = Some av ->
      Σ ;;; σ e⊢ tProj (ind, pars, arg) discr, [] ▷ av
  | env_eval_app_construct t argsv ind c cargsv a av :
      Σ ;;; σ e⊢ t, argsv ▷ vConstruct ind c cargsv ->
      Σ ;;; σ e⊢ a, [] ▷ av ->
      Σ ;;; σ e⊢ t, (argsv ++ [av]) ▷ vConstruct ind c (cargsv ++ [av])
  | env_eval_app_cofix t argsv mfix idx σ' fargsv a av :
      Σ ;;; σ e⊢ t, argsv ▷ vCoFix mfix idx σ' fargsv ->
      Σ ;;; σ e⊢ a, [] ▷ av ->
      Σ ;;; σ e⊢ t, (argsv ++ [av]) ▷ vCoFix mfix idx σ' (fargsv ++ [av])
  | env_eval_box_atom :
      Σ ;;; σ e⊢ tBox, [] ▷ vBox
  | env_eval_lambda_atom na body :
      Σ ;;; σ e⊢ tLambda na body, [] ▷ vLambda na body σ
  | env_eval_construct_atom ind c :
      Σ ;;; σ e⊢ tConstruct ind c, [] ▷ vConstruct ind c []
  | env_eval_fix_atom mfix idx :
      Σ ;;; σ e⊢ tFix mfix idx, [] ▷ vFix mfix idx σ []
  | env_eval_cofix_atom mfix idx :
      Σ ;;; σ e⊢ tCoFix mfix idx, [] ▷ vCoFix mfix idx σ []
  where "Σ ;;; σ 'e⊢' t , args ▷ v" := (env_eval Σ σ t args v) : type_scope.

  Derive Signature for env_eval.

  Lemma env_eval_forall_list_rect :
    forall (Σ : global_declarations) (P : list ee_val -> term -> list ee_val -> ee_val -> Type),
      (forall (σ : list ee_val) (a : term) (av : ee_val) (t : term) (argsv : list ee_val) (v : ee_val),
          Σ;;; σ e⊢ a, [] ▷ av ->
                       P σ a [] av -> Σ;;; σ e⊢ t, av :: argsv ▷ v -> P σ t (av :: argsv) v -> P σ (tApp t a) argsv v) ->
      (forall (σ : list ee_val) (i : nat) (v : ee_val), nth_error σ i = Some v -> P σ (tRel i) [] v) ->
      (forall (σ : list ee_val) (a : term) (argsv : list ee_val) av,
          Σ;;; σ e⊢ a, argsv ▷ vBox -> P σ a argsv vBox -> P σ a (argsv ++ [av]) vBox) ->
      (forall (σ : list ee_val) (f2 : term) (argsv : list ee_val) (na : name)
              (b : term) (σ' : list ee_val) (av res : ee_val),
          Σ;;; σ e⊢ f2, argsv ▷ vLambda na b σ' ->
          P σ f2 argsv (vLambda na b σ') ->
          Σ;;; (av :: σ') e⊢ b, [] ▷ res -> P (av :: σ') b [] res -> P σ f2 (argsv ++ [av]) res) ->
      (forall (σ : list ee_val) (na : name) (val : term) (valv : ee_val) (body : term) (v : ee_val),
          Σ;;; σ e⊢ val, [] ▷ valv ->
          P σ val [] valv ->
          Σ;;; (valv :: σ) e⊢ body, [] ▷ v -> P (valv :: σ) body [] v -> P σ (tLetIn na val body) [] v) ->
      (forall (σ : list ee_val) (discr : term) (ind : inductive) (pars c : nat)
              (argsv : list ee_val) (brs : list (nat × term)) (v : ee_val),
          Σ;;; σ e⊢ discr, [] ▷ vConstruct ind c argsv ->
          P σ discr [] (vConstruct ind c argsv) ->
          is_propositional Σ ind = Some false ->
          Σ;;; σ e⊢ (nth c brs (0, tDummy)).2, skipn pars argsv ▷ v ->
          P σ (nth c brs (0, tDummy)).2 (skipn pars argsv) v -> P σ (tCase (ind, pars) discr brs) [] v) ->
      (forall (σ : list ee_val) (f5 : term) (argsv : list ee_val) (mfix : mfixpoint term)
              (idx : nat) (σ' fargsv : list ee_val) (a : term) (av : ee_val) (def0 : def term)
              (v : ee_val),
          Σ;;; σ e⊢ f5, argsv ▷ vFix mfix idx σ' fargsv ->
          P σ f5 argsv (vFix mfix idx σ' fargsv) ->
          Σ;;; σ e⊢ a, [] ▷ av ->
          P σ a [] av ->
          nth_error mfix idx = Some def0 ->
          #|fargsv| = rarg def0 ->
          Σ;;; fix_env mfix σ' e⊢ dbody def0, fargsv ++ [av] ▷ v ->
          P (fix_env mfix σ') (dbody def0) (fargsv ++ [av]) v -> P σ f5 (argsv ++ [av]) v) ->
      (forall (σ : list ee_val) (f6 : term) (argsv : list ee_val) (mfix : mfixpoint term)
              (idx : nat) (σ' fargsv : list ee_val) (a : term) (av : ee_val) (def0 : def term),
          Σ;;; σ e⊢ f6, argsv ▷ vFix mfix idx σ' fargsv ->
          P σ f6 argsv (vFix mfix idx σ' fargsv) ->
          Σ;;; σ e⊢ a, [] ▷ av ->
          P σ a [] av ->
          nth_error mfix idx = Some def0 ->
          #|fargsv| < rarg def0 -> P σ f6 (argsv ++ [av]) (vFix mfix idx σ' (fargsv ++ [av]))) ->
      (forall (σ : list ee_val) (mfix : list (def term)) (idx : nat) (def0 : def term)
              (ind : inductive) (pars : nat) (args : list term) (argsv : list ee_val)
              (c : nat) (cargsv : list ee_val) (brs : list (nat × term)) (v : ee_val),
          nth_error mfix idx = Some def0 ->
          All2 (fun (t : term) (v0 : ee_val) => Σ;;; σ e⊢ t, [] ▷ v0 × P σ t [] v0) args argsv ->
          Σ;;; cofix_env mfix σ e⊢ dbody def0, argsv ▷ vConstruct ind c cargsv ->
          P (cofix_env mfix σ) (dbody def0) argsv (vConstruct ind c cargsv) ->
          is_propositional Σ ind = Some false ->
          Σ;;; σ e⊢ (nth c brs (0, tDummy)).2, skipn pars cargsv ▷ v ->
          P σ (nth c brs (0, tDummy)).2 (skipn pars cargsv) v ->
          P σ (tCase (ind, pars) (mkApps (tCoFix mfix idx) args) brs) [] v) ->
      (forall (σ : list ee_val) (c : kername) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall v : ee_val,
            cst_body decl = Some body ->
            Σ;;; [] e⊢ body, [] ▷ v ->
            P [] body [] v -> P σ (tConst c) [] v) ->
      (forall (σ : list ee_val) (discr : term) (ind : inductive) (argsv : list ee_val)
              (pars arg : nat) (av : ee_val),
          Σ;;; σ e⊢ discr, [] ▷ vConstruct ind 0 argsv ->
          P σ discr [] (vConstruct ind 0 argsv) ->
          is_propositional Σ ind = Some false ->
          nth_error argsv (pars + arg) = Some av -> P σ (tProj (ind, pars, arg) discr) [] av) ->
      (forall (σ : list ee_val) (t : term) (argsv : list ee_val) (ind : inductive)
              (c : nat) (cargsv : list ee_val) (a : term) (av : ee_val),
          Σ;;; σ e⊢ t, argsv ▷ vConstruct ind c cargsv ->
          P σ t argsv (vConstruct ind c cargsv) ->
          Σ;;; σ e⊢ a, [] ▷ av -> P σ a [] av -> P σ t (argsv ++ [av]) (vConstruct ind c (cargsv ++ [av]))) ->
      (forall (σ : list ee_val) (t : term) (argsv : list ee_val) (mfix : mfixpoint term)
              (idx : nat) (σ' fargsv : list ee_val) (a : term) (av : ee_val),
          Σ;;; σ e⊢ t, argsv ▷ vCoFix mfix idx σ' fargsv ->
          P σ t argsv (vCoFix mfix idx σ' fargsv) ->
          Σ;;; σ e⊢ a, [] ▷ av -> P σ a [] av -> P σ t (argsv ++ [av]) (vCoFix mfix idx σ' (fargsv ++ [av]))) ->
      (forall σ : list ee_val, P σ tBox [] vBox) ->
      (forall (σ : list ee_val) (na : name) (body : term), P σ (tLambda na body) [] (vLambda na body σ)) ->
      (forall (σ : list ee_val) (ind : inductive) (c : nat),
          P σ (tConstruct ind c) [] (vConstruct ind c [])) ->
      (forall (σ : list ee_val) (mfix : mfixpoint term) (idx : nat),
          P σ (tFix mfix idx) [] (vFix mfix idx σ [])) ->
      (forall (σ : list ee_val) (mfix : mfixpoint term) (idx : nat),
          P σ (tCoFix mfix idx) [] (vCoFix mfix idx σ [])) ->
      forall (σ : list ee_val) (t : term) (l : list ee_val) (e : ee_val), Σ;;; σ e⊢ t, l ▷ e -> P σ t l e.
  Proof.
    intros until 18.
    fix f 5.
    intros σ t l e ev.
    move f at top.
    destruct ev;
      try solve [multimatch goal with
                 | [H: _ |- _] => eapply H; eauto
                 end].
    eapply X7; eauto.
    clear -a f.
    revert args argsv a.
    fix f' 3.
    intros args argsv [].
    - apply All2_nil.
    - constructor.
      + split; [exact e|].
        apply f.
        exact e.
      + apply f'.
        exact a.
  Defined.

  Inductive full_ee_val : ee_val -> Type :=
  | fvLambda na body σ :
      All full_ee_val σ ->
      full_ee_val (vLambda na body σ)
  | fvFix mfix idx σ args def :
      nth_error mfix idx = Some def ->
      All full_ee_val σ ->
      All full_ee_val args ->
      #|args| <= rarg def ->
      full_ee_val (vFix mfix idx σ args)
  | fvCoFix mfix idx σ args :
      All full_ee_val σ ->
      All full_ee_val args ->
      full_ee_val (vCoFix mfix idx σ args)
  | fvBox : full_ee_val vBox
  | fvConstruct ind c args :
      All full_ee_val args ->
      full_ee_val (vConstruct ind c args).

  Derive Signature NoConfusion for full_ee_val.

  (*
  Lemma env_eval_to_value Σ σ t args v :
    Σ ;;; σ e⊢ t, args ▷ v ->
    All full_ee_val σ ->
    All full_ee_val args ->
    full_ee_val v.
  Proof.
    intros ev env_val args_val.
    induction ev using env_eval_forall_list_rect; auto.
    - eapply nth_error_all in env_val; eauto.
    - apply IHev2; auto.
      apply All_app in args_val as (?&?).
      depelim a0.
      constructor; auto.
      do 2 forward IHev1 by auto.
      depelim IHev1.
      auto.
    - apply IHev2; auto.
      do 2 forward IHev1 by auto.
      depelim IHev1.
      now apply All_skipn.
    - apply All_app in args_val as (?&?).
      do 2 forward IHev1 by auto.
      depelim IHev1.
      apply IHev3; auto.
      + admit.
      + apply All_app_inv; auto.
    - depelim args_val.
      econstructor; eauto.
      + do
*)

  Fixpoint term_of_ee_val (e : ee_val) : term :=
    match e with
    | vLambda na body σ => subst (map term_of_ee_val σ) 0 (tLambda na body)
    | vFix mfix idx σ args => mkApps (subst (map term_of_ee_val σ) 0 (tFix mfix idx))
                                     (map term_of_ee_val args)
    | vBox => tBox
    | vConstruct ind c args => mkApps (tConstruct ind c) (map term_of_ee_val args)
    | vCoFix mfix idx σ args => mkApps (subst (map term_of_ee_val σ) 0 (tCoFix mfix idx))
                                       (map term_of_ee_val args)
    end.

(*Lemma env_eval_closedn Σ σ t v k :
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
*)

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

  Local Existing Instance opt_wcbv_flags.

  Lemma closed_substl s t :
    All (closedn 0) s ->
    substl s t = subst0 s t.
  Proof.
    intros all.
    induction all in t |- *; cbn.
    - now rewrite subst_empty.
    - rewrite (subst_app_decomp [_]).
      cbn.
      rewrite lift_closed, closed_subst by auto.
      auto.
  Qed.

  Lemma substl_app l l' t :
    substl (l ++ l') t = substl l' (substl l t).
  Proof.
    induction l in t |- *; cbn; auto.
  Qed.

  (*
  From MetaCoq.Template Require Import Loader.
  Unset Guard Checking.
  MetaCoq Quote Definition foo := (fix f (n : nat) :=
                                     f n + g n
                                   with g (n : nat) :=
                                       0
                                         for f).
*)
  Lemma terms_of_env_fixes mfix σ :
    map term_of_ee_val (env_fixes mfix σ) =
    fix_subst (map (map_def (subst (map term_of_ee_val σ) #|mfix|)) mfix).
  Proof.
    unfold fix_subst, env_fixes.
    rewrite map_length.
    induction #|mfix| at 1 3; auto.
    cbn.
    rewrite Nat.add_0_r.
    f_equal; apply IHn.
  Qed.

  Lemma terms_of_env_cofixes mfix σ :
    map term_of_ee_val (env_cofixes mfix σ) =
    cofix_subst (map (map_def (subst (map term_of_ee_val σ) #|mfix|)) mfix).
  Proof.
    unfold cofix_subst, env_cofixes.
    rewrite map_length.
    induction #|mfix| at 1 3; auto.
    cbn.
    rewrite Nat.add_0_r.
    f_equal; apply IHn.
  Qed.

  Lemma env_eval_eval Σ σ t args v :
    Σ;;; σ e⊢ t, args ▷ v ->
    Σ e⊢ mkApps (subst (map term_of_ee_val σ) 0 t)
                (map term_of_ee_val args) ▷ term_of_ee_val v.
  Proof.
    intros ev.
    induction ev using env_eval_forall_list_rect; cbn in *; propify.
    - eapply eval_mkApps_inv in IHev2 as H; destruct H as (?&?&?&?).
      eapply eval_mkApps_congr; eauto.
      eapply eval_tApp_inv in e as H; destruct H as (?&?&?&?).
      eapply eval_tApp_congr.
      5: eauto.
      all: eauto.
      apply value_final.
      admit.
    - rewrite Nat.sub_0_r, nth_error_map, H.
      cbn.
      rewrite lift0_id.
      apply value_final.
      admit.
    - rewrite map_app, mkApps_app.
      eapply eval_box; auto.
      apply value_final.
      admit.
    - rewrite map_app, mkApps_app.
      cbn.
      eapply eval_beta; eauto.
      + eapply value_final; admit.
      + rewrite subst_app_simpl with (l := [_]) in IHev2.
        cbn in IHev2.
        rewrite closed_subst; auto.
        admit.
    - eapply eval_zeta; eauto.
      rewrite subst_app_simpl with (l := [_]) in IHev2.
      cbn in *.
      rewrite closed_subst; auto.
      admit.
    - eapply eval_iota; eauto.
      unfold iota_red.
      rewrite nth_map; auto.
      cbn.
      rewrite <- map_skipn.
      auto.
    - rewrite map_app, mkApps_app in *; cbn in *.
      eapply eval_fix; eauto.
      + eapply value_final; admit.
      + rewrite Nat.add_0_r, map_length.
        unfold cunfold_fix.
        rewrite nth_error_map, H.
        cbn.
        f_equal.
        f_equal; eauto.
        rewrite closed_substl by admit.
        unfold fix_env.
        rewrite map_app.
        cbn.
        rewrite subst_app_simpl.
        cbn.
        autorewrite with len.
        f_equal.
        now rewrite terms_of_env_fixes.
    - rewrite !map_app, !mkApps_app.
      eapply eval_fix_value.
      4: rewrite map_length; exact H0.
      2: apply value_final; admit.
      2: { unfold cunfold_fix.
           rewrite nth_error_map, H.
           cbn.
           reflexivity. }
      auto.
    - rewrite subst_mkApps.
      cbn.
      eapply red_cofix_case.
      + unfold cunfold_cofix.
        rewrite nth_error_map, H.
        cbn.
        reflexivity.
      + eapply eval_iota.
        2: auto.
        2: { unfold iota_red.
             rewrite nth_map; auto.
             cbn.
             rewrite map_skipn in IHev2.
             eauto. }
        rewrite closed_substl by admit.
        unfold cofix_env in IHev1.
        rewrite map_app, subst_app_simpl in IHev1.
        autorewrite with len in *.
        cbn in *.
        rewrite <- terms_of_env_cofixes.
        eapply eval_mkApps_inv in IHev1 as H'; destruct H' as (?&_&?&_).
        eapply eval_mkApps_congr.
        3: exact e.
        4: eauto.
        1: eauto.
        2: apply All2_map with (g := term_of_ee_val), All2_same.
        2: intros; apply value_final; admit.
        apply All2_map.
        eapply All2_impl; eauto.
        cbn.
        intros ? ? (?&?); auto.
    - eapply eval_delta; eauto.
      now rewrite subst_empty in IHev.
    - eapply eval_proj; eauto.
      rewrite nth_nth_error, nth_error_map, H0.
      cbn.
      apply value_final; admit.
    - rewrite !map_app, !mkApps_app.
      cbn.
      eapply eval_app_cong; auto.
      + rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps; auto.
      + apply value_final; admit.
    - rewrite !map_app, !mkApps_app.
      cbn.
      eapply eval_app_cong; auto.
      + rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps; auto.
      + apply value_final; admit.
    - eapply eval_atom; auto.
    - eapply eval_atom; auto.
    - eapply eval_atom; auto.
    - eapply eval_atom; auto.
    - eapply eval_atom; auto.
  Admitted.

  Lemma env_eval_box_app Σ σ argsv :
    Σ ;;; σ e⊢ tBox, argsv ▷ vBox.
  Proof.
    induction argsv using MCList.rev_ind.
    - eapply env_eval_box_atom.
    - eapply env_eval_box; eauto.
  Qed.

  Lemma env_eval_subst Σ σ t argsv v :
    Σ ;;; [] e⊢ subst (map term_of_ee_val σ) 0 t, argsv ▷ v ->
    ∑ v',
      Σ ;;; σ e⊢ t, argsv ▷ v' × term_of_ee_val v' = term_of_ee_val v.
  Proof.
    intros ev.
    induction t in σ, t, argsv, v, ev |- * using term_forall_list_ind; cbn in *.
    - depelim ev.
      + exists vBox.
        split; auto.
        eapply env_eval_box_app.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - rewrite Nat.sub_0_r in *.
      rewrite nth_error_map in ev.
      destruct nth_error eqn:nth; cbn in *.
      + rewrite lift0_id in ev.
Lemma env_eval_app_congr Σ σ t args v t' :
  Σ ;;; σ e⊢ t, args ▷ v ->
  Σ ;;; σ e⊢ t', args ▷ v
        exists e.
        split; [econstructor; eauto|].
        apply env_eval_eval in ev.
        cbn in ev.
        rewrite subst_empty in ev.
        eapply eval_deterministic; eauto.
        apply value_final.
        admit.
      + rewrite map_length in ev.
        depelim ev; try solve [destruct argsv; cbn in *; discriminate].
        rewrite nth_error_nil in e; discriminate.
    - depelim ev; try solve [destruct argsv; cbn in *; discriminate].
    - depelim ev; try solve [destruct argsv; cbn in *; discriminate].
    - depelim ev; try solve [destruct argsv; cbn in *; discriminate].
      cbn in *.
      eexists.
      split.
      + eapply env_eval_lambda_atom.
      + cbn.
        f_equal.
        now rewrite subst_empty.
    - depelim ev; try solve [destruct argsv; cbn in *; discriminate].
      eexists; split.
      + eapply env_eval_zeta.
        admit.
        admit.
      + admit.
    - depelim ev; try solve [destruct argsv; cbn in *; discriminate].

    depind ev.
    - destruct t0; cbn in *; try discriminate.
      + rewrite Nat.sub_0_r in *.
        rewrite nth_error_map in H.
        destruct nth_error eqn:nth; [|discriminate].
        cbn in *.
        constructor.
        rewrite lift0_id in H.
        destruct e; cbn in *; try discriminate.
        *
        econstructor.

  Lemma eval_env_eval' Σ hd args tv :
    Σ e⊢ mkApps hd args ▷ tv ->
    ∑ argsv v,
      All2 (fun a av => Σ ;;; [] e⊢ a, [] ▷ av) args argsv
      × Σ ;;; [] e⊢ hd, argsv ▷ v
      × term_of_ee_val v = tv.
  Proof.
    intros ev.
    depind ev.
    - destruct args as [|? ? _] using MCList.rev_ind.
      + cbn in *; subst.
        specialize (IHev1 _ [] _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] _ eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        exists [], vBox.
        split; auto.
        split; auto.
        eapply env_eval_app; eauto.
        eapply env_eval_box with (argsv := []).
        auto.
      + rewrite mkApps_app in H; cbn in H; noconf H.
        specialize (IHev1 _ _ _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] _ eq_refl) as (?&?&?&?&?).
        depelim a0.
        exists (x ++ [x2]), vBox.
        split; [apply All2_app; auto|].
        split; auto.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        eapply env_eval_box.
        auto.
    - destruct args as [|? ? _] using MCList.rev_ind.
      + cbn in *; subst.
        specialize (IHev1 _ [] _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] _ eq_refl) as (?&?&?&?&?).
        specialize (IHev3 _ [] _ eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        depelim a2.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf e0.
        eexists [], _.
        split; auto.
        exists [], x4.
        split; auto.
        split; auto.
        eapply env_eval_app; eauto.
        eapply env_eval_beta with (argsv := []); eauto.
        noconf e0.


End env_eval.

Notation "Σ ;;; σ 'e⊢' t ▷ v" :=
  (env_eval Σ σ t v) (at level 50, σ, t, v at next level) : type_scope.
