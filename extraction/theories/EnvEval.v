From Coq Require Import CMorphisms.
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

Set Default Goal Selector "!".

Set Keyed Unification.

Import ListNotations.

Section env_eval.
  Reserved Notation "Σ ;;; σ 'e⊢' t , args ▷ v" (at level 50, σ, t, v at next level).

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
      isApp a = false ->
      Σ ;;; σ e⊢ a, argsv ▷ vBox ->
      Σ ;;; σ e⊢ a, (argsv ++ [av]) ▷ vBox
  | env_eval_beta f argsv na b σ' av res :
      isApp f = false ->
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
      isApp f = false ->
      Σ ;;; σ e⊢ f, argsv ▷ vFix mfix idx σ' fargsv ->
      Σ ;;; σ e⊢ a, [] ▷ av ->
      nth_error mfix idx = Some def ->
      #|fargsv| = rarg def ->
      Σ ;;; (fix_env mfix σ') e⊢ dbody def, (fargsv ++ [av]) ▷ v ->
      Σ ;;; σ e⊢ f, (argsv ++ [av]) ▷ v
  | env_eval_fix_value f argsv mfix idx σ' fargsv a av def :
      isApp f = false ->
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
      isApp t = false ->
      Σ ;;; σ e⊢ t, argsv ▷ vConstruct ind c cargsv ->
      Σ ;;; σ e⊢ a, [] ▷ av ->
      Σ ;;; σ e⊢ t, (argsv ++ [av]) ▷ vConstruct ind c (cargsv ++ [av])
  | env_eval_app_cofix t argsv mfix idx σ' fargsv a av :
      isApp t = false ->
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

  (*
  Definition ex1 : [];;; [] e⊢ mkApps tBox [tBox; tBox], [] ▷ vBox.
  Proof.
    eapply env_eval_app; [econstructor|].
    eapply env_eval_box with (argsv := []).
    eapply env_eval_app; [econstructor|].
    eapply env_eval_box with (argsv := []).
    eapply env_eval_box_atom.
  Defined.

  Definition ex2 : [];;; [] e⊢ mkApps tBox [tBox; tBox], [] ▷ vBox.
  Proof.
    eapply env_eval_app; [econstructor|].
    eapply env_eval_app; [econstructor|].
    eapply env_eval_box with (argsv := [_]).
    eapply env_eval_box with (argsv := []).
    eapply env_eval_box_atom.
  Defined.

  Lemma foo : ex1 <> ex2.
  Proof.
    discriminate.
  Qed.
*)

  Derive Signature for env_eval.

  Inductive All2_dep {X Y} {T : X -> Y -> Type} (U : forall {x y}, T x y -> Type) :
    forall {xs : list X} {ys : list Y}, All2 T xs ys -> Type :=
  | All2_dep_nil : All2_dep (@U) All2_nil
  | All2_dep_cons
      {x y xs ys}
      {t : T x y}
      {a : All2 T xs ys}
      (u : U t)
      (ad : All2_dep (@U) a) : All2_dep (@U) (All2_cons t a).

  Global Arguments All2_dep_nil {_ _ _ _}.
  Global Arguments All2_dep_cons {_ _ _ _ _ _}.

  Lemma All2_dep_nondep
        {X Y}
        {T : X -> Y -> Type}
        {xs ys}
        {a : All2 T xs ys}
        {T' : X -> Y -> Type} :
    All2_dep (fun x y uxy => T' x y) a ->
    All2 T' xs ys.
  Proof.
    intros ad.
    induction ad; auto.
  Qed.

  Lemma env_eval_forall_list_rect :
      forall (Σ : global_declarations)
        (P : forall (σ : list ee_val) (t : term) (l : list ee_val) (e : ee_val),
             Σ;;; σ e⊢ t, l ▷ e -> Type),
      (forall (σ : list ee_val) (a : term) (av : ee_val) (t : term) (argsv : list ee_val)
         (v : ee_val) (e : Σ;;; σ e⊢ a, [] ▷ av),
       P σ a [] av e ->
       forall e0 : Σ;;; σ e⊢ t, av :: argsv ▷ v,
       P σ t (av :: argsv) v e0 -> P σ (tApp t a) argsv v (env_eval_app Σ σ a av t argsv v e e0)) ->
      (forall (σ : list ee_val) (i : nat) (v : ee_val) (e : nth_error σ i = Some v),
       P σ (tRel i) [] v (env_eval_rel Σ σ i v e)) ->
      (forall (σ : list ee_val) (a : term) (argsv : list ee_val) (av : ee_val)
         (e : isApp a = false) (e0 : Σ;;; σ e⊢ a, argsv ▷ vBox),
       P σ a argsv vBox e0 -> P σ a (argsv ++ [av]) vBox (env_eval_box Σ σ a argsv av e e0)) ->
      (forall (σ : list ee_val) (f2 : term) (argsv : list ee_val) (na : name)
         (b : term) (σ' : list ee_val) (av res : ee_val) (e : isApp f2 = false)
         (e0 : Σ;;; σ e⊢ f2, argsv ▷ vLambda na b σ'),
       P σ f2 argsv (vLambda na b σ') e0 ->
       forall e1 : Σ;;; (av :: σ') e⊢ b, [] ▷ res,
       P (av :: σ') b [] res e1 ->
       P σ f2 (argsv ++ [av]) res (env_eval_beta Σ σ f2 argsv na b σ' av res e e0 e1)) ->
      (forall (σ : list ee_val) (na : name) (val : term) (valv : ee_val) (body : term)
         (v : ee_val) (e : Σ;;; σ e⊢ val, [] ▷ valv),
       P σ val [] valv e ->
       forall e0 : Σ;;; (valv :: σ) e⊢ body, [] ▷ v,
       P (valv :: σ) body [] v e0 ->
       P σ (tLetIn na val body) [] v (env_eval_zeta Σ σ na val valv body v e e0)) ->
      (forall (σ : list ee_val) (discr : term) (ind : inductive) (pars c : nat)
         (argsv : list ee_val) (brs : list (nat × term)) (v : ee_val)
         (e : Σ;;; σ e⊢ discr, [] ▷ vConstruct ind c argsv),
       P σ discr [] (vConstruct ind c argsv) e ->
       forall (e0 : is_propositional Σ ind = Some false)
         (e1 : Σ;;; σ e⊢ (nth c brs (0, tDummy)).2, skipn pars argsv ▷ v),
       P σ (nth c brs (0, tDummy)).2 (skipn pars argsv) v e1 ->
       P σ (tCase (ind, pars) discr brs) [] v (env_eval_iota Σ σ discr ind pars c argsv brs v e e0 e1)) ->
      (forall (σ : list ee_val) (f5 : term) (argsv : list ee_val) (mfix : mfixpoint term)
         (idx : nat) (σ' fargsv : list ee_val) (a : term) (av : ee_val) (def0 : def term)
         (v : ee_val) (e : isApp f5 = false) (e0 : Σ;;; σ e⊢ f5, argsv ▷ vFix mfix idx σ' fargsv),
       P σ f5 argsv (vFix mfix idx σ' fargsv) e0 ->
       forall e1 : Σ;;; σ e⊢ a, [] ▷ av,
       P σ a [] av e1 ->
       forall (e2 : nth_error mfix idx = Some def0) (e3 : #|fargsv| = rarg def0)
         (e4 : Σ;;; fix_env mfix σ' e⊢ dbody def0, fargsv ++ [av] ▷ v),
       P (fix_env mfix σ') (dbody def0) (fargsv ++ [av]) v e4 ->
       P σ f5 (argsv ++ [av]) v
         (env_eval_fix Σ σ f5 argsv mfix idx σ' fargsv a av def0 v e e0 e1 e2 e3 e4)) ->
      (forall (σ : list ee_val) (f6 : term) (argsv : list ee_val) (mfix : mfixpoint term)
         (idx : nat) (σ' fargsv : list ee_val) (a : term) (av : ee_val) (def0 : def term)
         (e : isApp f6 = false) (e0 : Σ;;; σ e⊢ f6, argsv ▷ vFix mfix idx σ' fargsv),
       P σ f6 argsv (vFix mfix idx σ' fargsv) e0 ->
       forall e1 : Σ;;; σ e⊢ a, [] ▷ av,
       P σ a [] av e1 ->
       forall (e2 : nth_error mfix idx = Some def0) (l : #|fargsv| < rarg def0),
       P σ f6 (argsv ++ [av]) (vFix mfix idx σ' (fargsv ++ [av]))
         (env_eval_fix_value Σ σ f6 argsv mfix idx σ' fargsv a av def0 e e0 e1 e2 l)) ->
      (forall (σ : list ee_val) (mfix : list (def term)) (idx : nat) (def0 : def term)
         (ind : inductive) (pars : nat) (args : list term) (argsv : list ee_val)
         (c : nat) (cargsv : list ee_val) (brs : list (nat × term)) (v : ee_val)
         (e : nth_error mfix idx = Some def0)
         (a : All2 (fun (t : term) (v0 : ee_val) => Σ;;; σ e⊢ t, [] ▷ v0) args argsv)
         (ad : All2_dep (fun a av ev => P σ a [] av ev) a)
         (e0 : Σ;;; cofix_env mfix σ e⊢ dbody def0, argsv ▷ vConstruct ind c cargsv),
       P (cofix_env mfix σ) (dbody def0) argsv (vConstruct ind c cargsv) e0 ->
       forall (e1 : is_propositional Σ ind = Some false)
         (e2 : Σ;;; σ e⊢ (nth c brs (0, tDummy)).2, skipn pars cargsv ▷ v),
       P σ (nth c brs (0, tDummy)).2 (skipn pars cargsv) v e2 ->
       P σ (tCase (ind, pars) (mkApps (tCoFix mfix idx) args) brs) [] v
         (env_eval_cofix_case Σ σ mfix idx def0 ind pars args argsv c cargsv brs v e a e0 e1 e2)) ->
      (forall (σ : list ee_val) (c : kername) (decl : constant_body) (body : term)
         (isdecl : declared_constant Σ c decl) (v : ee_val) (e : cst_body decl = Some body)
         (e0 : Σ;;; [] e⊢ body, [] ▷ v),
       P [] body [] v e0 -> P σ (tConst c) [] v (env_eval_delta Σ σ c decl body isdecl v e e0)) ->
      (forall (σ : list ee_val) (discr : term) (ind : inductive) (argsv : list ee_val)
         (pars arg : nat) (av : ee_val) (e : Σ;;; σ e⊢ discr, [] ▷ vConstruct ind 0 argsv),
       P σ discr [] (vConstruct ind 0 argsv) e ->
       forall (e0 : is_propositional Σ ind = Some false) (e1 : nth_error argsv (pars + arg) = Some av),
       P σ (tProj (ind, pars, arg) discr) [] av (env_eval_proj Σ σ discr ind argsv pars arg av e e0 e1)) ->
      (forall (σ : list ee_val) (t : term) (argsv : list ee_val) (ind : inductive)
         (c : nat) (cargsv : list ee_val) (a : term) (av : ee_val) (e : isApp t = false)
         (e0 : Σ;;; σ e⊢ t, argsv ▷ vConstruct ind c cargsv),
       P σ t argsv (vConstruct ind c cargsv) e0 ->
       forall e1 : Σ;;; σ e⊢ a, [] ▷ av,
       P σ a [] av e1 ->
       P σ t (argsv ++ [av]) (vConstruct ind c (cargsv ++ [av]))
         (env_eval_app_construct Σ σ t argsv ind c cargsv a av e e0 e1)) ->
      (forall (σ : list ee_val) (t : term) (argsv : list ee_val) (mfix : mfixpoint term)
         (idx : nat) (σ' fargsv : list ee_val) (a : term) (av : ee_val) (e : isApp t = false)
         (e0 : Σ;;; σ e⊢ t, argsv ▷ vCoFix mfix idx σ' fargsv),
       P σ t argsv (vCoFix mfix idx σ' fargsv) e0 ->
       forall e1 : Σ;;; σ e⊢ a, [] ▷ av,
       P σ a [] av e1 ->
       P σ t (argsv ++ [av]) (vCoFix mfix idx σ' (fargsv ++ [av]))
         (env_eval_app_cofix Σ σ t argsv mfix idx σ' fargsv a av e e0 e1)) ->
      (forall σ : list ee_val, P σ tBox [] vBox (env_eval_box_atom Σ σ)) ->
      (forall (σ : list ee_val) (na : name) (body : term),
       P σ (tLambda na body) [] (vLambda na body σ) (env_eval_lambda_atom Σ σ na body)) ->
      (forall (σ : list ee_val) (ind : inductive) (c : nat),
       P σ (tConstruct ind c) [] (vConstruct ind c []) (env_eval_construct_atom Σ σ ind c)) ->
      (forall (σ : list ee_val) (mfix : mfixpoint term) (idx : nat),
       P σ (tFix mfix idx) [] (vFix mfix idx σ []) (env_eval_fix_atom Σ σ mfix idx)) ->
      (forall (σ : list ee_val) (mfix : mfixpoint term) (idx : nat),
       P σ (tCoFix mfix idx) [] (vCoFix mfix idx σ []) (env_eval_cofix_atom Σ σ mfix idx)) ->
      forall (σ : list ee_val) (t : term) (l : list ee_val) (e : ee_val) (e0 : Σ;;; σ e⊢ t, l ▷ e),
      P σ t l e e0.
  Proof.
    intros until 18.
    fix f 5.
    intros σ t l e ev.
    destruct ev;
      try solve [match goal with
                 | [H: _ |- _] =>
                   match H with
                   | f => fail 1
                   | _ => eapply H; eauto
                   end
                 end].
    eapply X7; eauto.
    clear -a f.
    revert args argsv a.
    fix f' 3.
    intros args argsv [].
    - apply All2_dep_nil.
    - constructor.
      + apply f.
      + apply f'.
  Defined.

  (*
  Lemma env_eval_unique_sig Σ σ hd argsv v v' :
    forall (ev1 : Σ;;; σ e⊢ hd, argsv ▷ v) (ev2 : Σ;;; σ e⊢ hd, argsv ▷ v'),
      {| pr1 := v; pr2 := ev1 |} = {| pr1 := v'; pr2 := ev2 |}.
  Proof.
    intros.
    induction ev1 in v, v', ev1, ev2 |- * using env_eval_forall_list_rect.
    - depind ev2; try discriminate.
      specialize (IHev1_1 _ ev2_1); noconf IHev1_1.
      now specialize (IHev1_2 _ ev2_2); noconf IHev1_2.

  Lemma env_eval_deterministic Σ σ hd argsv v v' :
    Σ;;; σ e⊢ hd, argsv ▷ v ->
    Σ;;; σ e⊢ hd, argsv ▷ v' ->
    v = v'.
  Proof.
    intros ev1 ev2.
    revert v' ev2.
    induction ev1 using env_eval_forall_list_rect; intros v' ev2.
    - depelim ev2.
      +
*)

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

  Definition teq (v v' : ee_val) : Type :=
    term_of_ee_val v = term_of_ee_val v'.

  Instance teq_equivalence : CRelationClasses.Equivalence teq.
  Proof.
    constructor; red; unfold teq; intros; congruence.
  Qed.

  Definition teqs := All2 teq.

  Instance teqs_equivalence : CRelationClasses.Equivalence teqs.
  Proof.
    constructor; red.
    - intros.
      apply All2_same; reflexivity.
    - intros x y eqs.
      eapply All2_sym.
      eapply All2_impl; eauto.
      intros; symmetry; auto.
    - intros; eapply All2_trans; eauto.
      apply teq_equivalence. (* ?? why does typeclasses eauto not work? *)
  Qed.

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

  Lemma terms_of_env_cofixes_nil mfix :
    map term_of_ee_val (env_cofixes mfix []) = cofix_subst mfix.
  Proof.
    rewrite terms_of_env_cofixes.
    f_equal.
    rewrite <- (map_id mfix) at 3.
    apply map_ext.
    intros []; unfold map_def; cbn; now rewrite subst_empty.
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
    - rewrite Nat.sub_0_r, nth_error_map, e.
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
        rewrite nth_error_map, e2.
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
      4: rewrite map_length; exact l.
      2: apply value_final; admit.
      2: { unfold cunfold_fix.
           rewrite nth_error_map, e2.
           cbn.
           reflexivity. }
      auto.
    - rewrite subst_mkApps.
      cbn.
      eapply red_cofix_case.
      + unfold cunfold_cofix.
        rewrite nth_error_map, e.
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
        3: exact e0.
        4: eauto.
        1: eauto.
        2: apply All2_map with (g := term_of_ee_val), All2_same.
        2: intros; apply value_final; admit.
        apply All2_map.
        apply All2_dep_nondep in ad; auto.
    - eapply eval_delta; eauto.
      now rewrite subst_empty in IHev.
    - eapply eval_proj; eauto.
      rewrite nth_nth_error, nth_error_map, e1.
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

  (*
  Instance env_eval_congr Σ :
    Proper (teqs ==> eq ==> teqs ==> teq ==> arrow) (env_eval Σ).
  Proof.
    repeat red.
    intros σ σ' σeq hd ? <- args args' argseq v v' veq ev.
    induction ev
      in σ, σ', σeq, hd, args, args', argseq, v, v', veq, ev
      using env_eval_forall_list_rect.
    - eapply env_eval_app.
      + eapply IHev1; eauto; reflexivity.
      + eapply IHev2; eauto.
        constructor; eauto.
        reflexivity.
    - depelim argseq.
      constructor.
      eapply All2_nth_error_Some in σeq as (?&?&?); eauto.
*)

Lemma env_eval_args_congr Σ σ hd args v args' :
  Σ;;; σ e⊢ hd, args ▷ v ->
  All2 teq args' args ->
  ∑ v', Σ;;; σ e⊢ hd, args' ▷ v' × teq v' v.
Proof.
  Admitted.

  (*
Lemma env_eval_app_congr Σ σ t args v t' :
  Σ ;;; σ e⊢ t, args ▷ v ->
  Σ ;;; σ e⊢ t', args ▷ v
*)

  Lemma env_eval_subst Σ σ t argsv v :
    Σ ;;; [] e⊢ subst (map term_of_ee_val σ) 0 t, argsv ▷ v ->
    ∑ v',
      Σ ;;; σ e⊢ t, argsv ▷ v' × teq v' v.
  Proof.
    Admitted.
  (*
    intros ev.
    induction t in σ, t, argsv, v, ev |- * using term_forall_list_ind; cbn in *.
    - admit.
    - rewrite Nat.sub_0_r in *.
      rewrite nth_error_map in ev.
      destruct nth_error eqn:nth; cbn in *.
      + rewrite lift0_id in ev.

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
*)
  Lemma env_eval_head_inv Σ σ t argsv v :
    Σ;;; σ e⊢ t, argsv ▷ v ->
    ∑ tv, Σ;;; σ e⊢ t, [] ▷ tv.
  Proof.
    Admitted.

  (*
  Lemma env_eval_tApp Σ σ hd arg argv argsv v :
    Σ;;; σ e⊢ tApp hd arg, argsv ▷ v ->
    Σ;;; σ e⊢ arg, [] ▷ argv ->
    Σ;;; σ e⊢ hd, (argv :: argsv) ▷ v.
  Proof.
    intros ev ev'.
    depelim ev.
    -
*)

  (*
  Lemma env_eval_mkApps Σ σ hd args argsv argsv' v :
    All2 (fun a av => Σ;;; σ e⊢ a, [] ▷ av) args argsv ->
    Σ;;; σ e⊢ mkApps hd args, argsv' ▷ v ->
    Σ;;; σ e⊢ hd, (argsv ++ argsv') ▷ v.
  Proof.
    intros all ev.
    induction all in argsv', ev |- * using All2_rev_rect; auto.
    rewrite mkApps_app in ev.
    cbn in ev.
    rewrite <- app_assoc.
    apply IHall.
    depelim ev.
    -
    cbn.
    eapply env_eval_app.
*)

  (*
  Lemma env_eval_mkApps_inv Σ σ hd args v :
    Σ;;; σ e⊢ mkApps hd args, [] ▷ v ->
    ∑ hdv argsv,
      Σ;;; σ e⊢ hd, [] ▷ hdv ×
      All2 (fun a av => Σ;;; σ e⊢ a, [] ▷ av) args argsv ×
      Σ;;; σ e⊢ hd, argsv ▷ v.
  Proof.
    revert hd v.
    induction args using MCList.rev_ind; intros hd v ev; eauto.
    rewrite mkApps_app in ev.
    cbn in ev.
    depelim ev; try solve [destruct argsv; cbn in *; discriminate].
    apply env_eval_head_inv in ev2 as H; destruct H as (?&?).
    eapply IHargs in e as (?&?&?&?&?).
    exists x1, (x2 ++ [av]).
    split; auto.
    split; [apply All2_app; auto|].
    depelim e0.
    eapply IHargs in ev2.
    induction args in hd, args, v, ev |- *; eauto.
    cbn in ev.
    apply IHargs in ev as (hdv&argsv&ev_hd&ev_args&ev).
    depelim ev_hd; try solve [destruct argsv0; cbn in *; discriminate].
*)

  Lemma env_eval_term_of_ee_val Σ σ v v' :
    full_ee_val v ->
    Σ;;; σ e⊢ term_of_ee_val v, [] ▷ v' ->
    teq v' v.
  Proof.
    Admitted.

  Lemma eval_env_eval' Σ hd args tv :
    Σ e⊢ mkApps hd args ▷ tv ->
    ∑ argsv,
      All2 (fun a av => Σ ;;; [] e⊢ a, [] ▷ av) args argsv
      × ∑ v, Σ ;;; [] e⊢ hd, argsv ▷ v
      × term_of_ee_val v = tv.
  Proof.
    intros ev.
    remember (mkApps hd args) eqn:eq.
    induction ev in hd, args, eq |- *.
    - destruct args as [|? ? _] using MCList.rev_ind.
      + cbn in *; subst.
        exists []; split; auto.
        specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        exists vBox.
        split; auto.
        eapply env_eval_app; eauto.
        eapply env_eval_box with (argsv := []).
        auto.
      + rewrite mkApps_app in eq; cbn in eq; noconf eq.
        specialize (IHev1 _ _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        depelim a0.
        exists (x ++ [x2]); split; [apply All2_app; auto|].
        exists vBox.
        split; auto.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        eapply env_eval_box.
        auto.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *; subst.
      + cbn in *; subst.
        specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev3 _ [] eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        depelim a2.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf e0.
        subst.
        exists []; split; auto.
        rewrite closed_subst in e3 by admit.
        rewrite <- subst_app_simpl in e3.
        apply env_eval_subst with (σ := [_] ++ _) in e3 as (?&?&?).
        cbn in *.
        eexists x.
        split; auto.
        eapply env_eval_app; eauto.
        eapply env_eval_beta with (argsv := []); eauto.
      + rewrite mkApps_app in eq; cbn in eq; noconf eq.
        specialize (IHev1 _ _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev3 _ [] eq_refl) as (?&?&?&?&?).
        depelim a1.
        depelim a2.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf e0.
        subst.
        exists (x ++ [x2]); split; [apply All2_app; auto|].
        rewrite closed_subst in e3 by admit.
        rewrite <- subst_app_simpl in e3.
        apply env_eval_subst with (σ := [_] ++ _) in e3 as (?&?&?).
        exists x0.
        split; auto.
        eapply env_eval_beta; eauto.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *;
        [subst|rewrite mkApps_app in eq; cbn in *; discriminate].
      exists []; split; auto.
      specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
      specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
      depelim a.
      depelim a0.
      subst.
      rewrite closed_subst in e1 by admit.
      apply env_eval_subst with (σ := [_]) in e1 as (?&?&?).
      exists x.
      eauto using env_eval.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *;
        [subst|rewrite mkApps_app in eq; cbn in *; discriminate].
      exists []; split; auto.
      specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
      specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
      depelim a.
      depelim a0.
      destruct x0; cbn in *; try discriminate; try solve_discr.
      noconf H.
      eapply env_eval_mkApps_inv in e2 as (hdv&argsv&?&?&?).
      rewrite <- (map_id argsv), <- map_skipn in a.
      apply All2_map_inv in a.
      eapply env_eval_args_congr in e2 as (?&?&?).
      2: { eapply All2_impl; eauto.
           cbn; intros.
           admit. }
      exists x.
      split; auto.
      eapply env_eval_iota; eauto.
    - discriminate.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *; subst.
      + cbn in *; subst.
        exists []; split; auto.
        specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev3 _ [] eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        depelim a2.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf H.
        rewrite <- closed_unfold_fix_cunfold_eq in e by admit.
        change (tApp ?h ?a) with (mkApps h [a]) in e4.
        rewrite mkApps_nested in e4.
        rewrite <- map_app with (l' := [x2]) in e4.
        apply env_eval_mkApps_inv in e4 as (hdv&argsv&?&?&ev_unf).
        unfold unfold_fix in e.
        rewrite nth_error_map, map_length in e.
        destruct nth_error eqn:nth; [|discriminate].
        cbn in *.
        noconf e.
        rewrite Nat.add_0_r in *.
        rewrite <- terms_of_env_fixes in ev_unf.
        rewrite <- (env_fixes_length mfix0 σ) in ev_unf.
        erewrite <- (map_length _ (env_fixes _ _)) in ev_unf.
        rewrite <- subst_app_simpl with (k := 0) in ev_unf.
        rewrite <- map_app in ev_unf.
        apply env_eval_subst in ev_unf as (?&ev_unf&?).
        eapply env_eval_args_congr in ev_unf as (fv&?&?).
        2: { rewrite <- (map_id argsv) in a0.
             apply All2_map_inv in a0.
             eapply All2_impl; eauto.
             cbn; intros.
             admit. }
        exists fv.
        split; [|unfold teq in *; congruence].
        eapply env_eval_app; eauto.
        eapply env_eval_fix with (argsv := []); eauto.
      + rewrite mkApps_app in eq; noconf eq.
        specialize (IHev1 _ _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev3 _ [] eq_refl) as (?&?&?&?&?).
        depelim a1.
        depelim a2.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf H.
        exists (x ++ [x2]); split; [apply All2_app; auto|].
        rewrite <- closed_unfold_fix_cunfold_eq in e by admit.
        change (tApp ?h ?a) with (mkApps h [a]) in e4.
        rewrite mkApps_nested in e4.
        rewrite <- map_app with (l' := [x2]) in e4.
        apply env_eval_mkApps_inv in e4 as (hdv&argsv&?&?&ev_unf).
        unfold unfold_fix in e.
        rewrite nth_error_map, map_length in e.
        destruct nth_error eqn:nth; [|discriminate].
        cbn in *.
        noconf e.
        rewrite Nat.add_0_r in *.
        rewrite <- terms_of_env_fixes in ev_unf.
        rewrite <- (env_fixes_length mfix0 σ) in ev_unf.
        erewrite <- (map_length _ (env_fixes _ _)) in ev_unf.
        rewrite <- subst_app_simpl with (k := 0) in ev_unf.
        rewrite <- map_app in ev_unf.
        apply env_eval_subst in ev_unf as (?&ev_unf&?).
        eapply env_eval_args_congr in ev_unf as (fv&?&?).
        2: { rewrite <- (map_id argsv) in a1.
             apply All2_map_inv in a1.
             eapply All2_impl; eauto.
             cbn; intros.
             admit. }
        exists fv.
        split; [|unfold teq in *; congruence].
        eapply env_eval_fix with (argsv := x); eauto.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *; subst.
      + cbn in *; subst.
        exists []; split; auto.
        specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf H.
        exists (vFix mfix0 idx σ (args ++ [x2])).
        cbn.
        rewrite map_app, mkApps_app; split; auto.
        unfold cunfold_fix in e.
        rewrite nth_error_map in e.
        destruct nth_error eqn:nth; [|discriminate].
        rewrite map_length in l.
        cbn in *.
        noconf e.
        eapply env_eval_app; eauto.
        eapply env_eval_fix_value with (argsv := []); eauto.
      + rewrite mkApps_app in eq; noconf eq.
        specialize (IHev1 _ _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        depelim a1.
        destruct x0; cbn in *; try discriminate; try solve_discr.
        noconf H.
        exists (x ++ [x2]); split; [apply All2_app; auto|].
        exists (vFix mfix0 idx σ (args0 ++ [x2])).
        cbn.
        rewrite map_app, mkApps_app; split; auto.
        unfold cunfold_fix in e.
        rewrite nth_error_map in e.
        destruct nth_error eqn:nth; [|discriminate].
        rewrite map_length in l.
        cbn in *.
        noconf e.
        eapply env_eval_fix_value; eauto.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *;
        [subst|rewrite mkApps_app in eq; cbn in *; discriminate].
      exists []; split; auto.
      specialize (IHev _ [] eq_refl) as (?&?&?&?&?).
      depelim a.
      subst.
      depelim e0; try solve [destruct argsv; cbn in *; discriminate].
      2: admit.
      rewrite <- closed_unfold_cofix_cunfold_eq in e by admit.
      unfold unfold_cofix in e.
      destruct nth_error eqn:nth; [|discriminate].
      noconf e.
      rewrite <- terms_of_env_cofixes_nil in e0_1.
      eapply env_eval_mkApps_inv in e0_1 as (fnv&args0v&?&?&?).
      eapply env_eval_subst in e1 as (ctorv&?&?).
      unfold teq in t.
      destruct ctorv; cbn in *; try discriminate; try solve_discr.
      noconf H.
      eapply env_eval_args_congr in e0_2 as (fv&?&?).
      2: { unfold teq.
           instantiate (1 := skipn pars args).
           apply All2_skipn.
           apply All2_map_inv with (f := term_of_ee_val) (g := term_of_ee_val).
           rewrite H0.
           apply All2_same; reflexivity. }
      exists fv.
      split; auto.
      eapply env_eval_cofix_case; eauto.
      unfold cofix_env; rewrite app_nil_r.
      auto.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *;
        [subst|rewrite mkApps_app in eq; cbn in *; discriminate].
      exists []; split; auto.
      specialize (IHev _ [] eq_refl) as (?&?&?&?&?).
      depelim a.
      subst.
      admit.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *;
        [subst|rewrite mkApps_app in eq; cbn in *; discriminate].
      exists []; split; auto.
      specialize (IHev _ [] eq_refl) as (?&?&?&?&?).
      depelim a.
      subst.
      exists x0.
      split; auto.
      eapply env_eval_delta; eauto.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *;
        [subst|rewrite mkApps_app in eq; cbn in *; discriminate].
      exists []; split; auto.
      specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
      specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
      depelim a.
      depelim a0.
      destruct x0; cbn in *; try discriminate; try solve_discr.
      noconf H.
      rewrite nth_nth_error in e2.
      rewrite nth_error_map in e2.
      destruct nth_error eqn:nth; cbn in *.
      2: { depelim e2; solve [destruct argsv; cbn in *; discriminate]. }
      eapply env_eval_term_of_ee_val in e2.
      2: admit.
      exists e1.
      split; auto.
      eapply env_eval_proj; eauto.
    - discriminate.
    - destruct args as [|? ? _] using MCList.rev_ind; cbn in *.
      + subst.
        exists []; split; auto.
        specialize (IHev1 _ [] eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        depelim a0.
        depelim a1.
        apply eval_to_value in ev1.
        destruct ev1.
        * destruct t; cbn in *; try discriminate.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             destruct args; [|discriminate].
             exists (vConstruct i1 n [x2]).
             split; eauto using env_eval.
             econstructor; eauto.
             eapply env_eval_app_construct with (argsv := []) (cargsv := []); eauto.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             destruct args; [|discriminate].
             exists (vCoFix mfix n σ [x2]).
             split; eauto using env_eval.
             econstructor; eauto.
             eapply env_eval_app_cofix with (argsv := []) (fargsv := []); eauto.
        * destruct t; cbn in *; try discriminate.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             exists (vConstruct i1 n (args ++ [x2])).
             cbn.
             rewrite map_app, mkApps_app.
             split; auto.
             eapply env_eval_app; eauto.
             eapply env_eval_app_construct with (argsv := []); eauto.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             exists (vCoFix mfix n σ (args ++ [x2])).
             cbn.
             rewrite map_app, mkApps_app.
             split; auto.
             eapply env_eval_app; eauto.
             eapply env_eval_app_cofix with (argsv := []); eauto.
        * destruct f0; try discriminate.
          rewrite isLambda_mkApps, isFixApp_mkApps in i by easy.
          discriminate.
      + rewrite mkApps_app in eq; noconf eq.
        specialize (IHev1 _ _ eq_refl) as (?&?&?&?&?).
        specialize (IHev2 _ [] eq_refl) as (?&?&?&?&?).
        depelim a1.
        exists (x ++ [x2]).
        split; [apply All2_app; auto|].
        apply eval_to_value in ev1.
        destruct ev1.
        * destruct t; cbn in *; try discriminate.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             destruct args0; [|discriminate].
             exists (vConstruct i1 n [x2]).
             cbn.
             split; auto.
             eapply env_eval_app_construct with (argsv := x) (cargsv := []); eauto.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             destruct args0; [|discriminate].
             exists (vCoFix mfix n σ [x2]).
             split; auto.
             eapply env_eval_app_cofix with (argsv := x) (fargsv := []); eauto.
        * destruct t; cbn in *; try discriminate.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             exists (vConstruct i1 n (args0 ++ [x2])).
             cbn.
             rewrite map_app, mkApps_app.
             split; auto.
             eapply env_eval_app_construct; eauto.
          -- destruct x0; cbn in *; try discriminate; try solve_discr.
             noconf H.
             exists (vCoFix mfix n σ (args0 ++ [x2])).
             cbn.
             rewrite map_app, mkApps_app.
             split; auto.
             eapply env_eval_app_cofix; eauto.
        * destruct f; try discriminate.
          rewrite isLambda_mkApps, isFixApp_mkApps in i by easy.
          discriminate.
    - subst.
      destruct args using MCList.rev_ind; [|rewrite mkApps_app in i; discriminate].
      cbn in *.
      exists []; split; auto.
      destruct hd; try discriminate.
      all: eauto using env_eval.
      1: { eexists; split; eauto using env_eval.
           cbn.
           now rewrite subst_empty. }
      all: eexists; split; eauto using env_eval.
      all: cbn.
      all: rewrite map_ext with (g := fun x => x)
        by (now intros []; unfold map_def; rewrite subst_empty).
      all: now rewrite map_id.
  Admitted.

  Lemma eval_env_eval Σ t v :
    Σ e⊢ t ▷ v ->
    ∑ v', Σ ;;; [] e⊢ t, [] ▷ v' × term_of_ee_val v' = v.
  Proof.
    intros ev.
    eapply eval_env_eval' with (args := []) in ev as (?&all&?).
    depelim all.
    auto.
  Qed.

End env_eval.

Notation "Σ ;;; σ 'e⊢' t ▷ v" :=
  (env_eval Σ σ t v) (at level 50, σ, t, v at next level) : type_scope.
