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

Definition consistent_mib_mask (mm : mib_masks) (mib : mutual_inductive_body) : Prop :=
  (#|param_mask mm| = ind_npars mib) /\
  ∥Alli (fun ind oib =>
           Alli (fun c '(_, args) => #|get_branch_mask mm ind c| = #|args|)
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

Lemma nth_analyze Σ t k state :
  wfe_term Σ t ->
  valid_ind_masks Σ state.2 ->
  nth k (analyze state t).1 false = nth k state.1 false && is_dead k t.
Proof.
  intros wf_t valid_im.
  induction t in k, state, wf_t, valid_im |- * using term_forall_list_ind; cbn in *; propify.
  - now btauto.
  - destruct (Nat.eqb_spec n k) as [<-|];
      [rewrite nth_clear_bit_eq|rewrite nth_clear_bit_neq by easy];
      btauto.
  - now btauto.
  - induction H; cbn in *; [now btauto|].
    propify.
    rewrite H, IHForall.
    btauto.
    easy.
    easy.
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
*)

(*
Lemma nth_analyze' t :
  (forall k state n,
      nth k (analyze_top_level analyze state n t).2.1 false = nth k state.1 false && is_dead k t) /\
  (forall k state,
      nth k (analyze state t).1 false = nth k state.1 false && is_dead k t).
Proof.
  induction t using term_forall_list_ind; cbn in *.
  - now split; intros; btauto.
  - split; intros.
    + destruct (Nat.eqb_spec n k) as [<-|].
      * rewrite nth_clear_bit_eq.
        now btauto.
      * rewrite nth_clear_bit_neq by easy.
        now btauto.
    + destruct (Nat.eqb_spec n k) as [<-|].
      * rewrite nth_clear_bit_eq.
        now btauto.
      * rewrite nth_clear_bit_neq by easy.
        now btauto.
  - now split; intros; btauto.
  - induction H; cbn in *; [now split; intros; btauto|].
    destruct H.
    destruct IHForall.
    split; intros.
    + rewrite H1, H2; [now btauto|exact 0].
    + rewrite H1, H2; [now btauto|exact 0].
  - destruct IHt.
    split; intros.
    + destruct n0; cbn.
      * now rewrite nth_tl, H0.
      * destruct analyze_top_level eqn:an.
        unfold remove_var.
        cbn.
        rewrite nth_tl.
        specialize (H (S k) (new_var state) n0).
        rewrite an in H.
        cbn in *.
        now rewrite H.
    + now rewrite nth_tl, H0.
  - destruct IHt1, IHt2.
    split; intros.
    + destruct analyze_top_level eqn:an.
      unfold remove_var.
      cbn.
      rewrite nth_tl.
      specialize (H1 (S k) (new_var (analyze state t1)) n0).
      rewrite an in H1.
      cbn in *.
      rewrite H1, H0.
      now btauto.
    + rewrite nth_tl, H2.
      cbn.
      rewrite H0.
      now btauto.
  - destruct IHt1, IHt2.
    split; intros.
    + rewrite H2, H0.
      now btauto.
    + rewrite H2, H0.
      now btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - destruct p, IHt.
    split; intros.
    + destruct get_mib_masks; cycle 1.
      * rewrite H0.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  -
    + destruct analyze_top_level eqn:an.
      unfold remove_var.
      cbn.
      rewrite nth_tl.
      specialize (H1 (S k) (new_var (analyze state t1)) n0).
      rewrite an in H1.
      cbn in *.
      rewrite H1, H0.
      now btauto.
    + rewrite nth_tl, H2.
      cbn.
      rewrite H0.
      now btauto.
      unfold new_var.
      cbn.
      easy.
      now btauto
        destruct k.
        -- cbn.
        rewrite hd_nth.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
  - now split; intros; btauto.
    + destruct k.
      cbn.
*)

(*
Lemma analyze_correct' Σ t :
  wfe_term Σ t ->
  (forall Γ im n mask Γ' im',
      analyze_top_level analyze (Γ, im) n t = (mask, (Γ', im')) ->
      (Γ', im') = analyze (Γ, im) t /\ valid_dearg_mask mask t /\ valid_cases im' t) /\
  (forall Γ im Γ' im',
      analyze (Γ, im) t = (Γ', im') ->
      (forall k, nth k Γ' false = nth k Γ false && is_dead k t) /\
      (forall t', valid_cases im t' -> valid_cases im' t') /\ valid_cases im' t).
Proof.
  induction t using term_forall_list_ind; cbn in *.
  - split; intros; noconf H; [easy|].
    split; [|easy].
    now intros; btauto.
  - split; intros; noconf H; [easy|].
    split; [|easy].
    intros.
    cbn.
    destruct (Nat.eqb_spec n k) as [<-|].
    + rewrite nth_clear_bit_eq.
      now btauto.
    + rewrite nth_clear_bit_neq by easy.
      now btauto.
  - split; intros; noconf H; [easy|].
    split; [|easy].
    intros; btauto.
  - split; intros.
    + noconf H0.
      cbn.
      split; [easy|].
      split; [easy|].
      induction H in Γ, im, Γ', im', H0 |- *; [easy|].
      destruct H.
      cbn in *.
      destruct fold_right eqn:fr.
      cbn in *; propify; split.
      * now apply H2 in H0.
      * apply IHForall in fr.
        apply H2 in H0 as (_ & ? & _).
        clear -H0 fr.
        induction l; [easy|].
        cbn in *; propify.
        now rewrite H0, IHl by easy.
    + induction H in Γ, im, Γ', im', H0 |- *; cbn in *;
        [noconf H0; split; intros; auto; btauto|].
      destruct H.
      destruct fold_right eqn:fr.
      apply IHForall in fr as (? & ?).
      apply H2 in H0 as (? & ?).
      split.
      * intros.
        rewrite H0, H3.
        now btauto.
      * propify.
        intuition auto.
        clear -H4 H7.
        induction l; [easy|].
        cbn in *; propify.
        now rewrite H4, IHl.
  - destruct IHt.
    split; intros; cbn in *.
    + destruct n0; cbn in *.
      * noconf H1.
        unfold new_var, remove_var; cbn in *.
        split; [easy|].
        split; [easy|].
        destruct analyze eqn:an.
        apply H0 in an.
        easy.
      * destruct analyze_top_level eqn:an.
        noconf H1.
        unfold new_var, remove_var in *; cbn in *.
        destruct a; cbn in *.
        apply H in an as (? & ?).
        propify.
        pattern (analyze (true :: Γ, im) t). (* wtf? *)
        rewrite <- H1.
        split; [easy|].
        intuition auto.
        destruct analyze eqn:an.
        apply H0 in an.
        intuition auto.
        noconf H1.
        specialize (H2 0).
        cbn in *.
        rewrite hd_nth.
        rewrite H2.
        now destruct ?.
    + destruct analyze eqn:an.
      apply H0 in an.
      unfold remove_var in *.
      cbn in *.
      noconf H1.
      intuition auto.
      rewrite nth_tl.
      rewrite H1.
      now btauto.
  - destruct IHt1, IHt2.
    split; intros.
    + unfold new_var, remove_var in *.

      destruct analyze eqn:an.
      apply H0 in an as (? & ?).

      destruct analyze_top_level eqn:an.
      cbn in *.
      noconf H3.
      destruct a.
      apply H1 in an as (-> & ? & ?).
      split; [easy|].
      split; [easy|].

      destruct analyze eqn:an.
      apply H2 in an as (? & ?).
      propify; intuition auto.
    + unfold new_var, remove_var in *.
      noconf H3; cbn in *.

      destruct (analyze (Γ, im) t1) eqn:an.
      cbn in *.
      apply H0 in an as (? & ?).
      destruct analyze eqn:an.
      apply H2 in an as (? & ?).
      cbn in *.
      split.
      * intros.
        rewrite nth_tl, H5, H3.
        now btauto.
      * propify.
        intuition auto.
  - destruct IHt1, IHt2.
    split; intros.
    + noconf H3; cbn in *.
      destruct (analyze (Γ, im) t1) eqn:an.
      propify.
      split; [easy|].
      split; [easy|].
      apply H0 in an as (? & ?).
      apply H2 in H3 as (? & ?).
      easy.
    + destruct (analyze (Γ, im) t1) eqn:an.
      propify.
      apply H0 in an as (? & ?).
      apply H2 in H3 as (? & ?).
      intuition auto.
      rewrite H3, H4.
      now btauto.
  - split; intros; noconf H; [easy|].
    split; [|easy].
    now intros; btauto.
  - split; intros; noconf H; [easy|].
    split; [|easy].
    now intros; btauto.
  - destruct IHt.
    split; intros.
    + destruct p.
      destruct get_mib_masks; cycle 1.
      { destruct analyze eqn:an.
        noconf H1.
        split; [easy|].
        split; [easy|].
        propify.
        apply H0 in an as (? & ? & ?).
        intuition auto.
        admit.
        admit. }
      admit.
    + admit.
  - destruct s as ((ind & npars) & arg).
    destruct IHt.
    admit.
  - split; intros.
    + unfold new_vars, remove_vars in *; cbn in *.
      noconf H0.
      split; [easy|].
      split; [easy|].
      induction H in Γ, im |- *; [easy|].
      cbn in *.

Lemma analyze_top_level_correct Γ im n t mask Γ' im' :
  analyze_top_level analyze (Γ, im) n t = (mask, (Γ', im')) ->
  (Γ', im') = analyze (Γ, im) t /\ valid_dearg_mask mask t /\ valid_cases im' t.
Proof.
  intros an.
  induction t in Γ, im, mask, Γ', im', an |- * using term_forall_list_ind;
    cbn in *; try solve [now noconf an].
  - noconf an.
    rewrite H0.
    split; [easy|].
    split; [easy|].
    induction H in Γ, im, H0 |- *; [easy|].
    cbn in *.
    propify; split.
    +
    induction l using List.rev_ind; [easy|].
    rewrite fold_left_app in *.
    cbn in *.
    apply Forall_snoc in H as (? & ?).
    rewrite forallb_app.
    cbn; propify.
    intuition auto.
    +
    apply and_assoc.
    split; [|easy].
    induction H; [easy|].
    cbn in *.
    propify; split; [|easy].
  - noconf an.
    cbn.
    easy.
  - noconf an.
    easy.
  -
*)

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
Lemma analyze_correct :
    + apply valid_masks_decl_add_const; [easy|easy|].
      admit.
