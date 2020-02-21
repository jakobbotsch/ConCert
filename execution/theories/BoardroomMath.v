From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import PArith.
From Coq Require Import Psatz.
From Coq Require Import SetoidTactics.
From Coq Require Import Field.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coqprime Require Import Zp FGroup EGroup Cyclic.
From Bignums Require Import BigZ.

Require Import Extras.
Import ListNotations.

Local Open Scope Z.

Class FField {A : Type} :=
  build_ffield {
    elmeq : A -> A -> Prop;
    elmeq_dec x y : {elmeq x y} + {~(elmeq x y)};
    zero : A;
    one : A;

    add : A -> A -> A;
    mul : A -> A -> A;

    opp : A -> A;
    inv : A -> A;
    pow : A -> Z -> A;

    order : Z;
    expeq e e' := e mod (order - 1) = e' mod (order - 1);

    order_ge_2 : order >= 2;

    elmeq_equiv :> Equivalence elmeq;
    add_proper :> Proper (elmeq ==> elmeq ==> elmeq) add;
    mul_proper :> Proper (elmeq ==> elmeq ==> elmeq) mul;
    opp_proper :> Proper (elmeq ==> elmeq) opp;
    inv_proper :> Proper (elmeq ==> elmeq) inv;
    pow_proper :> Proper (elmeq ==> eq ==> elmeq) pow;
    pow_exp_proper a :>
      ~(elmeq a zero) -> Proper (expeq ==> elmeq) (pow a);

    one_neq_zero : ~(elmeq one zero);

    add_comm a b : elmeq (add a b) (add b a);
    add_assoc a b c : elmeq (add a (add b c)) (add (add a b) c);

    mul_comm a b : elmeq (mul a b) (mul b a);
    mul_assoc a b c : elmeq (mul a (mul b c)) (mul (mul a b) c);

    add_0_l a : elmeq (add zero a) a;
    mul_0_l a : elmeq (mul zero a) zero;
    mul_1_l a : elmeq (mul one a) a;

    opp_inv_l a : elmeq (add (opp a) a) zero;
    inv_inv_l a : ~(elmeq a zero) -> elmeq (mul (inv a) a) one;
    inv_mul a b :
      ~(elmeq a zero) ->
      ~(elmeq b zero) ->
      inv (mul a b) = mul (inv a) (inv b);

    mul_add a b c : elmeq (mul (add a b) c) (add (mul a c) (mul b c));

    pow_0_r a :
      ~(elmeq a zero) ->
      elmeq (pow a 0) one;

    pow_1_r a : elmeq (pow a 1) a;

    pow_opp_1 a :
      ~(elmeq a zero) ->
      elmeq (pow a (-1)) (inv a);

    pow_plus a e e' :
      ~(elmeq a zero) ->
      elmeq (pow a (e + e')) (mul (pow a e) (pow a e'));

    pow_nonzero a e :
      ~(elmeq a zero) ->
      ~(elmeq (pow a e) zero);

    inv_nonzero a :
      ~(elmeq a zero) ->
      ~(elmeq (inv a) zero);
  }.

Arguments FField : clear implicits.

Delimit Scope ffield_scope with ffield.

Infix "==" := elmeq (at level 70) : ffield.
Notation "a !== b" := (~(elmeq a b)) (at level 70) : ffield.
Notation "0" := zero : ffield.
Notation "1" := one : ffield.
Infix "+" := add : ffield.
Infix "*" := mul : ffield.
Infix "^" := pow : ffield.
Notation "a 'exp=' b" := (expeq a b) (at level 70) : ffield.
Notation "a 'exp<>' b" := (~(expeq a b)) (at level 70) : ffield.

Local Open Scope ffield.
Global Instance oeq_equivalence {A : Type} (field : FField A) : Equivalence expeq.
Proof.
  unfold expeq.
  constructor.
  - constructor.
  - repeat intro; auto.
  - now intros ? ? ? -> ->.
Qed.

Definition FField_field_theory {A : Type} (field : FField A) :
  field_theory
    zero one
    add mul
    (fun x y => x + (opp y)) opp
    (fun x y => x * inv y) inv
    elmeq.
Proof.
  constructor; [constructor| | |].
  - apply add_0_l.
  - apply add_comm.
  - apply add_assoc.
  - apply mul_1_l.
  - apply mul_comm.
  - apply mul_assoc.
  - apply mul_add.
  - reflexivity.
  - intros x. rewrite add_comm. apply opp_inv_l.
  - apply one_neq_zero.
  - reflexivity.
  - apply inv_inv_l.
Qed.

Class Generator {A : Type} (field : FField A) :=
  build_generator {
    generator : A;
    generator_nonzero : generator !== 0;
  }.

Class DiscreteLog {A : Type} (field : FField A) (g : Generator field) :=
  build_log {
    (* This is computationally intractable, but we still elmequire it
    for ease of specification *)
    log : A -> Z;
    log_proper :> Proper (elmeq ==> expeq) log;
    pow_log a :
      a !== 0 ->
      generator ^ (log a) == a;

    log_1_l : log 1 exp= 0%Z;
    log_mul a b :
      a !== 0 ->
      b !== 0 ->
      log (a * b) exp= log a + log b;

    log_inv a : log (inv a) exp= -log a;
    log_generator : log generator = 1%Z;
  }.

Section WithFField.
  Context {A : Type}.
  Context {field : FField A}.
  Context {gen : Generator field}.
  Context {disc_log : DiscreteLog field gen}.

  Add Field ff : (FField_field_theory field).

  Local Open Scope ffield.

  Hint Resolve one_neq_zero pow_nonzero generator_nonzero inv_nonzero : core.

  Instance dr : DefaultRelation elmeq.

  Fixpoint prod (l : list A) : A :=
    match l with
    | [] => one
    | x :: xs => x * prod xs
    end.

  Instance plus_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.add.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Z.add_mod, xeq, yeq, <- Z.add_mod.
  Qed.

  Instance mul_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.mul.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Z.mul_mod, xeq, yeq, <- Z.mul_mod.
  Qed.

  Instance sub_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.sub.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Zminus_mod, xeq, yeq, <- Zminus_mod.
  Qed.

  Instance opp_expeq_proper : Proper (expeq ==> expeq) Z.opp.
  Proof.
    intros x x' xeq.
    rewrite <- !Z.sub_0_l.
    now rewrite xeq.
  Qed.

  Lemma log_pow a e :
    a !== 0 ->
    log (a ^ e) exp= e * log a.
  Proof.
    intros anz.
    induction e using Z.peano_ind.
    - rewrite pow_0_r; auto.
      apply log_1_l.
    - replace (Z.succ e) with (e + 1)%Z by lia.
      rewrite pow_plus by auto.
      rewrite log_mul; auto.
      rewrite IHe.
      replace ((e + 1) * log a)%Z with (e * log a + log a)%Z by lia.
      now rewrite pow_1_r.
    - replace (Z.pred e) with (e + (-1))%Z by lia.
      rewrite pow_plus by auto.
      rewrite log_mul by auto.
      rewrite IHe.
      rewrite (pow_opp_1 a) by auto.
      rewrite log_inv.
      now replace ((e + -1) * log a)%Z with (e * log a + - log a)%Z by lia.
  Qed.

  Lemma mul_both_l a b c :
    c !== 0 ->
    c * a == c * b ->
    a == b.
  Proof.
    intros cnz prod.
    rewrite <- (mul_1_l a), <- (mul_1_l b).
    rewrite <- (inv_inv_l c) by auto.
    now rewrite <- mul_assoc, prod, mul_assoc.
  Qed.

  Instance pow_generator_proper : Proper (expeq ==> elmeq) (pow generator) :=
    pow_exp_proper _ generator_nonzero.

  Lemma log_both a b :
    a !== 0 ->
    b !== 0 ->
    log a exp= log b ->
    a == b.
  Proof.
    intros an0 bn0 dleq.
    assert (generator ^ log a == generator ^ log a) as H by reflexivity.
    rewrite dleq in H at 1.
    now rewrite !pow_log in H by auto.
  Qed.

  Lemma log_pow_generator e :
    log (generator ^ e) exp= e.
  Proof.
    rewrite log_pow; auto.
    rewrite log_generator.
    now rewrite Z.mul_1_r.
  Qed.

  Lemma pow_both a b :
    generator ^ a == generator ^ b ->
    a exp= b.
  Proof.
    intros geq.
    assert (log (generator ^ a) exp= log (generator ^ a)) by reflexivity.
    rewrite geq in H at 1.
    now rewrite !log_pow_generator in H.
  Qed.

  Lemma int_domain a b :
    a !== 0 ->
    b !== 0 ->
    a * b !== 0.
  Proof.
    intros an0 bn0.
    apply (@field_is_integral_domain
             A
             0 1
             add
             mul
             (fun a b => a + (opp b))
             opp
             (fun a b => a * (inv b))
             inv); eauto.
    - typeclasses eauto.
    - constructor; typeclasses eauto.
    - apply F2AF.
      + typeclasses eauto.
      + constructor; typeclasses eauto.
      + apply (FField_field_theory field).
  Qed.

  Hint Resolve int_domain : core.

  Lemma mul_mul_zero a b :
    a * b == 0 -> a == 0 \/ b == 0.
  Proof.
    intros ab0.
    destruct (elmeq_dec a 0) as [?|a0]; auto.
    destruct (elmeq_dec b 0) as [?|b0]; auto.
    pose proof (int_domain _ _ a0 b0).
    contradiction.
  Qed.

  Hint Resolve mul_mul_zero : core.

  Lemma int_domain_full a b :
    a * b == 0 <-> a == 0 \/ b == 0.
  Proof.
    split; auto.
    intros [->| ->]; field.
  Qed.

  Lemma prod_units (xs : list A) :
    All (fun x => x !== 0) xs <-> prod xs !== 0.
  Proof.
    induction xs as [|x xs IH]; cbn in *; auto.
    - split; auto.
    - split.
      + intros.
        apply int_domain; intuition.
      + intros xprod.
        split.
        * intros eq; rewrite eq in *; rewrite mul_0_l in xprod.
          destruct (xprod ltac:(reflexivity)).
        * apply IH.
          intros eq; rewrite eq in *; rewrite mul_comm, mul_0_l in xprod.
          destruct (xprod ltac:(reflexivity)).
  Qed.

  Hint Resolve -> prod_units : core.
  Hint Resolve <- prod_units : core.

  Definition compute_public_key (sk : Z) : A :=
    generator ^ sk.

  Definition reconstructed_key (pks : list A) (n : nat) : A :=
    let lprod := prod (firstn n pks) in
    let rprod := inv (prod (skipn (S n) pks)) in
    lprod * rprod.

  Fixpoint reconstructed_keys_aux
           (pks : list A) (lprod rprod : A) : list A :=
    match pks with
    | [] => []
    | pk :: tl =>
      let rprod := rprod * pk in
      let rk := lprod * rprod in
      rk :: reconstructed_keys_aux tl (lprod * pk) rprod
    end.

  Definition reconstructed_keys (pks : list A) : list A :=
    let rprod := inv (prod pks) in
    reconstructed_keys_aux pks one rprod.

  Definition compute_public_vote (rk : A) (sk : Z) (sv : bool) : A :=
    rk ^ sk * if sv then generator else 1.

  Fixpoint bruteforce_tally_aux
           (aeq : forall a a', {a == a'} + {a !== a'})
           (n : nat)
           (votes_product : A) : option nat :=
    if aeq (generator ^ (Z.of_nat n)) votes_product then
      Some n
    else
      match n with
      | 0 => None
      | S n => bruteforce_tally_aux aeq n votes_product
      end%nat.

  Definition bruteforce_tally
           (aeq : forall a a', {a == a'} + {a !== a'})
           (votes : list A) : option nat :=
    bruteforce_tally_aux aeq (length votes) (prod votes).

  Definition elmseq (l l' : list A) : Prop :=
    Forall2 elmeq l l'.

  Instance prod_units_proper :
    Proper (elmseq ==> elmeq) prod.
  Proof.
    intros l l' leq.
    induction leq as [|x x' xs x's xeq xseq IH]; cbn in *.
    - reflexivity.
    - now rewrite xeq, IH.
  Qed.

  Instance elmseq_equiv : Equivalence elmseq.
  Proof.
    constructor.
    - intros l.
      induction l as [|x xs IH].
      + constructor.
      + now constructor.
    - intros l l' leq.
      induction leq.
      + constructor.
      + now constructor.
    - intros l l' l'' leq1 leq2.
      revert l'' leq2.
      induction leq1 as [|x xs IH]; intros l'' leq2.
      + inversion leq2; subst.
        constructor.
      + inversion leq2; subst.
        constructor.
        * rewrite H; assumption.
        * apply IHleq1.
          apply H4.
  Qed.

  Instance firstn_proper : Proper (eq ==> elmseq ==> elmseq) (@firstn A).
  Proof.
    intros n n' <- l l' leq.
    revert l l' leq.
    induction n; cbn in *; intros l l' leq.
    - reflexivity.
    - inversion leq; subst; try reflexivity.
      constructor; auto.
      apply IHn.
      apply H0.
  Qed.

  Instance skipn_proper : Proper (eq ==> elmseq ==> elmseq) (@skipn A).
  Proof.
    intros n n' <- l l' leq.
    revert l l' leq.
    induction n; cbn in *; intros l l' leq; auto.
    inversion leq; subst; try reflexivity.
    apply IHn.
    apply H0.
  Qed.

  Instance reconstructed_key_proper :
    Proper (elmseq ==> eq ==> elmeq) reconstructed_key.
  Proof.
    intros l l' leq x x' <-.
    unfold reconstructed_key.
    now rewrite leq.
  Qed.

  Instance cons_proper : Proper (elmeq ==> elmseq ==> elmseq) cons.
  Proof. intros x x' xeq l l' leq. constructor; auto. Qed.

  Instance reconstructed_keys_aux_proper :
    Proper (elmseq ==> elmeq ==> elmeq ==> elmseq) reconstructed_keys_aux.
  Proof.
    intros l l' leq.
    induction leq; intros lprod lprod' lprodeq rprod rprod' rprodeq; [reflexivity|].
    cbn.
    unshelve epose proof (IHleq (lprod * x) (lprod' * y) _ (rprod * x) (rprod' * y) _) as IH.
    + now rewrite lprodeq, H.
    + now rewrite rprodeq, H.
    + now rewrite IH, lprodeq, rprodeq, H.
  Qed.

  Lemma reconstructed_keys_proper :
    Proper (elmseq ==> elmseq) reconstructed_keys.
  Proof.
    intros l l' leq.
    unfold reconstructed_keys.
    now rewrite leq.
  Qed.

  Lemma reconstructed_keys_aux_nth pks1 pk pks2 :
    pk !== 0 ->
    All (fun x => x !== 0) pks2 ->
    reconstructed_key (pks1 ++ pk :: pks2) (length pks1) ==
    hd zero (reconstructed_keys_aux
                (pk :: pks2)
                (prod pks1)
                (inv (prod (pk :: pks2)))).
  Proof.
    intros unit units.
    unfold reconstructed_key.
    replace (length pks1) with (length pks1 + 0)%nat at 1 by lia.
    rewrite firstn_app_2; cbn.
    rewrite app_nil_r.
    replace (match pks1 ++ pk :: pks2 with | [] => [] | _ :: l => skipn (length pks1) l end)
      with pks2; cycle 1.
    { clear; induction pks1; auto. }

    field.
    auto.
  Qed.

  Lemma compute_public_key_unit sk :
    compute_public_key sk !== 0.
  Proof. apply pow_nonzero, generator_nonzero. Qed.
  Hint Resolve compute_public_key_unit : core.

  Lemma compute_public_keys_units sks :
    All (fun x => x !== 0) (map compute_public_key sks).
  Proof.
    induction sks as [|sk sks IH]; cbn; auto.
  Qed.
  Hint Resolve compute_public_keys_units : core.

  Lemma reconstructed_key_unit pks i :
    All (fun a => a !== 0) pks ->
    reconstructed_key pks i !== 0.
  Proof.
    intros all.
    unfold reconstructed_key.
    apply int_domain.
    - apply prod_units.
      apply (all_incl (firstn i pks) pks); auto.
      apply firstn_incl.
    - apply inv_nonzero.
      apply prod_units.
      apply (all_incl (skipn (S i) pks) pks); auto.
      apply skipn_incl.
  Qed.

  Lemma compute_public_vote_unit rk sk sv :
    rk !== 0 ->
    compute_public_vote rk sk sv !== 0.
  Proof.
    intros rk_unit.
    unfold compute_public_vote.
    destruct sv; auto.
  Qed.

  Hint Resolve
       compute_public_key_unit compute_public_keys_units
       reconstructed_key_unit compute_public_vote_unit : core.

  Lemma log_prod (l : list A) :
    All (fun a => a !== 0) l ->
    log (prod l) exp= sumZ log l.
  Proof.
    intros all.
    induction l as [|x xs IH]; cbn in *.
    - now rewrite log_1_l.
    - specialize (IH (proj2 all)).
      destruct all.
      rewrite log_mul by auto.
      now rewrite IH.
  Qed.

  Lemma prod_firstn_units n l :
    prod l !== 0 ->
    prod (firstn n l) !== 0.
  Proof.
    intros prodl.
    apply prod_units.
    pose proof (firstn_incl n l).
    apply all_incl with l; auto.
  Qed.

  Hint Resolve prod_firstn_units : core.

  Lemma prod_skipn_units n l :
    prod l !== 0 ->
    prod (skipn n l) !== 0.
  Proof.
    intros prodl.
    apply prod_units.
    pose proof (skipn_incl n l).
    apply all_incl with l; auto.
  Qed.

  Hint Resolve prod_skipn_units : core.

  Local Open Scope Z.
  Lemma sum_lemma l :
    sumZ (fun i => nth i l 0 *
                   (sumZ id (firstn i l) -
                    sumZ id (skipn (S i) l)))
         (seq 0 (length l)) = 0.
  Proof.
    rewrite (sumZ_seq_feq
               (fun i => sumZ (fun j => if Nat.ltb j i then nth i l 0 * nth j l 0 else 0)
                              (seq 0 (length l)) -
                         sumZ (fun j => if Nat.ltb i j then nth i l 0 * nth j l 0 else 0)
                              (seq 0 (length l))));
      cycle 1.
    {
      intros i ?.
      rewrite Z.mul_sub_distr_l.
      rewrite 2!sumZ_mul.
      unfold id.
      rewrite (sumZ_firstn 0) by (right; lia).
      rewrite (sumZ_skipn 0).
      apply f_equal2.
      - rewrite (sumZ_seq_split i) by lia.
        rewrite Z.add_comm.
        cbn -[Nat.ltb].
        rewrite sumZ_seq_n.
        rewrite (sumZ_seq_feq (fun _ => 0)); cycle 1.
        { intros j jlt. destruct (Nat.ltb_spec (j + i) i); auto; lia. }
        rewrite sumZ_zero.
        cbn -[Nat.ltb].
        apply sumZ_seq_feq.
        intros j jlt.
        destruct (Nat.ltb_spec j i); lia.
      - rewrite (sumZ_seq_split (S i)) by lia.
        rewrite (sumZ_seq_feq (fun _ => 0)); cycle 1.
        { intros j jlt. destruct (Nat.ltb_spec i j); auto; lia. }
        rewrite sumZ_zero.
        cbn.
        rewrite sumZ_seq_n.
        replace (length l - S i)%nat with (length l - i - 1)%nat by lia.
        apply sumZ_seq_feq.
        intros j jlt.
        replace (j + S i)%nat with (S (i + j))%nat by lia.
        destruct (Nat.leb_spec i (i + j)); lia.
    }

    rewrite <- sumZ_sub.
    rewrite sumZ_sumZ_seq_swap.
    match goal with
    | [|- ?a - ?b = 0] => enough (a = b) by lia
    end.
    apply sumZ_seq_feq.
    intros i ilt.
    apply sumZ_seq_feq.
    intros j jlt.
    destruct (i <? j)%nat; lia.
  Qed.

  Local Open Scope ffield.
  Lemma mul_public_votes
        (sks : list Z)
        (votes : nat -> bool) :
    prod (map (fun (i : nat) =>
                 compute_public_vote
                   (reconstructed_key (map compute_public_key sks) i)
                   (nth i sks 0%Z)
                   (votes i))
                 (seq 0 (length sks)))
    == generator ^ sumZ (fun i => if votes i then 1 else 0)%Z (seq 0 (length sks)).
  Proof.
    apply log_both; auto.
    - induction (seq 0 (length sks)); cbn; auto.
    - rewrite log_pow_generator, log_prod; cycle 1.
      {
        induction (seq 0 (length sks)); cbn; auto.
      }

      rewrite sumZ_map.
      unfold compute_public_vote.
      etransitivity.
      {
        apply sumZ_seq_feq_rel; try typeclasses eauto.
        intros i ilt.
        rewrite log_mul at 1 by (destruct (votes i); auto).
        setoid_replace (log (if votes i then generator else 1))
          with (if votes i then 1%Z else 0%Z) at 1;
          cycle 1.
        - destruct (votes i).
          + rewrite <- (pow_1_r generator).
            apply log_pow_generator.
          + apply log_1_l.
        - rewrite log_pow at 1 by auto.
          unfold reconstructed_key.
          rewrite log_mul at 1 by auto.
          rewrite log_prod at 1 by auto.
          rewrite log_inv at 1.
          rewrite log_prod at 1 by auto.
          rewrite 2!(sumZ_map_id log) at 1.
          rewrite firstn_map, skipn_map, !map_map.
          unfold compute_public_key.
          assert (forall l, sumZ id (map (fun x => log (generator ^ x)) l) exp= sumZ id l).
          { clear.
            intros l.
            induction l; cbn; auto.
            - reflexivity.
            - unfold id at 1 3.
              rewrite log_pow_generator.
              now rewrite IHl.
          }
          rewrite 2!H at 1.
          rewrite Z.add_opp_r.
          reflexivity.
      }

      rewrite sumZ_plus.
      rewrite sum_lemma.
      reflexivity.
  Qed.

  (*
  Lemma Z_eta z : match z with
                  | Z0 => Z0
                  | Zpos p => Zpos p
                  | Zneg p => Zneg p
                  end = z.
  Proof. now destruct z. Qed.

  (*
  Lemma sumZ_firstn_whole (f : Z -> Z) n (l : list Z) :
    sumZ f (firstn n l) =
    sumZ (fun i => if Nat.ltb i (length l) then f (nth i l 0%Z) else 0%Z) (seq 0 n).
  Proof.
    revert l f.
    induction n as [|n IH]; intros l f; auto.
    cbn -[Nat.ltb].
    rewrite sumZ_seq_n.
    destruct l as [|hd tl].
    - cbn.
      clear.
      induction (seq 0 n); auto.
    - cbn -[Nat.ltb].
      apply f_equal.
      rewrite IH.
      apply sumZ_exteq_proper; auto.
      intro a.
      replace (a + 1 <? S (length tl))%nat with (a <? length tl)%nat; cycle 1.
      { destruct (Nat.ltb_spec a (length tl)), (Nat.ltb_spec (a + 1) (S (length tl)));
          cbn in *; auto; lia. }
      destruct (Nat.ltb_spec a (length tl)); auto.
      destruct (a + 1)%nat eqn:a1; try lia.
      now replace a with n0 by lia.
  Qed.

  Lemma sumZ_skipn_whole (f : Z -> Z) n (l : list Z) :
    sumZ f (skipn n l) =
    sumZ (fun i => if Nat.ltb n i && Nat.ltb i (length l) then f (nth i l 0%Z) else 0%Z) (seq 0 n).
  Proof.
    replace (skipn n l) with (rev (firstn (length l - n) (rev l))) by admit.
    rewrite <- Permutation.Permutation_rev.
    rewrite sumZ_firstn_whole.
    induction l as [|x xs IH].
    - cbn.
      induction (seq 0 n); cbn; auto.
      rewrite <- IHl.
      destruct a; auto.
      destruct n; auto.
      cbn.
    apply sumZ_exteq_proper; auto.
    intros a.
    rewrite rev_length.
    destruct
    rewrite rev_nth.
    rewrite sumZ_firstn_whole.
    revert l f.
    induction n as [|n IH]; intros l f.
    - cbn.
    cbn -[Nat.ltb].
    rewrite sumZ_seq_n.
    destruct l as [|hd tl].
    - cbn.
      clear.
      induction (seq 0 n); auto.
    - cbn -[Nat.ltb].
      apply f_equal.
      rewrite IH.
      apply sumZ_exteq_proper; auto.
      intro a.
      replace (a + 1 <? S (length tl))%nat with (a <? length tl)%nat; cycle 1.
      { destruct (Nat.ltb_spec a (length tl)), (Nat.ltb_spec (a + 1) (S (length tl)));
          cbn in *; auto; lia. }
      destruct (Nat.ltb_spec a (length tl)); auto.
      destruct (a + 1)%nat eqn:a1; try lia.
      now replace a with n0 by lia.

  Lemma sum_split_center (l : list Z) i :
    sumZ id (firstn i l) - sumZ id (skipn (S i) l) =
    sumZ (fun j => (if Nat.ltb j i then 1
                    else if Nat.eqb j i then 0
                    else (-1)) * nth j l 0)%Z
         (seq 0 (length l)).
  Proof.
    destruct (i <=? length l)%nat eqn:le; [apply Nat.leb_le in le|apply Nat.leb_gt in le];
      cycle 1.
    {
      rewrite firstn_all2, skipn_none by lia.
      cbn -[Nat.ltb].
      rewrite Z.sub_0_r.
      revert l le.
      induction i as [|i IH]; intros l le.
      - lia.
      - destruct l; auto.
        cbn in le.
        specialize (IH l ltac:(lia)).
        cbn.
        rewrite sumZ_seq_n.
        rewrite Z_eta.
        apply f_equal.
        rewrite IH.
        apply sumZ_exteq_proper; auto.
        clear.
        intros n.
        replace (n + 1)%nat with (S n) by lia.
        repeat
          match goal with
          | [|- context[Nat.ltb ?a ?b]] => destruct (Nat.ltb_spec a b)
          | [|- context[Nat.leb ?a ?b]] => destruct (Nat.leb_spec a b)
          | [|- context[Nat.eqb ?a ?b]] => destruct (Nat.eqb_spec a b)
          end;
          cbn in *; lia.
    }

    revert l le.
    induction i as [|i IH]; intros l le.
    - cbn.
      induction l as [|x xs IH]; auto.
      cbn.
      rewrite sumZ_seq_n.
      destruct xs; auto.
      cbn.
      fold (Z.opp z).
      unfold id.
      replace (-(z + sumZ (fun x => x) xs)) with (-z + (- sumZ (fun x => x) xs))%Z by lia.
      apply f_equal.
      unfold id in IH; rewrite IH.
      rewrite (sumZ_seq_n _ 1).
      rewrite Z_eta.
    - destruct l; auto.
      cbn.
      rewrite Z_eta.
      unfold id.
      rewrite <- Z.add_sub_assoc.
      apply f_equal.
      rewrite sumZ_seq_n.
      rewrite IH.
      apply sumZ_exteq_proper; auto.
      intros n.
      replace (n + 1)%nat with (S n) by lia.
      repeat
        match goal with
        | [|- context[Nat.ltb ?a ?b]] => destruct (Nat.ltb_spec a b)
        | [|- context[Nat.leb ?a ?b]] => destruct (Nat.leb_spec a b)
        | [|- context[Nat.eqb ?a ?b]] => destruct (Nat.eqb_spec a b)
        end;
        cbn in *; lia.

    destruct (i <=? length l)%nat eqn:le; [apply Nat.leb_le in le|apply Nat.leb_gt in le];
      cycle 1.
    {
      rewrite firstn_all2, skipn_none by lia.
      cbn -[Nat.ltb].
      rewrite Z.sub_0_r.
      revert l le.
      induction i as [|i IH]; intros l le.
      - lia.
      - destruct l; auto.
        cbn in le.
        specialize (IH l ltac:(lia)).
        cbn.
        rewrite sumZ_seq_n.
        rewrite Z_eta.
        apply f_equal.
        rewrite IH.
        apply sumZ_exteq_proper; auto.
        clear.
        intros n.
        replace (n + 1)%nat with (S n) by lia.
        repeat
          match goal with
          | [|- context[Nat.ltb ?a ?b]] => destruct (Nat.ltb_spec a b)
          | [|- context[Nat.leb ?a ?b]] => destruct (Nat.leb_spec a b)
          | [|- context[Nat.eqb ?a ?b]] => destruct (Nat.eqb_spec a b)
          end;
          cbn in *; lia.
    }.
        destruct (n <? i)%nat eqn:lt; [apply Nat.ltb_lt in lt|apply Nat.ltb_ge in lt].
        Search (S _ =? S _).
        rewrite
        cbn.
        Search (_ + 1 <=? _).
        cbn.
        cbn.
      cbn -[Nat.ltb Z.mul] in *.
      rewrite sumZ_seq_n.
      destruct (Nat.ltb_spec 0 i); try lia.
      rewrite <- IH.
      unfold id.
      replace (length l + (i - length l))%nat with i in * by lia.
      rewrite firstn_nil in H.
      rewrite app_nil_r in *.
      rewrite H; cbn -[skipn Nat.ltb].

      rewrite firstn_le_length
    induction i as [|x xs IH].
    - rewrite firstn_nil. auto.
    - cbn
*)
  Local Open Scope Z.

  (*
  Local Open Scope ffield.
  Lemma mul_votes (sks : list Z) :
    prod (map (fun '(sk, rk) => pow rk sk)
                 (zip sks (reconstructed_keys (map compute_public_key sks))))
    == 1.
  Proof.


  Lemma sum_pks (sks : list Z) :
    sumZ (fun '(sk, rk) => sk * log rk)%Z
         (zip sks (reconstructed_keys (map compute_public_key sks))) exp= 0%Z.
  Proof.
    induction sks as [|sk sks IH]; cbn in *.
    1: reflexivity.
    setoid_replace
      (1 * (inv (compute_public_key sk *
                 prod (map compute_public_key sks)) *
            compute_public_key sk))
      with (inv (prod (map compute_public_key sks)))
      by (field; auto).


    replace (1 * pk) with pk by field.
    replace (inv (pk * prod pks) * pk) with (inv (prod pks)); cycle 1.
    { field. intuition. }
    replace (1 * (inv (prod pks))) with (inv (prod pks)); cycle 1.
    { field. intuition. }

    destruct units as [unit units].
    rewrite <- log_mul; auto.
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite <- (log_mul pk); auto.
    set (blah := match mod_inv _ _ * _ with _ => _ end).

  Lemma rks_alt sks n :
    All IsUnit sks ->
    (n < length sks)%nat ->
    reconstructed_key (map compute_public_key sks) n =
    generator ^ (sumZ id (firstn n sks) - sumZ id (skipn (S n) sks)) mod modulus.
  Proof.
    intros.
    induction n as [|n IH].
    - destruct sks; cbn in *; try lia.
      unfold reconstructed_key.
      cbn.
      rewrite eta_Z.

      unfold id at 1.
      replace (z + sumZ id sks - z) with (sumZ id sks) by lia.

  Lemma sum_pks pks :
    All IsUnit pks ->
    sumZ (fun '(pk, rk) => log pk + log rk)
         (zip pks (reconstructed_keys pks)) mod modulus = 0.
  Proof.
    intros units.
    induction pks as [|pk pks IH]; auto.
    cbn.
    rewrite !eta_Z.
    rewrite mod_inv_mod_idemp, mod_inv_mul.
    destruct units as [unit units].
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite <- (log_mul pk); auto.
    set (blah := match mod_inv _ _ * _ with _ => _ end).

Fixpoint mod_prod (l : list Z) (m : Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * mod_prod xs m mod m
  end.

Fixpoint mod_pow_aux (a : bigZ) (x : positive) (m : bigZ) (r : bigZ) : bigZ :=
  match x with
  | x~0%positive => mod_pow_aux (BigZ.square a mod m) x m r
  | x~1%positive => mod_pow_aux (BigZ.square a mod m) x m (r * a mod m)
  | _ => r * a mod m
  end.

Hint Rewrite BigZ.square_spec BigZ.spec_pow_pos : zsimpl.
Hint Rewrite BigN.spec_of_pos : nsimpl.

Global Instance BigZ_square_wd :
  Proper (BigZ.eq ==> BigZ.eq) BigZ.square.
Proof.
  intros a b eq.
  autorewrite with zsimpl in *.
  now rewrite eq.
Qed.

Global Instance mod_pow_aux_wd :
  Proper (BigZ.eq ==> eq ==> BigZ.eq ==> BigZ.eq ==> BigZ.eq) mod_pow_aux.
Proof.
  (*intros a1 a2 elmeq ? x -> m1 m2 meq r1 r2 elmeq.*)
  intros a1 a2 elmeq ? x ->.
  revert a1 a2 elmeq.
  induction x; intros a1 a2 elmeq m1 m2 meq r1 r2 elmeq.
  - cbn.
    apply IHx.
    + rewrite elmeq, meq.
      reflexivity.
    + auto.
    + rewrite elmeq, elmeq, meq.
      reflexivity.
  - cbn.
    apply IHx.
    + rewrite elmeq, meq.
      reflexivity.
    + auto.
    + rewrite elmeq.
      reflexivity.
  - cbn.
    rewrite elmeq, elmeq, meq.
    reflexivity.
Qed.

Definition mod_pow (a x m : Z) : Z :=
  match m with
  | Z0 => 0
  | _ =>
    match x with
    | Z0 => 1 mod m
    | Zneg _ => 0
    | Zpos x => [mod_pow_aux (BigZ.of_Z a) x (BigZ.of_Z m) 1]%bigZ
    end
  end.

Local Open Scope Z.
Lemma Z_pow_pos_mod_idemp a x m :
  Z.pow_pos (a mod m) x mod m = Z.pow_pos a x mod m.
Proof.
  destruct (m =? 0) eqn:mzero.
  {
    apply Z.eqb_eq in mzero.
    rewrite mzero.
    now rewrite 2!Zmod_0_r.
  }

  apply Z.eqb_neq in mzero.

  unfold Z.pow_pos.
  assert (H: forall start l x, Pos.iter (Z.mul l) start x = start * Pos.iter (Z.mul l) 1 x).
  {
    clear.
    intros start l x.
    revert start.
    induction x; intros start.
    - cbn.
      rewrite 2!IHx.
      rewrite (IHx (Pos.iter (Z.mul l) 1 x)).
      lia.
    - cbn.
      rewrite 2!IHx.
      rewrite (IHx (Pos.iter (Z.mul l) 1 x)).
      lia.
    - cbn.
      lia.
  }

  induction x.
  - cbn.
    rewrite (H _ (a mod m)).
    rewrite (H _ a).
    rewrite Z.mul_assoc.
    assert (H2: forall a b c,
               ((a mod m) * b * c) mod m = ((a mod m) * (b mod m) * (c mod m)) mod m).
    {
      clear.
      intros.
      rewrite <- Z.mul_assoc.
      rewrite Zmult_mod_idemp_l.

      rewrite <- Z.mul_assoc.
      rewrite Zmult_mod_idemp_l.

      rewrite 2!Z.mul_assoc.
      rewrite (Z.mul_comm _ (c mod m)).
      rewrite Zmult_mod_idemp_l.
      rewrite Z.mul_assoc.
      rewrite (Z.mul_comm _ (b mod m)).
      rewrite Zmult_mod_idemp_l.
      replace (b * (c * a)) with (a * b * c) by lia; auto.
    }

    rewrite H2.
    rewrite IHx.
    rewrite <- H2.

    rewrite <- Z.mul_assoc.
    now rewrite Zmult_mod_idemp_l.
  - cbn.
    rewrite H.
    rewrite Z.mul_mod by auto.
    rewrite IHx.
    rewrite <- Z.mul_mod by auto.
    now rewrite <- H.
  - cbn.
    rewrite 2!Z.mul_1_r.
    now apply Z.mod_mod.
Qed.

Lemma Z_pow_mod_idemp a x m :
  (a mod m)^x mod m = a^x mod m.
Proof.
  destruct x; auto.
  cbn.
  apply Z_pow_pos_mod_idemp.
Qed.

Lemma mod_pow_aux_spec a x m r :
  m != 0 ->
  mod_pow_aux a x m r == r * BigZ.pow_pos a x mod m.
Proof.
  cbn.
  intros nonzero.
  revert a r.
  induction x; intros a r.
  - cbn.
    specialize (IHx ((a * a) mod m) ((r * a) mod m))%bigZ.
    autorewrite with zsimpl.
    rewrite IHx.
    unfold "==".
    autorewrite with zsimpl.
    cbn -[Z.pow_pos].
    rewrite <- Z.mul_mod_idemp_r by auto.
    rewrite Z_pow_pos_mod_idemp.
    rewrite <- Z.mul_mod by auto.
    replace (x~1)%positive with (x*2+1)%positive by lia.
    rewrite Zpower_pos_is_exp.
    cbn.
    rewrite 2!Z.pow_pos_fold.
    rewrite Z.pow_mul_l.
    rewrite <- Z.pow_add_r by (auto with zarith).
    rewrite Zred_factor1.
    f_equal.
    lia.
  - cbn.
    rewrite IHx.
    unfold "==".
    autorewrite with zsimpl.
    cbn -[Z.pow_pos].
    rewrite <- Zmult_mod_idemp_r.
    rewrite Z_pow_pos_mod_idemp.
    rewrite Zmult_mod_idemp_r.
    replace (x~0)%positive with (x*2)%positive by lia.
    rewrite 2!Z.pow_pos_fold.
    rewrite Z.pow_mul_l.
    rewrite <- Z.pow_add_r by (auto with zarith).
    now rewrite Zred_factor1.
  - cbn.
    unfold "==".
    autorewrite with zsimpl.
    f_equal; lia.
Qed.

Lemma mod_pow_spec a x m :
  mod_pow a x m = a^x mod m.
Proof.
  unfold mod_pow.
  destruct m.
  - now rewrite Zmod_0_r.
  - destruct x; auto.
    rewrite mod_pow_aux_spec.
    + autorewrite with zsimpl.
      f_equal.
      cbn.
      destruct (Z.pow_pos _ _); auto.
    + intro cont.
      unfold "==" in *.
      cbn in *.
      autorewrite with nsimpl in cont.
      lia.
  - destruct x; auto.
    rewrite mod_pow_aux_spec.
    + autorewrite with zsimpl.
      f_equal.
      cbn.
      destruct (Z.pow_pos _ _); auto.
    + intro cont.
      unfold "==" in *.
      cbn in *.
      autorewrite with nsimpl in cont.
      lia.
Qed.

(* Find y such that x*y = 1 mod m *)
Definition mod_inv (x m : Z) : Z :=
  mod_pow x (m - 2) m.

Compute (mod_inv (mod_pow 33 47 59) 59).
Compute (FGroup.i (ZPGroup 59 ltac:(lia)) (gpow 33 (ZPGroup 59 ltac:(lia)) 47)).
Compute (inv 33 (ZPGroup 47 ltac:(lia)) (-1)).

Lemma mod_inv_spec x m :
  prime m ->
  x mod m <> 0 ->
  (x * mod_inv x m) mod m = 1.
Proof.
  intros is_prime xnm.
  pose proof (prime_ge_2 _ is_prime).
  unfold mod_inv.
  rewrite (mod_pow_spec x (m - 2) m).
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite <- Z.pow_succ_r by lia.
  replace (Z.succ (m - 2)) with (m - 1) by lia.
  (* Use proof of Euler's theorem from Coqprime *)
  rewrite <- (Euler.prime_phi_n_minus_1 _ is_prime).
  apply phi_power_is_1; try lia.
  apply rel_prime_sym.
  apply prime_rel_prime; auto.
  intros div.
  pose proof (Zdivide_mod _ _ div).
  tauto.
Qed.

Lemma mod_inv_mod_idemp (x m : Z) :
  mod_inv (x mod m) m = mod_inv x m.
Proof.
  unfold mod_inv.
  rewrite 2!mod_pow_spec.
  now rewrite Z_pow_mod_idemp.
Qed.

Lemma mod_inv_mul a b m :
  mod_inv (a * b) m =
  (mod_inv a m * mod_inv b m) mod m.
Proof.
  unfold mod_inv.
  now rewrite !mod_pow_spec, Z.pow_mul_l, Zmult_mod.
Qed.

Section Modulus.
  Context (modulus : Z).
  Context (is_prime : prime modulus).

  Let m_ge_2 := prime_ge_2 _ is_prime.

  Definition IsUnit (z : Z) : Prop :=
    z mod modulus <> 0.

  Record IsGenerator g : Prop :=
    build_is_generator {
      generator_between : 0 < g < modulus;
      generator_generates x :
        IsUnit x -> exists! e, 0 <= e < modulus /\ g ^ e mod modulus = x mod modulus;
      generator_order : g ^ (modulus - 1) mod modulus = 1;
    }.

  Context (generator : Z).
  Context (is_generator : IsGenerator generator).

  Definition Z_encode (z : Z) : nat :=
    Z.to_nat (if z <? 0 then -z * 2 + 1 else z * 2).
  Definition Z_decode (n : nat) : Z :=
    if Nat.even n then
      Z.of_nat n / 2
    else
      -Z.of_nat n / 2 + 1.
  Lemma Z_decode_encode (z : Z) : Z_decode (Z_encode z) = z.
  Proof.
    unfold Z_encode, Z_decode.
    destruct (z <? 0) eqn:lt0;
      [apply Z.ltb_lt in lt0|apply Z.ltb_ge in lt0].
    - rewrite Z2Nat.id by lia.
      rewrite Z2Nat.inj_add; try lia.
      rewrite Z2Nat.inj_mul; try lia.
      cbn; unfold Pos.to_nat; cbn.
      rewrite Nat.add_comm, Nat.mul_comm at 1.
      rewrite Nat.even_mul_add_2.
      cbn.
      rewrite Z.opp_add_distr, Z.mul_opp_l, Z.opp_involutive.
      cbn.
      rewrite Z.div_add_l by lia.
      cbn.
      lia.
    - rewrite Z2Nat.inj_mul by lia.
      cbn; unfold Pos.to_nat; cbn.
      rewrite Nat.even_mul; cbn; rewrite Bool.orb_true_r.
      rewrite Nat2Z.inj_mul.
      cbn; unfold Pos.to_nat; cbn.
      rewrite Z.div_mul by lia.
      rewrite Z2Nat.id; auto.
  Qed.

  Lemma deunique {A} (P : A -> Prop) :
    (exists! x, P x) -> exists x, P x.
  Proof.
    intros [x []].
    exists x; auto.
  Qed.

  Definition log_with_spec (x : Z) :
    IsUnit x ->
    { e : Z | 0 <= e < modulus /\ generator ^ e mod modulus = x mod modulus }.
  Proof.
    intros isunit.
    refine (constructive_definite_ground_description
              Z Z_encode Z_decode Z_decode_encode
              _ _ (generator_generates _ is_generator _ isunit)).
    intros e.
    destruct ((e >=? 0) && (e <? modulus) && (generator ^ e mod modulus =? x mod modulus))%bool eqn:test.
    - left.
      apply Bool.andb_true_iff in test; destruct test as [test test3].
      apply Bool.andb_true_iff in test; destruct test as [test1 test2].
      apply Z.geb_le in test1.
      apply Z.ltb_lt in test2.
      apply Z.eqb_eq in test3.
      tauto.
    - right.
      apply Bool.andb_false_iff in test; destruct test as [test|test].
      + apply Bool.andb_false_iff in test; destruct test as [test|test].
        * rewrite Z.geb_leb in test.
          apply Z.leb_gt in test.
          lia.
        * apply Z.ltb_ge in test.
          lia.
      + apply Z.eqb_neq in test.
        tauto.
  Defined.

  Definition log (x : Z) : Z.
  Proof.
    destruct (Z.eq_dec (x mod modulus) 0) as [eq|ne].
    - exact 0.
    - exact (proj1_sig (log_with_spec x ne)).
  Defined.

  Lemma log_spec x :
    IsUnit x ->
    0 <= log x < modulus /\
    generator ^ log x mod modulus = x mod modulus.
  Proof.
    intros is_unit.
    unfold log.
    destruct (Z.eq_dec _ _).
    - contradiction.
    - apply (proj2_sig (log_with_spec x n)).
  Qed.

  Lemma log_mul x y :
    IsUnit x ->
    IsUnit y ->
    log (x * y) = (log x + log y) mod modulus.
  Proof.
    Admitted.

  Lemma log_mod x :
    log x mod modulus = log x.
  Proof.
    unfold log.
    destruct (Z.eq_dec (x mod modulus) 0) as [eq|ne]; auto.
    pose proof (proj2_sig (log_with_spec x ne)) as H.
    cbn in H.
    destruct H as [H _].
    rewrite Z.mod_small; auto.
  Qed.

  Definition compute_public_key (sk : Z) : Z :=
    mod_pow generator sk modulus.

  Definition reconstructed_key (pks : list Z) (n : nat) : Z :=
    let lprod := mod_prod (firstn n pks) modulus in
    let rprod := mod_inv (mod_prod (skipn (S n) pks) modulus) modulus in
    (lprod * rprod) mod modulus.

  Fixpoint reconstructed_keys_aux
           (pks : list Z) (lprod rprod : Z) : list Z :=
    match pks with
    | [] => []
    | pk :: tl =>
      let rprod := rprod * pk in
      let rk := lprod * rprod mod modulus in
      rk :: reconstructed_keys_aux tl (lprod * pk) rprod
    end.

  Definition reconstructed_keys (pks : list Z) : list Z :=
    let rprod := mod_inv (mod_prod pks modulus) modulus in
    reconstructed_keys_aux pks 1 rprod.

  Lemma reconstructed_keys_aux_nth pks1 pk pks2 :
    IsUnit pk ->
    reconstructed_key (pks1 ++ pk :: pks2) (length pks1) =
    hd 0 (reconstructed_keys_aux (pk :: pks2)
                                 (mod_prod pks1 modulus)
                                 (mod_inv (mod_prod (pk :: pks2) modulus) modulus)).
  Proof.
    intros unit.
    unfold reconstructed_key.
    replace (length pks1) with (length pks1 + 0)%nat at 1 by lia.
    rewrite firstn_app_2; cbn.
    rewrite app_nil_r.
    replace (match pks1 ++ pk :: pks2 with | [] => [] | _ :: l => skipn (length pks1) l end)
      with pks2; cycle 1.
    { clear; induction pks1; auto. }
    rewrite mod_inv_mod_idemp, mod_inv_mul.
    rewrite <- (Z.mul_mod_idemp_r _ ((mod_inv pk modulus * mod_inv _ _) mod _ * pk)) by lia.
    rewrite Z.mul_mod_idemp_l by lia.
    replace (mod_inv pk _ * mod_inv _ _ * pk)
      with (pk * mod_inv pk modulus * mod_inv (mod_prod pks2 modulus) modulus)
      by lia.
    rewrite <- (Z.mul_mod_idemp_l (pk * _)) by lia.
    rewrite mod_inv_spec by auto.
    rewrite Z.mul_1_l.
    now rewrite Z.mul_mod_idemp_r by lia.
  Qed.

  Lemma eta_Z (z : Z) :
    match z with
    | Z0 => Z0
    | Zpos p => Zpos p
    | Zneg p => Zneg p
    end = z.
  Proof. now destruct z. Qed.

  Lemma rks_alt sks n :
    All IsUnit sks ->
    (n < length sks)%nat ->
    reconstructed_key (map compute_public_key sks) n =
    generator ^ (sumZ id (firstn n sks) - sumZ id (skipn (S n) sks)) mod modulus.
  Proof.
    intros.
    induction n as [|n IH].
    - destruct sks; cbn in *; try lia.
      unfold reconstructed_key.
      cbn.
      rewrite eta_Z.

      unfold id at 1.
      replace (z + sumZ id sks - z) with (sumZ id sks) by lia.


  Lemma sum_pks pks :
    All IsUnit pks ->
    sumZ (fun '(pk, rk) => log pk + log rk)
         (zip pks (reconstructed_keys pks)) mod modulus = 0.
  Proof.
    intros units.
    induction pks as [|pk pks IH]; auto.
    cbn.
    rewrite !eta_Z.
    rewrite mod_inv_mod_idemp, mod_inv_mul.
    destruct units as [unit units].
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite <- (log_mul pk); auto.
    set (blah := match mod_inv _ _ * _ with _ => _ end).


  (*
  Lemma reconstructed_keys_nth pks n :
    All IsUnit pks ->
    nth n (reconstructed_keys pks) 0 = reconstructed_key pks n.
  Proof.
    intros units.
    assert (exists pref pk suf,
               pref ++ pk :: suf = pks /\
               length pref = n /\
               IsUnit pk).
    { admit. }
    destruct H as [pref [pk [suf [<- [<- ?]]]]].
    rewrite reconstructed_keys_aux_nth by auto.
    unfold reconstructed_keys.
    cbn.
    fold (mod_prod suf modulus).
    fold (reconstructed_keys_aux pref
    fold (reconstructed_keys
    unfold hd.
    cbn.
    induction n as [|n IH].
    - cbn.
    unfold reconstructed_keys.
*)

  Lemma map_reconstructed_key pks :
    map (fun i => reconstructed_key
    map reconstructed_key

  Lemma prime_pow a b : b >= 0 -> (modulus | a ^ b) -> (modulus | a).
  Proof.
    intros nonnegative divides.
    destruct b as [|e|e].
    - pose proof (prime_ge_2 _ is_prime).
      apply Z.divide_1_r in divides.
      destruct divides; lia.
    - induction e as [|e IH] using Pos.peano_ind.
      + now rewrite Z.pow_1_r in divides.
      + rewrite Pos2Z.inj_succ in divides.
        rewrite <- Z.add_1_l in divides.
        rewrite Z.pow_add_r in divides; [|lia|lia].
        rewrite Z.pow_1_r in divides.
        destruct (prime_mult _ is_prime _ _ divides); auto.
    - lia.
  Qed.

  Lemma pow_0 b x :
    x >= 0 ->
    b ^ x mod modulus = 0 ->
    b mod modulus = 0.
  Proof.
    intros nonneg eq.
    pose proof (prime_ge_2 _ is_prime).
    apply Z.mod_divide; [lia|].
    apply Z.mod_divide in eq; [|lia].
    apply prime_pow with x; auto.
  Qed.
  (*
Lemma generator_pos b x :
  0 <= x ->
  b mod p <> 0 ->
  b ^ x mod p <> 0.
Proof.
  intros x_nonneg b_noncongruent.
  pose proof (prime_ge_2 _ is_prime).
  (*destruct is_generator as [g_between g_order].*)
  assert (b ^ x mod p <> 0).
  {
    apply pow_0 in eq; [|lia].
    apply Z.mod_divide in eq; [|lia].
    destruct eq as [k eq].
    subst.
    destruct k; cbn in *.
    - cbn in *; lia.
    - rewrite Z.mul_comm in g_between.
      pose proof (proj1 (Z.le_mul_diag_r modulus (Z.pos p) ltac:(lia)) ltac:(lia)).
      lia.
    - assert (Z.neg p <= -1) by lia.
      pose proof (proj1 (Z.le_mul_diag_l (Z.neg p) modulus ltac:(lia)) ltac:(lia)).
      lia.
  }

  pose proof (Z.mod_pos_bound (generator ^ n) modulus ltac:(lia)).
  lia.
Qed.
   *)

  Lemma log z :
    z <> 0 ->
    exists! e, generator ^ e mod modulus = z mod modulus.
  Proof.
    Admitted.

  Definition compute_public_vote (rk sk : Z) (sv : bool) : Z :=
    (mod_pow rk sk modulus * if sv then generator else 1) mod modulus.

  Lemma generator_pos x :
    0 <= x ->
    generator ^ x mod modulus > 0.
  Proof.
    intros nonneg.
    destruct is_generator as [between _].
    assert (generator^x mod modulus <> 0).
    {
      intros eq.
      apply pow_0 in eq; [|lia].
      apply Z.mod_divide in eq; [|lia].
      destruct eq as [k eq].
      subst.
      destruct k as [|k|k]; cbn -[Z.mul] in *.
      - cbn in *; lia.
      - rewrite Z.mul_comm in between.
        pose proof (proj1 (Z.le_mul_diag_r modulus (Z.pos k) ltac:(lia)) ltac:(lia)).
        lia.
      - assert (Z.neg k <= -1) by lia.
        pose proof (proj1 (Z.le_mul_diag_l (Z.neg k) modulus ltac:(lia)) ltac:(lia)).
        lia.
    }

    pose proof (Z.mod_pos_bound (generator^x) modulus ltac:(lia)).
    lia.
  Qed.

  Lemma AllUnits_pks sks :
    AllUnits sks -> AllUnits (map compute_public_key sks).
  Proof.
    intros sks_pos.
    apply AllUnits_map; auto.
    intros x x_gt.
    unfold compute_public_key.
    rewrite mod_pow_spec.
    apply generator_pos; lia.
  Qed.

  (*
  Lemma rks_prod (sks : list Z) (pks : list Z) :
    AllUnits sks ->
    pks = map compute_public_key sks ->
    prodZ (fun i => (reconstructed_key pks i) ^ nth i sks 0) (seq 0 (length sks)) mod modulus = 1.
  Proof.
    intros sks_pos pks_eq.
    assert (pks_pos: AllUnits pks) by (subst; auto using AllUnits_pks).

    assert (exists exps, map (fun exp => generator ^ exp mod modulus) exps =
                         map (fun i => reconstructed_key pks i) (seq 0 (length pks))).
    { clear -is_prime is_generator pks_pos.
      induction pks as [|pk pks IH].
      - now exists [].
      - apply AllUnits_cons_r in pks_pos.
        destruct pks_pos as [pk_pos pks_pos].
        destruct IH as [tl IH]; [tauto|].
        destruct (log pk ltac:(lia)) as [e [e_eq e_uniq]].
        exists (e :: tl).
        cbn.
        rewrite IH.

                                 k=
                               reconstructed_key pks
                                                 pose proof (prime_ge_2 _ modulus_prime).
                               generalize 0%nat.
                               induction sks as [|sk sks IH]; intros n.
                               - apply Z.mod_1_l; lia.
                               - apply AllUnitsKeys_cons in nonzero.
                                 destruct nonzero as [sk_nonzero nonzero].
                                 specialize (IH nonzero).
                                 cbn.

*)
*)
*)
End WithFField.

Section Zp.
  Local Open Scope Z.

  Fixpoint mod_pow_pos_aux (a : Z) (x : positive) (m : Z) (r : Z) : Z :=
    match x with
    | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : Z) (x : positive) (m : Z) : Z :=
    mod_pow_pos_aux a x m 1.

  Definition mod_pow (a x p : Z) : Z :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_pow_pos (mod_pow_pos a x p) (Z.to_pos (p - 2)) p
    end.

  Lemma Z_pow_pos_mod_idemp a x m :
    Z.pow_pos (a mod m) x mod m = Z.pow_pos a x mod m.
  Proof.
    destruct (m =? 0) eqn:mzero.
    {
      apply Z.eqb_eq in mzero.
      rewrite mzero.
      now rewrite 2!Zmod_0_r.
    }

    apply Z.eqb_neq in mzero.

    unfold Z.pow_pos.
    assert (H: forall start l x, Pos.iter (Z.mul l) start x = start * Pos.iter (Z.mul l) 1 x).
    {
      clear.
      intros start l x.
      revert start.
      induction x; intros start.
      - cbn.
        rewrite 2!IHx.
        rewrite (IHx (Pos.iter (Z.mul l) 1 x)).
        lia.
      - cbn.
        rewrite 2!IHx.
        rewrite (IHx (Pos.iter (Z.mul l) 1 x)).
        lia.
      - cbn.
        lia.
    }

    induction x.
    - cbn.
      rewrite (H _ (a mod m)).
      rewrite (H _ a).
      rewrite Z.mul_assoc.
      assert (H2: forall a b c,
                 ((a mod m) * b * c) mod m = ((a mod m) * (b mod m) * (c mod m)) mod m).
      {
        clear.
        intros.
        rewrite <- Z.mul_assoc.
        rewrite Zmult_mod_idemp_l.

        rewrite <- Z.mul_assoc.
        rewrite Zmult_mod_idemp_l.

        rewrite 2!Z.mul_assoc.
        rewrite (Z.mul_comm _ (c mod m)).
        rewrite Zmult_mod_idemp_l.
        rewrite Z.mul_assoc.
        rewrite (Z.mul_comm _ (b mod m)).
        rewrite Zmult_mod_idemp_l.
        replace (b * (c * a)) with (a * b * c) by lia; auto.
      }

      rewrite H2.
      rewrite IHx.
      rewrite <- H2.

      rewrite <- Z.mul_assoc.
      now rewrite Zmult_mod_idemp_l.
    - cbn.
      rewrite H.
      rewrite Z.mul_mod by auto.
      rewrite IHx.
      rewrite <- Z.mul_mod by auto.
      now rewrite <- H.
    - cbn.
      rewrite 2!Z.mul_1_r.
      now apply Z.mod_mod.
  Qed.

  Lemma mod_pow_pos_aux_0_r a x r :
    mod_pow_pos_aux a x 0 r = 0.
  Proof.
    revert a r.
    induction x; intros a r; cbn.
    + now (repeat rewrite ?IHx, ?Zmod_0_r).
    + now (repeat rewrite ?IHx, ?Zmod_0_r).
    + now rewrite !Zmod_0_r.
  Qed.

  Lemma mod_pow_pos_0_r a x :
    mod_pow_pos a x 0 = 0.
  Proof. apply mod_pow_pos_aux_0_r. Qed.

  Lemma mod_pow_pos_aux_spec a x p r :
    mod_pow_pos_aux a x p r = r * Z.pow_pos a x mod p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|nonzero].
    - now rewrite mod_pow_pos_aux_0_r, Zmod_0_r.
    - revert a r.
      induction x; intros a r.
      + cbn -[Z.pow_pos].
        specialize (IHx ((a * a) mod p) ((r * a) mod p)).
        rewrite IHx.
        rewrite <- Z.mul_mod_idemp_r by auto.
        rewrite Z_pow_pos_mod_idemp.
        rewrite <- Z.mul_mod by auto.
        replace (x~1)%positive with (x*2+1)%positive by lia.
        rewrite Zpower_pos_is_exp.
        cbn.
        rewrite 2!Z.pow_pos_fold.
        rewrite Z.pow_mul_l.
        rewrite <- Z.pow_add_r by (auto with zarith).
        rewrite Zred_factor1.
        f_equal.
        lia.
      + cbn -[Z.pow_pos].
        rewrite IHx.
        rewrite <- Zmult_mod_idemp_r.
        rewrite Z_pow_pos_mod_idemp.
        rewrite Zmult_mod_idemp_r.
        replace (x~0)%positive with (x*2)%positive by lia.
        rewrite 2!Z.pow_pos_fold.
        rewrite Z.pow_mul_l.
        rewrite <- Z.pow_add_r by (auto with zarith).
        now rewrite Zred_factor1.
      + cbn.
        f_equal; lia.
  Qed.

  Lemma mod_pow_pos_spec a x p :
    mod_pow_pos a x p = Z.pow_pos a x mod p.
  Proof.
    pose proof (mod_pow_pos_aux_spec a x p 1).
    now rewrite Z.mul_1_l in H.
  Qed.

  Lemma mod_pow_spec a x p :
    x >= 0 ->
    mod_pow a x p = a^x mod p.
  Proof.
    intros xp.
    unfold mod_pow.
    destruct x; try lia.
    now rewrite mod_pow_pos_spec by lia.
  Qed.

  Lemma Z_pow_mod_idemp a x p :
    (a mod p)^x mod p = a^x mod p.
  Proof.
    destruct x; auto.
    cbn.
    apply Z_pow_pos_mod_idemp.
  Qed.

  Lemma mod_pow_pos_aux_idemp a x p r :
    mod_pow_pos_aux (a mod p) x p r = mod_pow_pos_aux a x p r.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - now rewrite !mod_pow_pos_aux_0_r.
    - revert a r.
      induction x; intros a r; cbn in *.
      + rewrite <- Z.mul_mod by auto.
        now rewrite Z.mul_mod_idemp_r by auto.
      + now rewrite <- Z.mul_mod by auto.
      + now rewrite Z.mul_mod_idemp_r by auto.
  Qed.

  Lemma mod_pow_pos_idemp a x p :
    mod_pow_pos (a mod p) x p = mod_pow_pos a x p.
  Proof. apply mod_pow_pos_aux_idemp. Qed.

  Lemma mod_pow_idemp a x p :
    mod_pow (a mod p) x p = mod_pow a x p.
  Proof.
    unfold mod_pow.
    destruct p; auto.
    all: destruct x; auto.
    all: now rewrite mod_pow_pos_idemp by lia.
  Qed.

  Lemma mod_pow_pos_fermat a p :
    prime p ->
    a mod p <> 0 ->
    mod_pow_pos a (Z.to_pos (p - 1)) p = 1.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    rewrite mod_pow_pos_spec.
    rewrite Z.pow_pos_fold.
    rewrite Z2Pos.id by lia.
    (* Use proof of Euler's theorem from Coqprime *)
    rewrite <- (Euler.prime_phi_n_minus_1 _ isprime).
    apply phi_power_is_1; try lia.
    apply rel_prime_sym.
    apply prime_rel_prime; auto.
    intros div.
    pose proof (Zdivide_mod _ _ div).
    tauto.
  Qed.

  Lemma mod_pow_pos_exp_plus a x x' p :
    mod_pow_pos a (x + x') p = mod_pow_pos a x p * mod_pow_pos a x' p mod p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - now rewrite !mod_pow_pos_0_r.
    - rewrite !mod_pow_pos_spec by auto.
      rewrite !Z.pow_pos_fold.
      rewrite Pos2Z.inj_add.
      rewrite Z.pow_add_r by lia.
      now rewrite Z.mul_mod by auto.
  Qed.

  Lemma mod_pow_pos_exp_mul a x x' p :
    mod_pow_pos a (x * x') p = mod_pow_pos (mod_pow_pos a x p) x' p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - now rewrite !mod_pow_pos_0_r.
    - rewrite !mod_pow_pos_spec by auto.
      rewrite !Z.pow_pos_fold.
      rewrite Pos2Z.inj_mul.
      rewrite Z_pow_mod_idemp.
      now rewrite <- Z.pow_mul_r by lia.
  Qed.

  Lemma mod_pow_pos_1_l x p :
    mod_pow_pos 1 x p = 1 mod p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - unfold mod_pow_pos.
      cbn.
      generalize 1 at 1.
      generalize 1 at 1.
      induction x; intros a r; auto.
      + cbn.
        now rewrite IHx.
      + cbn.
        now rewrite IHx.
      + cbn.
        now rewrite Zmod_0_r.
    - rewrite mod_pow_pos_spec by auto.
      rewrite Z.pow_pos_fold.
      now rewrite Z.pow_1_l by lia.
  Qed.

  Lemma mod_pow_pos_mod a x p :
    mod_pow_pos a x p mod p = mod_pow_pos a x p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?];
      [now rewrite !mod_pow_pos_0_r|].
    now rewrite mod_pow_pos_spec, Z.mod_mod by auto.
  Qed.

  Lemma mod_pow_pos_succ_r a x p :
    a * mod_pow_pos a x p mod p = mod_pow_pos a (Pos.succ x) p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - rewrite !mod_pow_pos_0_r.
      now rewrite Zmod_0_r.
    - rewrite !mod_pow_pos_spec, !Z.pow_pos_fold.
      cbn.
      rewrite Z.mul_mod_idemp_r by lia.
      rewrite Z.pow_pos_fold.
      rewrite <- Z.pow_succ_r by lia.
      cbn.
      now rewrite <- Pos.add_1_r.
  Qed.

  Lemma mod_pow_exp_plus a x x' p :
    prime p ->
    mod_pow a (x + x') p = mod_pow a x p * mod_pow a x' p mod p.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    unfold mod_pow.
    destruct x, x'; cbn.
    all: try rewrite !Z.mod_1_l by lia; auto.
    all: try rewrite !Z.mul_1_l; try rewrite !Z.mul_1_r.
    all: try rewrite !mod_pow_pos_mod; auto.
    - apply mod_pow_pos_exp_plus.
    - destruct (Pos.eq_dec p0 p1) as [->|?].
      + rewrite Z.pos_sub_diag; cbn.
        rewrite mod_pow_pos_succ_r.
        rewrite <- mod_pow_pos_exp_mul.
        destruct (Z.eq_dec p 2) as [->|?].
        * cbn.
        replace (Pos.succ (Z.to_pos (p - 2))) with (Z.to_pos (p - 1)) by lia.
        rewrite <- mod_pow_pos_exp_mul.
        rewrite mod_pow_

    all: cbn.
    destruct x
    destruct p; auto.
    all: destruct (x + x') eqn:?, x, x'.
    all: try rewrite Z.pow_0_r, !Z.mod_1_l by lia; auto; try lia.
    - replace p1 with p0 by lia.

    destruct (Z.eq_dec p 0) as [->|?]; auto.

  (*
  Lemma mod_pow_pos_exp a x p k :
    prime p ->
    a mod p <> 0 ->
    mod_pow_pos a x p = mod_pow_pos a (x + Z.to_pos (k *  Z.p (Z.to_pos (Z.pos x mod (p - 1))) p.
  Proof.
    intros isprime ap0 xp0.
    pose proof (prime_ge_2 _ isprime).
    destruct (Z.pos x <? (p - 1)) eqn:lt.
    {
      apply Z.ltb_lt in lt.
      now rewrite Z.mod_small by lia.
    }

    apply Z.ltb_ge in lt.
    change x with (Z.to_pos (Z.pos x)) at 1.
    rewrite (Z.quot_rem' (Z.pos x) (p - 1)) at 1.
    rewrite Z2Pos.inj_add; cycle 1.
    + apply Z.mul_pos_pos; try lia.
      apply Z.quot_str_pos; lia.
    + rewrite Z.rem_mod_nonneg by lia.
      pose proof (Z.mod_pos_bound (Z.pos x) (p - 1) ltac:(lia)).
      lia.
    + rewrite Z2Pos.inj_mul; cycle 1.
      * lia.
      * apply Z.quot_str_pos; lia.
      * rewrite mod_pow_pos_exp_plus by lia.
        rewrite mod_pow_pos_exp_mul by lia.
        rewrite mod_pow_pos_fermat by auto.
        rewrite mod_pow_pos_1_l.
        rewrite Z.mod_1_l by lia.
        rewrite Z.mul_1_l.
        rewrite Z.rem_mod_nonneg by lia.
        now rewrite mod_pow_pos_mod.
  Qed.
*)

  Lemma mod_pow_exp a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x mod (p - 1)) p = mod_pow a x p.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    pose proof (Z.mod_pos_bound x (p - 1) ltac:(lia)).
    unfold mod_pow.
    destruct (x <? 0) eqn:lt.
    - apply Z.ltb_lt in lt.
      destruct x; try lia.
      cbn.
      pose proof (Z.mod_pos_bound (Z.neg p0) (p - 1) ltac:(lia)).
      destruct (Z.neg p0 mod (p - 1)) eqn:?; try lia.
      + pose proof (Z.neg p0
    rewrite (Z.div_mod x (p - 1)) at 2 by lia.
    rewrite !mod_pow_spec.
    rewrite mod_pow_plus.
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite Z.mul_comm, Z.mod_mul by lia.
    cbn.
    destruct (x <? 0) eqn:lt.
    - apply Z.ltb_lt in lt.
      Search (Z.rem).
Z.rem_bound_pos: forall a b : Z, 0 <= a -> 0 < b -> 0 <= Z.rem a b < b
      rewrite Z.rem_
    cbn.
    rewrite Z.mod_small; cycle 1.
    { Search (Z.rem _ _).
      apply Z.rem_bound_pos.
    rewrite mod_pow_spec by lia.
    rewrite
    rewrite Z.div_mod.
    Search (_ ^ (_ + _)).
    rewrite Z.pow_add_r.
    unfold mod_pow.
    destruct p; auto.
    - pose proof (Z.mod_pos_bound x (Z.pos p - 1) ltac:(lia)).
      destruct (x mod (Z.pos p - 1)) eqn:?; try lia.
      + destruct x; try lia.
        * rewrite <- mod_pow_pos_idemp by lia.
          assert (Z.pos p0
          replace (p0 with
          assert (p0
          replace p0
      destruct (x mod (Z.pos p - 1)


    all: pose proof (Z.mod_pos_bound x (Z.pos p - 1)).

    all:
    rewrite mod_pow_pos_spec.

  Lemma mod_pow_fermat_pos a p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (p - 1) p = 1.
  Proof.
    intros isprime ap.
    unfold mod_pow.
    pose proof (prime_ge_2 _ isprime).
    pose proof (mod_pow_pos_fermat _ _ isprime ap).
    destruct p; try lia.
    destruct (Z.pos p - 1) eqn:?; try lia.
    assumption.
  Qed.

  Lemma

  (*
  Lemma for_nonneg_exponent (P : Z -> Z -> Z -> Prop) p :
    p >= 2 ->
    (forall a, P a Z0 (mod_pow a Z0 p)) ->
    (forall a x, P a (Z.pos x) (mod_pow a (Z.pos x) p)) ->
    forall a x, P a x (mod_pow a x p).
  Proof.
    intros zero_case pos_case a x.
    unfold mod_pow in *.
    rewrite Z.quot_rem'
    destruct (Z.eq_dec p 0) as [->|ne].
    -
    destruct x; auto.
  Qed.
*)



Z.rem_mod: forall a b : Z, b <> 0 -> Z.rem a b = Z.sgn a * (Z.abs a mod Z.abs b)

Section BigZp.
  Section
  Local Open Scope bigZ.
  Fixpoint mod_pow_aux (a : bigZ) (x : positive) (m : bigZ) (r : bigZ) : bigZ :=
    match x with
    | x~0%positive => mod_pow_aux (BigZ.square a mod m) x m r
    | x~1%positive => mod_pow_aux (BigZ.square a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow (a x p : bigZ) : bigZ :=
    if p =? 0 then
      0
    else if x =? 0 then
      a^0 mod p
    else if 0 <? x then
      mod_pow_aux a (Z.to_pos (BigZ.to_Z x)) p 1
    else
      mod_pow_aux
        (mod_pow_aux a (Z.to_pos (BigZ.to_Z (-x))) p 1)
        (Z.to_pos (BigZ.to_Z (p - 2)))
        p 1.


  Local Open Scope Z.

  Hint Rewrite BigZ.square_spec BigZ.spec_pow_pos : zsimpl.
  Hint Rewrite BigN.spec_of_pos : nsimpl.

  Instance BigZ_square_wd :
    Proper (BigZ.eq ==> BigZ.eq) BigZ.square.
  Proof.
    intros a b eq.
    autorewrite with zsimpl in *.
    now rewrite eq.
  Qed.

  Instance mod_pow_aux_wd :
    Proper (BigZ.eq ==> eq ==> BigZ.eq ==> BigZ.eq ==> BigZ.eq) mod_pow_aux.
  Proof.
    (*intros a1 a2 elmeq ? x -> m1 m2 meq r1 r2 elmeq.*)
    intros a1 a2 elmeq ? x ->.
    revert a1 a2 elmeq.
    induction x; intros a1 a2 aeq m1 m2 meq r1 r2 req.
    - cbn.
      apply IHx.
      + rewrite aeq, meq.
        reflexivity.
      + auto.
      + rewrite aeq, meq, req.
        reflexivity.
    - cbn.
      apply IHx.
      + rewrite aeq, meq.
        reflexivity.
      + auto.
      + rewrite req.
        reflexivity.
    - cbn.
      rewrite aeq, meq, req.
      reflexivity.
  Qed.

  Lemma spec_mod_pow_aux a x p r :
    [mod_pow_aux a x p r] = mod_pow_aux_Z [a] x [p] [r].
  Proof.
    revert a p r.
    induction x; intros a p r; cbn in *.
    - rewrite IHx.
      now autorewrite with zsimpl.
    - rewrite IHx.
      now autorewrite with zsimpl.
    - now autorewrite with zsimpl.
  Qed.

  Hint Rewrite spec_mod_pow_aux : zsimpl.

  Lemma spec_mod_pow a x p :
    [mod_pow a x p] = mod_pow_Z [a] [x] [p].
  Proof.
    unfold mod_pow, mod_pow_Z.
    autorewrite with zsimpl.
    destruct (Z.eqb_spec [p] 0) as [->|ne]; auto; cbn.
    rewrite (proj2 (Z.eqb_neq _ _) ne).
    destruct (Z.compare_spec [x] [0]) as [->|?|?]; cbn in *.
    - autorewrite with zsimpl.
      destruct [p] eqn:eq; auto; congruence.
    - rewrite (proj2 (Z.eqb_neq [x] 0) ltac:(lia)).
      rewrite (proj2 (Z.ltb_ge 0 [x]) ltac:(lia)).
      autorewrite with zsimpl.
      destruct [x] eqn:?; try lia.
      cbn.
      destruct [p]; auto; congruence.
    - rewrite (proj2 (Z.eqb_neq [x] 0) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt 0 [x]) ltac:(lia)).
      autorewrite with zsimpl.
      destruct [x] eqn:?; try lia.
      cbn.
      destruct [p]; auto; congruence.
  Qed.

  Hint Rewrite spec_mod_pow : zsimpl.

  Local Open Scope bigZ.
  Lemma mod_pow_spec a x p :
    x >= 0 ->
    mod_pow a x p == a^x mod p.
  Proof.
    intros xp.
    unfold "==", "<=" in *; cbn in *.
    autorewrite with zsimpl in *.
    apply mod_pow_Z_spec.
    lia.
  Qed.

  Local Open Scope Z.
  Local Open Scope bigZ.
  Lemma mod_pow_mod_idemp a x p :
    mod_pow (a mod p) x p == mod_pow a x p.
  Proof.
    unfold "==".
    autorewrite with zsimpl.
    now rewrite mod_pow_Z_mod_idemp.
  Qed.

  Lemma mod_inv_spec x m :
    prime m ->
    x mod m <> 0 ->
    (x * mod_inv x m) mod m = 1.
  Proof.
    intros is_prime xnm.
    pose proof (prime_ge_2 _ is_prime).
    unfold mod_inv.
    rewrite (mod_pow_spec x (m - 2) m).
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite <- Z.pow_succ_r by lia.
    replace (Z.succ (m - 2)) with (m - 1) by lia.
    (* Use proof of Euler's theorem from Coqprime *)
    rewrite <- (Euler.prime_phi_n_minus_1 _ is_prime).
    apply phi_power_is_1; try lia.
    apply rel_prime_sym.
    apply prime_rel_prime; auto.
    intros div.
    pose proof (Zdivide_mod _ _ div).
    tauto.
  Qed.

  Lemma mod_inv_mod_idemp (x m : Z) :
    mod_inv (x mod m) m = mod_inv x m.
  Proof.
    unfold mod_inv.
    rewrite 2!mod_pow_spec.
    now rewrite Z_pow_mod_idemp.
  Qed.

  Lemma mod_inv_mul a b m :
    mod_inv (a * b) m =
    (mod_inv a m * mod_inv b m) mod m.
  Proof.
    unfold mod_inv.
    now rewrite !mod_pow_spec, Z.pow_mul_l, Zmult_mod.
  Qed.

  Lemma mod_pow_exp_fermat a e p :
    prime p ->
    mod_pow a (e mod p - 1) p = mod_pow a e p.
  Proof.
    Search (_ * _ + _).

  Local Open Scope Z.
  Definition Zp_ffield (p : Z) :
    prime p -> FField Z.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    refine
      {| elmeq a b := a mod p = b mod p;
         zero := 0;
         one := 1;
         add a a' := (a + a') mod p;
         mul a a' := (a * a') mod p;
         opp a := p - a;
         inv a := mod_inv a p;
         pow a e := mod_pow a e p;
         order := p;
      |}.
    - intros x y.
      apply Z.eq_dec.
    - lia.
    - constructor; auto.
      now intros a a' a'' -> ->.
    - intros a a' aeq b b' beq.
      now rewrite Z.add_mod, aeq, beq, <- Z.add_mod by lia.
    - intros a a' aeq b b' beq.
      now rewrite Z.mul_mod, aeq, beq, <- Z.mul_mod by lia.
    - intros a a' aeq.
      now rewrite Zminus_mod, aeq, <- Zminus_mod.
    - intros a a' aeq.
      now rewrite <- mod_inv_mod_idemp, aeq, mod_inv_mod_idemp.
    - intros a a' aeq e e' ->.
      now rewrite <- !(mod_pow_mod_idemp a), aeq, !mod_pow_mod_idemp.
    - intros a anp e e' eeq.
      cbn in anp.

      rewrite (proj2 (Z.eqb_neq _ _) anp).
      now rewrite eeq.
    - now rewrite Z.mod_1_l, Z.mod_0_l by lia.
    - intros a b.
      now replace (a + b) with (b + a) by lia.
    - intros a b c.
      rewrite !Z.mod_mod by lia.
      rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
      apply f_equal2; lia.
    - intros a b.
      now replace (a * b) with (b * a) by lia.
    - intros a b c.
      repeat (try rewrite Z.mul_mod_idemp_l; try rewrite Z.mul_mod_idemp_r); try lia.
      now replace (a * (b * c)) with (a * b * c) by lia.
    - intros a.
      now rewrite Z.mod_mod by lia.
    - intros a.
      now rewrite Z.mod_mod by lia.
    - intros a.
      rewrite Z.mod_mod by lia.
      now replace (1 * a) with a by lia.
    - intros a.
      rewrite Z.mod_mod by lia.
      replace (p - a + a) with p by lia.
      rewrite Z.mod_same, Z.mod_0_l; lia.
    - intros a anp.
      rewrite Z.mod_0_l, Z.mod_1_l in * by lia.
      pose proof (mod_inv_spec _ _ isprime anp).
      rewrite Z.mod_mod by lia.
      now rewrite Z.mul_comm.
    - intros a b anp bnp.
      now rewrite mod_inv_mod_idemp, mod_inv_mul.
    - intros a b c.
      repeat (try rewrite Z.mul_mod_idemp_l;
              try rewrite Z.mul_mod_idemp_r;
              try rewrite Z.add_mod_idemp_l;
              try rewrite Z.add_mod_idemp_r;
              try rewrite Z.mod_mod); try lia.
      apply f_equal2; lia.
    - intros a anp.
      cbn.
      rewrite mod_pow_spec.
      rewrite Z.pow_0_r.
      now destruct (a mod p =? 0);
        rewrite Z.mod_mod by lia.
    - intros a.
      rewrite !mod_pow_spec.
      destruct (Z.eq_dec p 2) as [->|?].
      + destruct (Z.eq_dec (a mod 2) 0) as [eq|neq].
        * rewrite eq.
          cbn.
          now rewrite Z.mul_1_r, eq.
        * rewrite (proj2 (Z.eqb_neq _ _) neq).
          cbn.
          pose proof (Z.mod_pos_bound a 2 ltac:(lia)).
          lia.
      + rewrite Z.mod_1_l by lia.
        rewrite Z.pow_1_r.
        destruct (a mod p =? 0); apply Z.mod_mod; lia.
    - intros a ap0.
      cbn in ap0.
      rewrite (proj2 (Z.eqb_neq _ _) ap0).
      unfold mod_inv.
      destruct (Z.eq_dec p 2) as [->|?]; auto.
      rewrite (Z_mod_nz_opp_full 1) by (rewrite Z.mod_1_l by lia; lia).
      rewrite Z.mod_1_l by lia.
      now replace (p - 1 - 1) with (p - 2) by lia.
    - intros a e e' ap0.
      cbn in ap0.
      rewrite (proj2 (Z.eqb_neq _ _) ap0).
      rewrite Z.add_mod by lia.
      rewrite !mod_pow_spec.
      rewrite !Z.mod_mod by lia.
      destruct (Z.eq_dec (a mod p) 0) as [eq|ne].
      + rewrite eq.
        cbn.
        rewrite !mod_pow_spec.
        Search (_ ^ (_ + _)).
        rewrite Z.pow_add_r.
        rewrite
    - intros a e anp.
      rewrite mod_pow_spec.
      cbn.
      assert (apprime : forall a, a mod p <> 0 -> rel_prime a p).
      {
        clear -isprime.
        intros a amodp.
        apply rel_prime_sym.
        apply prime_rel_prime; auto.
        intros div. apply Zdivide_mod in div.
        congruence.
      }

      assert (1 < p) as ltp by lia.
      assert (gpow_mod :
                forall a e,
                  a mod p <> 0 ->
                  0 <= e ->
                  a ^ e mod p = gpow (a mod p) (ZPGroup p ltp) e).
      {
        clear -isprime apprime.
        intros a e ap0 ege.
        apply Zpower_mod_is_gpow; auto.
      }

      assert (0 <= e mod (p - 1))
        by (pose proof (Z.mod_pos_bound e (p - 1) ltac:(lia)); lia).
      rewrite gpow_mod; auto.
      assert (in_zpstar: forall a, a mod p <> 0 <-> List.In (a mod p)
                                                            (FGroup.s (ZPGroup p ltp))).
      {
        clear -isprime apprime.
        intros a.
        split.
        - intros ap0.
          apply in_mod_ZPGroup.
          auto.
        - intros isin.
          cbn in *.
          pose proof (IGroup.isupport_is_inv_true _ _ _ _ _ _ isin).
          rewrite rel_prime_is_inv in H by lia.
          destruct (rel_prime_dec (a mod p) p); try congruence.
          apply Zrel_prime_neq_mod_0; [lia|].
          apply rel_prime_mod_rev; auto; lia.
      }

      apply in_zpstar.
      rewrite <- gpow_mod; auto.
      rewrite Z.mod_mod by lia.
      rewrite gpow_mod; auto.
      apply gpow_in.
      now apply in_zpstar.
  Defined.

End Zp.

Section WithZp.
End WithZp.
