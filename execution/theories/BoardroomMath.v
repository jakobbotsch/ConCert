From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import PArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From Coq Require Import SetoidTactics.
From Coq Require Import Field.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coqprime Require Import Zp FGroup EGroup Cyclic.
From Bignums Require Import BigZ.
From Equations Require Import Equations.

Require Import Extras.
Import ListNotations.

Local Open Scope Z.

Class BoardroomAxioms {A : Type} :=
  {
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

Arguments BoardroomAxioms : clear implicits.

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
Global Instance oeq_equivalence {A : Type} (field : BoardroomAxioms A) : Equivalence expeq.
Proof.
  unfold expeq.
  constructor.
  - constructor.
  - repeat intro; auto.
  - now intros ? ? ? -> ->.
Qed.

Definition BoardroomAxioms_field_theory {A : Type} (field : BoardroomAxioms A) :
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

Class Generator {A : Type} (field : BoardroomAxioms A) :=
  build_generator {
    generator : A;
    generator_nonzero : generator !== 0;
    generator_generates a : a !== 0 -> exists! e, 0 <= e < order - 1 /\ generator^e == a;
  }.

Class DiscreteLog {A : Type} (field : BoardroomAxioms A) (g : Generator field) :=
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

Section WithBoardroomAxioms.
  Context {A : Type}.
  Context {field : BoardroomAxioms A}.
  Context {gen : Generator field}.
  Context {disc_log : DiscreteLog field gen}.

  Add Field ff : (BoardroomAxioms_field_theory field).

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
      + apply (BoardroomAxioms_field_theory field).
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
           (n : nat)
           (votes_product : A) : option nat :=
    if elmeq_dec (generator ^ (Z.of_nat n)) votes_product then
      Some n
    else
      match n with
      | 0 => None
      | S n => bruteforce_tally_aux n votes_product
      end%nat.

  Definition bruteforce_tally (votes : list A) : option nat :=
    bruteforce_tally_aux (length votes) (prod votes).

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

  Global Instance prod_perm_proper :
    Proper (@Permutation A ==> elmeq) prod.
  Proof.
    intros l l' permeq.
    induction permeq.
    - reflexivity.
    - cbn.
      now rewrite IHpermeq.
    - cbn.
      rewrite !mul_assoc.
      now rewrite (mul_comm y).
    - now rewrite IHpermeq1, IHpermeq2.
  Qed.

  Global Instance bruteforce_tally_aux_proper :
    Proper (eq ==> elmeq ==> eq) bruteforce_tally_aux.
  Proof.
    intros n ? <- p p' prodeq.
    induction n as [|n IH].
    - cbn.
      destruct (elmeq_dec _ _), (elmeq_dec _ _); auto.
      + rewrite prodeq in e; contradiction.
      + rewrite <- prodeq in e; contradiction.
    - cbn.
      destruct (elmeq_dec _ _), (elmeq_dec _ _); auto.
      + rewrite prodeq in e; contradiction.
      + rewrite <- prodeq in e; contradiction.
  Qed.

  Global Instance bruteforce_tally_proper :
    Proper (@Permutation A ==> eq) bruteforce_tally.
  Proof.
    unfold bruteforce_tally.
    now intros ? ? <-.
  Qed.

  Lemma bruteforce_tally_aux_correct result max :
    Z.of_nat max < order - 1 ->
    (result <= max)%nat ->
    bruteforce_tally_aux max (generator ^ Z.of_nat result) = Some result.
  Proof.
    intros max_lt result_le.
    induction max as [|max IH].
    - replace result with 0%nat by lia.
      cbn.
      destruct (elmeq_dec _ _); auto.
      contradiction n; reflexivity.
    - destruct (Nat.eq_dec result (S max)) as [->|?].
      + cbn.
        destruct (elmeq_dec _ _); auto.
        contradiction n; reflexivity.
      + cbn -[Z.of_nat].
        destruct (elmeq_dec _ _) as [eq|?]; auto.
        * pose proof (generator_generates (generator ^ Z.of_nat result) ltac:(auto)).
          destruct H as [e [sat unique]].
          unshelve epose proof (unique (Z.of_nat (S max)) _) as smax.
          { split; auto; lia. }
          unshelve epose proof (unique (Z.of_nat result) _) as res.
          { split; [lia|reflexivity]. }
          rewrite <- (Z2Nat.id e) in smax, res by lia.
          apply Nat2Z.inj in smax.
          apply Nat2Z.inj in res.
          congruence.
        * apply IH; lia.
  Qed.

  Lemma sumZ_sumnat_votes (svs : nat -> bool) l :
    sumZ (fun i => if svs i then 1%Z else 0%Z) l =
    Z.of_nat (sumnat (fun i => if svs i then 1%nat else 0%nat) l).
  Proof.
    induction l as [|x xs IH]; auto.
    cbn.
    rewrite IH, Nat2Z.inj_add.
    destruct (svs x); lia.
  Qed.

  Lemma bruteforce_tally_correct sks pks svs pvs pvs_passed count :
    Z.of_nat count < order - 1 ->
    pks = map (fun i => compute_public_key (sks i)) (seq 0 count) ->
    pvs = map (fun i => compute_public_vote (reconstructed_key pks i)
                                            (sks i)
                                            (svs i))
              (seq 0 count) ->
    Permutation pvs pvs_passed ->
    bruteforce_tally pvs_passed =
    Some (sumnat (fun i => if svs i then 1 else 0)%nat (seq 0 count)).
  Proof.
    unfold bruteforce_tally.
    intros countlt -> -> <-.
    pose proof order_ge_2.
    rewrite map_length, seq_length.
    set (sks_list := map sks (seq 0 count)).
    replace (map (fun i => compute_public_key (sks i)) (seq 0 count))
      with (map compute_public_key sks_list); cycle 1.
    {
      subst sks_list.
      now rewrite map_map.
    }
    replace (map (fun i => compute_public_vote
                             (reconstructed_key (map compute_public_key sks_list) i)
                             (sks i)
                             (svs i))
                 (seq 0 count))
      with (map (fun i => compute_public_vote
                             (reconstructed_key (map compute_public_key sks_list) i)
                             (nth i sks_list 0%Z)
                             (svs i))
                (seq 0 (length sks_list))); cycle 1.
    {
      subst sks_list.
      rewrite map_length, seq_length.
      apply map_ext_in.
      intros a ain.
      apply in_seq in ain.
      rewrite (map_nth_alt a (seq 0 count) sks 0%Z 0%nat) by (rewrite seq_length; lia).
      now rewrite seq_nth by lia.
    }

    rewrite mul_public_votes.
    subst sks_list.
    unshelve epose proof
             (sumnat_min_max (fun i => if svs i then 1 else 0) (seq 0 count) 0 1 _)%nat.
    { intros; cbn; destruct (svs a); lia. }
    rewrite map_length, seq_length in *.
    rewrite Nat.mul_0_l, Nat.mul_1_l in *.
    rewrite sumZ_sumnat_votes.
    now rewrite bruteforce_tally_aux_correct by lia.
  Qed.

End WithBoardroomAxioms.

Module Zp.
  Local Open Scope Z.

  Fixpoint mod_pow_pos_aux (a : Z) (x : positive) (m : Z) (r : Z) : Z :=
    match x with
    | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : Z) (x : positive) (m : Z) : Z :=
    mod_pow_pos_aux a x m 1.

  Definition mod_inv (a : Z) (p : Z) : Z :=
    mod_pow_pos a (Z.to_pos (p - 2)) p.

  Definition mod_pow (a x p : Z) : Z :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_inv (mod_pow_pos a x p) p
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
  Lemma mod_inv_0_r a :
    mod_inv a 0 = 0.
  Proof. apply mod_pow_pos_0_r. Qed.
  Lemma mod_pow_0_r a x :
    mod_pow a x 0 = 0.
  Proof.
    destruct x; auto; cbn.
    - apply mod_pow_pos_0_r.
    - now rewrite mod_pow_pos_0_r.
  Qed.

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

  Lemma mod_pow_pos_aux_mod_idemp a x p r :
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

  Lemma mod_pow_pos_mod_idemp a x p :
    mod_pow_pos (a mod p) x p = mod_pow_pos a x p.
  Proof. apply mod_pow_pos_aux_mod_idemp. Qed.

  Lemma mod_inv_mod_idemp a p :
    mod_inv (a mod p) p = mod_inv a p.
  Proof. apply mod_pow_pos_mod_idemp. Qed.

  Lemma mod_pow_mod_idemp a x p :
    mod_pow (a mod p) x p = mod_pow a x p.
  Proof.
    unfold mod_pow.
    destruct p; auto.
    all: destruct x; auto.
    all: now rewrite mod_pow_pos_mod_idemp by lia.
  Qed.

  Lemma mod_pow_pos_aux_mod a x p r :
    mod_pow_pos_aux a x p r mod p = mod_pow_pos_aux a x p r.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - now rewrite mod_pow_pos_aux_0_r.
    - rewrite mod_pow_pos_aux_spec.
      now rewrite Z.mod_mod by auto.
  Qed.
  Lemma mod_pow_pos_mod a x p :
    mod_pow_pos a x p mod p = mod_pow_pos a x p.
  Proof. apply mod_pow_pos_aux_mod. Qed.
  Lemma mod_inv_mod a p :
    mod_inv a p mod p = mod_inv a p.
  Proof. apply mod_pow_pos_mod. Qed.

  Lemma mod_pow_mod a x p :
    mod_pow a x p mod p = mod_pow a x p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - now rewrite mod_pow_0_r.
    - destruct x; cbn.
      + now rewrite Z.mod_mod by auto.
      + now rewrite mod_pow_pos_mod.
      + now rewrite mod_inv_mod.
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

  Lemma mod_pow_fermat a p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (p - 1) p = 1.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    pose proof (mod_pow_pos_fermat _ _ isprime ap).
    destruct p; try lia.
    destruct (Z.pos p - 1) eqn:?; try lia.
    assumption.
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

  Lemma mod_pow_pos_aux_1_l x p r :
    mod_pow_pos_aux 1 x p r = r mod p.
  Proof.
    destruct (Z.eq_dec p 0) as [->|?].
    - now rewrite mod_pow_pos_aux_0_r, Zmod_0_r.
    - revert r.
      induction x; intros r; cbn.
      + rewrite mod_pow_pos_aux_mod_idemp.
        rewrite Z.mul_1_r.
        rewrite IHx.
        apply Z.mod_mod; auto.
      + rewrite mod_pow_pos_aux_mod_idemp.
        apply IHx.
      + now rewrite Z.mul_1_r.
  Qed.
  Lemma mod_pow_pos_1_l x p :
    mod_pow_pos 1 x p = 1 mod p.
  Proof. apply mod_pow_pos_aux_1_l. Qed.
  Lemma mod_inv_1_l p :
    mod_inv 1 p = 1 mod p.
  Proof. apply mod_pow_pos_1_l. Qed.
  Lemma mod_pow_1_l x p :
    mod_pow 1 x p = 1 mod p.
  Proof.
    destruct x; auto; cbn.
    - apply mod_pow_pos_1_l.
    - rewrite mod_pow_pos_1_l, mod_inv_mod_idemp.
      apply mod_inv_1_l.
  Qed.

  Lemma mod_pow_pos_aux_1_r a p r :
    mod_pow_pos_aux a 1 p r = a * r mod p.
  Proof.
    cbn.
    now rewrite Z.mul_comm.
  Qed.
  Lemma mod_pow_pos_1_r a p :
    mod_pow_pos a 1 p = a mod p.
  Proof.
    cbn -[Z.mul].
    now rewrite Z.mul_1_l.
  Qed.
  Lemma mod_pow_1_r a p :
    mod_pow a 1 p = a mod p.
  Proof.
    cbn -[Z.mul].
    now rewrite Z.mul_1_l.
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

  Lemma mul_mod_inv a p :
    prime p ->
    a mod p <> 0 ->
    a * mod_inv a p mod p = 1.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    unfold mod_inv.
    rewrite mod_pow_pos_succ_r.
    destruct (Z.eq_dec p 2) as [->|?].
    - cbn.
      pose proof (Z.mod_pos_bound a 2 ltac:(lia)).
      rewrite Z.mul_mod by discriminate.
      now replace (a mod 2) with 1 in * by lia.
    - rewrite <- Z2Pos.inj_succ by lia.
      replace (Z.succ (p - 2)) with (p - 1) by lia.
      apply mod_pow_pos_fermat; auto.
  Qed.

  Lemma mul_mod_nonzero a b p :
    prime p ->
    a mod p <> 0 ->
    b mod p <> 0 ->
    a * b mod p <> 0.
  Proof.
    intros isprime ap0 bp0.
    intros abp0.
    pose proof (prime_ge_2 _ isprime).
    pose proof (proj1 (Z.mod_divide _ p ltac:(lia)) abp0) as pdiv.
    pose proof (prime_mult _ isprime _ _ pdiv) as onediv.
    destruct onediv as [div|div]; apply Z.mod_divide in div; lia.
  Qed.
  Hint Resolve mul_mod_nonzero : core.

  Lemma mod_mod_nonzero a p :
    a mod p <> 0 ->
    (a mod p) mod p <> 0.
  Proof.
    intros ap0.
    destruct (Z.eq_dec p 0) as [->|?].
    - cbn in ap0.
      rewrite Zmod_0_r in ap0.
      congruence.
    - rewrite Z.mod_mod by auto.
      auto.
  Qed.
  Hint Resolve mod_mod_nonzero.

  Lemma mod_pow_pos_aux_nonzero a x p r :
    prime p ->
    a mod p <> 0 ->
    r mod p <> 0 ->
    mod_pow_pos_aux a x p r <> 0.
  Proof.
    intros prime.
    pose proof (prime_ge_2 _ prime).
    revert a r.
    induction x; intros a r ap0 rp0; cbn; auto.
  Qed.
  Hint Resolve mod_pow_pos_aux_nonzero : core.

  Lemma mod_pow_pos_nonzero a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow_pos a x p <> 0.
  Proof.
    intros isprime ap0.
    apply mod_pow_pos_aux_nonzero; auto.
    pose proof (prime_ge_2 _ isprime).
    now rewrite Z.mod_1_l by lia.
  Qed.
  Hint Resolve mod_pow_pos_nonzero : core.
  Lemma mod_inv_nonzero a p :
    prime p ->
    a mod p <> 0 ->
    mod_inv a p <> 0.
  Proof.
    intros isprime ap0.
    apply mod_pow_pos_nonzero; auto.
  Qed.
  Hint Resolve mod_inv_nonzero : core.
  Lemma mod_pow_nonzero a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a x p <> 0.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x; cbn; auto.
    - rewrite Z.mod_1_l by lia; discriminate.
    - apply mod_inv_nonzero; auto.
      rewrite mod_pow_pos_mod; auto.
  Qed.
  Hint Resolve mod_pow_nonzero : core.
  Lemma mod_pow_pos_mod_nonzero a x p :
    mod_pow_pos a x p <> 0 ->
    mod_pow_pos a x p mod p <> 0.
  Proof. rewrite mod_pow_pos_mod; auto. Qed.
  Lemma mod_inv_mod_nonzero a p :
    mod_inv a p <> 0 ->
    mod_inv a p mod p <> 0.
  Proof. rewrite mod_inv_mod; auto. Qed.
  Lemma mod_pow_mod_nonzero a x p :
    mod_pow a x p <> 0 ->
    mod_pow a x p mod p <> 0.
  Proof. rewrite mod_pow_mod; auto. Qed.
  Hint Resolve mod_pow_pos_mod_nonzero mod_inv_mod_nonzero mod_pow_mod_nonzero : core.

  Lemma mod_mul_both_l a b c p :
    prime p ->
    c mod p <> 0 ->
    c * a mod p = c * b mod p ->
    a mod p = b mod p.
  Proof.
    intros isprime cp0 eq.
    pose proof (prime_ge_2 _ isprime).
    rewrite <- (Z.mul_1_l a).
    rewrite <- (Z.mul_1_l b).
    rewrite <- (mul_mod_inv c _ isprime cp0).
    rewrite !Z.mul_mod_idemp_l by lia.
    rewrite (Z.mul_comm c).
    rewrite <- 2!Z.mul_assoc.
    rewrite <- (Z.mul_mod_idemp_r _ (c * a)) by lia.
    rewrite <- (Z.mul_mod_idemp_r _ (c * b)) by lia.
    now rewrite eq.
  Qed.

  Lemma mod_inv_mul a b p :
    prime p ->
    a mod p <> 0 ->
    b mod p <> 0 ->
    mod_inv (a * b) p = mod_inv b p * mod_inv a p mod p.
  Proof.
    intros isprime ap0 bp0.
    pose proof (prime_ge_2 _ isprime).
    unfold mod_inv.
    rewrite !mod_pow_pos_spec, !Z.pow_pos_fold.
    rewrite Z.pow_mul_l.
    rewrite Z.mul_mod by lia.
    rewrite <- !Z.pow_pos_fold, <- !mod_pow_pos_spec.
    now rewrite Z.mul_comm.
  Qed.

  Lemma mod_pow_succ a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (Z.succ x) p = a * mod_pow a x p mod p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x.
    - cbn.
      rewrite Z.mod_1_l by lia.
      rewrite Z.mul_1_r.
      destruct a; auto.
    - cbn -[Pos.add].
      rewrite mod_pow_pos_succ_r.
      now replace (p0 + 1)%positive with (Pos.succ p0) by lia.
    - cbn.
      destruct (Pos.eq_dec p0 1) as [->|?].
      + cbn -[Z.mul].
        rewrite Z.mul_1_l.
        rewrite mod_inv_mod_idemp.
        rewrite mul_mod_inv by auto.
        now rewrite Z.mod_1_l by lia.
      + rewrite Z.pos_sub_lt by lia.
        cbn.
        rewrite <- mod_inv_mod.
        apply mod_mul_both_l with (mod_inv a p); auto.
        rewrite Z.mul_assoc.
        rewrite <- (Z.mul_mod_idemp_l (mod_inv a p * a)) by lia.
        rewrite (Z.mul_comm _ a).
        rewrite mul_mod_inv by auto.
        rewrite <- mod_inv_mul by auto.
        rewrite Z.mul_comm.
        rewrite <- mod_inv_mod_idemp.
        rewrite mod_pow_pos_succ_r.
        replace (Pos.succ (p0 - 1)) with p0 by lia.
        now rewrite Z.mul_1_l, mod_inv_mod.
  Qed.

  Lemma mod_pow_pred a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (Z.pred x) p = mod_inv a p * mod_pow a x p mod p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    rewrite <- mod_pow_mod.
    apply mod_mul_both_l with a; auto.
    rewrite <- mod_pow_succ by auto.
    replace (Z.succ (Z.pred x)) with x by lia.
    rewrite Z.mul_assoc.
    rewrite <- Z.mul_mod_idemp_l by lia.
    rewrite mul_mod_inv by auto.
    now rewrite Z.mul_1_l, mod_pow_mod.
  Qed.

  Lemma mod_pow_exp_plus a x x' p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x + x') p = mod_pow a x p * mod_pow a x' p mod p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    revert x'.
    induction x using Z.peano_ind; intros x'.
    - cbn.
      rewrite Z.mod_1_l by lia.
      rewrite Z.mul_1_l.
      now rewrite mod_pow_mod by lia.
    - replace (Z.succ x + x') with (Z.succ (x + x')) by lia.
      rewrite mod_pow_succ by auto.
      rewrite IHx.
      rewrite Z.mul_mod_idemp_r by lia.
      rewrite Z.mul_assoc.
      rewrite <- Z.mul_mod_idemp_l by lia.
      now rewrite <- mod_pow_succ by auto.
    - replace (Z.pred x + x') with (x + Z.pred x') by lia.
      rewrite IHx.
      rewrite !mod_pow_pred by auto.
      rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia.
      apply f_equal2; lia.
  Qed.

  Lemma mod_inv_involutive a p :
    prime p ->
    a mod p <> 0 ->
    mod_inv (mod_inv a p) p = a mod p.
  Proof.
    intros isprime ap0.
    rewrite <- mod_inv_mod.
    apply mod_mul_both_l with (mod_inv a p); auto.
    rewrite mul_mod_inv by auto.
    now rewrite Z.mul_comm, mul_mod_inv by auto.
  Qed.

  Lemma mod_pow_exp_mul a x x' p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x * x') p = mod_pow (mod_pow a x p) x' p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x, x'; cbn;
      repeat (
          try rewrite Z.mod_1_l by lia;
          try rewrite mod_pow_pos_1_l;
          try rewrite mod_inv_1_l);
      auto.
    - apply mod_pow_pos_exp_mul.
    - now rewrite mod_pow_pos_exp_mul.
    - unfold mod_inv.
      rewrite <- !mod_pow_pos_exp_mul.
      rewrite <- Pos.mul_assoc.
      now rewrite (Pos.mul_comm p1).
    - unfold mod_inv.
      rewrite <- !mod_pow_pos_exp_mul.
      replace (p0 * (Z.to_pos (p - 2) * (p1 * Z.to_pos (p - 2))))%positive
        with (p0 * p1 * Z.to_pos (p - 2) * Z.to_pos (p - 2))%positive
        by lia.
      rewrite !mod_pow_pos_exp_mul.
      pose proof mod_inv_involutive.
      unfold mod_inv in H0.
      rewrite H0 by auto.
      now rewrite mod_pow_pos_mod.
  Qed.

  Lemma mod_pow_exp_opp a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (-x) p = mod_inv (mod_pow a x p) p.
  Proof.
    intros isprime ap0.
    pose proof (prime_ge_2 _ isprime).
    destruct x; auto.
    - cbn.
      rewrite mod_inv_mod_idemp.
      now rewrite mod_inv_1_l.
    - cbn.
      rewrite mod_inv_involutive by auto.
      now rewrite mod_pow_pos_mod.
  Qed.

  Lemma mod_pow_exp_mod a x p :
    prime p ->
    a mod p <> 0 ->
    mod_pow a (x mod (p - 1)) p = mod_pow a x p.
  Proof.
    intros isprime ap.
    pose proof (prime_ge_2 _ isprime).
    rewrite (Z.div_mod x (p - 1)) at 2 by lia.
    rewrite mod_pow_exp_plus by auto.
    rewrite mod_pow_exp_mul by auto.
    rewrite mod_pow_fermat by auto.
    rewrite mod_pow_1_l, !Z.mod_1_l by lia.
    now rewrite Z.mul_1_l, mod_pow_mod.
  Qed.

  Definition boardroom_axioms (p : Z) :
    prime p -> BoardroomAxioms Z.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    refine
      {|
        elmeq a b := a mod p = b mod p;
        zero := 0;
        one := 1;
        add a a' := (a + a') mod p;
        mul a a' := (a * a') mod p;
        opp a := p - a;
        inv a := mod_inv a p;
        pow a e := mod_pow a e p;
        order := p;
      |}.
    - intros x y; apply Z.eq_dec.
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
      rewrite <- (mod_pow_exp_mod _ e), <- (mod_pow_exp_mod _ e') by auto.
      now rewrite eeq.
    - now rewrite Z.mod_1_l, Z.mod_0_l by lia.
    - intros a b.
      now rewrite Z.add_comm.
    - intros a b c.
      rewrite !Z.mod_mod by lia.
      rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
      apply f_equal2; lia.
    - intros a b.
      now rewrite Z.mul_comm.
    - intros a b c.
      repeat (try rewrite Z.mul_mod_idemp_l; try rewrite Z.mul_mod_idemp_r); try lia.
      now rewrite Z.mul_assoc.
    - intros a.
      now rewrite Z.mod_mod by lia.
    - intros a.
      now rewrite Z.mod_mod by lia.
    - intros a.
      rewrite Z.mod_mod by lia.
      now rewrite Z.mul_1_l.
    - intros a.
      rewrite Z.mod_mod by lia.
      replace (p - a + a) with p by lia.
      rewrite Z.mod_same, Z.mod_0_l; lia.
    - intros a anp.
      now rewrite Z.mul_comm, mul_mod_inv by auto.
    - intros a b c.
      repeat (try rewrite Z.mul_mod_idemp_l;
              try rewrite Z.mul_mod_idemp_r;
              try rewrite Z.add_mod_idemp_l;
              try rewrite Z.add_mod_idemp_r;
              try rewrite Z.mod_mod); try lia.
      apply f_equal2; lia.
    - intros a anp.
      cbn.
      now rewrite Z.mod_1_l at 1 by lia.
    - intros a.
      now rewrite mod_pow_mod, mod_pow_1_r.
    - intros a ap0.
      rewrite (mod_pow_exp_opp _ 1) by auto.
      rewrite mod_pow_1_r.
      now rewrite mod_inv_mod_idemp.
    - intros a e e' ap0.
      now rewrite mod_pow_exp_plus by auto.
    - auto.
    - auto.
  Defined.
End Zp.

Module BigZp.
  Local Open Scope bigZ.
  Fixpoint mod_pow_pos_aux (a : bigZ) (x : positive) (m : bigZ) (r : bigZ) : bigZ :=
    match x with
    | x~0%positive => mod_pow_pos_aux (BigZ.square a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (BigZ.square a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : bigZ) (x : positive) (m : bigZ) : bigZ :=
    mod_pow_pos_aux a x m 1.

  Definition mod_inv (a : bigZ) (p : bigZ) : bigZ :=
    mod_pow_pos a (Z.to_pos (BigZ.to_Z (p - 2))) p.

  Definition mod_pow (a : bigZ) (x : Z) (p : bigZ) : bigZ :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_inv (mod_pow_pos a x p) p
    end.

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
    Proper (BigZ.eq ==> eq ==> BigZ.eq ==> BigZ.eq ==> BigZ.eq) mod_pow_pos_aux.
  Proof.
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

  Lemma spec_mod_pow_pos_aux a x p r :
    [mod_pow_pos_aux a x p r] = Zp.mod_pow_pos_aux [a] x [p] [r].
  Proof.
    revert a p r.
    induction x; intros a p r; cbn in *.
    - rewrite IHx.
      now autorewrite with zsimpl.
    - rewrite IHx.
      now autorewrite with zsimpl.
    - now autorewrite with zsimpl.
  Qed.
  Hint Rewrite spec_mod_pow_pos_aux : zsimpl.

  Lemma spec_mod_pow_pos a x p :
    [mod_pow_pos a x p] = Zp.mod_pow_pos [a] x [p].
  Proof. apply spec_mod_pow_pos_aux. Qed.
  Hint Rewrite spec_mod_pow_pos : zsimpl.

  Lemma spec_mod_inv a p :
    [mod_inv a p] = Zp.mod_inv [a] [p].
  Proof.
    unfold mod_inv, Zp.mod_inv.
    now autorewrite with zsimpl.
  Qed.
  Hint Rewrite spec_mod_inv : zsimpl.

  Lemma spec_mod_pow a x p :
    [mod_pow a x p] = Zp.mod_pow [a] x [p].
  Proof.
    unfold mod_pow, Zp.mod_pow.
    now destruct x; autorewrite with zsimpl.
  Qed.
  Hint Rewrite spec_mod_pow : zsimpl.

  Hint Rewrite BigZ.spec_modulo : zsimpl.

  Definition boardroom_axioms (p : bigZ) :
    prime [p] -> BoardroomAxioms bigZ.
  Proof.
    intros isprime.
    pose proof (prime_ge_2 _ isprime).
    refine
      {| elmeq a b := a mod p == b mod p;
         zero := 0;
         one := 1;
         add a a' := (a + a') mod p;
         mul a a' := (a * a') mod p;
         opp a := p - a;
         inv a := mod_inv a p;
         pow a e := mod_pow a e p;
         order := BigZ.to_Z p;
      |}; unfold "==".
    - intros x y.
      apply Z.eq_dec.
    - lia.
    - constructor; auto.
      now intros a a' a'' -> ->.
    - intros a a' aeq b b' beq.
      autorewrite with zsimpl in *.
      now rewrite Z.add_mod, aeq, beq, <- Z.add_mod by lia.
    - intros a a' aeq b b' beq.
      autorewrite with zsimpl in *.
      now rewrite Z.mul_mod, aeq, beq, <- Z.mul_mod by lia.
    - intros a a' aeq.
      autorewrite with zsimpl in *.
      now rewrite Zminus_mod, aeq, <- Zminus_mod.
    - intros a a' aeq.
      autorewrite with zsimpl in *.
      now rewrite <- Zp.mod_inv_mod_idemp, aeq, Zp.mod_inv_mod_idemp.
    - intros a a' aeq e e' ->.
      autorewrite with zsimpl in *.
      now rewrite <- !(Zp.mod_pow_mod_idemp [a]), aeq, !Zp.mod_pow_mod_idemp.
    - intros a anp e e' eeq.
      autorewrite with zsimpl in *.
      rewrite <- (Zp.mod_pow_exp_mod _ e), <- (Zp.mod_pow_exp_mod _ e') by auto.
      now rewrite eeq.
    - autorewrite with zsimpl in *.
      now rewrite Z.mod_1_l, Z.mod_0_l by lia.
    - intros a b.
      autorewrite with zsimpl in *.
      now rewrite Z.add_comm.
    - intros a b c.
      autorewrite with zsimpl in *.
      rewrite !Z.mod_mod by lia.
      rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
      apply f_equal2; lia.
    - intros a b.
      autorewrite with zsimpl in *.
      now rewrite Z.mul_comm.
    - intros a b c.
      autorewrite with zsimpl in *.
      repeat (try rewrite Z.mul_mod_idemp_l; try rewrite Z.mul_mod_idemp_r); try lia.
      now rewrite Z.mul_assoc.
    - intros a.
      autorewrite with zsimpl in *.
      now rewrite Z.mod_mod by lia.
    - intros a.
      autorewrite with zsimpl in *.
      now rewrite Z.mod_mod by lia.
    - intros a.
      autorewrite with zsimpl in *.
      rewrite Z.mod_mod by lia.
      now rewrite Z.mul_1_l.
    - intros a.
      autorewrite with zsimpl in *.
      rewrite Z.mod_mod by lia.
      replace ([p] - [a] + [a])%Z with [p] by lia.
      rewrite Z.mod_same, Z.mod_0_l; lia.
    - intros a anp.
      autorewrite with zsimpl in *.
      now rewrite Z.mul_comm, Zp.mul_mod_inv by auto.
    - intros a b c.
      autorewrite with zsimpl in *.
      repeat (try rewrite Z.mul_mod_idemp_l;
              try rewrite Z.mul_mod_idemp_r;
              try rewrite Z.add_mod_idemp_l;
              try rewrite Z.add_mod_idemp_r;
              try rewrite Z.mod_mod); try lia.
      apply f_equal2; lia.
    - intros a anp.
      autorewrite with zsimpl in *.
      cbn.
      now rewrite Z.mod_1_l at 1 by lia.
    - intros a.
      autorewrite with zsimpl in *.
      now rewrite Zp.mod_pow_mod, Zp.mod_pow_1_r.
    - intros a ap0.
      autorewrite with zsimpl in *.
      rewrite (Zp.mod_pow_exp_opp _ 1) by auto.
      rewrite Zp.mod_pow_1_r.
      now rewrite Zp.mod_inv_mod_idemp.
    - intros a e e' ap0.
      autorewrite with zsimpl in *.
      now rewrite Zp.mod_pow_exp_plus by auto.
    - intros a e ap0.
      autorewrite with zsimpl in *.
      auto.
    - intros a ap0.
      autorewrite with zsimpl in *.
      auto.
  Defined.
End BigZp.
