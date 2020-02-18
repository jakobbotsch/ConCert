From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import PArith.
From Coq Require Import Psatz.
From Coq Require Import SetoidTactics.
From Coq Require Import Field.
From Coq Require Import ZArith.

Require Import Extras.
Import ListNotations.

Local Open Scope Z.

Class FField {A : Type} :=
  build_ffield {
    elmeq : A -> A -> Prop;
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
    pow_proper :> Proper (elmeq ==> expeq ==> elmeq) pow;

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

    add_mul a b c : elmeq (mul (add a b) c) (add (mul a c) (mul b c));

    int_domain a b :
      ~(elmeq a zero) ->
      ~(elmeq b zero) ->
      ~(elmeq (mul a b) zero);

    pow_0_r a e :
      ~(elmeq a zero) ->
      ~(elmeq (pow a e) zero);
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
  - apply add_mul.
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
  build_discrete_log {
    (* This is computationally intractable, but we still elmequire it
    for ease of specification *)
    discrete_log : A -> Z;
    discrete_log_proper :> Proper (elmeq ==> expeq) discrete_log;
    inv_discrete_log a :
      a !== 0 ->
      generator ^ (discrete_log a) == a;
    discrete_log_mul a b :
      a !== 0 ->
      b !== 0 ->
      discrete_log (a * b) exp= discrete_log a + discrete_log b
  }.

Section WithFField.
  Context {A : Type}.
  Context {field : FField A}.
  Context {gen : Generator field}.
  Context {disc_log : DiscreteLog field gen}.

  Add Field ff : (FField_field_theory field).

  Local Open Scope ffield.

  Instance dr : DefaultRelation elmeq.

  Fixpoint ff_prod (l : list A) : A :=
    match l with
    | [] => one
    | x :: xs => x * ff_prod xs
    end.

  Lemma units_prod (xs : list A) :
    All (fun x => x !== 0) xs ->
    ff_prod xs !== 0.
  Proof.
    intros units.
    induction xs as [|x xs IH]; cbn in *.
    - apply one_neq_zero.
    - apply int_domain; intuition.
  Qed.
  Hint Resolve units_prod : core.

  Definition compute_public_key (sk : Z) : A :=
    generator ^ sk.

  Definition reconstructed_key (pks : list A) (n : nat) : A :=
    let lprod := ff_prod (firstn n pks) in
    let rprod := inv (ff_prod (skipn (S n) pks)) in
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
    let rprod := inv (ff_prod pks) in
    reconstructed_keys_aux pks one rprod.

  Definition elmseq (l l' : list A) : Prop :=
    Forall2 elmeq l l'.

  Instance units_prod_proper :
    Proper (elmseq ==> elmeq) ff_prod.
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
                (ff_prod pks1)
                (inv (ff_prod (pk :: pks2)))).
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
    pose proof (units_prod _ units).
    intuition.
  Qed.

  Lemma compute_public_key_unit sk :
    compute_public_key sk !== 0.
  Proof.
    cbn.
    apply pow_0_r.
    apply generator_nonzero.
  Qed.
  Hint Resolve compute_public_key_unit : core.

  Lemma compute_public_keys_units sks :
    All (fun x => x !== 0) (map compute_public_key sks).
  Proof.
    induction sks as [|sk sks IH]; cbn; auto.
  Qed.
  Hint Resolve compute_public_keys_units : core.

  Instance plus_expeq_proper : Proper (expeq ==> expeq ==> expeq) Z.add.
  Proof.
    intros x x' xeq y y' yeq.
    unfold "exp=" in *.
    assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
    now rewrite Z.add_mod, xeq, yeq, <- Z.add_mod.
  Qed.

  Lemma Z_eta z : match z with
                  | Z0 => Z0
                  | Zpos p => Zpos p
                  | Zneg p => Zneg p
                  end = z.
  Proof. now destruct z. Qed.

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

  Local Open Scope Z.
  Lemma sum_lemma l :
    sumZ (fun i => nth i l 0 *
                   (sumZ id (firstn i l) -
                    sumZ id (skipn (S i) l)))
         (seq 0 (length l)) = 0.
  Proof.
    assert (forall i < length l, nth i l 0 * (sumZ id (firstn i l) - sumZ
    replace (sumZ (fun i => nth i l 0 *
                            (sumZ id (firstn i l) -
                             sumZ id (skipn (S i) l)))
                  (seq 0 (length l)))
      with (sumZ (fun i => nth i l 0 *
                           (sumZ (fun j => if Nat.ltb j i
                                           then nth j l 0
                                           else if Nat.eqb j i then 0
                                                else - nth j l 0)
                                 (seq 0 (length l))))
                 (seq 0 (length l))); cycle 1.
    {
      induction l as [|z zs IH]; auto.
      cbn -[Nat.ltb Nat.eqb].
      rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      replace (0 <? 0)%nat with false; cycle 1.
      { Search (?a <? ?a)%nat.

    setoid_rewrite <- Z.add_opp_r.
    rewrite <- sumZ_app.


  Lemma mul_votes (sks : list Z) :
    ff_prod (map (fun '(sk, rk) => pow rk sk)
                 (zip sks (reconstructed_keys (map compute_public_key sks))))
    == 1.
  Proof.

  Lemma sum_pks (sks : list Z) :
    sumZ (fun '(sk, rk) => sk * discrete_log rk)%Z
         (zip sks (reconstructed_keys (map compute_public_key sks))) exp= 0%Z.
  Proof.
    induction sks as [|sk sks IH]; cbn in *.
    1: reflexivity.
    setoid_replace
      (1 * (inv (compute_public_key sk *
                 ff_prod (map compute_public_key sks)) *
            compute_public_key sk))
      with (inv (ff_prod (map compute_public_key sks)))
      by (field; auto).


    replace (1 * pk) with pk by field.
    replace (inv (pk * ff_prod pks) * pk) with (inv (ff_prod pks)); cycle 1.
    { field. intuition. }
    replace (1 * (inv (ff_prod pks))) with (inv (ff_prod pks)); cycle 1.
    { field. intuition. }

    destruct units as [unit units].
    rewrite <- discrete_log_mul; auto.
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite <- (discrete_log_mul pk); auto.
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
    sumZ (fun '(pk, rk) => discrete_log pk + discrete_log rk)
         (zip pks (reconstructed_keys pks)) mod modulus = 0.
  Proof.
    intros units.
    induction pks as [|pk pks IH]; auto.
    cbn.
    rewrite !eta_Z.
    rewrite mod_inv_mod_idemp, mod_inv_mul.
    destruct units as [unit units].
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite <- (discrete_log_mul pk); auto.
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
      rewrite Nat.even_add_mul_2.
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

  Definition discrete_log_with_spec (x : Z) :
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

  Definition discrete_log (x : Z) : Z.
  Proof.
    destruct (Z.eq_dec (x mod modulus) 0) as [eq|ne].
    - exact 0.
    - exact (proj1_sig (discrete_log_with_spec x ne)).
  Defined.

  Lemma discrete_log_spec x :
    IsUnit x ->
    0 <= discrete_log x < modulus /\
    generator ^ discrete_log x mod modulus = x mod modulus.
  Proof.
    intros is_unit.
    unfold discrete_log.
    destruct (Z.eq_dec _ _).
    - contradiction.
    - apply (proj2_sig (discrete_log_with_spec x n)).
  Qed.

  Lemma discrete_log_mul x y :
    IsUnit x ->
    IsUnit y ->
    discrete_log (x * y) = (discrete_log x + discrete_log y) mod modulus.
  Proof.
    Admitted.

  Lemma discrete_log_mod x :
    discrete_log x mod modulus = discrete_log x.
  Proof.
    unfold discrete_log.
    destruct (Z.eq_dec (x mod modulus) 0) as [eq|ne]; auto.
    pose proof (proj2_sig (discrete_log_with_spec x ne)) as H.
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
    sumZ (fun '(pk, rk) => discrete_log pk + discrete_log rk)
         (zip pks (reconstructed_keys pks)) mod modulus = 0.
  Proof.
    intros units.
    induction pks as [|pk pks IH]; auto.
    cbn.
    rewrite !eta_Z.
    rewrite mod_inv_mod_idemp, mod_inv_mul.
    destruct units as [unit units].
    rewrite <- Z.add_mod_idemp_l by lia.
    rewrite <- (discrete_log_mul pk); auto.
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

  Lemma discrete_log z :
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
        destruct (discrete_log pk ltac:(lia)) as [e [e_eq e_uniq]].
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
End Modulus.

From mathcomp Elmequire Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Elmequire Import fintype bigop prime finset fingroup morphism.
From mathcomp Elmequire Import perm automorphism quotient gproduct ssralg.
From mathcomp Elmequire Import finalg zmodp poly cyclic.

Section Foo.
  Context `(blah : nat).
  Lemma foo (G : {set 'units_Zp blah}) x (gen : generator G x) : True.
