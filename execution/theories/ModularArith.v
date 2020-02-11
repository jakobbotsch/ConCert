From Bignums Require Import BigZ.
From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Program.
From Coq Require Import PArith.
From Coq Require Import Psatz.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import Zwf.

Definition mod_prod (l : list Z) (m : Z) : Z :=
  fold_right (fun e r => e * r mod m) 1 l.

Local Open Scope bigZ.
Fixpoint mod_pow_aux (a : bigZ) (x : positive) (m : bigZ) (r : bigZ) : bigZ :=
  match x with
  | x~0%positive => mod_pow_aux (BigZ.square a mod m) x m r
  | x~1%positive => mod_pow_aux (BigZ.square a mod m) x m (r * a mod m)
  | _ => r * a mod m
  end.

Global Instance BigZ_square_wd :
  Proper (BigZ.eq ==> BigZ.eq) BigZ.square.
Proof.
  intros a b eq.
  rewrite 2!BigZ.square_spec.
  now rewrite eq.
Qed.

Global Instance mod_pow_aux_wd :
  Proper (BigZ.eq ==> eq ==> BigZ.eq ==> BigZ.eq ==> BigZ.eq) mod_pow_aux.
Proof.
  (*intros a1 a2 aeq ? x -> m1 m2 meq r1 r2 req.*)
  intros a1 a2 aeq ? x ->.
  revert a1 a2 aeq.
  induction x; intros a1 a2 aeq m1 m2 meq r1 r2 req.
  - cbn.
    apply IHx.
    + rewrite aeq, meq.
      reflexivity.
    + auto.
    + rewrite req, aeq, meq.
      reflexivity.
  - cbn.
    apply IHx.
    + rewrite aeq, meq.
      reflexivity.
    + auto.
    + rewrite req.
      reflexivity.
  - cbn.
    rewrite req, aeq, meq.
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
    rewrite BigZ.square_spec.
    rewrite IHx.
    unfold "==".
    rewrite 2!BigZ.spec_modulo.
    rewrite 2!BigZ.spec_mul.
    rewrite 2!BigZ.spec_pow_pos.
    rewrite 2!BigZ.spec_modulo.
    rewrite 2!BigZ.spec_mul.
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
    rewrite 2!BigZ.spec_modulo.
    rewrite 2!BigZ.spec_mul.
    rewrite 2!BigZ.spec_pow_pos.
    rewrite BigZ.spec_modulo.
    rewrite BigZ.spec_square.
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
    rewrite 2!BigZ.spec_modulo.
    rewrite 2!BigZ.spec_mul.
    rewrite BigZ.spec_pow_pos.
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
    + rewrite BigZ.spec_modulo.
      rewrite BigZ.spec_mul.
      rewrite BigZ.spec_pow_pos.
      rewrite 2!BigZ.spec_of_Z.
      f_equal.
      cbn.
      destruct (Z.pow_pos _ _); auto.
    + intro cont.
      unfold "==" in *.
      cbn in *.
      rewrite BigN.spec_of_pos in cont.
      lia.
  - destruct x; auto.
    rewrite mod_pow_aux_spec.
    + rewrite BigZ.spec_modulo.
      rewrite BigZ.spec_mul.
      rewrite BigZ.spec_pow_pos.
      rewrite 2!BigZ.spec_of_Z.
      f_equal.
      cbn.
      destruct (Z.pow_pos _ _); auto.
    + intro cont.
      unfold "==" in *.
      cbn in *.
      rewrite BigN.spec_of_pos in cont.
      lia.
Qed.

(* returns (x, y) such that x*m + y*n = gcd(x, y) *)
Fixpoint egcd_aux
        (n : nat)
        (r0 a0 b0 r1 a1 b1 : bigZ) {struct n} : Z * Z :=
  match n with
  | 0%nat => (0, 0)
  | S n => let '(q, r) := BigZ.div_eucl r0 r1 in
           if (r =? 0)%bigZ then
             ([a1], [b1])
           else
             egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
  end.

Definition egcd (m n : Z) : Z * Z :=
  let num_steps := S (Z.to_nat (Z.log2 m + Z.log2 n)) in
  match m, n with
  | Z0, _ => (0, 1)
  | _, Z0 => (1, 0)
  | Zneg m, Zneg n => egcd_aux num_steps
                               (BigZ.of_Z (Z.pos m)) 1 0
                               (BigZ.of_Z (Z.pos n)) 0 1
  | Zneg m, Zpos n => let (x, y) := egcd_aux num_steps
                                             (BigZ.of_Z (Z.pos m)) 1 0
                                             (BigZ.of_Z (Z.pos n)) 0 1 in
                      (* x*-m + y*n = gcd(-m, n) *)
                      (-x, y)
  | Zpos m, Zneg n => let (x, y) := egcd_aux num_steps
                                             (BigZ.of_Z (Z.pos m)) 1 0
                                             (BigZ.of_Z (Z.pos n)) 0 1 in
                      (x, -y)
  | Zpos m, Zpos n => egcd_aux num_steps (BigZ.of_Z (Z.pos m)) 1 0 (BigZ.of_Z (Z.pos n)) 0 1
  end.

(*
Lemma egcd_aux_gcd (steps : nat) (r0 a0 b0 r1 a1 b1 m n : bigZ) :
  1 + Z.log2 r0 + Z.log2 r1 <= Z.of_nat steps ->
  r0 > 0 ->
  r1 > 0 ->
  a0 * m + b0 = r0 ->
  a1 * n + b1 = r1 ->
  let (x, y) := egcd_aux steps r0 a0 b0 r1 a1 b1 in
  Zis_gcd m n (x*r0 + y*r1).
Proof.
  Admitted.
  revert r0 a0 b0 r1 a1 b1 m n.
  induction steps as [| steps IH];
    intros r0 a0 b0 r1 a1 b1 m n enough_steps r0_pos r1_pos r0_eq r1_eq.
  - assert (0 <= Z.log2 r0) by (apply Z.log2_nonneg).
    assert (0 <= Z.log2 r1) by (apply Z.log2_nonneg).
    assert (r0 <= 1) by (apply Z.log2_null; lia).
    assert (r1 <= 1) by (apply Z.log2_null; lia).
    lia.
  - cbn.
    pose proof (Z.div_eucl_eq r0 r1 ltac:(lia)).
    destruct (Z.div_eucl r0 r1) as [q r] eqn:div.
    subst r0 r1.
    destruct (r =? 0) eqn:rzero.
    + apply Z.eqb_eq in rzero.
      subst r.
      rewrite Z.add_0_r in *.
      rewrite H in *.
      subst r1.
      replace (a1 * (r1 * q) + b1 * r1) with (r1 * (a1 * q + b1)) by lia.
      replace r1 with (r1 * 1) at 2 by lia.
      apply Zis_gcd_mult.*)

Lemma egcd_gcd m n :
  let (x, y) := egcd m n in
  x*m + y*n = Z.gcd m n.
Proof.
  Admitted.

(* Find y such that x*y = 1 mod m *)
Definition mod_inv (x m : Z) : Z :=
  fst (egcd x m).

Lemma mod_inv_spec x m :
  prime m ->
  x mod m <> 0 ->
  (x * mod_inv x m) mod m = 1.
Proof.
  intros is_prime val_between.
  unfold mod_inv.
  pose proof (egcd_gcd x m).
  destruct (egcd x m).
  cbn.
  destruct is_prime as [m_larger rel_primes].
  pose proof (Z_mod_lt x m ltac:(lia)).
  pose proof (rel_primes (x mod m) ltac:(lia)).
  replace (Z.gcd x m) with 1 in *.
  2: {
    symmetry.
    rewrite Z.gcd_comm.
    rewrite <- (Z.gcd_mod x m) by lia.
    apply Zgcd_1_rel_prime; auto.
  }
  assert (eq_long: (z * x + z0 * m) mod m = x * z mod m).
  {
    rewrite <- (Zplus_mod_idemp_r (z0 * m)).
    rewrite <- (Zmult_mod_idemp_r m).
    rewrite Z_mod_same_full.
    replace (z0 * 0) with 0 by lia.
    cbn.
    now replace (z * x + 0) with (x * z) by lia.
  }
  rewrite <- eq_long, H.
  auto with zarith.
  now apply Z.mod_1_l.
Qed.

Definition IsGenerator n modulus : Prop :=
  mod_pow n modulus modulus = 1 /\
  forall n', 0 < n' < modulus -> mod_pow n n' modulus <> 1.
