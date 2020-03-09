From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
Import ListNotations.

Local Open Scope Z.

Fixpoint egcd_aux
        (n : nat)
        (r0 a0 b0 r1 a1 b1 : Z) {struct n} : Z * Z :=
  match n with
  | 0%nat => (0, 0)
  | S n => let (q, r) := Z.div_eucl r0 r1 in
           if r =? 0 then
             (a1, b1)
           else
             egcd_aux n r1 a1 b1 r (a0 - q*a1) (b0 - q*b1)
  end.

(* returns (x, y) such that x*m + y*n = Z.gcd(x, y) *)
Definition egcd (m n : Z) : Z * Z :=
  if m =? 0 then
    (0, Z.sgn n)
  else if n =? 0 then
    (Z.sgn m, 0)
  else
    let num_steps := S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))) in
    if Z.abs m <? Z.abs n then
      let (x, y) := egcd_aux num_steps (Z.abs n) 1 0 (Z.abs m) 0 1 in
      (Z.sgn m * y, Z.sgn n * x)
    else
      let (x, y) := egcd_aux num_steps (Z.abs m) 1 0 (Z.abs n) 0 1 in
      (Z.sgn m * x, Z.sgn n * y).

(*
Lemma egcd_aux_spec steps r0 a0 b0 r1 a1 b1 (P : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) :
  0 < r1 ->
  r1 <= r0 ->
  Z.log2 r0 + Z.log2 r1 < Z.of_nat steps ->

  Z.gcd r0 r1 = Z.gcd m n ->
  let (x, y) := egcd_aux steps r0 a0 b0 r1 a1 b1 in
  x*m + y*n = Z.gcd m n.
*)

Lemma egcd_aux_spec m n steps r0 a0 b0 r1 a1 b1 :
  Z.log2 r0 + Z.log2 r1 < Z.of_nat steps ->
  0 < r1 ->
  r1 <= r0 ->
  r0 = a0*m + b0*n ->
  r1 = a1*m + b1*n ->
  Z.gcd r0 r1 = Z.gcd m n ->
  let (x, y) := egcd_aux steps r0 a0 b0 r1 a1 b1 in
  x*m + y*n = Z.gcd m n.
Proof.
  revert r0 a0 b0 r1 a1 b1.
  induction steps as [|steps IH];
    intros r0 a0 b0 r1 a1 b1 enough_steps r1pos r1gt r0eq r1eq is_gcd.
  {
    cbn -[Z.add] in enough_steps.
    pose proof (Z.log2_nonneg r0).
    pose proof (Z.log2_nonneg r1).
    lia.
  }
  cbn.
  pose proof (Z_div_mod r0 r1 ltac:(lia)).
  destruct (Z.div_eucl r0 r1) as [q r].
  destruct (Z.eqb_spec r 0) as [->|?].
  - destruct H.
    rewrite Z.add_0_r in *.
    rewrite <- r1eq.
    rewrite <- is_gcd.
    rewrite H.
    rewrite Z.gcd_comm.
    now rewrite Z.gcd_mul_diag_l by lia.
  - apply IH; auto.
    + destruct H.
      destruct q; try lia; cycle 1.
      {
        pose proof (Z.mul_pos_neg r1 (Z.neg p) ltac:(lia) ltac:(lia)).
        lia.
      }
      assert (r + r1 <= r0).
      {
        enough (r1 <= r1 * Z.pos p) by lia.
        apply Z.le_mul_diag_r; lia.
      }
      assert (Z.log2 r1 + Z.log2 r < Z.log2 r0 + Z.log2 r1).
      {
        enough (Z.log2 r < Z.log2 r0) by lia.
        pose proof (Z.log2_le_mono (r*2^1) r0 ltac:(lia)).
        rewrite <- Z.shiftl_mul_pow2 in H2 by lia.
        rewrite Z.log2_shiftl in H2 by lia.
        lia.
      }
      lia.
    + lia.
    + lia.
    + rewrite !Z.mul_sub_distr_r.
      replace (a0 * m - q * a1 * m + (b0 * n - q * b1 * n))
        with (a0 * m + b0*n + (-1) * (q*(a1*m + b1*n)))
        by lia.
      rewrite <- r0eq, <-r1eq.
      lia.
    + rewrite <- is_gcd.
      rewrite (proj1 H).
      rewrite (Z.gcd_comm (r1 * q + r)).
      rewrite Z.add_comm, Z.mul_comm.
      now rewrite Z.gcd_add_mult_diag_r.
Qed.

Lemma egcd_spec m n :
  let (x, y) := egcd m n in
  m*x + n*y = Z.gcd m n.
Proof.
  unfold egcd.
  destruct (Z.eqb_spec m 0) as [->|?].
  { apply Z.sgn_abs. }
  destruct (Z.eqb_spec n 0) as [->|?].
  { rewrite Z.gcd_0_r, Z.add_0_r; apply Z.sgn_abs. }
  pose proof (Z.log2_nonneg (Z.abs m)).
  pose proof (Z.log2_nonneg (Z.abs n)).
  destruct (Z.ltb_spec (Z.abs m) (Z.abs n)).
  - unshelve epose proof (egcd_aux_spec
                            (Z.abs n) (Z.abs m)
                            (S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))))
                            (Z.abs n) 1 0
                            (Z.abs m) 0 1
                            _ _ _ _ _ _); try lia.
    + rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      lia.
    + destruct (egcd_aux _ _ _ _ _ _ _).
      rewrite !Z.mul_assoc.
      rewrite Z.gcd_abs_l, Z.gcd_comm, Z.gcd_abs_l in H2.
      rewrite !Z.sgn_abs.
      lia.
  - unshelve epose proof (egcd_aux_spec
                            (Z.abs m) (Z.abs n)
                            (S (Z.to_nat (Z.log2 (Z.abs m) + Z.log2 (Z.abs n))))
                            (Z.abs m) 1 0
                            (Z.abs n) 0 1
                            _ _ _ _ _ _); try lia.
    + rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      lia.
    + destruct (egcd_aux _ _ _ _ _ _ _).
      rewrite !Z.mul_assoc.
      rewrite Z.gcd_abs_l, Z.gcd_comm, Z.gcd_abs_l, Z.gcd_comm in H2.
      rewrite !Z.sgn_abs.
      lia.
Qed.

Lemma mul_fst_egcd a n :
  rel_prime a n ->
  a * fst (egcd a n) mod n = 1 mod n.
Proof.
  destruct (Z.eqb_spec n 0) as [->|?].
  { intros; now rewrite !Zmod_0_r. }
  intros relprime.
  pose proof (egcd_spec a n).
  destruct (egcd a n) as [x y]; cbn.
  rewrite (proj2 (Zgcd_1_rel_prime _ _) relprime) in H.
  replace (a * x) with (1  + (-y)*n) by lia.
  rewrite <- Z.add_mod_idemp_r by lia.
  now rewrite Z.mod_mul, Z.add_0_r by lia.
Qed.

Lemma rel_prime_egcd a n :
  rel_prime a n ->
  rel_prime (fst (egcd a n)) n.
Proof.
  intros relprime.
  pose proof (egcd_spec a n).
  destruct (egcd a n) as [x y]; cbn.
  apply Zgcd_1_rel_prime in relprime.
  rewrite relprime in *.
  apply bezout_rel_prime.
  rewrite (Z.mul_comm n) in H.
  apply (Bezout_intro  _ _ _ _ _ H).
Qed.

(*
(*
Lemma egcd_aux_funelim
      (P : Z -> Z -> Z -> Z -> Z -> Z -> Z * Z -> Prop) :
  (forall a0 b0 r1 a1 b1 q,
      0 < r1 ->
      P (r1 * q) a0 b0 r1 a1 b1 (a1, b1)) ->
  (forall a0 b0 r1 a1 b1 q r result,
      0 < r1 ->
      0 < r < r1 ->
      P r1 a1 b1 r (a0 - q*a1) (b0 - q*b1) result ->
      P (r1*q + r) a0 b0 r1 a1 b1 result) ->
  forall r0 a0 b0 r1 a1 b1,
    0 < r1 <= r0 ->
    P r0 a0 b0 r1 a1 b1 (egcd_aux (Z.to_nat (Z.log2 r0 + Z.log2 r1 + 1)) r0 a0 b0 r1 a1 b1).
Proof.
  intros base ind r0 a0 b0 r1 a1 b1 bound.
  enough (forall steps,
             Z.log2 r0 + Z.log2 r1 < Z.of_nat steps ->
             P r0 a0 b0 r1 a1 b1 (egcd_aux steps r0 a0 b0 r1 a1 b1)) as H.
  {
    apply H.
    pose proof (Z.log2_nonneg r0).
    pose proof (Z.log2_nonneg r1).
    rewrite Z2Nat.id; lia.
  }

  intros steps.
  revert r0 a0 b0 r1 a1 b1 bound.
  induction steps as [|steps IH]; intros r0 a0 b0 r1 a1 b1 bound enough_steps;
    cbn.
  - pose proof (Z.log2_nonneg r0).
    pose proof (Z.log2_nonneg r1).
    lia.
  - pose proof (Z_div_mod r0 r1 ltac:(lia)).
    destruct (Z.div_eucl r0 r1) as [q r].
    destruct (Z.eqb_spec r 0) as [->|?].
    + destruct H.
      rewrite Z.add_0_r in *.
      subst r0.
      apply base; lia.
    + pose proof (Z.log2_nonneg r0).
      pose proof (Z.log2_nonneg r1).
      unshelve epose proof (IH r1 a1 b1 r (a0 - q*a1) (b0 - q*b1) _ _) as IH; try lia.
      * destruct H.
        destruct q; try lia; cycle 1.
        {
          pose proof (Z.mul_pos_neg r1 (Z.neg p) ltac:(lia) ltac:(lia)).
          lia.
        }
        assert (r + r1 <= r0).
        {
          enough (r1 <= r1 * Z.pos p) by lia.
          apply Z.le_mul_diag_r; lia.
        }
        assert (Z.log2 r1 + Z.log2 r < Z.log2 r0 + Z.log2 r1).
        {
          enough (Z.log2 r < Z.log2 r0) by lia.
          pose proof (Z.log2_le_mono (r*2^1) r0 ltac:(lia)).
          rewrite <- Z.shiftl_mul_pow2 in H4 by lia.
          rewrite Z.log2_shiftl in H4 by lia.
          lia.
        }
        lia.
      * destruct H as [-> H].
        destruct (egcd_aux _ _ _ _ _ _ _) as [x y].
        apply ind; auto; lia.
Qed.

Lemma egcd_aux_spec' m n :
  0 < n <= m ->
  let (x, y) := egcd_aux (Z.to_nat (Z.log2 m + Z.log2 n + 1)) m 1 0 n 0 1 in
  x*m + y*n = Z.gcd m n.
Proof.
  unshelve epose proof
           (egcd_aux_funelim
              (fun r0 a0 b0 r1 a1 b1 '(x, y) =>
                 r0 = a0*m + b0*n ->
                 r1 = a1*m + b1*n ->
                 Z.gcd r0 r1 = Z.gcd m n ->
                 x*m + y*n = Z.gcd m n)
              _ _).
  - cbn.
    intros a0 b0 r1 a1 b1 q r1pos r1qeq r1eq gcdeq.
    rewrite <- r1eq, <- gcdeq.
    rewrite Z.gcd_comm.
    now rewrite Z.gcd_mul_diag_l by lia.
  - cbn.
    intros a0 b0 r1 a1 b1 q r [x y] r1pos bound IH r1qreq r1eq gcdeq.
    apply IH; try lia.
    + rewrite !Z.mul_sub_distr_r.
      replace (a0 * m - q * a1 * m + (b0 * n - q * b1 * n))
        with (a0 * m + b0*n + (-1) * (q*(a1*m + b1*n)))
        by lia.
      rewrite <- r1eq, <- r1qreq.
      lia.
    + rewrite <- gcdeq.
      rewrite (Z.gcd_comm (r1 * q + r)).
      rewrite Z.add_comm, Z.mul_comm.
      now rewrite Z.gcd_add_mult_diag_r.
  - intros.
    cbn in H.
    specialize (H m 1 0 n 0 1 ltac:(auto)).
    destruct (egcd_aux _ _ _ _ _ _ _).
    apply H; auto; lia.
Qed.

Lemma egcd_aux_same m a0 b0 a1 b1 :
  0 < m ->
  egcd_aux (Z.to_nat (Z.log2 m + Z.log2 m + 1)) m a0 b0 m a1 b1 = (a1, b1).
Proof.
  intros lt.
  apply (egcd_aux_funelim (fun r0 a0 b0 r1 a1 b1 res => res = (a1, b1))); auto; try lia.
  intros.
  pattern (egcd_aux (Z.to_nat (Z.log2 m + Z.log2 m + 1)) m a0 b0 m a1 b1).
  apply (egcd_aux_funelim _ _ _ m a0 b0 m a1 b1).
  apply egcd_aux_funelim with (r0 := m) (r1 := m); auto; try lia.
  - intros.
    cbn.
  intros mpos.
  specialize (ltac:(lia) : m <= m).
  revert mpos.
  apply egcd_aux_funelim with (P := fun r0 a0 b0 r1 a1 b1 result => result = (a1, b1)).
  auto.
  intros.
  cbn.

  revert m a0 b0 a1 b1.
  induction steps as [|steps IH]; intros m a0 b0 a1 b1 enough_steps; cbn; auto.
  - pose proof (Z.log2_nonneg m).
    lia.
  -

Lemma div_eucl_same m :
  m <> 0 -> Z.div_eucl m m = (1, 0).
Proof.
  intros neq.
  pose proof (Z_div_mod_full m m neq).
  unfold Remainder in H.
  destruct (Z.div_eucl m m) as [q r].
  destruct H.
  destruct (Z.eq_dec r 0) as [->|?].
  - rewrite Z.add_0_r in *.
    symmetry in H.
    rewrite Z.mul_comm in H.
    apply Z.mul_id_l in H; auto.
    congruence.
  - pose proof (Z.divide_refl m).
    rewrite H in H1 at 2.
    unshelve epose proof (Z.divide_add_cancel_r m (m * q) r _ _); auto with zarith.
    pose proof (Znumtheory.Zdivide_bounds _ _ H2 n).
    lia.
Qed.

Lemma egcd_aux_same m a0 b0 a1 b1 :
  0 < m ->
  egcd_aux (S (Z.to_nat (Z.log2 m + Z.log2 m))) m a0 b0 m a1 b1 = (a1, b1).
Proof.
  intros mpos.
  specialize (ltac:(lia) : m <= m).
  revert mpos.
  apply egcd_aux_funelim with (P := fun r0 a0 b0 r1 a1 b1 result => result = (a1, b1)).
  auto.
  intros.
  cbn.

  revert m a0 b0 a1 b1.
  induction steps as [|steps IH]; intros m a0 b0 a1 b1 enough_steps; cbn; auto.
  - pose proof (Z.log2_nonneg m).
    lia.
  -
  admit.
  destruct (Z.eq_dec m 0) as [->|?]; cbn; auto.
  now rewrite div_eucl_same; cbn.
  -
  rewrite div_eucl_same by lia.
  Search (Z.div_eucl _ _).

Lemma egcd_comm m n :
  let (x, y) := egcd m n in egcd n m = (y, x).
Proof.
  unfold egcd.
  destruct (Z.eqb_spec m 0) as [->|?], (Z.eqb_spec n 0) as [->|?]; auto.
  rewrite <- Z.gtb_ltb.
  destruct (Z.compare_spec (Z.abs n) (Z.abs m)) as [eq|?|?].
  - rewrite Z.gtb_ltb.
    rewrite eq.
    rewrite Z.ltb_irrefl.
    destruct (egcd_aux _ _ _ _ _ _ _).
kw  unfold "<?".
  destruct (Z.ltb_spec (Z.abs m) (Z.abs n)).
  - rewrite (proj2 (Z.ltb_ge (Z.abs n) (Z.abs m)) ltac:(lia)).
    rewrite (Z.add_comm (Z.log2 (Z.abs n))).
    now destruct (egcd_aux _ _ _ _ _ _ _).
  -
    rewrite (proj2 (Z.ltb_ge (Z.abs n) (Z.abs m)) ltac:(lia)).
kwj    replace (Z.log2 (Z.abs n) + Z.log2 (Z.abs m)) with (
    cbn.
    rewrite <- Z.gtb_ltb.
    Search "gtb".
    rewrite Z.gtb_le
    rewrite (Z.ltb_ge
  unfold "<?", ">?".
  destruct (Z.compare_spec (Z.abs n) (Z.abs m)) as [->|?|?].
  - destruct
  Z.cmp_spec
  destruct (Z.ltb_spec (Z.abs m) (Z.abs n)).
  -
  pose proof (egcd_spec m n).
  pose proof (egcd_spec n m).
  destruct (egcd m n) as [x y], (egcd n m) as [x' y'].
  rewrite Z.gcd_comm in H0.
*)

From Equations Require Import Equations.

Definition inspect {A} (a : A) : { x | x = a } :=
  exist _ a eq_refl.

Equations? egcd_aux_eqs (r0 a0 b0 r1 a1 b1 : Z) (r1pos : 0 < r1) (r0large : r1 <= r0) : Z * Z
  by wf (Z.to_nat (Z.log2 r0 + Z.log2 r1)) lt :=
egcd_aux_eqs r0 a0 b0 r1 a1 b1 _ _ with inspect (Z.div_eucl r0 r1) :=
  | exist _ (q, r) _ with inspect (r =? 0) := {
    | exist _ true _ := (a1, b1);
    | exist _ false _ := egcd_aux_eqs r1 a1 b1 r (a0 - q*a1) (b0 - q*b1) _ _
  }.
Proof.
  all: symmetry in wildcard1; apply Z.eqb_neq in wildcard1.
  all: pose proof (Z_div_mod r0 r1 ltac:(lia)).
  all: destruct (Z.div_eucl r0 r1) as [q' r'].
  all: replace q' with q in * by congruence;
    replace r' with r in * by congruence;
    clear q' r' wildcard.
  - lia.
  - apply Z.compare_gt_iff in H.
    lia.
  - destruct q; try lia; cycle 1.
    {
      pose proof (Z.mul_pos_neg r1 (Z.neg p) ltac:(lia) ltac:(lia)).
      lia.
    }
    assert (r + r1 <= r0).
    {
      enough (r1 <= r1 * Z.pos p) by lia.
      apply Z.le_mul_diag_r; lia.
    }
    assert (Z.log2 r1 + Z.log2 r < Z.log2 r0 + Z.log2 r1).
    {
      enough (Z.log2 r < Z.log2 r0) by lia.
      pose proof (Z.log2_le_mono (r*2^1) r0 ltac:(lia)).
      rewrite <- Z.shiftl_mul_pow2 in H1 by lia.
      rewrite Z.log2_shiftl in H1 by lia.
      lia.
    }
    pose proof (Z.log2_nonneg r).
    pose proof (Z.log2_nonneg r0).
    pose proof (Z.log2_nonneg r1).
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma foo r0 a0 b0 r1 a1 b1 r1pos r0large :
  egcd_aux_eqs r0 a0 b0 r1 a1 b1 r1pos r0large =
  egcd_aux (Z.to_nat (Z.log2 r0 + Z.log2 r1)) r0 a0 b0 r1 a1 b1.
Proof.
  funelim (egcd_aux_eqs r0 a0 b0 r1 a1 b1 r1pos r0large).
  - cbn in *.
    admit.
  - cbn in *.

    *)
