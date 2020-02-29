(* This file implements various helper functions and proofs *)

From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Psatz.
From Coq Require Import Eqdep_dec.
Require Import Automation.
Import ListNotations.

Fixpoint find_first {A B : Type} (f : A -> option B) (l : list A)
  : option B :=
  match l with
  | hd :: tl => match f hd with
                | Some b => Some b
                | None => find_first f tl
                end
  | [] => None
  end.

Fixpoint map_option {A B : Type} (f : A -> option B) (l : list A)
  : list B :=
  match l with
  | hd :: tl => match f hd with
                  | Some b => b :: map_option f tl
                  | None => map_option f tl
                end
  | [] => []
  end.

Definition with_default {A : Type} (a : A) (o : option A) : A :=
  match o with
  | Some v => v
  | None => a
  end.

Definition unpack_option {A : Type} (a : option A) :=
  match a return match a with
                  | Some _ => A
                  | None => unit
                  end with
  | Some x => x
  | None => tt
  end.

Fixpoint sumZ {A : Type} (f : A -> Z) (xs : list A) : Z :=
  match xs with
  | [] => 0
  | x :: xs' => f x + sumZ f xs'
  end.

Fixpoint sumnat {A : Type} (f : A -> nat) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => f x + sumnat f xs'
  end.

Lemma sumnat_app
      {A : Type} {f : A -> nat} {xs ys : list A} :
  sumnat f (xs ++ ys) = sumnat f xs + sumnat f ys.
Proof.
  revert ys.
  induction xs as [| x xs IH]; intros ys; auto.
  cbn.
  rewrite IH.
  lia.
Qed.

Lemma sumnat_permutation
      {A : Type} {f : A -> nat} {xs ys : list A}
      (perm_eq : Permutation xs ys) :
  sumnat f xs = sumnat f ys.
Proof. induction perm_eq; perm_simplify; lia. Qed.

Instance sumnat_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A:=A) ==> eq) sumnat.
Proof. repeat intro. subst. now apply sumnat_permutation. Qed.

Lemma sumnat_map {A B : Type} (f : A -> B) (g : B -> nat) (xs : list A) :
  sumnat g (map f xs) =
  sumnat (fun a => g (f a)) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumZ_permutation
      {A : Type} {f : A -> Z} {xs ys : list A}
      (perm_eq : Permutation xs ys) :
  sumZ f xs = sumZ f ys.
Proof. induction perm_eq; perm_simplify; lia. Qed.

Instance sumZ_perm_proper {A : Type} :
  Proper (eq ==> Permutation (A:=A) ==> eq) sumZ.
Proof. repeat intro. subst. now apply sumZ_permutation. Qed.

Local Open Scope Z.
Lemma sumZ_app
      {A : Type} {f : A -> Z} {xs ys : list A} :
  sumZ f (xs ++ ys) = sumZ f xs + sumZ f ys.
Proof.
  revert ys.
  induction xs as [| x xs IH]; intros ys; auto.
  cbn.
  rewrite IH.
  lia.
Qed.

Lemma sumZ_map {A B : Type} (f : A -> B) (g : B -> Z) (xs : list A) :
  sumZ g (map f xs) =
  sumZ (fun a => g (f a)) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumZ_filter {A : Type} (f : A -> Z) (pred : A -> bool) (xs : list A) :
  sumZ f (filter pred xs) =
  sumZ (fun a => if pred a then f a else 0) xs.
Proof.
  induction xs as [|hd tl IH]; auto.
  cbn.
  destruct (pred hd); auto.
  cbn.
  now rewrite IH.
Qed.

Lemma sumZ_mul (f : Z -> Z) (l : list Z) (z : Z) :
  z * sumZ f l = sumZ (fun z' => z * f z') l.
Proof.
  induction l; auto; cbn in *; lia.
Qed.

Fixpoint prodZ {A : Type} (f : A -> Z) (l : list A) : Z :=
  match l with
  | [] => 1
  | x :: xs => f x * prodZ f xs
  end.

Lemma in_app_cons_or {A : Type} (x y : A) (xs ys : list A) :
  x <> y ->
  In x (xs ++ y :: ys) ->
  In x (xs ++ ys).
Proof.
  intros x_neq_y x_in.
  apply in_or_app.
  apply in_app_or in x_in.
  destruct x_in as [?|x_in]; auto.
  destruct x_in; auto; congruence.
Qed.

Lemma incl_split {A : Type} (l m n : list A) :
  incl (l ++ m) n -> incl l n /\ incl m n.
Proof.
  intros H.
  unfold incl in *.
  Hint Resolve in_or_app : core.
  auto.
Qed.

Lemma NoDup_incl_reorganize
      {A : Type}
      (l l' : list A) :
  NoDup l' ->
  incl l' l ->
  exists suf, Permutation (l' ++ suf) l.
Proof.
  revert l.
  induction l' as [| x xs IH]; intros l nodup_l' incl_l'_l.
  - exists l. apply Permutation_refl.
  - assert (x_in_l: In x l).
    + apply (incl_l'_l x). left. constructor.
    + destruct (in_split _ _ x_in_l) as [pref [suf eq]]; subst.
      inversion nodup_l'; subst.
      assert (incl xs (pref ++ suf)).
      * intros a a_in.
        apply in_or_app.
        apply (incl_split [x] xs _) in incl_l'_l.
        destruct incl_l'_l as [incl_x incl_xs].
        intuition.
        specialize (incl_xs a a_in).
        apply in_app_or in incl_xs.
        destruct incl_xs as [in_pref | [in_x | in_suf]]; auto.
        congruence.
      * destruct (IH _ H2 H) as [suf' perm_suf'].
        exists suf'.
        perm_simplify.
Qed.

Lemma in_NoDup_app {A : Type} (x : A) (l m : list A) :
  In x l -> NoDup (l ++ m) -> ~In x m.
Proof.
  intros in_x_l nodup_l_app_m in_x_m.
  destruct (in_split _ _ in_x_l) as [l1 [l2 eq]]; subst.
  replace ((l1 ++ x :: l2) ++ m) with (l1 ++ x :: (l2 ++ m)) in nodup_l_app_m.
  - apply (NoDup_remove_2 _ _ _) in nodup_l_app_m.
    rewrite app_assoc in nodup_l_app_m.
    auto.
  - rewrite app_comm_cons.
    appify.
    now rewrite app_assoc.
Qed.

Lemma seq_app start len1 len2 :
  seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
  revert start.
  induction len1 as [| len1 IH]; intros start.
  - now rewrite Nat.add_0_r.
  - cbn.
    rewrite IH.
    f_equal; f_equal; f_equal.
    lia.
Qed.

Lemma sumZ_seq_S f start len :
  sumZ f (seq start (S len)) = sumZ f (seq start len) + f (start + len)%nat.
Proof.
  replace (S len) with (len + 1)%nat by lia.
  rewrite (seq_app start len 1).
  rewrite sumZ_app.
  cbn.
  lia.
Qed.

Lemma forall_respects_permutation {A} (xs ys : list A) P :
  Permutation xs ys -> Forall P xs -> Forall P ys.
Proof.
  intros perm all.
  apply Forall_forall.
  intros y y_in.
  pose proof (proj1 (Forall_forall P xs) all).
  apply H.
  apply Permutation_in with ys; symmetry in perm; auto.
Qed.

Instance Forall_Permutation_proper {A} :
  Proper (eq ==> @Permutation A ==> iff) (@Forall A).
Proof.
  intros f f' ? xs ys perm.
  subst f'.
  split; apply forall_respects_permutation; auto; symmetry; auto.
Qed.

Instance forallb_Permutation_proper {A} :
  Proper (eq ==> @Permutation A ==> eq) (@forallb A).
Proof.
  assert (H: forall f (xs ys : list A),
             Permutation xs ys -> forallb f xs = true -> forallb f ys = true).
  {
    intros f xs ys perm all.
    apply forallb_forall.
    intros x x_in.
    pose proof (proj1 (forallb_forall f xs) all).
    apply H.
    now rewrite perm.
  }

  intros ? f -> xs ys perm.
  destruct (forallb f xs) eqn:forall1, (forallb f ys) eqn:forall2; auto.
  - pose proof (H _ _ _ perm forall1); congruence.
  - pose proof (H _ _ _ (Permutation_sym perm) forall2); congruence.
Qed.

Lemma Forall_false_filter_nil {A : Type} (pred : A -> bool) (l : list A) :
  Forall (fun a => pred a = false) l -> filter pred l = [].
Proof.
  intros all.
  induction l as [|hd tl IH]; auto.
  inversion_clear all as [|? ? head_false tail_false].
  cbn.
  now rewrite head_false, IH.
Qed.

Lemma Forall_app {A : Type} (P : A -> Prop) (l l' : list A) :
  Forall P l /\ Forall P l' <-> Forall P (l ++ l').
Proof.
  revert l'.
  induction l as [ |hd tl IH].
  - cbn.
    split; intros; auto.
    tauto.
  - intros l'.
    split.
    + intros [all1 all2].
      inversion_clear all1.
      cbn.
      constructor; auto.
      apply -> IH.
      tauto.
    + intros all.
      cbn in all.
      inversion_clear all as [ | ? ? P_phd all_rest].
      enough (P hd /\ Forall P tl /\ Forall P l') by
          (split; try constructor; tauto).
      split; auto.
      now apply IH.
Qed.

Lemma filter_app {A} (pred : A -> bool) (l l' : list A) :
  filter pred (l ++ l') = filter pred l ++ filter pred l'.
Proof.
  induction l as [|hd tl IH]; auto.
  cbn.
  rewrite IH.
  destruct (pred hd); auto.
Qed.

Lemma filter_filter {A : Type} (f g : A -> bool) (l : list A) :
  filter f (filter g l) = filter (fun a => (f a && g a)%bool) l.
Proof.
  induction l as [|? ? IH]; auto.
  cbn.
  destruct (f a) eqn:fa, (g a); auto.
  - cbn. now rewrite IH, fa.
  - cbn. now rewrite IH, fa.
Qed.

Lemma filter_map {A B : Type} (f : A -> B) (pred : B -> bool) (l : list A) :
  filter pred (map f l) =
  map f (filter (fun a => pred (f a)) l).
Proof.
  induction l as [|hd tl IH]; auto.
  cbn.
  rewrite IH.
  destruct (pred (f hd)); auto.
Qed.

Lemma filter_false {A : Type} (l : list A) :
  filter (fun _ => false) l = [].
Proof. induction l; auto. Qed.

Lemma filter_true {A : Type} (l : list A) :
  filter (fun _ => true) l = l.
Proof.
  induction l as [|? ? IH]; auto.
  cbn.
  now rewrite IH.
Qed.

Lemma Permutation_filter {A : Type} (pred : A -> bool) (l l' : list A) :
  Permutation l l' ->
  Permutation (filter pred l) (filter pred l').
Proof.
  intros perm.
  induction perm; auto.
  - cbn.
    destruct (pred x); auto.
  - cbn.
    destruct (pred x), (pred y); auto.
    constructor.
  - rewrite IHperm1; auto.
Qed.

Fixpoint zip {X Y} (xs : list X) (ys : list Y) : list (X * Y) :=
  match xs, ys with
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | _, _ => []
  end.

Lemma nth_snoc {A} (l : list A) (a b : A)  :
  nth (length l) (l ++ [a]) b = a.
Proof. induction l; auto. Qed.

Lemma firstn_app_invl {A} (l1 l2 l3 : list A) :
  firstn (length l1 + length l2) l3 = l1 ++ l2 -> firstn (length l1) l3 = l1.
Proof.
  revert l3.
  induction l1 as [|x xs IH]; auto; intros l3 H.
  cbn in *.
  destruct l3; inversion H.
  apply f_equal; auto.
Qed.

Lemma existsb_forallb {A} f (l : list A) :
  existsb f l = negb (forallb (fun x => negb (f x)) l).
Proof.
  induction l as [|x xs IH]; auto.
  cbn.
  now rewrite IH, Bool.negb_andb, Bool.negb_involutive.
Qed.

Lemma forallb_existsb {A} f (l : list A) :
  forallb f l = negb (existsb (fun x => negb (f x)) l).
Proof.
  induction l as [|x xs IH]; auto.
  cbn.
  now rewrite IH, Bool.negb_orb, Bool.negb_involutive.
Qed.

Fixpoint All {A} (f : A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => f x /\ All f xs
  end.

Local Open Scope nat.
Lemma sumZ_seq_n (f : nat -> Z) n len :
  sumZ f (seq n len) =
  sumZ (fun i => f (i + n)) (seq 0 len).
Proof.
  revert n f.
  induction len as [|len IH]; intros n f; auto.
  cbn.
  apply f_equal.
  rewrite (IH 1), (IH (S n)).
  clear.
  induction (seq 0 len); auto.
  cbn.
  rewrite IHl.
  now replace (a + 1 + n) with (a + S n) by lia.
Qed.

Lemma sumZ_zero {A} (l : list A) :
  sumZ (fun _ => 0%Z) l = 0%Z.
Proof. induction l; auto. Qed.

Lemma sumZ_seq_feq (f g : nat -> Z) len :
  (forall i, i < len -> f i = g i)%nat ->
  sumZ g (seq 0 len) = sumZ f (seq 0 len).
Proof.
  revert f g.
  induction len as [|len IH]; intros f g all_same; auto.
  cbn.
  rewrite 2!(sumZ_seq_n _ 1).
  rewrite (all_same 0%nat ltac:(lia)).
  apply f_equal.
  apply IH.
  intros i lt.
  now specialize (all_same (i + 1)%nat ltac:(lia)).
Qed.

Lemma sumZ_firstn {A} default (f : A -> Z) n l :
  (n <= length l \/ f default = 0%Z) ->
  sumZ f (firstn n l) =
  sumZ (fun i => f (nth i l default)) (seq 0 n).
Proof.
  revert l.
  induction n as [|n IH]; intros l le; auto.
  cbn.
  rewrite sumZ_seq_n.
  destruct l; cbn in *.
  - destruct le; [lia|].
    rewrite H.
    clear -H.
    rewrite (sumZ_seq_feq (fun i : nat => 0%Z)).
    + now rewrite sumZ_zero.
    + intros i ?; destruct (i + 1); now rewrite H.
  - apply f_equal.
    rewrite IH by lia.
    apply sumZ_seq_feq.
    intros i.
    intros lt.
    destruct (i + 1) eqn:i1; [lia|].
    now replace n0 with i by lia.
Qed.

Lemma sumZ_skipn {A} default (f : A -> Z) n l :
  sumZ f (skipn n l) =
  sumZ (fun i => f (nth (n + i) l default)) (seq 0 (length l - n)).
Proof.
  revert l.
  induction n as [|n IH]; intros l; cbn.
  - rewrite Nat.sub_0_r.
    rewrite <- (sumZ_firstn default).
    + now rewrite firstn_all.
    + left; lia.
  - destruct l; auto.
    cbn.
    apply IH.
Qed.

Local Open Scope Z.
Lemma sumZ_add {A} (f g : A -> Z) l :
  sumZ (fun a => f a + g a) l = sumZ f l + sumZ g l.
Proof.
  induction l; auto; cbn in *; lia.
Qed.
Lemma sumZ_sub {A} (f g : A -> Z) l :
  sumZ (fun a => f a - g a) l =
  sumZ f l - sumZ g l.
Proof.
  induction l; auto; cbn; lia.
Qed.

Lemma sumZ_seq_split split_len (f : nat -> Z) start len :
  (split_len <= len)%nat ->
  sumZ f (seq start len) =
  sumZ f (seq start split_len) + sumZ f (seq (start + split_len) (len - split_len)).
Proof.
  rewrite <- sumZ_app.
  rewrite <- seq_app.
  intros le.
  now replace (split_len + (len - split_len))%nat with len by lia.
Qed.

Lemma sumZ_sumZ_swap {A B} (f : A -> B -> Z) (xs : list A) (ys : list B) :
  sumZ (fun a => sumZ (f a) (ys)) xs =
  sumZ (fun b => sumZ (fun a => f a b) xs) ys.
Proof.
  revert ys.
  induction xs as [|x xs IH]; intros ys; cbn.
  - now rewrite sumZ_zero.
  - rewrite IH.
    clear IH.
    induction ys as [|y ys IH]; cbn; auto.
    rewrite <- IH.
    lia.
Qed.

Lemma All_Forall {A} (l : list A) f :
  All f l <-> Forall f l.
Proof.
  induction l.
  - split; cbn; auto.
  - split; cbn.
    + intros [fa all].
      constructor; tauto.
    + intros all.
      inversion all; tauto.
Qed.

Lemma all_incl {A} (l l' : list A) f :
  incl l l' -> All f l' -> All f l.
Proof.
  intros incl all.
  apply All_Forall.
  apply All_Forall in all.
  apply Forall_forall.
  pose proof (Forall_forall f l').
  firstorder.
Qed.

Lemma firstn_incl {A} n (l : list A) : incl (firstn n l) l.
Proof.
  unfold incl.
  intros a.
  revert l.
  induction n as [|n IH]; intros l isin; try contradiction.
  cbn in *.
  destruct l; try contradiction.
  cbn in *.
  destruct isin; try tauto.
  right.
  auto.
Qed.

Lemma skipn_incl {A} n (l : list A) : incl (skipn n l) l.
Proof.
  unfold incl.
  intros a.
  revert l.
  induction n as [|n IH]; intros l isin; auto.
  cbn in *.
  destruct l; try contradiction.
  cbn in *.
  right; auto.
Qed.

Lemma sumZ_seq_feq_rel (f g : nat -> Z) len (R : Z -> Z -> Prop) :
  Reflexive R ->
  Proper (R ==> R ==> R) Z.add ->
  (forall i, i < len -> R (f i) (g i))%nat ->
  R (sumZ f (seq 0 len)) (sumZ g (seq 0 len)).
Proof.
  intros refl proper all_same.
  revert f g all_same.
  induction len as [|len IH]; intros f g all_same; auto.
  cbn.
  rewrite 2!(sumZ_seq_n _ 1).
  apply proper.
  - apply all_same; lia.
  - apply IH.
    intros i ilt.
    now specialize (all_same (i + 1)%nat ltac:(lia)).
Qed.

Lemma sumZ_map_id {A} (f : A -> Z) l :
  sumZ f l = sumZ id (map f l).
Proof.
  induction l; cbn; auto.
  unfold id.
  now rewrite IHl.
Qed.

Lemma firstn_map {A B} (f : A -> B) n l :
  firstn n (map f l) = map f (firstn n l).
Proof.
  revert l.
  induction n; intros l; cbn; auto.
  destruct l; cbn; auto.
  apply f_equal.
  auto.
Qed.

Lemma skipn_map {A B} (f : A -> B) n l :
  skipn n (map f l) = map f (skipn n l).
Proof.
  revert l.
  induction n; intros l; cbn; auto.
  destruct l; cbn; auto.
Qed.

Lemma map_nth_alt {A B} n (l : list A) (f : A -> B) d1 d2 :
  (n < length l)%nat ->
  nth n (map f l) d1 = f (nth n l d2).
Proof.
  revert n.
  induction l as [|x xs IH]; intros n nlt; cbn in *; try lia.
  destruct n as [|n]; auto.
  apply IH.
  lia.
Qed.

Lemma sumZ_min_max {A} (f : A -> Z) l min max :
  (forall a, In a l -> min <= f a <= max) ->
  min * Z.of_nat (length l) <= sumZ f l <= max * Z.of_nat (length l).
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    lia.
  - cbn.
    unshelve epose proof (IH _) as IH.
    + intros a ain.
      apply all; right; auto.
    + specialize (all x (or_introl eq_refl)).
      lia.
Qed.

Lemma sumZ_min {A} (f : A -> Z) l min :
  (forall a, In a l -> f a >= min) ->
  min * Z.of_nat (length l) <= sumZ f l.
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    lia.
  - cbn.
    unshelve epose proof (IH _) as IH.
    + intros a ain.
      apply all; right; auto.
    + specialize (all x (or_introl eq_refl)).
      lia.
Qed.

Lemma sumZ_max {A} (f : A -> Z) l max :
  (forall a, In a l -> f a <= max) ->
  sumZ f l <= max * Z.of_nat (length l).
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    lia.
  - cbn.
    unshelve epose proof (IH _) as IH.
    + intros a ain.
      apply all; right; auto.
    + specialize (all x (or_introl eq_refl)).
      lia.
Qed.

Local Open Scope nat.
Lemma sumnat_min_max {A} (f : A -> nat) l min max :
  (forall a, In a l -> min <= f a <= max) ->
  min * length l <= sumnat f l <= max * length l.
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    lia.
  - cbn.
    unshelve epose proof (IH _) as IH.
    + intros a ain.
      apply all; right; auto.
    + specialize (all x (or_introl eq_refl)).
      lia.
Qed.

Lemma sumnat_max {A} (f : A -> nat) l max :
  (forall a, In a l -> f a <= max) ->
  sumnat f l <= max * length l.
Proof.
  intros all.
  induction l as [|x xs IH].
  - cbn.
    lia.
  - cbn.
    unshelve epose proof (IH _) as IH.
    + intros a ain.
      apply all; right; auto.
    + specialize (all x (or_introl eq_refl)).
      lia.
Qed.

Lemma list_eq_nth {A} (xs ys : list A) :
  length xs = length ys ->
  (forall i a a', nth_error xs i = Some a -> nth_error ys i = Some a' -> a = a') ->
  xs = ys.
Proof.
  revert ys.
  induction xs as [|x xs IH]; intros ys len_xs all_eq.
  - destruct ys; cbn in *; auto; lia.
  - cbn.
    destruct ys as [|y ys]; cbn in *; try lia.
    rewrite (all_eq 0 x y); cbn; auto.
    apply f_equal.
    apply IH.
    + lia.
    + intros i a b ntha nthb.
      apply all_eq with (S i); cbn; auto.
Qed.

Lemma nth_error_seq_in i start len :
  i < len ->
  nth_error (seq start len) i = Some (start + i).
Proof.
  revert i start.
  induction len as [|len IH]; intros i start ilt; try lia.
  cbn.
  destruct i as [|i]; cbn.
  - f_equal; lia.
  - rewrite IH by lia.
    f_equal; lia.
Qed.

Lemma nth_error_snoc {B} (l : list B) (x : B) :
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  rewrite nth_error_app2 by lia.
  now replace (length l - length l) with 0 by lia.
Qed.

Definition large_modulus : Z :=
32317006071311007300338913926423828248817941241140239112842009751400741706634354222619689417363569347117901737909704191754605873209195028853758986185622153212175412514901774520270235796078236248884246189477587641105928646099411723245426622522193230540919037680524235519125679715870117001058055877651038861847280257976054903569732561526167081339361799541336476559160368317896729073178384589680639671900977202194168647225871031411336429319536193471636533209717077448227988588565369208645296636077250268955505928362751121174096972998068410554359584866583291642136218231078990999448652468262416972035911852507045361090559.

Definition large_generator : Z := 2.
