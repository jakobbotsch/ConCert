From Coq Require Import Permutation.
From stdpp Require Import sorting.

Section Sorting.
  Context {A : Type}.
  Context (R : A -> A -> Prop).
  Context (H : forall x y, {R x y} + {~R x y}).

  Definition sort (l : list A) : list A :=
    @merge_sort A R H l.

  Lemma sort_Permutation l :
    Permutation (sort l) l.
  Proof. apply merge_sort_Permutation. Qed.

  Lemma Sorted_sort :
    (forall x y, R x y \/ R y x) ->
    forall l, Sorted R (sort l).
  Proof. apply Sorted_merge_sort. Qed.

  Lemma StronglySorted_sort :
    (forall x y z, R x y -> R y z -> R x z) ->
    (forall x y, R x y \/ R y x) ->
    forall l, StronglySorted R (sort l).
  Proof. apply StronglySorted_merge_sort. Qed.
End Sorting.
