(* This file provides an interface for std++'s finite maps *)

From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From stdpp Require gmap.
Require Import Monads.
Require Import BoundedN.
Require Import Automation.
Import ListNotations.

Notation FMap := gmap.gmap.

Module FMap.
  Generalizable All Variables.

  Notation empty := stdpp.base.empty.
  Notation add := stdpp.base.insert.
  Notation find := stdpp.base.lookup.
  Notation remove := stdpp.base.delete.
  Notation elements := fin_maps.map_to_list.
  Notation size := stdpp.base.size.
  Notation of_list := fin_maps.list_to_map.
  Notation union := stdpp.base.union.
  Notation alter := stdpp.base.alter.
  Notation partial_alter := stdpp.base.partial_alter.

  Definition keys {K V : Type} `{countable.Countable K} (m : FMap K V) : list K :=
    map fst (elements m).

  Definition values {K V : Type} `{countable.Countable K} (m : FMap K V) : list V :=
    map snd (elements m).

  Section Theories.
    Context {K V : Type} `{countable.Countable K}.

    Proposition of_elements_eq (m : FMap K V) :
      of_list (elements m) = m.
    Proof. apply fin_maps.list_to_map_to_list. Qed.

    Lemma find_union_None k (m1 m2 : FMap K V) :
      find k m1 = None ->
      find k m2 = None ->
      find k (union m1 m2) = None.
    Proof.
      intros find1 find2.
      apply fin_maps.lookup_union_None; auto.
    Qed.

    Lemma find_union_Some_l k v (m1 m2 : FMap K V) :
      find k m1 = Some v ->
      find k (union m1 m2) = Some v.
    Proof. apply fin_maps.lookup_union_Some_l. Qed.

    Lemma find_add (k : K) (v : V) (m : FMap K V) :
      find k (add k v m) = Some v.
    Proof. apply fin_maps.lookup_insert. Qed.

    Lemma find_add_ne (k k' : K) (v : V) (m : FMap K V) :
      k <> k' -> find k' (add k v m) = find k' m.
    Proof. apply fin_maps.lookup_insert_ne. Qed.

    Lemma find_partial_alter f k (m : FMap K V) :
      find k (partial_alter f k m) = f (find k m).
    Proof. apply fin_maps.lookup_partial_alter. Qed.

    Lemma find_partial_alter_ne f k k' (m : FMap K V) :
      k <> k' ->
      find k' (partial_alter f k m) = find k' m.
    Proof. apply fin_maps.lookup_partial_alter_ne. Qed.

    Lemma find_empty k :
      FMap.find k (FMap.empty : FMap K V) = None.
    Proof. apply fin_maps.lookup_empty. Qed.

    Lemma elements_add k v (m : FMap K V) :
      find k m = None ->
      Permutation (elements (add k v m)) ((k, v) :: elements m).
    Proof. apply fin_maps.map_to_list_insert. Qed.

    Lemma elements_empty : (elements empty : list (K * V)) = [].
    Proof. now rewrite fin_maps.map_to_list_empty. Qed.

    Lemma elements_add_empty (k : K) (v : V) :
      FMap.elements (FMap.add k v FMap.empty) = [(k, v)].
    Proof. now rewrite fin_maps.insert_empty, fin_maps.map_to_list_singleton. Qed.

    Lemma add_remove k v (m : FMap K V) :
      add k v (remove k m) = add k v m.
    Proof. apply fin_maps.insert_delete. Qed.

    Lemma add_add k v v' (m : FMap K V) :
      add k v (add k v' m) = add k v m.
    Proof. apply fin_maps.insert_insert. Qed.

    Lemma remove_add k v (m : FMap K V) :
      find k m = None ->
      remove k (add k v m) = m.
    Proof. apply fin_maps.delete_insert. Qed.

    Lemma find_remove k (m : FMap K V) :
      find k (remove k m) = None.
    Proof. apply fin_maps.lookup_delete. Qed.

    Lemma add_commute (k k' : K) (v v' : V) (m : FMap K V) :
      k <> k' ->
      FMap.add k v (FMap.add k' v' m) = FMap.add k' v' (FMap.add k v m).
    Proof. apply fin_maps.insert_commute. Qed.

    Lemma add_id k v (m : FMap K V) :
      find k m = Some v ->
      add k v m = m.
    Proof. apply fin_maps.insert_id. Qed.

    Lemma keys_already k v v' (m : FMap K V) :
      find k m = Some v ->
      Permutation (keys (add k v' m)) (keys m).
    Proof.
      revert k.
      induction m using fin_maps.map_ind; intros k find_some.
      + rewrite find_empty in find_some.
        congruence.
      + destruct (stdpp.base.decide (k = i)) as [->|].
        * rewrite fin_maps.insert_insert.
          unfold keys.
          rewrite 2!fin_maps.map_to_list_insert by auto.
          cbn.
          reflexivity.
        * rewrite find_add_ne in find_some by auto.
          specialize (IHm _ find_some).
          rewrite add_commute by auto.
          unfold keys.
          rewrite elements_add by (now rewrite find_add_ne by auto).
          setoid_rewrite elements_add at 2; auto.
          cbn.
          now rewrite IHm.
    Qed.

    Lemma ind (P : FMap K V -> Prop) :
      P empty ->
      (forall k v m, find k m = None -> P m -> P (add k v m)) ->
      forall m, P m.
    Proof. apply fin_maps.map_ind. Qed.

    Lemma size_empty : size (@FMap.empty (FMap K V) _) = 0.
    Proof. apply fin_maps.map_size_empty. Qed.

    Lemma size_add_new k v (m : FMap K V) :
      FMap.find k m = None ->
      size (FMap.add k v m) = S (size m).
    Proof. apply fin_maps.map_size_insert. Qed.

    Lemma size_add_existing k v (m : FMap K V) :
      FMap.find k m <> None ->
      size (FMap.add k v m) = size m.
    Proof.
      revert k v.
      induction m using ind; intros kadd vadd find_some.
      - rewrite find_empty in find_some.
        congruence.
      - destruct (stdpp.base.decide (k = kadd)) as [->|?].
        + rewrite add_add.
          now rewrite !size_add_new by auto.
        + rewrite add_commute by auto.
          rewrite find_add_ne in find_some by auto.
          rewrite size_add_new.
          * rewrite (IHm _ _ find_some).
            now rewrite size_add_new by auto.
          * now rewrite find_add_ne by auto.
    Qed.

    Lemma length_elements (m : FMap K V) : length (FMap.elements m) = size m.
    Proof.
      induction m using ind.
      - now rewrite size_empty, elements_empty.
      - rewrite elements_add, size_add_new by auto.
        cbn.
        now rewrite IHm.
    Qed.

    Lemma NoDup_elements (m : FMap K V) : NoDup (elements m).
    Proof. apply base.NoDup_ListNoDup. apply fin_maps.NoDup_map_to_list. Qed.

    Lemma In_elements p (m : FMap K V) :
      In p (elements m) <-> find (fst p) m = Some (snd p).
    Proof.
      destruct p as [k v].
      cbn in *.
      induction m using ind.
      - rewrite elements_empty, find_empty.
        split; easy.
      - rewrite elements_add by auto.
        destruct (stdpp.base.decide (k = k0)) as [->|?].
        + rewrite find_add.
          cbn.
          split; intros.
          * destruct H1; try congruence.
            apply IHm in H1.
            congruence.
          * left; congruence.
        + cbn.
          rewrite find_add_ne by auto.
          split; intros.
          * apply IHm.
            destruct H1; auto; congruence.
          * tauto.
    Qed.

    Lemma list_to_map_flip (m : FMap K V) l :
      Permutation (elements m) l ->
      m = of_list l.
    Proof. apply fin_maps.list_to_map_flip. Qed.
  End Theories.
End FMap.

Hint Resolve
     FMap.find_union_None
     FMap.find_union_Some_l
     FMap.find_add
     FMap.find_add_ne : core.

Instance empty_set_eq_dec : stdpp.base.EqDecision Empty_set.
Proof. decidable.solve_decision. Defined.
Program Instance empty_set_countable : countable.Countable Empty_set :=
  {| countable.encode e := 1%positive; countable.decode d := None; |}.
Solve Obligations with contradiction.
