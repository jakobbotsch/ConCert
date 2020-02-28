From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Orders.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From Coq Require Import Mergesort.
From Coq Require Program.
From RecordUpdate Require Import RecordUpdate.
Require Import Automation.
Require Import Blockchain.
Require Import BoundedN.
Require Import Containers.
From stdpp Require countable.
Require ContractMonads.
Require Import Extras.
Require Import BoardroomMath.
Require Import Monads.
Require Import Serializable.
From ConCert.Execution Require Import Sorting.

Import ListNotations.
Import RecordSetNotations.

Section BoardroomVoting.
Context `{Base : ChainBase}.
Context `(H : Z -> Z).
(*Context (verify_vote (vote : Z) (rk : Z) (jj*)
Context (modulus : Z).
Context (modulus_prime : prime modulus).

Instance zp : BoardroomAxioms Z := Zp.boardroom_axioms _ modulus_prime.
Context {generator : Generator zp}.
Context {discr_log : DiscreteLog zp generator}.

(* Allow us to automatically derive Serializable instances *)
Set Nonrecursive Elimination Schemes.

Record Setup :=
  build_setup {
    eligible_voters : FMap Address unit;
    finish_registration_by : nat;
    finish_commit_by : option nat;
    finish_vote_by : nat;
    registration_deposit : Amount;
  }.


Record VoterInfo :=
  build_voter_info {
    voter_index : nat;
    vote_hash : Z;
    public_vote : Z;
}.

Record State :=
  build_state {
    owner : Address;
    registered_voters : FMap Address VoterInfo;
    public_keys : list Z;
    setup : Setup;
    result : option nat;
  }.

Inductive Msg :=
| signup (pk : Z)
| commit_to_vote (hash : Z)
| submit_vote (v : Z) (proof : Z)
| tally_votes.

Global Instance VoterInfo_settable : Settable _ :=
  settable! build_voter_info <voter_index; vote_hash; public_vote>.

Global Instance State_settable : Settable _ :=
  settable! build_state <owner; registered_voters; public_keys; setup; result>.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance VoterInfo_serializable : Serializable VoterInfo :=
  Derive Serializable VoterInfo_rect<build_voter_info>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<signup, commit_to_vote, submit_vote, tally_votes>.

Class VoteProofScheme :=
  build_vote_proof_scheme {
    make_vote_proof (pks : list Z) (index : nat)
                    (secret_key : Z) (secret_vote : bool) : Z;
    verify_vote (pks : list Z) (index : nat) (public_vote proof : Z) : bool;

    (*
    verify_vote_spec pks index pv proof :
      verify_vote pks index pv proof = true ->
      exists sk sv, proof = make_vote_proof pks index sk sv;
*)
  }.

Context `{VoteProofScheme}.

Local Open Scope Z.

Import ContractMonads.

Definition init : ContractIniter Setup State :=
  do owner <- lift caller_addr;
  do setup <- deployment_setup;
  do lift (if finish_registration_by setup <? finish_vote_by setup then Some tt else None)%nat;
  accept_deployment
    {| owner := owner;
       registered_voters := FMap.empty;
       public_keys := [];
       setup := setup;
       result := None; |}.

Definition receive : ContractReceiver State Msg State :=
  do state <- my_state;
  do caller <- lift caller_addr;
  do cur_slot <- lift current_slot;
  do msg <- call_msg >>= lift;
  match msg with
  | signup pk =>
    do lift (if finish_registration_by (setup state) <? cur_slot then None else Some tt)%nat;
    do lift (if FMap.find caller (eligible_voters (setup state)) then Some tt else None);
    do lift (if FMap.find caller (registered_voters state) then None else Some tt);
    do amt <- lift call_amount;
    do lift (if amt =? (registration_deposit (setup state)) then Some tt else None);
    do lift (if Z.of_nat (length (public_keys state)) <? modulus - 2 then Some tt else None);
    let index := length (public_keys state) in
    let inf := {| voter_index := index;
                  vote_hash := 0;
                  public_vote := 0; |} in
    let new_state := state<|registered_voters ::= FMap.add caller inf|>
                          <|public_keys ::= fun l => l ++ [pk]|> in
    accept_call new_state

  | commit_to_vote hash =>
    do commit_by <- lift (finish_commit_by (setup state));
    do lift (if commit_by <? cur_slot then None else Some tt)%nat;
    do inf <- lift (FMap.find caller (registered_voters state));
    let inf := inf<|vote_hash := hash|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | submit_vote v proof =>
    do lift (if finish_vote_by (setup state) <? cur_slot then None else Some tt)%nat;
    do inf <- lift (FMap.find caller (registered_voters state));
    do lift (if finish_commit_by (setup state) then
               if H v =? vote_hash inf then Some tt else None
             else
               Some tt);
    do lift (if verify_vote (public_keys state) (voter_index inf) v proof then Some tt else None);
    let inf := inf<|public_vote := v|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | tally_votes =>
    do lift (if cur_slot <? finish_vote_by (setup state) then None else Some tt)%nat;
    do lift (match result state with | Some _ => None | None => Some tt end);
    let voters := FMap.values (registered_voters state) in
    do lift (if existsb (fun vi => public_vote vi =? 0) voters then None else Some tt);
    let votes := map public_vote voters in
    do res <- lift (bruteforce_tally votes);
    accept_call (state<|result := Some res|>)
  end.

Definition boardroom_voting : Contract Setup Msg State.
Proof with cbn -[Nat.ltb].
  refine (build_contract init receive _ _).
  - repeat intro; subst.
    cbn -[Nat.ltb].
    destruct (_ <? _)%nat; auto.
  - intros c1 c2 ceq ctx ? <- state ? <- msg ? <-.
    unfold run_contract_receiver...
    destruct msg as [msg|]; [|congruence]...
    destruct msg.
    + rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (FMap.find _ _); auto.
      destruct (FMap.find _ _); auto.
      destruct (_ =? _)%Z; auto.
      destruct (_ <? _); auto.
    + destruct (finish_commit_by _); auto.
      rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (FMap.find _ _); auto.
    + rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (FMap.find _ _); auto.
      destruct (finish_commit_by _); [destruct (_ =? _); auto|].
      all: destruct (verify_vote _ _ _ _); auto.
    + rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (result _); auto.
      destruct (existsb _ _); auto.
      destruct (bruteforce_tally _); auto.
Defined.

Definition make_signup_msg (sk : Z) : Msg :=
  signup (compute_public_key sk).

Definition make_commit_msg (pks : list Z) (my_index : nat) (sk : Z) (sv : bool) : Msg :=
  commit_to_vote (H (compute_public_vote (reconstructed_key pks my_index) sk sv)).

Definition make_vote_msg (pks : list Z) (my_index : nat) (sk : Z) (sv : bool) : Msg :=
  submit_vote (compute_public_vote (reconstructed_key pks my_index) sk sv)
              (make_vote_proof pks my_index sk sv).

Section Theories.

Fixpoint CallAssumptions
         (pks : list Z)
         (index : Address -> nat)
         (sks : Address -> Z)
         (svs : Address -> bool)
         (calls : list (ContractCallInfo Msg)) : Prop :=
  match calls with
  | call :: calls =>
    let caller := Blockchain.call_from call in
    match Blockchain.call_msg call with
    | Some (signup pk as m) => m = make_signup_msg (sks caller)
    | Some (submit_vote _ _ as m) =>
      m = make_vote_msg pks (index caller) (sks caller) (svs caller)
    | _ => True
    end /\ CallAssumptions pks index sks svs calls
  | [] => True
  end.

Definition IndexAssumptions (voters : FMap Address VoterInfo) index : Prop :=
  forall addr inf,
    FMap.find addr voters = Some inf ->
    voter_index inf = index addr.

Definition num_signups (calls : list (ContractCallInfo Msg)) :=
  sumnat (fun cc => match Blockchain.call_msg cc with
                    | Some (signup _) => 1
                    | _ => 0
                    end)%nat calls.

Lemma voter_info_update (voters : FMap Address VoterInfo) index addr vi_before vi_after :
  IndexAssumptions (FMap.add addr vi_after voters) index ->
  FMap.find addr voters = Some vi_before ->
  voter_index vi_before = voter_index vi_after ->
  IndexAssumptions voters index.
Proof.
  unfold IndexAssumptions in *.
  intros index_assum inf index_same addr' inf' find_addr.
  destruct (address_eqb_spec addr addr') as [->|].
  - specialize (index_assum addr' vi_after).
    replace inf' with vi_before in * by congruence.
    rewrite index_same.
    apply index_assum.
    now rewrite FMap.find_add.
  - apply index_assum.
    rewrite FMap.find_add_ne by auto; congruence.
Qed.

Opaque zp.
Local Open Scope nat.

(*
Definition WellIndexed (voters : list (Address * VoterInfo)) : Prop :=
  Permutation (map (fun '(_, vinf) => voter_index vinf) voters)
              (seq 0 (length voters)).

Arguments WellIndexed !voters.

Definition find_voter voters i : list (Address * VoterInfo) :=
  match find (fun '(k, vinf) => voter_index vinf =? i) voters with
  | Some x => [x]
  | None => []
  end.

Arguments find_voter !voters.

Instance WellIndexed_iff_proper :
  Proper (Permutation ==> iff) WellIndexed.
Proof.
  unfold WellIndexed.
  intros l l' perm.
  now rewrite (Permutation_map _ perm), (Permutation_length perm).
Qed.

Lemma WellIndexed_ind (P : list (Address * VoterInfo) -> Prop) :
  P [] ->
  (forall l x,
      WellIndexed l ->
      voter_index (snd x) = length l ->
      P l ->
      P (l ++ [x])) ->
  forall l, WellIndexed l -> P l.
Proof.
  intros nil_case cons_case l.
  unfold WellIndexed.
  set (n := length l) at 0.
  specialize (eq_refl : length l = n).
  clearbody n.
  revert l.
  induction n; intros l eq perm.
  - apply length_zero_iff_nil in eq.
    subst l; auto.
  - rewrite eq in *.
    (*
    pose proof (seq_NoDup (S n) 0).
    pose proof (Permutation_NoDup (Permutation_sym perm) H1).
    replace (S n) with (n + 1) in * by lia.
    rewrite seq_app in *.
    cbn in *.
    assert (incl (seq 0 n) (seq 0 n ++ [n])).
    { apply incl_appl, incl_refl. }
    pose proof (NoDup_incl_reorganize _ _ (seq_NoDup n 0) H3).



NoDup_incl_reorganize:
  forall (A : Type) (l l' : list A),
  NoDup l' -> incl l' l -> exists suf : list A, Permutation (l' ++ suf) l
*)

    replace (S n) with (n + 1) in perm by lia.
    rewrite seq_app in perm.
    cbn in perm.
    assert (In n (seq 0 n ++ [n])).
    { apply in_app_iff; right; cbn; auto. }
    rewrite <- perm in H1.
    apply In_nth_error in H1.
    destruct H1 as [index nth_index].
    assert (Permutation (map (fun '(_, vinf) => voter_index vinf)
                             (firstn index l ++ skipn (S index) l))
                        (seq 0 n)).
    {

      pose proof (seq_NoDup 0 n).
      apply Permutation_NoDup'
    assert (length (firstn index l ++ skipn (S index) l) = n).
    {
      rewrite app_length, firstn_length, skipn_length.
      assert (index < length l).
      {
        replace (length l) with (length (map (fun '(_, vinf) => voter_index vinf) l))
          by (now rewrite map_length).
        apply nth_error_Some.
        congruence.
      }
      lia.
    }

    specialize (IHn (firstn index l ++ skipn (S index) l) ltac:(auto)).
    rewrite H1 in IHn.
    + rewrite app_length, firstn_length, skipn_length.
      assert (index < length l).
      {
        replace (length l) with (length (map (fun '(_, vinf) => voter_index vinf) l))
          by (now rewrite map_length).
        apply nth_error_Some.
        congruence.
      }
      lia.
    +
    rewrite min_l by lia.
      lia.
    rewrite eq in IHn.
    replace (index + (S n - S index)) with n in IHn by lia.
    specialize (IHn eq_refl).
    replace (Init.Nat.min index (length l)) with (length l) in IHn by lia.
nth_error_Some: forall (A : Type) (l : list A) (n : nat), nth_error l n <> None <-> n < length l
    apply in_map_iff in H1.
    induction l as [|x xs IH]; auto.

  induction (seq 0 (length l)) eqn:seq using List.rev_ind; intros perm.
  - symmetry in perm.
    apply Permutation_nil in perm.
    apply map_eq_nil in perm.
    subst l.
    auto.
  - cbn in wi.
    assert (In start (start :: seq (S start) len)) by (left; auto).
    rewrite <- wi in H1.
    apply in_map_iff in H1.
    destruct H1 as [[k v] ?].

  revert l wi.
  generalize 0.
  induction l using List.rev_ind; intros wil; auto.

  apply (app_case l x).
  apply app_case.
  apply IHl.


Lemma find_voter_perm voters voters' i :
  WellIndexed voters ->
  Permutation voters voters' ->
  find_voter voters i = find_voter voters' i.
Proof.
  intros wellind perm.
  induction perm.
  - auto.
  - unfold find_voter.
    cbn.
    destruct x as [k v].
    destruct (Nat.eqb_spec (voter_index v) i); auto.
    apply IHperm; auto.
    unfold WellIndexed in wellind.
    unfold
  unfold find_voter.
*)

Definition ordered_voters_list (voters : list (Address * VoterInfo))
  : list (Address * VoterInfo) :=
  flat_map (fun i =>
              match find (fun '(k, vinf) => voter_index vinf =? i) voters with
              | Some x => [x]
              | None => []
              end) (seq 0 (length voters)).

Definition ordered_voters
           (voters : FMap Address VoterInfo) : list (Address * VoterInfo) :=
  ordered_voters_list (FMap.elements voters).

Lemma not_in_later (k : Address) (v : VoterInfo) f start count :
  (forall i, start <= i < start + count -> ~ In (k, v) (f i)) ->
  ~ In (k, v) (flat_map f (seq start count)).
Proof.
  intros all_notin isin.
  rewrite flat_map_concat_map in isin.
  apply In_concat in isin.
  destruct isin as [insub [isinsub ?]].
  apply in_map_iff in isinsub.
  destruct isinsub as [i [eq ?]].
  apply in_seq in H2.
  specialize (all_notin i H2).
  congruence.
Qed.

Lemma NoDup_ordered_voters_indices voters :
  NoDup (map (fun '(_, vinf) => voter_index vinf) (ordered_voters voters)).
Proof.
  unfold ordered_voters, ordered_voters_list.
  assert (forall {A} (x : A), NoDup [x]) by (constructor; cbn; try constructor; intuition).
  rewrite flat_map_concat_map.
  rewrite concat_map.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  apply NoDup_flat_map_disjoint.
  - intros; destruct (find _ _); cbn; auto; constructor.
  - intros b b' bneq bin b'in c inc.
    destruct (find _ _) eqn:f1, (find (fun '(_, vinf) => voter_index vinf =? b') _) eqn:f2;
      repeat
        match goal with
        | [H: find _ _ = _ |- _] => try apply find_some in H;
                                      try apply find_none in H
        end;
      cbn in *.
    + destruct p as [k v], p0 as [k' v'].
      destruct f1 as [_ f1], f2 as [_ f2].
      apply Nat.eqb_eq in f1.
      apply Nat.eqb_eq in f2.
      intros.
      intuition.
    + auto.
    + auto.
    + auto.
  - apply seq_NoDup.
Qed.

Lemma NoDup_ordered_voters voters :
  NoDup (ordered_voters voters).
Proof.
  apply (NoDup_map_inv (fun '(_, vinf) => voter_index vinf)).
  apply NoDup_ordered_voters_indices.
Qed.

Lemma ordered_voters_list_perm {voters voters' : list (Address * VoterInfo)} :
  Permutation voters voters' ->
  NoDup (map (fun '(k, vinf) => voter_index vinf) voters) ->
  ordered_voters_list voters = ordered_voters_list voters'.
Proof.
  intros perm nodup.
  unfold ordered_voters_list.
  rewrite <- (Permutation_length perm).
  induction (seq 0 (length (voters))) as [|i tl IH]; auto.
  cbn.
  rewrite IH.
  f_equal.
  clear IH.
  induction perm.
  - auto.
  - destruct x as [k v]; cbn.
    destruct (Nat.eqb_spec (voter_index v) i); auto.
    apply IHperm.
    cbn in nodup.
    inversion nodup; auto.
  - cbn in *.
    destruct x as [k v], y as [k' v'].
    destruct (Nat.eqb_spec (voter_index v') i), (Nat.eqb_spec (voter_index v) i); auto.
    inversion_clear nodup; cbn in *.
    contradiction H1.
    left; congruence.
  - rewrite IHperm1 by auto.
    apply IHperm2.
    now rewrite <- perm1.
Qed.

Lemma ordered_voters_list_index_bound l :
  All (fun '(_, vinf) => voter_index vinf < length l) (ordered_voters_list l).
Proof.
  unfold ordered_voters_list.
  apply All_Forall.
  apply Forall_forall.
  intros [k v].
  rewrite flat_map_concat_map.
  intros isin.
  apply In_concat in isin.
  destruct isin as [? [? ?]].
  apply in_map_iff in H1.
  destruct H1 as [? [? ?]].
  destruct (find _ _) eqn:find; cbn.
  - subst x.
    cbn in *.
    destruct H2; try easy.
    apply find_some in find.
    destruct find.
    destruct p as [k' v'].
    inversion H1; subst.
    apply Nat.eqb_eq in H4.
    apply in_seq in H3.
    lia.
  - subst x; cbn in *; easy.
Qed.

Lemma find_ordered_voters_list_none l :
  find (fun '(_, vinf) => voter_index vinf =? length l) (ordered_voters_list l) = None.
Proof.
  pose proof (ordered_voters_list_index_bound l).
  induction (ordered_voters_list l); cbn; auto.
  cbn in H1.
  destruct H1, a.
  destruct (Nat.eqb_spec (voter_index v) (length l)); [lia|].
  auto.
Qed.

Lemma ordered_voters_add addr (voter : VoterInfo) (voters : FMap Address VoterInfo) :
  FMap.find addr voters = None ->
  voter_index voter = FMap.size voters ->
  Permutation (ordered_voters voters) (FMap.elements voters) ->
  Permutation (ordered_voters (FMap.add addr voter voters))
              (FMap.elements (FMap.add addr voter voters)).
Proof.
  intros find_none index is_perm.
  unfold ordered_voters.
  assert (Permutation (FMap.elements (FMap.add addr voter voters))
                      (FMap.elements voters ++ [(addr, voter)]))
    by (rewrite FMap.elements_add by auto; perm_simplify).
  rewrite (ordered_voters_list_perm H1); cycle 1.
  {
    rewrite FMap.elements_add by auto.
    rewrite <- is_perm.
    cbn.
    constructor.
    - intros isin.
      apply in_map_iff in isin.
      destruct isin as [? [? ?]].
      destruct x as [k v].
      unfold ordered_voters in H3.
      pose proof (ordered_voters_list_index_bound (FMap.elements voters)).
      apply All_Forall in H4.
      pose proof (proj1 (Forall_forall _ _) H4 _ H3).
      cbn in *.
      rewrite FMap.length_elements in H5.
      lia.
    - apply NoDup_ordered_voters_indices.
  }
  rewrite FMap.elements_add by auto.
  unfold ordered_voters_list.
  rewrite flat_map_concat_map, app_length.
  cbn.
  rewrite seq_app, map_app, concat_app.
  cbn.
  rewrite find_app_last; cycle 1.
  {
    apply (find_none_perm _ _ _ is_perm).
    unfold ordered_voters.
    apply find_ordered_voters_list_none.
  }
  rewrite app_nil_r.
  cbn.
  rewrite <- FMap.length_elements in index.
  rewrite index, Nat.eqb_refl.
  perm_simplify.
  rewrite (map_ext_in _ (fun i => match find (fun '(_, vinf) => voter_index vinf =? i)
                                             (FMap.elements voters) with
                                  | Some x => [x]
                                  | None => []
                                  end)); cycle 1.
  {
    intros i iin.
    symmetry.
    destruct (find _ _) eqn:find.
    - now rewrite find_app_first with (a := p) by auto.
    - rewrite find_app_last by auto.
      cbn.
      apply in_seq in iin.
      destruct (Nat.eqb_spec (voter_index voter) i); auto; lia.
  }
  rewrite <- flat_map_concat_map.
  apply is_perm.
Qed.

Lemma find_NoDup_perm_voters addr vnew (voters : FMap Address VoterInfo) index :
  NoDup (map (fun '(_, v) => voter_index v) (FMap.elements (FMap.add addr vnew voters))) ->
  find (fun '(_, v) => voter_index v =? index) (FMap.elements (FMap.add addr vnew voters)) =
  find (fun '(_, v) => voter_index v =? index)
       ((addr, vnew) :: FMap.elements (FMap.remove addr voters)).
Proof.
  intros nodup.
  rewrite <- FMap.add_remove in *.
  unshelve epose proof (FMap.elements_add addr vnew (FMap.remove addr voters) _) as perm.
  { apply FMap.find_remove. }
  induction perm.
  - auto.
  - cbn.
    destruct x as [k v].
    destruct (Nat.eqb_spec (voter_index v) index); auto.
    apply IHperm.
    cbn in nodup; inversion nodup; auto.
  - cbn.
    destruct x as [k v], y as [k' v'].
    destruct (Nat.eqb_spec (voter_index v) index),
             (Nat.eqb_spec (voter_index v') index); cbn in *; auto.
    inversion nodup; cbn in *.
    intuition.
  - rewrite IHperm1, IHperm2; auto.
    now rewrite <- perm1.
Qed.

Lemma find_NoDup_elements k v (voters : FMap Address VoterInfo) :
  In (k, v) (FMap.elements voters) ->
  NoDup (map (fun '(_, v) => voter_index v) (FMap.elements voters)) ->
  find (fun '(_, v') => voter_index v' =? voter_index v) (FMap.elements voters) =
  Some (k, v).
Proof.
  intros isin nodup.
  induction (FMap.elements voters) as [|[k' v'] xs IH]; cbn in *; auto; try contradiction.
  inversion nodup; subst.
  destruct isin as [eq|isin].
  - inversion eq; subst; clear eq.
    now rewrite Nat.eqb_refl.
  - destruct (Nat.eqb_spec (voter_index v') (voter_index v)); auto.
    specialize (IH isin H4).
    contradiction H3.
    rewrite e.
    clear -isin.
    induction xs as [|[k' v''] xs IH]; auto.
    cbn in *.
    destruct isin as [eq|isin]; [inversion eq; subst; cbn|]; tauto.
Qed.

Lemma ordered_voters_modify voters addr vold vnew :
  FMap.find addr voters = Some vold ->
  voter_index vold = voter_index vnew ->
  Permutation (ordered_voters voters) (FMap.elements voters) ->
  Permutation (ordered_voters (FMap.add addr vnew voters))
              (FMap.elements (FMap.add addr vnew voters)).
Proof.
  intros find_some index perm.
  unfold ordered_voters.
  apply (NoDup_Permutation (NoDup_ordered_voters (FMap.add addr vnew voters))
                           (FMap.NoDup_elements (FMap.add addr vnew voters))).
  intros [k v].
  unfold ordered_voters, ordered_voters_list.
  rewrite FMap.length_elements, FMap.size_add_existing, <- FMap.length_elements by congruence.
  split.
  - intros isin.
    rewrite flat_map_concat_map in isin.
    apply In_concat in isin.
    destruct isin as [? [? ?]].
    apply in_map_iff in H1.
    destruct H1 as [? [? ?]].
    destruct (find _ _) eqn:find.
    + subst.
      apply List.find_some in find.
      destruct find.
      destruct p as [k' v'].
      cbn in H2.
      apply Nat.eqb_eq in H4.
      destruct H2; [|easy].
      now inversion H2; subst.
    + subst; cbn in *; easy.
  - intros isin.
    rewrite flat_map_concat_map.
    apply In_concat.
    exists [(k, v)].
    split; cbn; auto.
    apply in_map_iff.
    exists (voter_index v).
    pose proof (NoDup_ordered_voters_indices voters).
    rewrite perm in H1.
    pose proof (FMap.NoDup_elements_modify addr vold vnew _ _ find_some index H1).
    rewrite find_NoDup_perm_voters by auto.
    rewrite <- FMap.add_remove in isin, H2.
    rewrite FMap.elements_add in isin, H2 by auto.
    cbn in isin.
    destruct isin as [eq|isin].
    + cbn.
      inversion eq; subst.
      rewrite Nat.eqb_refl.
      split; auto.
      apply in_seq.
      split; [lia|].
      cbn.
      rewrite <- index.
      pose proof (proj2 (FMap.In_elements k vold _) find_some) as isin.
      rewrite <- perm in isin.
      pose proof (ordered_voters_list_index_bound (FMap.elements voters)) as allbound.
      apply All_Forall in allbound.
      rewrite Forall_forall in allbound.
      specialize (allbound _ isin).
      cbn in allbound.
      lia.
    + cbn in *.
      destruct (Nat.eqb_spec (voter_index vnew) (voter_index v)).
      * inversion H2; subst.
        exfalso.
        apply H5.
        rewrite e.
        clear -isin.
        induction (FMap.elements (FMap.remove addr voters)); cbn in *; try easy.
        destruct a.
        destruct isin as [eq|isin]; [inversion eq; subst|]; tauto.
      * inversion H2; subst.
        rewrite (find_NoDup_elements k) by auto.
        split; auto.
        apply in_seq.
        split; [lia|].
        cbn.
        apply FMap.In_elements_remove in isin.
      rewrite <- perm in isin.
      pose proof (ordered_voters_list_index_bound (FMap.elements voters)) as allbound.
      apply All_Forall in allbound.
      rewrite Forall_forall in allbound.
      now specialize (allbound _ isin).
Qed.

(*
Lemma nth_ordered_voters k v voters :
  FMap.find k voters = Some v ->
  nth_error (ordered_voters voters) (voter_index v) = Some (k, v).
Proof.
*)

(*
Lemma bruteforce_correct
      (voters : FMap Address VoterInfo)
      (sks : Address -> Z)
      (svs : Address -> bool)
      (pks : list Z) :
  Permutation (ordered_voters voters) (FMap.elements voters) ->
  (forall addr inf,
      FMap.find addr voters = Some inf ->
      voter_index inf < length pks /\
      nth (voter_index inf) pks 0%Z = compute_public_key (sks addr) /\
      public_vote inf = compute_public_vote (reconstructed_key pks (voter_index inf))
                                            (sks addr)
                                            (svs addr)) ->
  bruteforce_tally (map public_vote (FMap.values voters)) =
  Some (sumnat (fun party => if svs party then 1 else 0) (FMap.keys voters)).
Proof.
  intros perm all.
  set (geti i := nth_error (ordered_voters voters) i).
  set (sksi i := match geti i with
                 | Some (k, _) => sks k
                 | None => 0%Z
                 end).
  set (svsi i := match geti i with
                 | Some (k, _) => svs k
                 | None => false
                 end).
  assert (Permutation
            (map public_vote (FMap.values voters))
            (map (fun i => compute_public_vote
                             (reconstructed_key pks i)
                             (sksi i)
                             (svsi i))
                 (seq 0 (FMap.size voters)))).
  {
    unfold FMap.values.
    rewrite <- perm.
    unfold ordered_voters, ordered_voters_list in geti |- *.
    rewrite <- FMap.length_elements.
    revert geti sksi svsi.
    generalize 0.
    induction (length (FMap.elements voters)) as [|n IH]; [easy|].
    intros i geti sksi svsi.
    cbn.
    destruct (find _ _) eqn:find.
    - apply find_some in find.
      destruct find.
      destruct p as [k v].
      apply Nat.eqb_eq in H2.
      cbn.
      apply FMap.In_elements in H1.
      pose proof (all _ _ H1).
      destruct H3 as [? [? ->]].
      rewrite H2.
      replace (sksi i) with (sks k); cycle 1.
      + unset_all; subst.
        cbn.
        rewrite (find_NoDup_elements k v).
        cbn.
        unfold sksi, geti.
        rewrite flat_map_concat_map.
        cbn.
      unfold sksi, svsi, geti.
    generalize 0.
    induction (
  unfold FMap.keys, FMap.values.
  rewrite <- perm.
  rewrite sumnat_map.
  set (geti i := nth_error (ordered_voters voters) i).
  set (sksi i := match geti i with
                 | Some (k, _) => sks k
                 | None => 0%Z
                 end).
  set (svsi i := match geti i with
                 | Some (k, _) => svs k
                 | None => false
                 end).
  unshelve epose proof (bruteforce_tally_correct sksi pks svsi _ _ (length pks) _ _ _ _);
    cycle 2.
  - admit.
  - admit.
  - reflexivity.
  - reflexivity.
  -
  rewrite sumnat_map, map_map.
  unfold bruteforce_tally.
  rewrite <- perm.
  rewrite map_length.
  rewrite <- perm.
  apply bruteforce_tally_correct.
  rewrite map_map.
  rewrite (map_ext_in _ (fun '(_, v) => public_vote (
  unfold FMap.keys, FMap.values in *.
  set (parties := map (fun '(k, v) => (sks k, nth (voter_index v) pks 0%Z, svs k, public_vote v))
                      (FMap.elements voters)).
         (forall (addr : Address) (inf : VoterInfo),
          FMap.find addr (registered_voters prev_state) = Some inf ->
          voter_index inf < length (public_keys prev_state) /\
          nth (voter_index inf) (public_keys prev_state) 0%Z = compute_public_key (sks addr) /\
          (public_vote inf = 0%Z \/
           public_vote inf =
           compute_public_vote (reconstructed_key pks (voter_index inf)) (sks addr) (svs addr)))) /\

Definition voter_by_index (m : FMap Address VoterInfo) i : option (Address * VoterInfo) :=
  find (fun '(_, v) => voter_index v =? i) (FMap.elements m).
*)

Definition lookup_public_key (m : FMap Address VoterInfo) pks addr : option Z :=
  do x <- FMap.find addr m;
  nth_error pks (voter_index x).

Lemma nth_error_snoc {B} (l : list B) (x : B) :
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  rewrite nth_error_app2 by lia.
  now replace (length l - length l) with 0 by lia.
Qed.

Lemma map_option_ext_in {B C} (f g : B -> option C) (l : list B) :
  (forall b, In b l -> f b = g b) ->
  map_option f l = map_option g l.
Proof.
  revert f g.
  induction l as [|b bs IH]; cbn; intros; try tauto.
  rewrite H1 by intuition.
  now rewrite (IH f g) by auto.
Qed.

Lemma in_notin {A} k k' (l : list A) :
  In k l -> ~In k' l -> k <> k'.
Proof.
  intros isin notin.
  induction l.
  - cbn in isin; congruence.
  - cbn in *.
    intuition.
Qed.

Lemma map_option_public_keys_add k v (m : FMap Address VoterInfo) pks pk ovs :
  voter_index v = length pks ->
  map_option (lookup_public_key m pks) ovs = pks ->
  map_option (lookup_public_key (FMap.add k v m) (pks ++ [pk])) (ovs ++ [k]) =
  pks ++ [pk].
Proof.
  intros index prev_map.
  rewrite map_option_app.
  cbn.
  rewrite FMap.find_add, index, nth_error_snoc.
  f_equal.
  rewrite <- prev_map.
  clear prev_map.
  Admitted.

Lemma map_option_public_keys_modify k vold vnew (m : FMap Address VoterInfo) pks ovs :
  voter_index vold = voter_index vnew ->
  map_option (lookup_public_key m pks) ovs = pks ->
  map_option (lookup_public_key (FMap.add k vnew m) pks) ovs = pks.
Proof.
  Admitted.

  (*
  rewrite map_option_ext_in with (g := lookup_public_key m pks); cycle 1.
  {
    intros b bin.
    unfold lookup_public_key.
    pose proof (in_notin _ _ _ bin nin).
    rewrite

  from_other : ctx_from ctx <> ctx_contract_address ctx
  facts : CallFacts chain ctx prev_state
  ovs : list Address
  H1 : map_option (lookup_public_key (registered_voters prev_state) (public_keys prev_state))
         ovs = public_keys prev_state
  intime : Blockchain.current_slot chain <= finish_registration_by (setup prev_state)
  u : unit
  new : FMap.find (ctx_from ctx) (registered_voters prev_state) = None
  tag : Please reestablish the invariant after a nonrecursive call
  signup_assum : signup pk = make_signup_msg (sks (ctx_from ctx))
  call_assum : CallAssumptions pks index sks svs prev_inc_calls
  index_assum : IndexAssumptions
                  (FMap.add (ctx_from ctx)
                     {|
                     voter_index := length (public_keys prev_state);
                     vote_hash := 0;
                     public_vote := 0 |} (registered_voters prev_state)) index
  pks_assum : firstn (length (public_keys prev_state) + length [pk]) pks =
              public_keys prev_state ++ [pk]
  ============================
  map_option
    (lookup_public_key
       (FMap.add (ctx_from ctx)
          {| voter_index := length (public_keys prev_state); vote_hash := 0; public_vote := 0 |}
          (registered_voters prev_state)) (public_keys prev_state ++ [pk]))
    (ovs ++ [ctx_from ctx]) = public_keys prev_state ++ [pk]
*)

Lemma length_map_option {A B} (f : A -> option B) l :
  length (map_option f l) <= length l.
Proof.
  induction l as [|x xs IH]; cbn; try lia.
  destruct (f x); cbn in *; try lia.
Qed.

Lemma map_option_all_some {A B} (f : A -> option B) l res :
  length res = length l ->
  map_option f l = res ->
  All (fun a => f a <> None) l.
Proof.
  revert l.
  induction res as [|r rs IH]; intros l len_res map_opt.
  - cbn in len_res.
    symmetry in len_res.
    destruct l; cbn in *; auto; lia.
  - cbn in *.
    destruct l as [|x xs]; cbn in *; try lia.
    destruct (f x).
    + split; auto.
      apply IH; auto.
      congruence.
    + pose proof (length_map_option f xs).
      assert (length (map_option f xs) = length (r :: rs)) by congruence.
      cbn in *.
      lia.
Qed.

(*
Lemma bruteforce_correct voters pks platonic_pks ovs sks svs n :
  Permutation ovs (FMap.elements voters) ->
  map_option (fun '(_, v) => public_key v) ovs = pks ->
  firstn (length pks) platonic_pks = pks ->
  (forall addr inf,
      FMap.find addr voters = Some inf ->
      voter_index inf < length pks ->
      nth_error pks (voter_index inf) = Some (compute_public_key (sks addr)) /\
      (public_vote inf = 0%Z \/
       public_vote inf = compute_public_vote (reconstructed_key platonic_pks (voter_index inf))
                                             (sks addr)
                                             (svs addr))) ->
  existsb (fun vi => (public_vote vi =? 0)%Z) (FMap.values voters) = false ->
  bruteforce_tally (map public_vote (FMap.values (voters))) = Some n ->
  n = sumnat (fun party => if svs party then 1 else 0)
             (FMap.keys voters).
Proof.
  intros map_public_keys pks_eq addrs all_pvs bruteforce_eq.
  set (sksi i := match nth_error ovs i with
                 | Some a => sks a
                 | None => 0%Z
                 end).
  set (svsi i := match nth_error ovs i with
                 | Some a => svs a
                 | None => false
                 end).
  pose proof (map_option_all_some (fun addr => lookup_public_key voters pks addr)
                                  ovs pks ltac:(auto) ltac:(auto)).
  assert (Permutation (map public_vote (FMap.values voters))
                      (map (fun i =>
                              compute_public_vote (reconstructed_key pks i)
                                                  (sksi i)
                                                  (svsi i))
                           (seq 0 (length ovs)))).
  {
    admit.
    (*
    generalize 0 as start.
    clear -H1 map_public_keys pks_eq.
    revert pks sksi svsi H1 pks_eq map_public_keys.
    induction ovs as [|ov ovstl IH] at 3 4 5 6; intros pks sksi svsi all map_opt len_ovs start.
    - admit.
    - cbn in all.
      cbn.
     *)
  }
  erewrite bruteforce_tally_correct with (sks0 := sksi)
                                         (svs0 := svsi)
                                         (pks0 := pks)
                                         (count := length pks).
  - intros.
    inversion_clear H3.
    clear.




(*
  prev_inc_calls : list (ContractCallInfo Msg)
  prev_out_txs : list Tx
  new_state : State
  new_acts : list ActionBody
  from_other : ctx_from ctx <> ctx_contract_address ctx
  facts : CallFacts chain ctx prev_state
  ovs : list Address
  ovs_IH : map_option
             (lookup_public_key (registered_voters prev_state) (public_keys prev_state)) ovs =
           public_keys prev_state
  IH : forall (addr : Address) (inf : VoterInfo),
       FMap.find addr (registered_voters prev_state) = Some inf ->
       voter_index inf < length (public_keys prev_state) /\
       nth (voter_index inf) (public_keys prev_state) 0%Z = compute_public_key (sks addr) /\
       (public_vote inf = 0%Z \/
        public_vote inf =
        compute_public_vote (reconstructed_key pks (voter_index inf)) (sks addr) (svs addr))
  intime : finish_vote_by (setup prev_state) <= Blockchain.current_slot chain
  all_voted : existsb (fun vi : VoterInfo => (public_vote vi =? 0)%Z)
                (FMap.values (registered_voters prev_state)) = false
  n : nat
  bruteforce : bruteforce_tally (map public_vote (FMap.values (registered_voters prev_state))) =
               Some n
  tag : Please reestablish the invariant after a nonrecursive call
  call_assum : CallAssumptions pks index sks svs prev_inc_calls
  index_assum : IndexAssumptions (registered_voters prev_state) index
  pks_assum : firstn (length (public_keys prev_state)) pks = public_keys prev_state
  ============================
  n =
  sumnat (fun party : Address => if svs party then 1 else 0)
    (FMap.keys (registered_voters prev_state))
*)

*)
Lemma no_outgoing bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
  outgoing_acts bstate caddr = [].
Proof.
  contract_induction; intros; cbn -[Nat.ltb] in *; auto.
  - now inversion IH.
  - destruct msg as [msg|]; cbn -[Nat.ltb] in *; try congruence.
    destruct msg.
    + destruct (_ <? _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (_ =? _)%Z; cbn in *; try congruence.
      destruct (_ <? _)%Z; cbn in *; try congruence.
      now inversion_clear receive_some.
    + destruct (finish_commit_by _); cbn -[Nat.ltb] in *; try congruence.
      destruct (_ <? _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      now inversion_clear receive_some.
    + destruct (_ <? _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (if finish_commit_by (setup prev_state)
                      then if (H v =? vote_hash v0)%Z then Some tt else None
                      else Some tt); cbn in *; try congruence.
      destruct (verify_vote _ _ _ _); cbn in *; try congruence.
      now inversion_clear receive_some.
    + destruct (_ <? _); cbn in *; try congruence.
      destruct (result _); cbn in *; try congruence.
      destruct (existsb _ _); cbn in *; try congruence.
      destruct (bruteforce_tally _); cbn in *; try congruence.
      now inversion_clear receive_some.
  - inversion IH.
  - subst out_queue.
    now apply Permutation_nil in perm.
  - [AddBlockFacts]: exact (fun _ _ _ _ _ _ => True).
    [DeployFacts]: exact (fun _ _ => True).
    [CallFacts]: exact (fun _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.

Lemma Permutation_modify k vold vnew (m : FMap Address VoterInfo) :
  FMap.find k m = Some vold ->
  voter_index vold = voter_index vnew ->
  Permutation (map (fun '(_, v) => voter_index v)
                   (FMap.elements m))
              (seq 0 (FMap.size m)) ->
  Permutation
    (map (fun '(_, v0) => voter_index v0)
         (FMap.elements (FMap.add k vnew m)))
    (seq 0 (FMap.size m)).
Proof.
  intros find_some index old_perm.
  rewrite <- old_perm.
  rewrite <- (FMap.add_id _ _ _ find_some) at 2.
  rewrite <- (FMap.add_remove k vold).
  rewrite (FMap.elements_add_existing k vold vnew) by auto.
  rewrite FMap.elements_add by auto.
  cbn.
  now rewrite index.
Qed.

Theorem boardroom_voting_correct_strong
        bstate caddr (trace : ChainTrace empty_state bstate)
        pks index sks svs :
    env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\

      finish_registration_by (setup cstate) < finish_vote_by (setup cstate) /\

      (Blockchain.current_slot bstate < finish_vote_by (setup cstate) ->
       result cstate = None) /\

      length (public_keys cstate) = FMap.size (registered_voters cstate) /\
      length (public_keys cstate) = num_signups inc_calls /\

      (Z.of_nat (length (public_keys cstate)) < modulus - 1)%Z /\

      (CallAssumptions pks index sks svs inc_calls ->
       IndexAssumptions (registered_voters cstate) index ->
       (finish_registration_by (setup cstate) < Blockchain.current_slot bstate ->
        num_signups inc_calls = length pks) ->
       firstn (length (public_keys cstate)) pks = public_keys cstate ->

       Permutation (map (fun '(_, v) => voter_index v)
                        (FMap.elements (registered_voters cstate)))
                   (seq 0 (length (public_keys cstate))) /\

       (forall addr inf,
           FMap.find addr (registered_voters cstate) = Some inf ->
           voter_index inf < length (public_keys cstate) /\
           nth_error (public_keys cstate) (voter_index inf) =
           Some (compute_public_key (sks addr)) /\
           (public_vote inf = 0%Z \/
            public_vote inf = compute_public_vote
                                (reconstructed_key pks (voter_index inf))
                                (sks addr)
                                (svs addr))) /\
       (result cstate = None \/
        result cstate = Some (sumnat (fun party => if svs party then 1 else 0)%nat
                                     (FMap.keys (registered_voters cstate))))).
Proof.
  contract_induction; intros.
  - [AddBlockFacts]: exact (fun _ old_slot _ _ new_slot _ => old_slot < new_slot).
    subst AddBlockFacts.
    cbn in facts.
    destruct_and_split; try tauto.
    + eauto with lia.
    + intros; eauto with lia.
  - cbn -[Nat.ltb] in *.
    destruct (_ <? _) eqn:ltb; [|congruence].
    apply Nat.ltb_lt in ltb.
    inversion_clear init_some.
    cbn.
    split; auto.
    split; auto.
    split; [symmetry; apply FMap.size_empty|].
    pose proof (prime_ge_2 _ modulus_prime).
    split; [lia|].
    split; [lia|].
    intros _ index_assum pks_assum.
    rewrite FMap.elements_empty.
    split; [auto|].
    split; [|tauto].
    intros ? ? find.
    now rewrite FMap.find_empty in find.
  - auto.
  - cbn -[Nat.ltb] in receive_some.
    destruct msg as [msg|]; cbn -[Nat.ltb] in *; [|congruence].
    destruct msg.
    + (* signup *)
      destruct (_ <? _)%nat eqn:intime in receive_some; cbn -[Nat.ltb] in *; [congruence|].
      apply Nat.ltb_ge in intime.
      destruct (FMap.find _ _) in receive_some; cbn in *; [|congruence].
      destruct (FMap.find _ _) eqn:new in receive_some; cbn in *; [congruence|].
      destruct (_ =? _)%Z in receive_some; cbn in *; [|congruence].
      destruct (_ <? _)%Z eqn:lt in receive_some; cbn in *; [|congruence].
      inversion_clear receive_some.
      cbn.
      split; [lia|].
      split; [tauto|].
      split.
      { rewrite app_length, FMap.size_add_new by auto; cbn; lia. }
      apply Z.ltb_lt in lt.
      rewrite app_length in *.
      cbn.
      fold (num_signups prev_inc_calls).
      split; [destruct_and_split; lia|].
      split; [lia|].
      intros [signup_assum call_assum] index_assum num_signups_assum pks_assum.
      destruct IH as [reg_lt [cur_lt [_ [_ [_ IH]]]]].
      unshelve epose proof (IH _ _ _ _) as IH.
      * auto.
      * intros addr' inf' find.
        apply index_assum.
        destruct (address_eqb_spec addr' (ctx_from ctx)) as [->|].
        -- destruct (FMap.find _ _); congruence.
        -- rewrite FMap.find_add_ne; auto.
      * intros.
        lia.
      * apply firstn_app_invl with (l2 := [pk]); auto.
      * split.
        {
          destruct IH as [perm _].
          cbn.
          rewrite FMap.elements_add by auto.
          cbn.
          rewrite seq_app.
          cbn.
          perm_simplify.
        }
        split; cycle 1.
        {
          left.
          apply cur_lt.
          lia.
        }
        intros addr inf find_add.
        destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
        -- rewrite (FMap.find_add (ctx_from ctx)) in find_add.
           inversion_clear find_add.
           cbn.
           unfold make_signup_msg in signup_assum.
           rewrite nth_error_snoc.
           repeat split; auto; try congruence; lia.
        -- rewrite FMap.find_add_ne in find_add by auto.
           destruct IH as [_ [IH _]].
           specialize (IH _ _ find_add).
           split; [lia|].
           now rewrite nth_error_app1 by lia.
    + (* commit_to_vote *)
      destruct (finish_commit_by _); cbn -[Nat.ltb] in *; [|congruence].
      destruct (_ <? _); cbn in *; [congruence|].
      destruct (FMap.find _ _) eqn:found; cbn in *; [|congruence].
      inversion_clear receive_some; cbn.
      split; [lia|].
      split; [tauto|].
      split.
      { rewrite FMap.size_add_existing by congruence; tauto. }
      split; [tauto|].
      split; [tauto|].
      intros [_ call_assum] index_assum num_signups_assum pks_assum.
      destruct IH as [_ [_ [len_pks [_ [_ IH]]]]].
      unshelve epose proof (IH call_assum _ num_signups_assum pks_assum) as IH.
      {
        apply (voter_info_update _ _ (ctx_from ctx) v (v<|vote_hash := hash|>));
          auto.
      }
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split.
      {
        destruct IH as [perm _].
        rewrite len_pks in *.
        apply Permutation_modify with (vold := v); auto.
      }

      split; try tauto.
      intros addr inf find_add.
      destruct IH as [_ [IH _]].
      destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
      * rewrite FMap.find_add in find_add.
        inversion_clear find_add; cbn.
        auto.
      * rewrite FMap.find_add_ne in find_add by auto.
        auto.
    + (* submit_vote *)
      destruct (_ <? _); cbn -[Nat.ltb] in *; [congruence|].
      destruct (FMap.find _ _) eqn:found; cbn in *; [|congruence].
      destruct (if finish_commit_by _ then _ else _); cbn in *; [|congruence].
      destruct (verify_vote _ _ _ _); cbn in *; [|congruence].
      inversion_clear receive_some; cbn.
      split; [lia|].
      split; [tauto|].
      rewrite FMap.size_add_existing by congruence.
      split; [tauto|].
      split; [tauto|].
      split; [tauto|].
      intros [vote_assum call_assum] index_assum num_signups_assum pks_assum.
      destruct IH as [_ [_ [len_pks [_ [_ IH]]]]].
      pose proof (voter_info_update
                    (registered_voters prev_state)
                    index
                    (ctx_from ctx)
                    v0
                    (v0<|public_vote := v|>)
                    index_assum
                    found
                    eq_refl) as prev_index_assum.
      specialize (IH call_assum prev_index_assum num_signups_assum pks_assum).
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split.
      {
        destruct IH as [perm _].
        rewrite len_pks in *.
        apply Permutation_modify with (vold := v0); auto.
      }
      split; [|tauto].
      intros addr inf find_add.
      destruct IH as [_ [IH _]].
      destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
      * rewrite FMap.find_add in find_add.
        inversion_clear find_add; cbn.
        specialize (IH _ _ found).
        repeat split; try tauto.
        right.
        unfold make_vote_msg in *.
        unfold IndexAssumptions in *.
        specialize (prev_index_assum _ _ found).
        rewrite prev_index_assum.
        congruence.
      * rewrite FMap.find_add_ne in find_add by auto.
        auto.
    + (* tally_votes *)
      destruct (_ <? _) eqn:intime; cbn in *; [congruence|].
      destruct (result prev_state); cbn in *; [congruence|].
      destruct (existsb _ _) eqn:all_voted; cbn in *; [congruence|].
      destruct (bruteforce_tally _) eqn:bruteforce; cbn -[Nat.ltb] in *; [|congruence].
      inversion_clear receive_some; cbn.
      apply Nat.ltb_ge in intime.
      split; [lia|].
      split; [intros; lia|].
      split; [tauto|].
      split; [tauto|].
      split; [tauto|].
      intros [_ call_assum] index_assum num_signups_assum pks_assum.
      split; [tauto|].
      split; [tauto|].
      right.
      apply f_equal.
      destruct IH as [finish_before_vote [_ [len_pks [len_pks' [party_count IH]]]]].
      specialize (IH call_assum index_assum num_signups_assum pks_assum).
      destruct IH as [perm [addrs _]].
      unfold FMap.values in bruteforce.
      rewrite map_map in bruteforce.
      rewrite (map_ext_in _ (fun '(_, v) => public_vote v)) in bruteforce
        by (now intros []).
      rewrite (bruteforce_tally_correct
                    (FMap.elements (registered_voters prev_state))
                    (fun '(_, v) => voter_index v)
                    (fun '(addr, _) => sks addr)
                    (public_keys prev_state)
                    (fun kvp => svs (fst kvp))
                    (fun '(_, v) => public_vote v)) in bruteforce.
      * inversion bruteforce.
        unfold FMap.keys.
        now rewrite sumnat_map.
      * now rewrite FMap.length_elements, <- len_pks.
      * now rewrite FMap.length_elements, <- len_pks.
      * auto.
      * intros [k v] kvpin.
        apply FMap.In_elements in kvpin.
        specialize (addrs _ _ kvpin).
        tauto.
      * intros [k v] kvpin.
        rewrite existsb_forallb in all_voted.
        apply Bool.negb_false_iff in all_voted.
        rewrite forallb_forall in all_voted.
        unshelve epose proof (all_voted v _) as all_voted.
        {
          apply in_map_iff.
          exists (k, v).
          tauto.
        }
        apply Bool.negb_true_iff in all_voted.
        apply Z.eqb_neq in all_voted.
        apply FMap.In_elements in kvpin.
        specialize (addrs _ _ kvpin).
        cbn.
        destruct addrs as [_ [_ []]]; try congruence.
        fold (num_signups prev_inc_calls) in *.
        specialize (num_signups_assum ltac:(lia)).
        replace (length (public_keys prev_state)) with (length pks) in pks_assum by congruence.
        rewrite firstn_all in *.
        congruence.
  - [CallFacts]: exact (fun _ ctx _ => ctx_from ctx <> ctx_contract_address ctx).
    subst CallFacts; cbn in *; congruence.
  - auto.
  - [DeployFacts]: exact (fun _ _ => True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    + destruct valid_header; auto.
    + destruct_action_eval; auto.
      intros.
      pose proof (no_outgoing _ _ from_reachable H1).
      unfold outgoing_acts in H3.
      rewrite queue_prev in H3.
      cbn in H3.
      destruct (address_eqb_spec (act_from act) to_addr); cbn in *; try congruence.
      subst act; cbn in *; congruence.
Qed.

Theorem boardroom_voting_correct
        bstate caddr (trace : ChainTrace empty_state bstate)
        pks index sks svs :
    env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\

      (CallAssumptions pks index sks svs inc_calls ->
       IndexAssumptions (registered_voters cstate) index ->
       (finish_registration_by (setup cstate) < Blockchain.current_slot bstate ->
        num_signups inc_calls = length pks) ->
       firstn (length (public_keys cstate)) pks = public_keys cstate ->

       (result cstate = None \/
        result cstate = Some (sumnat (fun party => if svs party then 1 else 0)%nat
                                     (FMap.keys (registered_voters cstate))))).
Proof.
  intros deployed.
  destruct (boardroom_voting_correct_strong bstate caddr trace pks index sks svs deployed)
    as [cstate [depinfo [inc_calls P]]].
  exists cstate, depinfo, inc_calls.
  tauto.
Qed.

End Theories.

End BoardroomVoting.
(*

Require Import LocalBlockchain.

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
  let rprod := fold_right (fun e r => (e * r) mod modulus) 1 pks in
  let rprod := mod_inv rprod modulus in
  reconstructed_keys_aux pks 1 rprod.


Definition modulus : Z := 1552518092300708935130918131258481755631334049434514313202351194902966239949102107258669453876591642442910007680288864229150803718918046342632727613031282983744380820890196288509170691316593175367469551763119843371637221007210577919.
Definition generator : Z := 2.
Definition sk n := mod_pow ((Z.of_nat n + 1234583932) * (modulus - 23241)) 159338231 modulus.

Definition num_parties : nat := 7.
Definition votes_for : nat := 3.
Definition sks : list Z := Eval native_compute in map sk (seq 7 num_parties).
Definition pks : list Z := Eval native_compute in map (fun sk => mod_pow generator sk modulus) sks.
Definition svs : list bool :=
  Eval compute in map (fun _ => true)
                      (seq 0 votes_for)
                  ++ map (fun _ => false)
                         (seq 0 (num_parties - votes_for)).
Definition expected_result : nat :=
  Eval compute in (fold_right (fun (e : bool) r => r + if e then 1 else 0) 0 svs)%nat.
Definition rks : Vector.t Z (length pks) := Eval native_compute in reconstructed_keys modulus pks.
Definition pvs : list Z :=
  Eval native_compute in
    (fix f (sks : list Z) (rks : list Z) (svs : list bool) :=
       match sks, rks, svs with
       | sk :: sks, rk :: rks, sv :: svs =>
         (mod_pow rk sk modulus * generator^(if sv then 1 else 0)) mod modulus :: f sks rks svs
       | _, _, _ => []
       end) sks (Vector.to_list rks) svs.

Definition A a :=
  BoundedN.of_Z_const AddrSize a.

Local Open Scope nat.
Definition addrs : list Address.
Proof.
  let rec add_addr z n :=
    match n with
    | O => constr:(@nil Address)
    | S ?n => let tail := add_addr (z + 1)%Z n in
              constr:(cons (A z) tail)
    end in
  let num := eval compute in num_parties in
  let tm := add_addr 11%Z num in
  let tm := eval vm_compute in tm in
  exact tm.
Defined.

Definition deploy_setup :=
  {| eligible_voters := FMap.of_list (map (fun a => (a, tt)) addrs);
     finish_registration_by := 3;
     finish_commit_by := None;
     finish_vote_by := 5;
     registration_deposit := 0; |}.

Import Blockchain.
Definition boardroom_example : option nat :=
  let chain : LocalChainBuilderDepthFirst := builder_initial in
  let creator := A 10 in
  let add_block (chain : LocalChainBuilderDepthFirst) (acts : list Action) :=
      let next_header :=
          {| block_height := S (chain_height chain);
             block_slot := S (current_slot chain);
             block_finalized_height := finalized_height chain;
             block_creator := creator;
             block_reward := 50; |} in
      builder_add_block chain next_header acts in
  do chain <- add_block chain [];
  let dep := build_act creator (create_deployment 0 (boardroom_voting id modulus generator) deploy_setup) in
  do chain <- add_block chain [dep];
  do caddr <- hd None (map Some (FMap.keys (lc_contracts (lcb_lc chain))));
  let reg addr pk := build_act addr (act_call caddr 0 (serialize (signup pk))) in
  let calls := map (fun '(addr, pk) => reg addr pk) (zip addrs pks) in
  do chain <- add_block chain calls;
  let vote addr v := build_act addr (act_call caddr 0 (serialize (submit_vote v))) in
  let votes := map (fun '(addr, pv) => vote addr pv) (zip addrs pvs) in
  do chain <- add_block chain votes;
  do chain <- add_block chain [];
  let tally := build_act creator (act_call caddr 0 (serialize tally_votes)) in
  do chain <- add_block chain [tally];
  do state <- contract_state (lcb_lc chain) caddr;
  result state.

Eval native_compute in boardroom_example.
*)
