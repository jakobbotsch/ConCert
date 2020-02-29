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
