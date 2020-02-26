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
Lemma bruteforce_correct
      (voters : FMap Address VoterInfo)
      (sks : Address -> Z)
      (svs : Address -> bool)
      (pks : list Z)
      (n : nat) :
  (forall (addr : Address) (inf : VoterInfo),
    FMap.find addr voters = Some inf ->
    nth (voter_index inf) pks 0%Z = compute_public_key (sks addr) /\
    public_vote inf = compute_public_vote (reconstructed_key pks (voter_index inf))
                                          (sks addr) (svs addr)) ->
  bruteforce_tally (map public_vote (FMap.values voters)) = Some n ->
  n = sumnat (fun party => if svs party then 1 else 0) (FMap.keys voters).
Proof.
  intros.
  unfold FMap.keys, FMap.values in *.
  set (parties := map (fun '(k, v) => (sks k, nth (voter_index v) pks 0%Z, svs k, public_vote v))
                      (FMap.elements voters)).
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

Lemma flat_map_ext_in {B C} (f f' : B -> list C) (l : list B) :
  (forall b, In b l -> f b = f' b) ->
  flat_map f l = flat_map f' l.
Proof.
  intros.
  rewrite !flat_map_concat_map.
  apply f_equal.
  now apply map_ext_in.
Qed.

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

Lemma NoDup_app {B} (l l' : list B) :
  NoDup l ->
  NoDup l' ->
  (forall b, In b l -> ~In b l') ->
  NoDup (l ++ l').
Proof.
  intros nodupl nodupl' all_nin.
  induction l as [|b bs IH]; cbn; auto.
  constructor.
  - inversion nodupl; subst.
    intros isin.
    apply in_app_iff in isin.
    destruct isin; [easy|].
    apply (all_nin b); auto.
    left; auto.
  - apply IH.
    + inversion nodupl; auto.
    + intros b' inb'.
      apply all_nin.
      right; auto.
Qed.

Lemma NoDup_app_comm {B} (bs bs' : list B) :
  NoDup (bs ++ bs') <-> NoDup (bs' ++ bs).
Proof.
  intros.
  now rewrite (Permutation_app_comm bs bs').
Qed.

Lemma NoDup_flat_map_disjoint {B C} (f : B -> list C) (l : list B) :
  (forall b, In b l -> NoDup (f b)) ->
  (forall b b', b <> b' -> In b l -> In b' l -> forall c, In c (f b) -> ~In c (f b')) ->
  NoDup l ->
  NoDup (flat_map f l).
Proof.
  intros all_disjoint all_pairwise_disjoint nodupb.
  induction l as [|b bs IH]; cbn; [constructor|].
  unshelve epose proof (IH _ _) as IH.
  - intros a ain; apply all_disjoint; cbn; tauto.
  - intros a a' aneq ain a'in.
    apply all_pairwise_disjoint; cbn; tauto.
  - cbn in *.
    apply NoDup_app; auto.
    + apply IH; inversion nodupb; auto.
    + intros c cin cinmap.
      rewrite flat_map_concat_map in cinmap.
      apply In_concat in cinmap.
      destruct cinmap as [inl [inll incl]].
      apply in_map_iff in inll.
      destruct inll as [x [<- inxbs]].
      inversion nodupb; subst.
      unshelve epose proof (in_NoDup_app x bs [b] inxbs _).
      { apply NoDup_app_comm; cbn; auto. }
      cbn in H1.
      unshelve epose proof (all_pairwise_disjoint b x _ _ _ c cin); tauto.
Qed.

Lemma NoDup_ordered_voters voters :
  NoDup (ordered_voters voters).
Proof.
  unfold ordered_voters, ordered_voters_list.
  assert (forall {A} (x : A), NoDup [x]) by (constructor; cbn; try constructor; intuition).
  apply NoDup_flat_map_disjoint.
  - intros; destruct (find _ _); auto; constructor.
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

Lemma In_ordered_voters_add addr voter addr_add voter_add voters :
  FMap.find addr_add voters = None ->
  voter_index voter_add = FMap.size voters ->
  Permutation (ordered_voters voters) (FMap.elements voters) ->
  In (addr, voter) (ordered_voters (FMap.add addr_add voter_add voters)) <->
  (addr, voter) = (addr_add, voter_add) \/ In (addr, voter) (FMap.elements voters).
Proof.
  (*
  intros find_none index is_perm.
  split.
  - intros isin.
    induction voters using FMap.ind.
    + unfold
    unfold ordered_voters in isin.
    rewrite FMap.size_add_new in isin by auto.
   *)
  Admitted.

Lemma ordered_voters_add addr (voter : VoterInfo) (voters : FMap Address VoterInfo) :
  FMap.find addr voters = None ->
  voter_index voter = FMap.size voters ->
  Permutation (ordered_voters voters) (FMap.elements voters) ->
  Permutation (ordered_voters (FMap.add addr voter voters))
              (FMap.elements (FMap.add addr voter voters)).
Proof.
  intros find_none index is_perm.
  apply (NoDup_Permutation (NoDup_ordered_voters (FMap.add addr voter voters))
                           (FMap.NoDup_elements (FMap.add addr voter voters))).
  setoid_rewrite FMap.elements_add; auto.
  intros [addr' voter'].
  split.
  - intros isin.
    apply In_ordered_voters_add in isin; auto.
    destruct isin; [left; congruence|right;tauto].
  - intros isin.
    apply In_ordered_voters_add; auto.
    destruct isin; [left; congruence|right; tauto].
Qed.

Lemma ordered_voters_modify voters addr vold vnew :
  FMap.find addr voters = Some vold ->
  voter_index vold = voter_index vnew ->
  Permutation (ordered_voters voters) (FMap.elements voters) ->
  Permutation (ordered_voters (FMap.add addr vnew voters))
              (FMap.elements (FMap.add addr vnew voters)).
Proof.
  intros find_some index perm.
  apply (NoDup_Permutation (NoDup_ordered_voters (FMap.add addr vnew voters))
                           (FMap.NoDup_elements (FMap.add addr vnew voters))).
  intros x.
  rewrite FMap.In_elements.
  split.
  - intros isin.
    admit.
  - intros find.
    unfold ordered_voters.
    unfold ordered_voters_list.

  induction voters using FMap.ind.
  - unfold ordered_voters.
    induction

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

      finish_registration_by (setup cstate) < finish_vote_by (setup cstate) /\

      (Blockchain.current_slot bstate < finish_vote_by (setup cstate) ->
       result cstate = None) /\

      length (public_keys cstate) = FMap.size (registered_voters cstate) /\

      (CallAssumptions pks index sks svs inc_calls ->
       firstn (length (public_keys cstate)) pks = public_keys cstate ->
       IndexAssumptions (registered_voters cstate) index ->
       (Permutation (FMap.elements (registered_voters cstate))
                    (ordered_voters (registered_voters cstate)) /\
         forall addr inf,
           FMap.find addr (registered_voters cstate) = Some inf ->
           voter_index inf < length (public_keys cstate) /\
           nth (voter_index inf) (public_keys cstate) 0%Z = compute_public_key (sks addr) /\
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
    eauto with lia.
  - cbn -[Nat.ltb] in *.
    unfold boardroom_voting in init_some.
    destruct (_ <? _) eqn:ltb; [|congruence].
    apply Nat.ltb_lt in ltb.
    inversion_clear init_some.
    cbn.
    setoid_rewrite FMap.find_empty.
    intuition.
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
      inversion_clear receive_some.
      cbn.
      split; [lia|].
      split; [tauto|].
      split.
      { rewrite app_length, FMap.size_add_new by auto; cbn; lia. }
      intros [signup_assum call_assum] pks_assum index_assum.
      split; [|intuition].
      destruct IH as [_ [_ [num_pks IH]]].
      specialize (IH call_assum).
      rewrite app_length in *.
      cbn.
      unshelve epose proof (IH _ _) as IH; [eauto using firstn_app_invl| |].
      {
        intros addr' inf' find.
        apply index_assum.
        destruct (address_eqb_spec addr' (ctx_from ctx)) as [->|].
        - destruct (FMap.find _ _); congruence.
        - rewrite FMap.find_add_ne; auto.
      }

      destruct IH as [[IH_perm IH] _].
      split; cycle 1.
      {
        intros addr inf find_add.
        destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
        - rewrite (FMap.find_add (ctx_from ctx)) in find_add.
          inversion_clear find_add.
          cbn.
          unfold make_signup_msg in signup_assum.
          rewrite nth_snoc.
          repeat split; auto; try congruence; lia.
        - rewrite FMap.find_add_ne in find_add by auto.
          specialize (IH _ _ find_add).
          split; [lia|].
          now rewrite app_nth1 by lia.
      }

      now rewrite ordered_voters_add by easy.
    + (* commit_to_vote *)
      destruct (finish_commit_by _); cbn -[Nat.ltb] in *; [|congruence].
      destruct (_ <? _); cbn in *; [congruence|].
      destruct (FMap.find _ _) eqn:found; cbn in *; [|congruence].
      inversion_clear receive_some; cbn.
      split; [lia|].
      split; [tauto|].
      split.
      { rewrite FMap.size_add_existing by congruence; tauto. }
      intros [_ call_assum] pks_assum index_assum.
      destruct IH as [_ [_ [_ IH]]].
      unshelve epose proof (IH call_assum pks_assum _) as IH.
      {
        apply (voter_info_update _ _ (ctx_from ctx) v (v<|vote_hash := hash|>));
          auto.
      }
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split; [|tauto].
      split; [tauto|].
      intros addr inf find_add.
      destruct IH as [IH _].
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
      intros [vote_assum call_assum] pks_assum index_assum.
      destruct IH as [_ [_ IH]].
      pose proof (voter_info_update
                    (registered_voters prev_state)
                    index
                    (ctx_from ctx)
                    v0
                    (v0<|public_vote := v|>)
                    index_assum
                    found
                    eq_refl) as prev_index_assum.
      specialize (IH call_assum pks_assum prev_index_assum).
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split; [|tauto].
      intros addr inf find_add.
      destruct IH as [IH _].
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
      intros [_ call_assum] pks_assum index_assum.
      split; [tauto|].
      right.
      apply f_equal.
      destruct IH as [_ [_ IH]].
      specialize (IH call_assum pks_assum index_assum).
      destruct IH as [IH _].
      rewrite (bruteforce_tally_correct
                 (FMap.size (registered_voters prev_state))
                 (fun i =>

      set (
      unfold bruteforce_tally in bruteforce.
      assert (IH':
      split; [tauto|].
      destruct IH as [_ [_ IH]].
      specialize (IH call_assum pks_assum).
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split; [|tauto].
      intros addr inf find_add.
      destruct IH as [IH _].
      destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
      * rewrite FMap.find_add in find_add.
        inversion_clear find_add; cbn.
        auto.
      * rewrite FMap.find_add_ne in find_add by auto.
        auto.


      split; [|intuition].
      split.
      * intros.
      split;
      split; [tauto|].

      split; try tauto.


    unfold run_contract_receiver in *.
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
