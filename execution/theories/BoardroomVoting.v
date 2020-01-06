From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require VectorDef.
From RecordUpdate Require Import RecordUpdate.
Require Import Automation.
Require Import Blockchain.
Require Import Containers.
Require ContractMonads.
Require Import Monads.
Require Import Serializable.

Import ListNotations.
Import RecordSetNotations.

Section BoardroomVoting.
Context `{Base : ChainBase}.
Context `{H : Z -> Z}.

Local Open Scope Z.
Definition prime : Z :=
  32317006071311007300338913926423828248817941241140239112842009751400741706634354222619689417363569347117901737909704191754605873209195028853758986185622153212175412514901774520270235796078236248884246189477587641105928646099411723245426622522193230540919037680524235519125679715870117001058055877651038861847280257976054903569732561526167081339361799541336476559160368317896729073178384589680639671900977202194168647225871031411336429319536193471636533209717077448227988588565369208645296636077250268955505928362751121174096972998068410554359584866583291642136218231078990999448652468262416972035911852507045361090559.

Definition generator : Z := 2.

(* Allow us to automatically derive Serializable instances *)
Set Nonrecursive Elimination Schemes.

Record Setup :=
  build_setup {
    eligible_voters : FMap Address unit;
    finish_registration_by : nat;
    begin_election_by : nat;
    finish_commit_by : option nat;
    finish_vote_by : nat;
    registration_deposit : Amount;
  }.

Record VoterInfo :=
  build_voter_info {
    index : nat;
    public_key : Z;
    vote_hash : Z;
    public_vote : Z;
}.

Record State :=
  build_state {
    owner : Address;
    registered_voters : FMap Address VoterInfo;
    setup : Setup;
    result : option nat;
  }.

Inductive Msg :=
| signup (pk : Z)
| commit_to_vote (hash : Z)
| submit_vote (v : Z)
| tally_votes.

Global Instance VoterInfo_settable : Settable _ :=
  settable! build_voter_info <index; public_key; vote_hash; public_vote>.

Global Instance State_settable : Settable _ :=
  settable! build_state <owner; registered_voters; setup; result>.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance VoterInfo_serializable : Serializable VoterInfo :=
  Derive Serializable VoterInfo_rect<build_voter_info>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<signup, commit_to_vote, submit_vote, tally_votes>.

Import ContractMonads.

Definition init : ContractIniter Setup State :=
  do owner <- lift caller_addr;
  do setup <- deployment_setup;
  accept_deployment
    {| owner := owner;
       registered_voters := FMap.empty;
       setup := setup;
       result := None; |}.

Axiom todo : forall {T}, T.

Definition mod_pow (a x m : Z) : Z := todo.

Lemma mod_pow_spec a x m :
  mod_pow a x m = a^x mod m.
Proof.
  Admitted.

Fixpoint bruteforce_tally (n : nat) (product : Z) : option nat :=
  if mod_pow generator (Z.of_nat n) prime =? product then
    Some n
  else
    match n with
    | 0 => None
    | S n => bruteforce_tally n product
    end%nat.

Definition receive : ContractReceiver State Msg State :=
  do state <- my_state;
  do caller <- lift caller_addr;
  do cur_slot <- lift current_slot;
  do msg <- call_msg >>= lift;
  match msg with
  | signup pk =>
    do lift (if finish_registration_by (setup state) <? cur_slot then None else Some tt)%nat;
    do lift (if FMap.mem caller (eligible_voters (setup state)) then Some tt else None);
    let index := FMap.size (registered_voters state) in
    let inf := {| index := index;
                  public_key := pk;
                  vote_hash := 0;
                  public_vote := 0; |} in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | commit_to_vote hash =>
    do commit_by <- lift (finish_commit_by (setup state));
    do lift (if commit_by <? cur_slot then None else Some tt)%nat;
    do inf <- lift (FMap.find caller (registered_voters state));
    let inf := inf<|vote_hash := hash|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | submit_vote v =>
    do lift (if finish_vote_by (setup state) <? cur_slot then None else Some tt)%nat;
    do inf <- lift (FMap.find caller (registered_voters state));
    do lift (if H v =? vote_hash inf then Some tt else None);
    let inf := inf<|public_vote := v|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | tally_votes =>
    do lift (if cur_slot <? finish_vote_by (setup state) then None else Some tt)%nat;
    do lift (match result state with | Some _ => None | None => Some tt end);
    let votes := map public_vote (FMap.values (registered_voters state)) in
    let product := fold_right (fun e r => e * r mod prime) 1%Z votes in
    let max_vote := FMap.size (registered_voters state) in
    do res <- lift (bruteforce_tally max_vote product);
    accept_call (state<|result := Some res|>)
  end.

Program Definition boardroom_voting : Contract Setup Msg State :=
  build_contract init receive _ _.
Next Obligation. now repeat intro; subst. Qed.
Next Obligation with cbn -[Nat.leb].
  intros c1 c2 ceq ctx ? <- state ? <- msg ? <-.
  unfold run_contract_receiver...
  destruct msg as [msg|]; [|congruence]...
  destruct msg.
  - rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (FMap.mem _ _); auto.
  - destruct (finish_commit_by _); auto.
    rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (FMap.find _ _); auto.
  - rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (FMap.find _ _); auto.
    destruct (_ =? _); auto.
  - rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (result _); auto.
    destruct (_ (FMap.size _)); auto.
Qed.

Section Theories.

Record PrivateVoterInfo (vinf : VoterInfo) (Yi : Z) :=
  build_private_voter_info {
    secret_key : Z;
    actual_vote : bool;
    secret_key_match : mod_pow generator secret_key prime = public_key vinf;
    vote_match :
      let vote_num := if actual_vote then generator else 1 in
      public_vote vinf = ((mod_pow Yi secret_key prime) * vote_num) mod prime;
  }.

(* Find y such that x*y = 1 mod m *)
Definition mod_inv (x m : Z) : Z := todo.
Lemma mod_inv_spec x m :
  (x * mod_inv x m) mod m = 1.
Proof.
  Admitted.

Fixpoint reconstructed_keys
        (voters : list VoterInfo) (cummul : Z) : Vector.t Z (length voters) :=
  match voters with
  | [] => Vector.nil
  | hd :: tl =>
    let nom := public_key hd * cummul mod prime in
    let denom := fold_right (fun e r => e * r mod prime) 1 (map public_key voters) in
    Vector.cons ((nom * mod_inv denom prime) mod prime) (reconstructed_keys tl nom)
  end.

Definition SecretKeysAccessible calls : Prop :=
  Forall (fun call => match Blockchain.call_msg call with
                      | Some (signup public_key) =>
                        exists secret_key,
                          mod_pow generator secret_key prime = public_key
                      | _ => True
                      end) calls.

Theorem boardroom_voting_correct bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      let Ys := reconstructed_keys (FMap.values (registered_voters cstate)) in
      SecretKeysAccessible inc_calls ->
      True.

End Theories.

End BoardroomVoting.
