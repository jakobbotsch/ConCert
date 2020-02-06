From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From Coq Require Program.
From RecordUpdate Require Import RecordUpdate.
Require Import Automation.
Require Import Blockchain.
Require Import BoundedN.
Require Import Containers.
From stdpp Require countable.
Require ContractMonads.
Require Import Extras.
Require Import ModularArith.
Require Import Monads.
Require Import Serializable.

Import ListNotations.
Import RecordSetNotations.

Section BoardroomVoting.
Context `{Base : ChainBase}.
Context `(H : Z -> Z).
(*Context (verify_vote (vote : Z) (rk : Z) (jj*)
Context (modulus : Z).
Context (generator : Z).
Context (modulus_prime : prime modulus).

Class VoteProofScheme :=
  build_vote_proof_scheme {
    make_vote_proof (pks : list Z) (index : nat)
                    (secret_key : Z) (secret_vote : bool) : Z;
    verify_vote (pks : list Z) (index : nat) (public_vote proof : Z) : bool;

    verify_vote_spec pks index pv proof :
      verify_vote pks index pv proof = true ->
      exists sk sv, proof = make_vote_proof pks index sk sv;
  }.

Context `{VoteProofScheme}.

Local Open Scope Z.

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
    index : nat;
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
  settable! build_voter_info <index; vote_hash; public_vote>.

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

Fixpoint bruteforce_tally (n : nat) (product : Z) : option nat :=
  if mod_pow generator (Z.of_nat n) modulus =? product then
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
    do lift (if FMap.mem caller (registered_voters state) then None else Some tt);
    do amt <- lift call_amount;
    do lift (if amt =? (registration_deposit (setup state)) then Some tt else None);
    let index := length (public_keys state) in
    let inf := {| index := index;
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
    do lift (if verify_vote (public_keys state) (index inf) v proof then Some tt else None);
    let inf := inf<|public_vote := v|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | tally_votes =>
    do lift (if cur_slot <? finish_vote_by (setup state) then None else Some tt)%nat;
    do lift (match result state with | Some _ => None | None => Some tt end);
    let votes := map public_vote (FMap.values (registered_voters state)) in
    let product := fold_right (fun e r => e * r mod modulus) 1%Z votes in
    let max_vote := FMap.size (registered_voters state) in
    do res <- lift (bruteforce_tally max_vote product);
    accept_call (state<|result := Some res|>)
  end.

Program Definition boardroom_voting : Contract Setup Msg State :=
  build_contract init receive _ _.
Next Obligation.
  repeat intro; subst.
  cbn -[Nat.ltb].
  destruct (_ <? _)%nat; auto.
Qed.
Next Obligation with cbn -[Nat.leb].
  intros c1 c2 ceq ctx ? <- state ? <- msg ? <-.
  unfold run_contract_receiver...
  destruct msg as [msg|]; [|congruence]...
  destruct msg.
  - rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (FMap.mem _ _); auto.
    destruct (FMap.mem _ _); auto.
    destruct (_ =? _)%Z; auto.
  - destruct (finish_commit_by _); auto.
    rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (FMap.find _ _); auto.
  - rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (FMap.find _ _); auto.
    destruct (finish_commit_by _); [destruct (_ =? _); auto|].
    all: destruct (verify_vote _ _ _ _); auto.
  - rewrite <- ceq.
    destruct (_ <? _)%nat; auto.
    destruct (result _); auto.
    destruct (_ (FMap.size _)); auto.
Qed.

Definition reconstructed_key (pks : list Z) (n : nat) : Z :=
  let prod := fold_right (fun e r => (e * r) mod modulus) 1 in
  let lprod := prod (firstn n pks) in
  let rprod := mod_inv (prod (skipn (S n) pks)) modulus in
  (lprod * rprod) mod modulus.

Definition compute_public_key (sk : Z) : Z :=
  mod_pow generator sk modulus.

Definition compute_public_vote (rk sk : Z) (sv : bool) : Z :=
  (mod_pow rk sk modulus * if sv then generator else 1) mod modulus.

Definition make_signup_msg (sk : Z) : Msg :=
  signup (compute_public_key sk).

Definition make_commit_msg (pks : list Z) (my_index : nat) (sk : Z) (sv : bool) : Msg :=
  commit_to_vote (H (compute_public_vote (reconstructed_key pks my_index) sk sv)).

Definition make_vote_msg (pks : list Z) (my_index : nat) (sk : Z) (sv : bool) : Msg :=
  submit_vote (compute_public_vote (reconstructed_key pks my_index) sk sv)
              (make_vote_proof pks my_index sk sv).

Section Theories.

Fixpoint SecretsKnown
         (sks : Address -> Z)
         (svs : Address -> bool)
         (calls : list (ContractCallInfo Msg)) : Prop :=
  match calls with
  | call :: calls =>
    let caller := Blockchain.call_from call in
    match Blockchain.call_msg call with
    | Some (signup pk as m) => m = make_signup_msg (sks caller)
    | Some (submit_vote _ _ as m) =>
      exists pks my_index, m = make_vote_msg pks my_index (sks caller) (svs caller)
    | _ => True
    end /\ SecretsKnown sks svs calls
  | [] => True
  end.

Local Open Scope nat.
Theorem boardroom_voting_correct bstate caddr (trace : ChainTrace empty_state bstate) :
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
      forall sks svs,
        SecretsKnown sks svs inc_calls ->
        (forall addr inf,
            FMap.find addr (registered_voters cstate) = Some inf ->
            index inf < length (public_keys cstate) /\
            nth (index inf) (public_keys cstate) 0%Z = compute_public_key (sks addr)) /\
        (result cstate = None \/
         result cstate = Some (sumnat
                                 (fun party => if svs party then 1 else 0)%nat
                                 (FMap.keys (registered_voters cstate)))).
Proof.
  contract_induction; intros.
  - split; [tauto|].
    [AddBlockFacts]: exact (fun _ old_slot _ _ new_slot _ => old_slot < new_slot).
    subst AddBlockFacts.
    cbn in facts.
    split; [destruct IH as [_ [IH _]]|tauto].
    intros fact.
    apply IH.
    lia.
  - cbn -[Nat.ltb] in *.
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
      destruct (FMap.mem _ _) in receive_some; cbn in *; [|congruence].
      destruct (FMap.mem _ _) in receive_some; cbn in *; [congruence|].
      destruct (_ =? _)%Z in receive_some; cbn in *; [|congruence].
      inversion_clear receive_some.
      cbn.
      split; [lia|].
      split; [tauto|].
      intros.
      split; [|intuition].
      intros.
      destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
      * rewrite FMap.find_add in H2.
        inversion_clear H2.
        cbn.
        unfold make_signup_msg in H1.
        rewrite nth_snoc.
        rewrite app_length.
        cbn.
        split; [lia|].
        destruct H1; congruence.
      * rewrite FMap.find_add_ne in H2 by auto.
        destruct IH as [_ [_ IH]].
        destruct H1 as [_ H1].
        specialize (IH sks svs H1).
        destruct IH as [IH _].
        specialize (IH _ _ H2).
        rewrite app_length; split; [lia|].
        destruct IH.
        now rewrite app_nth1 by lia.
    + (* commit_to_vote *)

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
