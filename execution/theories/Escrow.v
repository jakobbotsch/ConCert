(* This file defines a simple escrow contr based on the "safe
remote purchase" example in Solidity's docs. This contract allows a
seller to sell an item in a trustless setting assuming rational
actors. With the premise that the seller wants to sell an item for 1
ETH, the contract works in the following way:

1. The seller deploys the contract and commits 2 ETH.
2. The buyer commits 2 ETH before the deadline.
3. The seller hands over the item (around the smart contract).
4. The buyer confirms he has received the item. He gets 1 ETH back
while the seller gets 3 ETH back.

If the buyer does not commit the funds, the seller gets his money back
after the deadline. Due to the expectation that the buyer is rational
we can also assume that the seller will confirm he has received the
item to get his own funds back. *)

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
Require Import Automation.
Require Import Blockchain.
Require Import Extras.
Require Import Monads.
Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.

Section Escrow.
Context `{Base : ChainBase}.

Set Nonrecursive Elimination Schemes.

Record Setup :=
  build_setup {
      setup_buyer : Address;
    }.

Inductive NextStep :=
(* Waiting for buyer to commit itemvalue * 2 *)
| buyer_commit
(* Waiting for buyer to confirm item received *)
| buyer_confirm
(* Waiting for buyer and seller to withdraw their funds. *)
| withdrawals
(* No next step, sale is done. *)
| none.

Record State :=
  build_state {
      last_action : nat;
      next_step : NextStep;
      seller : Address;
      buyer : option Address;
      seller_withdrawable : Amount;
      buyer_withdrawable : Amount;
    }.

Inductive Msg :=
| commit_money
| confirm_item_received
| withdraw
| unstuck.

Global Instance State_settable : Settable _ :=
  settable! build_state <last_action; next_step; seller; buyer;
                         seller_withdrawable; buyer_withdrawable>.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance NextStep_serializable : Serializable NextStep :=
  Derive Serializable NextStep_rect<buyer_commit, buyer_confirm, withdrawals, none>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<commit_money, confirm_item_received, withdraw, unstuck>.

Open Scope Z.
Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
  : option State :=
  let seller := ctx_from ctx in
  let buyer := setup_buyer setup in
  do if (buyer =? seller)%address then None else Some tt;
  do if ctx_amount ctx =? 0 then None else Some tt;
  do if Z.even (ctx_amount ctx) then Some tt else None;
  Some (build_state (current_slot chain) buyer_commit seller None 0 0).

Definition receive
           (chain : Chain) (ctx : ContractCallContext)
           (state : State) (msg : option Msg)
  : option (State * list ActionBody) :=
  match msg, next_step state with
  | Some commit_money, buyer_commit =>

    let item_price := (account_balance chain (ctx_contract_address ctx)
                       - ctx_amount ctx) / 2 in
    let expected := item_price * 2 in
    do if ctx_amount ctx =? expected then Some tt else None;
    Some (state<|next_step := buyer_confirm|>
               <|buyer := Some (ctx_from ctx)|>
               <|last_action := current_slot chain|>, [])

  | Some confirm_item_received, buyer_confirm =>
    let item_price := account_balance chain (ctx_contract_address ctx) / 4 in
    do buyer <- buyer state;
    do if (ctx_from ctx =? buyer)%address then Some tt else None;
    do if ctx_amount ctx =? 0 then Some tt else None;
    let new_state :=
        state<|next_step := withdrawals|>
             <|buyer_withdrawable := item_price|>
             <|seller_withdrawable := item_price * 3|> in
    Some (new_state, [])

  | Some withdraw, withdrawals =>
    do buyer <- buyer state;
    do if ctx_amount ctx =? 0 then Some tt else None;
    let from := ctx_from ctx in
    do '(to_pay, new_state) <-
       match from =? buyer, from =? state.(seller) with
       | true, _ => Some (buyer_withdrawable state, state<|buyer_withdrawable := 0|>)
       | _, true => Some (seller_withdrawable state, state<|seller_withdrawable := 0|>)
       | _, _ => None
       end%address;
    do if to_pay >? 0 then Some tt else None;
    let new_state :=
        match buyer_withdrawable new_state, seller_withdrawable new_state with
        | 0, 0 => new_state<|next_step := none|>
        | _, _ => new_state
        end in
    Some (new_state, [act_transfer (ctx_from ctx) to_pay])

  | Some unstuck, step =>
    do if ctx_amount ctx =? 0 then Some tt else None;
    do if (last_action state + 50 <? current_slot chain)%nat then None else Some tt;
    let balance := account_balance chain (ctx_contract_address ctx) in
    do '(seller_withdraw, buyer_withdraw) <-
       match step with
       | buyer_commit => Some (balance, 0)
       | buyer_confirm => Some (balance / 2, balance / 2)
       | _ => None
       end;
    let new_state := state<|seller_withdrawable := seller_withdraw|>
                          <|buyer_withdrawable := buyer_withdraw|>
                          <|next_step := withdrawals|> in
    Some (new_state, [])

  | _, _ => None
  end.

Ltac solve_contract_proper :=
  repeat
    match goal with
    | [|- ?x _  = ?x _] => unfold x
    | [|- ?x _ _ = ?x _ _] => unfold x
    | [|- ?x _ _ _ = ?x _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [|- Some _ = Some _] => f_equal
    | [|- pair _ _ = pair _ _] => f_equal
    | [|- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [|- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Program Definition contract : Contract Setup Msg State :=
  build_contract init _ receive _.
Next Obligation. repeat intro; solve_contract_proper. Qed.
Next Obligation. repeat intro; solve_contract_proper. Qed.

Section Theories.
  Lemma no_self_calls bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Escrow.contract : WeakContract) ->
    Forall (fun abody => match abody with
                         | act_transfer to _ => (to =? caddr)%address = false
                         | _ => False
                         end) (outgoing_acts bstate caddr).
  Proof.
    contract_induction; intros; cbn in *; auto.
    - now inversion IH.
    - apply Forall_app; split; try tauto.
      clear IH.
      unfold receive in receive_some.
      destruct_match as [[]|] in receive_some; try congruence.
      + destruct_match in receive_some; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        inversion_clear receive_some; auto.
      + destruct_match in receive_some; try congruence.
        destruct (buyer prev_state) as [buyer|]; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        inversion_clear receive_some; auto.
      + destruct_match in receive_some; try congruence.
        destruct (buyer prev_state) as [buyer|]; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        * destruct_match in receive_some; cbn in *; try congruence.
          inversion_clear receive_some.
          constructor; try constructor.
          apply address_eq_ne; auto.
        * destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some; cbn in *; try congruence.
          inversion_clear receive_some.
          constructor; try constructor.
          apply address_eq_ne; auto.
      + destruct_match in receive_some; cbn -[Nat.ltb] in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *;
          inversion_clear receive_some; cbn in *; auto.
    - inversion_clear IH as [|? ? head_not_me tail_not_me].
      apply Forall_app; split; auto; clear tail_not_me.
      destruct head; try contradiction.
      destruct action_facts as [? [? ?]].
      destruct_address_eq; congruence.
    - now rewrite <- perm.
    - instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ => True).
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.

  Definition outgoing_txs_to
             {bstate_from bstate_to : ChainState}
             (trace : ChainTrace bstate_from bstate_to)
             (caddr to : Address) : list Tx :=
    filter (fun tx => (tx_to tx =? to)%address) (outgoing_txs trace caddr).

  Definition incoming_txs_from
             {bstate_from bstate_to : ChainState}
             (trace : ChainTrace bstate_from bstate_to)
             (caddr from : Address) : list Tx :=
    filter (fun tx => (tx_from tx =? from)%address) (incoming_txs trace caddr).

  Lemma balance_consistent bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Escrow.contract : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      contract_state bstate caddr = Some cstate /\
      deployment_info trace caddr = Some depinfo /\
      incoming_calls trace caddr = Some inc_calls /\
      let item_worth := deployment_amount depinfo / 2 in
      deployment_amount depinfo = 2 * item_worth /\
      match next_step cstate with
      | buyer_commit => account_balance bstate caddr = 2 * item_worth /\
                        outgoing_acts bstate caddr = []
      | buyer_confirm => account_balance bstate caddr = 4 * item_worth /\
                         outgoing_acts bstate caddr = []
      | withdrawals =>
        cstate.(buyer_withdrawable) + cstate.(seller_withdrawable) +
        sumZ act_body_amount (outgoing_acts bstate caddr) =
        account_balance bstate caddr
      | none => sumZ act_body_amount (outgoing_acts bstate caddr) =
                account_balance bstate caddr
      end.
  Proof.
    contract_induction; intros; cbn in *; auto.
    - unfold Escrow.init in *.
      destruct_match in init_some; cbn in *; try congruence.
      destruct_match in init_some; cbn in *; try congruence.
      destruct_match eqn:amount_even in init_some; cbn in *; try congruence.
      inversion init_some; subst; clear init_some.
      cbn.
      assert (ctx_amount ctx mod 2 = 0).
      {
        rewrite Zeven_mod in amount_even.
        unfold Zeq_bool in *.
        destruct_match eqn:amount_mod_2 in amount_even; try congruence; auto.
        destruct (Z.compare_spec (ctx_amount ctx mod 2) 0); auto; try congruence.
      }
      rewrite <- (Z_div_exact_2 (ctx_amount ctx) 2) by (auto; lia).
      tauto.
    - split; [tauto|].
      destruct IH as [_ IH].
      destruct (next_step cstate); try solve [destruct IH; congruence].
      + lia.
      + lia.
    - split; [tauto|].
      unfold Escrow.receive in *.
      set (item_worth := deployment_amount dep_info / 2) in *.
      destruct msg as [[| | |]|]; try congruence.
      + destruct (next_step prev_state); try congruence.
        destruct_match eqn:proper_amount in receive_some; cbn in *; try congruence.
        inversion_clear receive_some.
        cbn.
        split; try tauto.
        destruct IH as [deployed_even [balance_eq _]].
        apply Z.eqb_eq in proper_amount.
        rewrite balance_eq in proper_amount.
        replace (account_balance _ _) with (2 * item_worth + 2 * item_worth / 2 * 2) by lia.
        change 4 with (2 * 2).
        rewrite <- Z.mul_assoc.
        rewrite <- Z.mul_comm.
        rewrite Z.div_mul by lia.
        lia.
      + destruct_match eqn:prev_next_step in receive_some; cbn in *; try congruence.
        destruct (buyer prev_state); cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match eqn:zero_amount in receive_some; cbn in *; try congruence.
        inversion_clear receive_some.
        cbn.
        destruct IH as [deployed_even [balance_eq ->]].
        apply Z.eqb_eq in zero_amount.
        rewrite zero_amount in *.
        replace (account_balance _ _) with (4 * item_worth) in * by lia.
        cbn.
        rewrite <- Z.mul_comm.
        rewrite Z.div_mul by lia.
        lia.
      + destruct IH as [_ IH].
        destruct_match eqn:prev_next_step in receive_some; cbn in *; try congruence.
        destruct (buyer prev_state) as [buyer|]; cbn in *; try congruence.
        destruct_match eqn:zero_amount in receive_some; cbn in *; try congruence.
        apply Z.eqb_eq in zero_amount.
        rewrite zero_amount in *.
        destruct (address_eqb_spec (ctx_from ctx) buyer) as [->|];
          cbn in *.
        * destruct_match in receive_some; cbn in *; try congruence.
          inversion_clear receive_some.
          cbn.
          destruct (seller_withdrawable _) eqn:prev_seller_withdrawable;
            cbn in *.
          -- lia.
          -- rewrite prev_next_step, prev_seller_withdrawable.
             lia.
          -- rewrite prev_next_step, prev_seller_withdrawable.
             lia.
        * destruct (address_eqb_spec (ctx_from ctx) (seller prev_state)) as [->|];
            cbn in *; try congruence.
          destruct_match in receive_some; cbn in *; try congruence.
          inversion_clear receive_some.
          cbn.
          destruct (buyer_withdrawable _) eqn:prev_buyer_withdrawable;
            cbn in *.
          -- lia.
          -- rewrite prev_next_step, prev_buyer_withdrawable.
             lia.
          -- rewrite prev_next_step, prev_buyer_withdrawable.
             lia.
      + destruct_match eqn:zero_amount in receive_some; cbn -[Nat.ltb] in *; try congruence.
        apply Z.eqb_eq in zero_amount; rewrite zero_amount in *.
        destruct_match in receive_some; cbn -[Nat.ltb] in *; try congruence.
        destruct_match eqn:prev_next_step in receive_some; cbn -[Nat.ltb] in *;
          inversion receive_some; subst; cbn; try congruence.
        * destruct IH as [_ [IH ->]]; cbn; lia.
        * destruct IH as [_ [IH -> ]]; cbn.
          replace (account_balance chain (ctx_contract_address ctx))
            with (item_worth * 2 * 2) by lia.
          rewrite Z.div_mul by lia.
          lia.
    - instantiate (CallFacts := fun _ ctx _ => ctx_from ctx <> ctx_contract_address ctx);
        subst CallFacts; cbn in *.
      congruence.
    - split; try tauto.
      destruct IH as [_ IH].
      destruct_match.
      + split; try tauto; destruct IH as [_ ->].
        auto using Permutation_nil.
      + split; try tauto; destruct IH as [_ ->].
        auto using Permutation_nil.
      + now rewrite <- perm.
      + now rewrite <- perm.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      intros.
      pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption))
           as all.
      unfold outgoing_acts in *.
      rewrite queue_prev in *.
      subst act; cbn in all.
      destruct_address_eq; cbn in *; auto.
      inversion_clear all as [|? ? hd _].
      destruct msg.
      + contradiction.
      + rewrite address_eq_refl in hd.
        congruence.
  Qed.

  Definition net_balance_effect
             {bstate_from bstate_to : ChainState}
             (trace : ChainTrace bstate_from bstate_to)
             (caddr addr : Address) : Amount :=
    sumZ tx_amount (outgoing_txs_to trace caddr addr)
    - sumZ tx_amount (incoming_txs_from trace caddr addr).

  Definition is_escrow_finished cstate :=
    match next_step cstate with
    | none => true
    | _ => false
    end.

  Local Open Scope bool.
  Definition buyer_confirmed (inc_calls : list (ContractCallInfo Msg)) buyer :=
    existsb (fun call => (call_from call =? buyer)%address &&
                         match call_msg call with
                         | Some confirm_item_received => true
                         | _ => false
                         end) inc_calls.

  Corollary escrow_well_behaved
            {ChainBuilder : ChainBuilderType}
            prev new header acts :
    builder_add_block prev header acts = Some new ->
    let trace := builder_trace new in
    forall caddr,
      env_contracts new caddr = Some (Escrow.contract : WeakContract) ->
      exists (depinfo : DeploymentInfo Setup)
             (cstate : State)
             (inc_calls : list (ContractCallInfo Msg)),
        deployment_info trace caddr = Some depinfo /\
        contract_state new caddr = Some cstate /\
        incoming_calls trace caddr = Some inc_calls /\
        let item_worth := deployment_amount depinfo / 2 in
        let seller := deployment_from depinfo in
        let buyer := setup_buyer (deployment_setup depinfo) in
        is_escrow_finished cstate = true ->
        account_balance new caddr = 0 /\
        (* Buyer confirmed and sale succeeded *)
        ((buyer_confirmed inc_calls buyer = true /\
          net_balance_effect trace caddr seller = item_worth /\
          net_balance_effect trace caddr buyer = -item_worth) \/
         (* Buyer did not confirm so seller eventually withdrew their commitment *)
         (buyer_confirmed inc_calls buyer = false /\
          net_balance_effect trace caddr seller = 0 /\
          net_balance_effect trace caddr buyer = 0)).
  Proof.
  Admitted.

End Theories.

End Escrow.
