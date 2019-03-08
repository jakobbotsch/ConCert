From SmartContracts Require Import Monads.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import LocalBlockchain.
From SmartContracts Require Import Congress.
From SmartContracts Require Import Oak.
From Containers Require SetInterface MapInterface OrderedTypeEx.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.

Section LocalBlockchainTests.
  (* Addresses *)
  Let congress_1 := 1.
  Let baker := 10.
  Let person_1 := 11.
  Let person_2 := 12.
  Let person_3 := 13.

  Let otry x :=
    match x with
    | Some y => y
    | None => LocalBlockchain.initial_chain
    end.
  Let lce_to_chain l := build_chain lc_interface l.(lce_lc) .
  Local Coercion lce_to_chain : LocalChainEnvironment >-> Chain.

  Let chain1 :=
    LocalBlockchain.initial_chain.

  (* Baker mines an empty block (and gets some coins) *)
  Let chain2 :=
    otry (LocalBlockchain.add_block baker [] chain1).

  Compute (account_balance chain2 person_1).
  Compute (account_balance chain2 baker).

  (* Baker transfers 10 coins to person_1 *)
  Let chain3 :=
    otry (LocalBlockchain.add_block baker [(baker, act_transfer person_1 10)] chain2).

  Compute (account_balance chain3 person_1).
  Compute (account_balance chain3 baker).

  (* person_1 deploys a Congress contract *)
  Let setup_rules :=
    {| min_vote_count_permille := 200; (* 20% of congress needs to vote *)
       margin_needed_permille := 500;
       debating_period_in_blocks := 0; |}.

  Let setup := Congress.build_setup setup_rules.

  Let deploy_congress : ChainAction :=
    create_deployment 5 Congress.contract setup.

  Let chain4 :=
    otry (LocalBlockchain.add_block baker [(person_1, deploy_congress)] chain3).

  Compute (contract_deployment chain4 congress_1).
  Compute (account_balance chain4 person_1).
  Compute (account_balance chain4 baker).
  Compute (account_balance chain4 congress_1).

  Let congress_ifc :=
    match get_contract_interface
            chain4 congress_1
            Congress.Setup Congress.Msg Congress.State with
    | Some x => x
    (* This stuff is just to make the test example easier
       since we know it will not fail *)
    | None =>
      build_contract_interface
        0
        0
        setup
        (fun c => None)
        (fun a => deploy_congress)
        (fun a m => deploy_congress)
    end.

  Let congress_state chain : Congress.State :=
    match congress_ifc.(get_state) chain with
    | Some s => s
    | None => {| owner := 0;
                 state_rules := setup_rules;
                 proposals := MapInterface.empty Proposal;
                 next_proposal_id := 0;
                 members := SetInterface.empty |}
    end.

  Compute (congress_ifc.(get_state) chain4).
  Compute (SetInterface.elements (congress_state chain4).(members)).

  (* person_1 adds person_1 and person_2 as members of congress *)
  Let add_person p :=
    congress_ifc.(call) 0 (add_member p).

  Let chain5 := otry (LocalBlockchain.add_block baker [(person_1, add_person person_1) ;
                                                       (person_1, add_person person_2)] chain4).

  Compute (SetInterface.elements (congress_state chain4).(members)).
  Compute (account_balance chain5 congress_1).

  (* person_1 creates a proposal to send 3 coins to person_3 using funds
     of the contract *)
  Let create_proposal_call :=
    congress_ifc.(call) 0 (create_proposal [cact_transfer person_3 3]).

  Let chain6 := otry (LocalBlockchain.add_block baker [(person_1, create_proposal_call)] chain5).
  Compute (MapInterface.elements (congress_state chain6).(proposals)).

  (* person_1 and person_2 votes for the proposal *)
  Let vote_proposal :=
    congress_ifc.(call) 0 (vote_for_proposal 1).

  Let chain7 := otry (LocalBlockchain.add_block baker [(person_1, vote_proposal);
                                                       (person_2, vote_proposal)] chain6).
  Compute (MapInterface.elements (congress_state chain7).(proposals)).

  (* Finish the proposal *)
  Let finish_proposal :=
    congress_ifc.(call) 0 (finish_proposal 1).

  Let chain8 := otry (LocalBlockchain.add_block baker [(person_1, finish_proposal)] chain7).
  (* Balances before: *)
  Compute (account_balance chain7 congress_1).
  Compute (account_balance chain7 person_3).
  (* Balances after: *)
  Compute (account_balance chain8 congress_1).
  Compute (account_balance chain8 person_3).
End LocalBlockchainTests.
