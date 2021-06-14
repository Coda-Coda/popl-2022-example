(* Require Import DeepSpec.Advice. *)
Require Import DataTypeOps.
Require Import LayerCROWDFUNDING.
Require Import LayerETH_layer.

Require Import DeepSpec.lib.Monad.StateMonadOption.
Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import lib.ArithInv.
Import DeepSpec.lib.Monad.Monad.MonadNotation.

Require Import Lia.
Require Import List.
Require Import ZArith.
Require Import cclib.Maps.
Require Import cclib.Integers.

Require Import DataTypes.
Require Import SingleTransferCheck.
Require Import backend.MachineModel.

Require Import DataTypes.
Import ListNotations.

Require Import core.MemoryModel. 
Require Import HyperTypeInst.
Require Import SingleTransferCheck.
Require Import GenericMachineEnv.

Require Import Additions.Tactics.

Open Scope Z.

Module FunctionalCorrectness.

Section Block_Context. (* like bstep *)
(* "Forall Blocks:" *)
Context
  (coinbase : int256)
  (timestamp : int256)
  (number : int256)
  (blockhash : int256 -> int256)
  (chainid : int256).

Section Nested_Calls_Context.
(* "Forall calls from EoA:" *)
Context
  (origin: addr).

Section Individual_Call_Context. (* like mstep *)
(* "Forall function calls: "*)
Context 
  (contract_address : addr)
  (caller: addr)
  (callvalue : int256)
  (initial_balances : addr -> int256)
  (address_always_accepts_funds : addr -> bool).

  Context {HmemOps: MemoryModelOps mem}.
  Context {memModelOps : MemoryModelOps mem}.
  Instance GlobalLayerSpec : LayerSpecClass := {
    memModelOps := memModelOps;
    GetHighData := global_abstract_data_type 
  }.
  
Definition initial_me := 
  GenericMachineEnv.generic_machine_env coinbase timestamp number blockhash chainid origin contract_address caller callvalue initial_balances address_always_accepts_funds.

  (*
From the Scilla repository: https://github.com/Zilliqa/scilla-coq/blob/master/Contracts/Crowdfunding.v
Definition balance_backed (st: cstate crowdState) : Prop :=
  (* If the campaign not Crowdfunding_funded... *)
  ~~ (Crowdfunding_funded (state st)) ->
  (* the contract has enough funds to reimburse everyone. *)
  sumn (map snd (Crowdfunding_backers (state st))) <= balance st.
*)

Inductive ContractCall :=
 | NoOp
 | contractStep_token_transfer (a : addr) (amount : int256)
 | contractStep_crowdfunding_donate (value : int256)
 | contractStep_crowdfunding_getFunds
 | contractStep_crowdfunding_claim
.

Definition updateTimeAndBlock me_before block_count time_passing : 
(machine_env global_abstract_data_type) :=
(* TODO-Daniel consider using the style of update_me_balance instead. *)
  {|  me_address := me_address me_before;
      me_origin := me_origin me_before;
      me_caller := me_caller me_before;
      me_callvalue := me_callvalue me_before;
      me_coinbase := me_coinbase me_before; 
      me_timestamp := Int256.add time_passing (me_timestamp me_before);
      me_number := Int256.add block_count (me_number me_before);
      me_balance := me_balance me_before;
      me_blockhash := me_blockhash me_before;
      me_transfer := me_transfer me_before;
      me_callmethod := me_callmethod me_before;
      me_log := me_log me_before;
      me_chainid := me_chainid me_before;
      me_selfbalance := me_selfbalance me_before;
|}.

Definition validTimeChange block_count time_passing current_block_number current_timestamp : bool :=
  (* Note, testing for positive block_count and time_passing is unnecessary while they are Int256 values.
     It would be necessary to add positivity checks if using Z instead of course. *)
  ((Int256.intval block_count) + (Int256.intval current_block_number) <=? Int256.max_unsigned)%Z
  && ((Int256.intval time_passing) + (Int256.intval current_timestamp) <=? Int256.max_unsigned)%Z.

Definition updateBalances sender recipient amount balances : (addr -> int256) :=
  (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
  fun a => if Int256.eq a sender then Int256.sub (balances sender) amount
  else if Int256.eq a recipient then Int256.add (balances recipient) amount
  else (balances a).

Definition extract_balances_from_me (me_current : machine_env global_abstract_data_type) : addr -> int256 := 
   (* For the purposes of being able to retreive balances outside of a contract call init_global_abstract_data is used which *really should* have nil for ETH_successful_transfers. *) (*TODO-Daniel, that we have to do this is a little messy. *)
  me_balance me_current init_global_abstract_data.

Definition update_me_balance me_before current_balances : machine_env global_abstract_data_type :=
  GenericMachineEnv.generic_machine_env (me_coinbase me_before) (me_timestamp me_before) (me_number me_before) (me_blockhash me_before) (me_chainid me_before) (me_origin me_before) (me_address me_before) (me_caller me_before) (@me_callvalue global_abstract_data_type me_before) current_balances address_always_accepts_funds.

Definition noOverflowInTransfer (sender recipient : addr) (amount : int256) (balances : addr -> int256) : bool := 
  ((Int256.intval (balances sender)) - (Int256.intval amount) >=? 0)%Z
  && ((Int256.intval (balances recipient)) + (Int256.intval amount) <=? Int256.max_unsigned)%Z
.


Definition execute_contract_call (* Note that this leaves blocknumber and timestamp UNCHANGED. Changes to these should be handled elsewhere. *)
   (call : ContractCall)
   (d_before : global_abstract_data_type)
   (me_before : (machine_env (global_abstract_data_type)))
   : (global_abstract_data_type * (machine_env global_abstract_data_type))
:=
match call with
| NoOp => (d_before, me_before)
| contractStep_token_transfer a amount => 
    match runStateT (Crowdfunding_token_transfer_opt a amount me_before) d_before with
    | Some (_, d_after) => (d_after, me_before) (* TODO fix me return value esp. balances. *)
    | None => (d_before, me_before)
    end
| contractStep_crowdfunding_donate value => (d_before, me_before)
| contractStep_crowdfunding_getFunds => (d_before, me_before)
| contractStep_crowdfunding_claim => (d_before, me_before)
end.

Inductive BlockchainAction (me_before : machine_env global_abstract_data_type) :=
  | contractExecution (c : ContractCall)
  | timePassing (block_count time_passing : int256)
                (prf : validTimeChange block_count time_passing (me_number me_before) (me_timestamp me_before) = true)
  | externalBalanceTransfer (sender recipient : addr) (amount : int256)
                            (prf : sender <> contract_address /\  noOverflowInTransfer sender recipient amount (extract_balances_from_me me_before) = true)
  | noOp.

Record StepInfo := {
  d_before_StepInfo : global_abstract_data_type;
  me_before_StepInfo : machine_env global_abstract_data_type;
  next_action_StepInfo : BlockchainAction me_before_StepInfo
}.

Definition step
  (s : StepInfo)
  : (global_abstract_data_type * (machine_env global_abstract_data_type))
  :=
  let action := next_action_StepInfo s in
  let d_before := d_before_StepInfo s in
  let me_before := me_before_StepInfo s in
  match action with
  | contractExecution c =>
      execute_contract_call c d_before me_before
  | timePassing block_count time_passing prf => 
      (d_before, updateTimeAndBlock me_before block_count time_passing)
  | externalBalanceTransfer sender recipient amount prf =>
      (d_before, update_me_balance me_before (updateBalances sender recipient amount (extract_balances_from_me me_before)))
  | noOp => (d_before, me_before)
  end.

Definition Sequence := list StepInfo.

Fixpoint ValidSequence_helper (seq : Sequence) :=
(* Assumes the initial state was valid *)
(* Note that the order in the sequence is increasing, e.g. [1 (init), 2, 3, 4, 5, ...] *)
  match seq with
  | [] => True
  | [s] => True
  | s1 :: ((s2 :: _) as tl) => 
       step s1 = (d_before_StepInfo s2, me_before_StepInfo s2)
    /\ ValidSequence_helper tl
end.

Definition ValidSequence (seq : Sequence) :=
(* Checks the initial state is valid, then calls ValidSequence_helper *)
(* Note that the order in the sequence is increasing, e.g. [1 (init), 2, 3, 4, 5, ...] *)
  match seq with
  | [] => True
  | s :: _ => 
              d_before_StepInfo s = init_global_abstract_data
           /\ me_before_StepInfo s = initial_me 
           /\ ValidSequence_helper seq
end.

Inductive ReachableState : global_abstract_data_type -> (machine_env (global_abstract_data_type)) -> Prop :=
  | initialState : ReachableState init_global_abstract_data initial_me (* TODO switch to Crowdfunding_constructor_opt *)
  | blockchainStep : forall s1 me_after d_after,
                      let me_before := me_before_StepInfo s1 in
                      let d_before := d_before_StepInfo s1 in
                      let blockchain_action := next_action_StepInfo s1 in
                      ReachableState d_before me_before
                      ->
                      (d_after, me_after) = step {| 
                                                   me_before_StepInfo := me_before;
                                                   d_before_StepInfo := d_before; 
                                                   next_action_StepInfo := blockchain_action
                                                 |}
                      -> ReachableState d_after me_after.

Definition ReachableState' (d_current : global_abstract_data_type) (me_current : machine_env (global_abstract_data_type)) : Prop := 
  let s :=  {| 
              me_before_StepInfo := me_current;
              d_before_StepInfo := d_current; 
              next_action_StepInfo := noOp me_current
            |} in  
exists (seq : Sequence) (prf : ValidSequence seq), Lists.List.In s seq.

Lemma ReachableStateEquivalence : forall (d_current : global_abstract_data_type) (me_current : machine_env (global_abstract_data_type)),
  ReachableState d_current me_current = ReachableState' d_current me_current.
(* TODO? *)
  Abort.

End Individual_Call_Context.

End Nested_Calls_Context.

End Block_Context.

End FunctionalCorrectness.
