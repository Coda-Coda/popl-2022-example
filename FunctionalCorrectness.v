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

(*
The goal here is to, in a sense, quantify over an arbitrary snapshot of the Blockchain and then model all possible interactions after that point. In particular, modelling most precisely the smart contract.
*)

Section Blockchain_Model.
Context
  (snapshot_timestamp : int256)
  (snapshot_number : int256)
  (snapshot_blockhash : int256 -> int256)
  (snapshot_balances : addr -> int256).

Context
(address_accepts_funds : machine_env_state global_abstract_data_type -> global_abstract_data_type -> addr -> addr -> int256 -> bool).

Record persistent_state := mkPersistentState {
  ps_timestamp : int256;
  ps_number : int256;
  ps_balance : addr -> int256;
  ps_blockhash : int256 -> int256
}.

Definition snapshot_ps :=
  mkPersistentState
    snapshot_timestamp
    snapshot_number
    snapshot_blockhash
    snapshot_balances
.

Context {HmemOps: MemoryModelOps mem}.
Context {memModelOps : MemoryModelOps mem}.
Instance GlobalLayerSpec : LayerSpecClass := {
  memModelOps := memModelOps;
  GetHighData := global_abstract_data_type 
}.

Context
  (contract_address : addr).

Inductive FunctionCall :=
 | contractStep_token_transfer (a : addr) (amount : int256)
 | contractStep_crowdfunding_donate (value : int256)
 | contractStep_crowdfunding_getFunds
 | contractStep_crowdfunding_claim
.

Inductive ContractCall :=
 | NonExistentFunction (* Calling a function that is not defined for this contract. Causes a revert. *)
 | CallFunction (f : FunctionCall) (origin caller : addr) (callvalue coinbase chainid : int256).

Definition updateTimeAndBlock ps_before block_count time_passing : persistent_state :=
mkPersistentState
  (Int256.add time_passing (ps_timestamp ps_before))
  (Int256.add block_count (ps_number ps_before))
  (ps_balance ps_before)
  (ps_blockhash ps_before)
.

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

Definition extract_balances_from_me (ps_current : persistent_state) : addr -> int256 := 
  ps_balance ps_current.

Definition update_ps_balance ps_before latest_balances : persistent_state :=
  mkPersistentState
  (ps_timestamp ps_before)
  (ps_number ps_before)
  latest_balances
  (ps_blockhash ps_before)
.

Definition noOverflowInTransfer (sender recipient : addr) (amount : int256) (balances : addr -> int256) : bool := 
  ((Int256.intval (balances sender)) - (Int256.intval amount) >=? 0)%Z
  && ((Int256.intval (balances recipient)) + (Int256.intval amount) <=? Int256.max_unsigned)%Z
.

Definition ps_new_balance (ps_before : persistent_state) (d : global_abstract_data_type) : persistent_state :=
  mkPersistentState
    (ps_timestamp ps_before)
    (ps_number ps_before)
    (fun a => GenericMachineEnv.current_balances contract_address (ps_balance ps_before) (ETH_successful_transfers d) a)
    (ps_blockhash ps_before)
.

Definition extract_persistent_state (me : machine_env global_abstract_data_type) (d : global_abstract_data_type) : persistent_state :=
  mkPersistentState
    (me_timestamp me)
    (me_number me)
    (me_balance me d)
    (me_blockhash me)
.

Definition execute_contract_call (* Note that this leaves blocknumber and timestamp UNCHANGED. Changes to these should be handled elsewhere. *)
   (call : ContractCall)
   (d_before : global_abstract_data_type)
   (ps_before : persistent_state)
   : (global_abstract_data_type * persistent_state)
:=
match call with
| NonExistentFunction => (d_before, ps_before)
| CallFunction f origin caller callvalue coinbase chainid =>
  let me_before := GenericMachineEnv.generic_machine_env
  coinbase
  (ps_timestamp ps_before)
  (ps_number ps_before)
  (ps_blockhash ps_before)
  chainid
  origin 
  contract_address
  caller
  callvalue
  (ps_balance ps_before)
  address_accepts_funds
  in  
  match f with
    | contractStep_token_transfer a amount => 
        match runStateT (Crowdfunding_token_transfer_opt a amount me_before) d_before with
        | Some (_, d_after) => (d_after, extract_persistent_state me_before d_after)
        | None => (d_before, ps_before)
        end
    | contractStep_crowdfunding_donate value => (d_before, ps_before)
    | contractStep_crowdfunding_getFunds => (d_before, ps_before)
    | contractStep_crowdfunding_claim => (d_before, ps_before)
  end
end.

Inductive BlockchainAction (ps_before : persistent_state) :=
  | contractExecution (c : ContractCall)
  | timePassing (block_count time_passing : int256)
                (prf : validTimeChange block_count time_passing (ps_number ps_before) (ps_timestamp ps_before) = true)
  | externalBalanceTransfer (sender recipient : addr) (amount : int256)
                            (prf : sender <> contract_address /\  noOverflowInTransfer sender recipient amount (extract_balances_from_me ps_before) = true)
  | noOp.

Record StepInfo := {
  d_before_StepInfo : global_abstract_data_type;
  ps_before_StepInfo : persistent_state;
  next_action_StepInfo : BlockchainAction ps_before_StepInfo
}.

Definition step
  (s : StepInfo)
  : (global_abstract_data_type * persistent_state)
  :=
  let action := next_action_StepInfo s in
  let d_before := d_before_StepInfo s in
  let ps_before := ps_before_StepInfo s in
  match action with
  | contractExecution c =>
      execute_contract_call c d_before ps_before
  | timePassing block_count time_passing prf => 
      (d_before, updateTimeAndBlock ps_before block_count time_passing)
  | externalBalanceTransfer sender recipient amount prf =>
      (d_before, update_ps_balance ps_before (updateBalances sender recipient amount (extract_balances_from_me ps_before)))
  | noOp => (d_before, ps_before)
  end.

Definition Sequence := list StepInfo.

Fixpoint ValidSequence_helper (seq : Sequence) :=
(* Assumes the initial state was valid *)
(* Note that the order in the sequence is increasing, e.g. [1 (init), 2, 3, 4, 5, ...] *)
  match seq with
  | [] => True
  | [s] => True
  | s1 :: ((s2 :: _) as tl) => 
       step s1 = (d_before_StepInfo s2, ps_before_StepInfo s2)
    /\ ValidSequence_helper tl
end.

Definition ValidSequence (seq : Sequence) :=
(* Checks the initial state is valid, then calls ValidSequence_helper *)
(* Note that the order in the sequence is increasing, e.g. [1 (init), 2, 3, 4, 5, ...] *)
  match seq with
  | [] => True
  | s :: _ => 
              d_before_StepInfo s = init_global_abstract_data
           /\ ps_before_StepInfo s = snapshot_ps 
           /\ ValidSequence_helper seq
end.

Inductive ReachableState : global_abstract_data_type -> persistent_state -> Prop :=
  | initialState : ReachableState init_global_abstract_data snapshot_ps (* TODO switch to Crowdfunding_constructor_opt *)
  | blockchainStep : forall s1 me_after d_after,
                      let me_before := ps_before_StepInfo s1 in
                      let d_before := d_before_StepInfo s1 in
                      let blockchain_action := next_action_StepInfo s1 in
                      ReachableState d_before me_before
                      ->
                      (d_after, me_after) = step {| 
                                                   ps_before_StepInfo := me_before;
                                                   d_before_StepInfo := d_before; 
                                                   next_action_StepInfo := blockchain_action
                                                 |}
                      -> ReachableState d_after me_after.

Definition ReachableState' (d_current : global_abstract_data_type) (ps_current : persistent_state) : Prop := 
  let s :=  {| 
              ps_before_StepInfo := ps_current;
              d_before_StepInfo := d_current; 
              next_action_StepInfo := noOp ps_current
            |} in  
exists (seq : Sequence) (prf : ValidSequence seq), Lists.List.In s seq.

Lemma ReachableStateEquivalence : forall (d_current : global_abstract_data_type) (ps_current : persistent_state),
  ReachableState d_current ps_current = ReachableState' d_current ps_current.
(* TODO? *)
  Abort.

End Blockchain_Model.

End FunctionalCorrectness.
