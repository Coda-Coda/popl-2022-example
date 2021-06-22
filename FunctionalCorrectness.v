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
 | contractStep_donate (value : int256)
 | contractStep_getFunds
 | contractStep_claim
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
    | contractStep_donate amount => 
        match runStateT (Crowdfunding_donate_opt amount me_before) d_before with
        | Some (_, d_after) => (d_after, extract_persistent_state me_before d_after)
        | None => (d_before, ps_before)
        end
    | contractStep_getFunds => 
        match runStateT (Crowdfunding_getFunds_opt me_before) d_before with
        | Some (_, d_after) => (d_after, extract_persistent_state me_before d_after)
        | None => (d_before, ps_before)
        end
    | contractStep_claim => 
        match runStateT (Crowdfunding_claim_opt me_before) d_before with
        | Some (_, d_after) => (d_after, extract_persistent_state me_before d_after)
        | None => (d_before, ps_before)
        end
  end
end.

Lemma OneTransferOnly : forall call d_before ps_before,
  (ETH_successful_transfers d_before = [])
  ->
  let (d_after, ps_after) := (execute_contract_call call d_before ps_before) in
  (length (ETH_successful_transfers d_after) <= 1)%nat.
  Proof.
    intros.
    destruct call eqn:Case.
    - simpl. rewrite H. auto.
    - destruct f eqn:SCase;
        (simpl;
        match goal with
        | [ |- context[runStateT ?X ]] => destruct (runStateT X) eqn:SSCase end;
        [ destruct p;
          (try (apply SingleTransferCheck.Crowdfunding_donate_opt_single_transfer with (arg1:=value) (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=ps_balance ps_before) (address_accepts_funds:=address_accepts_funds) (result:=u); [assumption | apply SSCase]);
          try (apply SingleTransferCheck.Crowdfunding_getFunds_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=ps_balance ps_before) (address_accepts_funds:=address_accepts_funds) (result:=u); [assumption | apply SSCase]);
          try (apply SingleTransferCheck.Crowdfunding_claim_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=ps_balance ps_before) (address_accepts_funds:=address_accepts_funds) (result:=u); [assumption | apply SSCase]))
        |
          rewrite H; auto
        ])
        .
  Qed.

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

(* Inductive ValidSequence (s : Sequence) : Prop :=
  | validEmptySeq : s = [] -> ValidSequence s
  | validSingletonSeq : match s with
  d_before_StepInfo s = init_global_abstract_data
  /\ ps_before_StepInfo s = snapshot_ps -> ValidSequence seq. *)

Fixpoint ValidSequence (seq : Sequence) :=
(* Note that the order in the sequence is decreasing, e.g. [n, n-1, ..., 2, 1 (init)] *)
match seq with
  | [] => True
  | [s] => (*Initial state validity*)   
           d_before_StepInfo s = init_global_abstract_data
           /\ ps_before_StepInfo s = snapshot_ps      
  | sNew :: ((sCurrent :: _) as tl) => 
  step sCurrent = (d_before_StepInfo sNew, ps_before_StepInfo sNew)
/\ ValidSequence tl
end.

Inductive ReachableState : global_abstract_data_type -> persistent_state -> Prop :=
  | initialState : ReachableState init_global_abstract_data snapshot_ps (* TODO switch to Crowdfunding_constructor_opt *)
  | blockchainStep : forall s_before ps_after d_after,
                      let ps_before := ps_before_StepInfo s_before in
                      let d_before := d_before_StepInfo s_before in
                      let blockchain_action := next_action_StepInfo s_before in
                      ReachableState d_before ps_before
                      ->
                      (d_after, ps_after) = step {| 
                                                   ps_before_StepInfo := ps_before;
                                                   d_before_StepInfo := d_before; 
                                                   next_action_StepInfo := blockchain_action
                                                 |}
                      -> ReachableState d_after ps_after.

Definition ReachableState' (d_current : global_abstract_data_type) (ps_current : persistent_state) : Prop := 
  let s :=  {| 
              ps_before_StepInfo := ps_current;
              d_before_StepInfo := d_current; 
              next_action_StepInfo := noOp ps_current
            |} in  
exists (seq : Sequence) (prf : ValidSequence seq), Lists.List.In s seq.

Definition ReachableState'' (d_current : global_abstract_data_type) (ps_current : persistent_state) : Prop := 
  let head :=  {| 
              ps_before_StepInfo := ps_current;
              d_before_StepInfo := d_current; 
              next_action_StepInfo := noOp ps_current
            |} in  
exists (seq : Sequence) (prf : ValidSequence (head :: seq)), True.

Lemma ValidSequenceOfShorter :
  forall a seq, ValidSequence (a :: seq) -> ValidSequence (seq).
Proof.
  intros.
  destruct seq.
   - simpl; apply I.
   - simpl in *. destruct H.
     assumption.
Qed.

Lemma ValidSequenceSub : forall s1 s2, ValidSequence (s1 ++ s2) -> ValidSequence s2.
Proof.
  induction s1.
   - intros. rewrite app_nil_l in H. assumption.
   - intros. rewrite <- app_comm_cons in H.
     apply ValidSequenceOfShorter in H.
     auto.
Qed.

Lemma ReachableStateEquivalence'' : forall (d_current : global_abstract_data_type) (ps_current : persistent_state),
  ReachableState' d_current ps_current <-> ReachableState'' d_current ps_current.
  Proof.
    split.
     - intros.
       destruct H. destruct H.
       unfold ReachableState''.
       apply in_split in H.
       destruct H. destruct H.
       rewrite H in x0.
       pose proof (ValidSequenceSub x1 ({|
       d_before_StepInfo := d_current;
       ps_before_StepInfo := ps_current;
       next_action_StepInfo := noOp ps_current |} :: x2) x0).
       exists x2.
       exists H0.
       reflexivity.
     - intros. destruct H. destruct H. destruct H.
       unfold ReachableState'.
       exists ({|
       d_before_StepInfo := d_current;
       ps_before_StepInfo := ps_current;
       next_action_StepInfo := noOp ps_current |} :: x).
       exists x0.
       simpl. left. reflexivity.
  Qed. 

Lemma ListSplit : forall {A:Type} l, exists (l1 l2 : list A), l = l1 ++ l2.
Proof.
intros.
exists l. exists [].
simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma ReachableStateEquivalence' : forall (d_current : global_abstract_data_type) (ps_current : persistent_state),
  ReachableState d_current ps_current <-> ReachableState'' d_current ps_current.
Proof.
  split.
    - intros.
      induction H.
      + unfold ReachableState''.
        exists [].
        assert(ValidSequence
        [{|
         d_before_StepInfo := init_global_abstract_data;
         ps_before_StepInfo := snapshot_ps;
         next_action_StepInfo := noOp snapshot_ps |}]).
        simpl. split; reflexivity.
        exists H.
        reflexivity.
      + unfold ReachableState'' in IHReachableState.
        destruct IHReachableState. destruct H1. destruct H1.
        unfold ReachableState''.
        destruct (step
        {|
        d_before_StepInfo := d_before;
        ps_before_StepInfo := ps_before;
        next_action_StepInfo := blockchain_action |}) eqn:Case.
        inversion H0.
        subst.
        exists ({|
        d_before_StepInfo := d_before;
        ps_before_StepInfo := ps_before;
        next_action_StepInfo := blockchain_action |} :: x).
        assert(ValidSequence
        ({|
         d_before_StepInfo := g;
         ps_before_StepInfo := p;
         next_action_StepInfo := noOp p |}
         :: {|
            d_before_StepInfo := d_before;
            ps_before_StepInfo := ps_before;
            next_action_StepInfo := blockchain_action |} :: x)).
            {
              simpl. split. assumption.
              destruct x eqn:SCase.
                - simpl in x0. assumption.
                - split.
                  + simpl in x0. destruct x0. assumption.
                  + apply ValidSequenceOfShorter in x0. assumption.
            }
        exists H1.
        reflexivity.
  - intros.
    unfold ReachableState'' in H.
    destruct H as [seq [Hseq Hs]].
    clear Hs. revert Hseq. revert ps_current. revert d_current. revert seq.
    induction seq.
    + intros.
      simpl in Hseq.
      destruct Hseq.
      subst.
      apply initialState.
    + destruct a eqn:Ha.
      pose proof (IHseq d_before_StepInfo0 ps_before_StepInfo0).
      intros.
      pose proof Hseq as HseqCopy.
      apply ValidSequenceOfShorter in Hseq.
      apply H in Hseq.
      apply blockchainStep with (s_before:=a). rewrite Ha. simpl. assumption.
      
      simpl in HseqCopy.
      destruct HseqCopy.
      symmetry. rewrite Ha. simpl. assumption.
Qed.

Lemma ReachableStateEquivalence''' : forall (d_current : global_abstract_data_type) (ps_current : persistent_state),
  ReachableState d_current ps_current <-> ReachableState' d_current ps_current.
  Proof.
    intros.
    rewrite ReachableStateEquivalence'.
    rewrite ReachableStateEquivalence''.
    split; intros; assumption.
  Qed.

Hint Rewrite ReachableStateEquivalence' ReachableStateEquivalence'' ReachableStateEquivalence''' : ReachableStateEquivalencesHints.

Lemma ReachableStateEquivalences : forall (d_current : global_abstract_data_type) (ps_current : persistent_state),
   (ReachableState d_current ps_current <-> ReachableState' d_current ps_current)
/\ (ReachableState' d_current ps_current <-> ReachableState'' d_current ps_current)
/\ (ReachableState'' d_current ps_current <-> ReachableState d_current ps_current).
Proof.
  intros.
  autorewrite with ReachableStateEquivalencesHints.
  remember (ReachableState'' d_current ps_current) as A.
  clear.
  firstorder.
Qed.

(* Start of Crowdfunding Proofs. *)

Definition Safe (P : global_abstract_data_type -> persistent_state -> Prop ) :=
   forall d ps, ReachableState d ps -> P d ps.

Definition sumInt256Tree (t : Int256Tree.t int256) : Z := 
  List.fold_left 
    (fun z elem => (Int256.unsigned (snd elem) + z)%Z)
    (Int256Tree.elements t)
    0%Z.

Definition balance_backed (d : global_abstract_data_type) (ps : persistent_state) : Prop := 
  (Crowdfunding_funded d) = false
  -> sumInt256Tree (Crowdfunding_backers d)
     <= Int256.unsigned (ps_balance ps (contract_address)).

Lemma sufficient_funds_safe : Safe balance_backed. (*First lemma. *)
Proof.
  (* TODO, prove. *)
Abort.

End Blockchain_Model.

End FunctionalCorrectness.
