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


Section GenericProofs.
Lemma fold_snd_map : 
  forall  A B (m : list (A * B)) x f,

  (fold_left (fun (a : B) (p : A * B) => f a (snd p))
   m x) = 
  (fold_left f
  (map snd m) x).
Proof.
    intro.
    induction m.
    - intros. simpl. reflexivity.
    - intros. simpl. rewrite IHm. reflexivity.
Qed. 

Lemma sum_starting_from_init_equals_sum_plus_init : 
forall (init : Z) (m : Int256Tree.t Z),
  Int256Tree.fold1 Z.add m init = Z.add (Int256Tree.fold1 Z.add m 0) init.
  Proof.
    intros.
    repeat rewrite Int256Tree.fold1_spec.
    assert(
    forall x,
      (fold_left (fun (a : Z) (p : Int256Tree.elt * Z) => Z.add a (snd p))
      (Int256Tree.elements m) x) = 
      (fold_left Z.add
      (map snd (Int256Tree.elements m)) x)).
      {
        intros.
        apply fold_snd_map.
      }
    repeat rewrite H. clear H.
    rewrite <- fold_left_last.
    repeat rewrite fold_symmetric; try (intros; lia).
    remember (map snd (Int256Tree.elements m)) as l.
    clear Heql. clear m. generalize dependent l.
    induction l.
     - simpl. lia.
     - simpl.
      rewrite IHl.
      reflexivity.
  Qed.


Lemma Int256Tree_sum_set_value_initially_zero : 
  forall (m: Int256Tree.t Z32)  k v, Int256Tree.get_default 0 k m = 0
                -> Int256Tree_Properties.sum (Int256Tree.set k v m) = 
                   Int256Tree_Properties.sum m + v.
Proof.
  unfold Z32.
  intros.
  pose (@Int256Tree_Properties.sum_get_default 0 k v (Int256Tree.set k v m)) as Lemma1.
  simpl in Lemma1.
  unfold Int256Tree_Properties.sum.
  rewrite Lemma1; [|  unfold Int256Tree.get_default;
                      rewrite Int256Tree.gss;
                      reflexivity].
  rewrite Int256Tree_Properties.fold1_remove_set; [|intros; lia].
  unfold Int256Tree.get_default in H.

  destruct (Int256Tree.get k m) eqn:Case.
  - rewrite H in Case.
     assert(Zswap : forall x y a : Z, a + x + y = a + y + x) by (intros; lia).
     epose (Int256Tree_Properties.fold1_get Z.add Zswap v Case) as H0.
     rewrite Z.add_0_r in H0.
     rewrite <- H0.
     pose Int256Tree_Properties.sum_extensional.
     apply sum_starting_from_init_equals_sum_plus_init.
   - 
   assert(Int256Tree.get_default 0 k m = 0).
   unfold Int256Tree.get_default.
   rewrite Case. reflexivity. 
   pose (@Int256Tree_Properties.sum_get_default v k 0 m H0).
   rewrite Z.add_0_r in e.
   rewrite <- e.
   apply sum_starting_from_init_equals_sum_plus_init.
Qed.

Lemma EmptyUpdateBalancesIsSame :
  forall a contract_address balances, 
  GenericMachineEnv.current_balances contract_address balances [] a = balances a.
Proof.
  intros.
  unfold GenericMachineEnv.current_balances.
  destruct (Int256.eq a contract_address).
    - unfold GenericMachineEnv.credits_to_address, GenericMachineEnv.debits_from_contract. simpl.
      lia. 
    - unfold GenericMachineEnv.credits_to_address, GenericMachineEnv.debits_from_contract. simpl.
      lia.
Qed.

End GenericProofs.

Module FunctionalCorrectness.

(*
The goal here is to, in a sense, quantify over an arbitrary snapshot of the Blockchain and then model all possible interactions after that point. In particular, modelling most precisely the smart contract.
*)

Section Blockchain_Model.
Context
  (snapshot_timestamp : int256)
  (snapshot_number : int256)
  (snapshot_blockhash : int256 -> int256)
  (snapshot_balances : addr -> Z).

Context
  (snapshot_balances_nonnegative_prf : forall a, 0 <= snapshot_balances a).

Context
(address_accepts_funds : GenericMachineEnv.machine_env_state -> global_abstract_data_type -> addr -> addr -> Z -> bool).

Record persistent_state := mkPersistentState {
  ps_timestamp : int256;
  ps_number : int256;
  ps_balance : addr -> Z;
  ps_blockhash : int256 -> int256
}.

Definition snapshot_ps :=
  mkPersistentState
    snapshot_timestamp
    snapshot_number
    snapshot_balances
    snapshot_blockhash
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
 | CallFunction (f : FunctionCall) (origin caller : addr) (callvalue : Z) (coinbase chainid : int256).

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

Definition update_balances sender recipient amount balances : (addr -> Z) :=
  (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
  fun a => 
  if Int256.eq sender recipient then balances a else
    if Int256.eq a sender then (balances sender) - amount else
     if Int256.eq a recipient then (balances recipient) + amount
      else (balances a).

Definition update_ps_balance ps_before latest_balances : persistent_state :=
  mkPersistentState
  (ps_timestamp ps_before)
  (ps_number ps_before)
  latest_balances
  (ps_blockhash ps_before)
.

Definition noOverflowOrUnderflowInTransfer (sender recipient : addr) (amount : Z) (balances : addr -> Z) : bool := 
  ((balances sender) - amount >=? 0)%Z
  && ((balances recipient) + amount <=? Int256.max_unsigned)%Z
.

Definition ps_new_balance (ps_before : persistent_state) (d : global_abstract_data_type) : persistent_state :=
  mkPersistentState
    (ps_timestamp ps_before)
    (ps_number ps_before)
    (fun a => GenericMachineEnv.current_balances contract_address (ps_balance ps_before) (ETH_successful_transfers d) a)
    (ps_blockhash ps_before)
.

Definition next_persistent_state (me : machine_env global_abstract_data_type) (d : global_abstract_data_type) : persistent_state :=
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
   (prf : ETH_successful_transfers d_before = [])
   : (global_abstract_data_type * persistent_state)
:=
match call with
| NonExistentFunction => (d_before, ps_before)
| CallFunction f origin caller callvalue coinbase chainid =>
  (* Ensure the transfer of callvalue to the contract doesn't overflow, if so revert. *)
  if noOverflowOrUnderflowInTransfer caller contract_address callvalue (ps_balance ps_before)
  then
      let me := GenericMachineEnv.generic_machine_env
      coinbase
      (ps_timestamp ps_before)
      (ps_number ps_before)
      (ps_blockhash ps_before)
      chainid
      origin 
      contract_address
      caller
      callvalue
      (update_balances caller contract_address callvalue (ps_balance ps_before))
      address_accepts_funds
      in
      match f with
      | contractStep_donate amount => 
          match runStateT (Crowdfunding_donate_opt me) d_before with
          | Some (_, d_after) => 
            (d_after, next_persistent_state me d_after)
          | None => (d_before, ps_before) (* Revert *)
          end
      | contractStep_getFunds => 
          match runStateT (Crowdfunding_getFunds_opt me) d_before with
          | Some (_, d_after) => (d_after, next_persistent_state me d_after)
          | None => (d_before, ps_before) (* Revert *)
          end
      | contractStep_claim => 
          match runStateT (Crowdfunding_claim_opt me) d_before with
          | Some (_, d_after) => (d_after, next_persistent_state me d_after)
          | None => (d_before, ps_before) (* Revert *)
          end
    end
  else
    (d_before, ps_before) (* Revert due to overflow of contract_balance or insufficient funds in caller. *)
end.

Lemma OneTransferOnly : forall call d_before ps_before prf,
  (ETH_successful_transfers d_before = [])
  ->
  let (d_after, ps_after) := (execute_contract_call call d_before ps_before prf) in
  (length (ETH_successful_transfers d_after) <= 1)%nat.
  Proof.
    intros.
    destruct call eqn:Case.
    - simpl. rewrite H. auto.
    - unfold execute_contract_call.
      destruct (noOverflowOrUnderflowInTransfer caller
      contract_address callvalue
      (ps_balance ps_before)).
      + destruct f eqn:SCase;
      (simpl;
      match goal with
      | [ |- context[runStateT ?X ]] => destruct (runStateT X) eqn:SSCase end;
      [ destruct p;
        (try (apply SingleTransferCheck.Crowdfunding_donate_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=(update_balances caller contract_address callvalue (ps_balance ps_before))) (address_accepts_funds:=address_accepts_funds) (result:=u); [assumption | apply SSCase]);
        try (apply SingleTransferCheck.Crowdfunding_getFunds_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=(update_balances caller contract_address callvalue (ps_balance ps_before))) (address_accepts_funds:=address_accepts_funds) (result:=u); [assumption | apply SSCase]);
        try (apply SingleTransferCheck.Crowdfunding_claim_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=(update_balances caller contract_address callvalue (ps_balance ps_before))) (address_accepts_funds:=address_accepts_funds) (result:=u); [assumption | apply SSCase]))
      |
        rewrite H; auto
      ]).
      + simpl. rewrite H. auto.
Qed.

Inductive BlockchainAction (ps_before : persistent_state) :=
  | contractExecution (c : ContractCall)
  | timePassing (block_count time_passing : int256)
                (prf : validTimeChange block_count time_passing (ps_number ps_before) (ps_timestamp ps_before) = true)
  | externalBalanceTransfer (sender recipient : addr) (amount : Z)
                            (prf : sender <> contract_address /\  noOverflowOrUnderflowInTransfer sender recipient amount (ps_balance ps_before) = true)
  | noOp.

Record StepInfo := {
  d_before_StepInfo : global_abstract_data_type;
  ps_before_StepInfo : persistent_state;
  next_action_StepInfo : BlockchainAction ps_before_StepInfo
}.

Definition resetTransfers (d : global_abstract_data_type) : global_abstract_data_type :=
  {|
  Crowdfunding_owner := Crowdfunding_owner d;
  Crowdfunding_max_block := Crowdfunding_max_block d;
  Crowdfunding_goal := Crowdfunding_goal d;
  Crowdfunding_backers := Crowdfunding_backers d;
  Crowdfunding_funded := Crowdfunding_funded d;
  Crowdfunding_deadlinePassed_msg := Crowdfunding_deadlinePassed_msg d;
  Crowdfunding_successfullyDonated_msg := Crowdfunding_successfullyDonated_msg d;
  Crowdfunding_alreadyDonated_msg := Crowdfunding_alreadyDonated_msg d;
  Crowdfunding_funded_msg := Crowdfunding_funded_msg d;
  Crowdfunding_failed_msg := Crowdfunding_failed_msg d;
  Crowdfunding_too_early_to_claim_funds_msg := Crowdfunding_too_early_to_claim_funds_msg d;
  Crowdfunding_too_early_to_reclaim_msg := Crowdfunding_too_early_to_reclaim_msg d;
  Crowdfunding_cannot_refund_msg := Crowdfunding_cannot_refund_msg d;
  Crowdfunding_here_is_your_money_msg := Crowdfunding_here_is_your_money_msg d;
  ETH_successful_transfers := nil
|}.


Program Definition step
  (s : StepInfo)
  : (global_abstract_data_type * persistent_state)
  :=
  let action := next_action_StepInfo s in
  let d_before := d_before_StepInfo s in
  let ps_before := ps_before_StepInfo s in
  match action with
  | contractExecution c =>
      execute_contract_call c (resetTransfers d_before) ps_before _
  | timePassing block_count time_passing prf => 
      (d_before, updateTimeAndBlock ps_before block_count time_passing)
  | externalBalanceTransfer sender recipient amount prf =>
      (d_before, update_ps_balance ps_before (update_balances sender recipient amount (ps_balance ps_before)))
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

Definition balance_backed (d : global_abstract_data_type) (ps : persistent_state) : Prop := 
  (Crowdfunding_funded d) = false
  -> Int256Tree_Properties.sum (Crowdfunding_backers d)
     <= (ps_balance ps (contract_address)).

Lemma sufficient_funds_safe : Safe balance_backed. (*First lemma. *)
Proof.
  unfold Safe.
  intros.
  induction H.
  - unfold balance_backed. simpl. intros.
    unfold Int256Tree_Properties.sum. unfold Int256Tree.empty.
    unfold Int256Tree.fold1. simpl.
    apply snapshot_balances_nonnegative_prf.
  - destruct blockchain_action eqn:Case.
    + destruct c eqn:SCase.
      * unfold step in H0. simpl in H0. inversion H0. assumption.
      * destruct f eqn:SSCase.
        {
          unfold step in H0. simpl in H0.
          destruct (noOverflowOrUnderflowInTransfer caller contract_address callvalue
          (ps_balance ps_before));
          [|
            inversion H0;
            unfold resetTransfers; unfold balance_backed; simpl;
            unfold balance_backed in IHReachableState;
            assumption
          ].
          - match goal with
            | H : context[runStateT ?X ] |- _ => destruct (runStateT X) eqn:SSSCase end; [|inversion H0; assumption].
            destruct p.
            Transparent Crowdfunding_donate_opt.
            unfold Crowdfunding_donate_opt in SSSCase.
            inv_runStateT_branching; subst; discriminate.
        }
Abort.

End Blockchain_Model.

End FunctionalCorrectness.
