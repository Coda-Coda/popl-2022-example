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

Lemma sum_set_0_remove : 
  forall k m,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) 0 =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) 0.
Proof.
  intros.
  pose (Int256Tree.grs k m).
  pose (Int256Tree_Properties.set_permutation 0 e).
  rewrite <- Int256Tree_Properties.elements_set_decompose in p.
  repeat rewrite Int256Tree.fold1_spec.
  assert(Hf_comm : forall (b1 b2 : Int256Tree.elt * Z) (a : Z),
  a + snd b1 + snd b2 = a + snd b2 + snd b1) by (intros; lia).
  epose (@Int256Tree_Properties.fold1_permutation 
            _ _ (fun (a:Z) (p0 : Int256Tree.elt * Z) => a + snd p0)
            Hf_comm
            (Int256Tree.elements (Int256Tree.set k 0 m))
            ((k, 0) :: Int256Tree.elements (Int256Tree.remove k m))
            p).
  rewrite e0.
  simpl.
  reflexivity.
Qed.

Lemma sum_set_0_minus : forall k m v, Int256Tree.get_default 0 k m = v ->
Int256Tree_Properties.sum (Int256Tree.set k 0 m) = Int256Tree_Properties.sum m - v.
Proof.
  intros.
  unfold Int256Tree_Properties.sum.
  unfold Int256Tree.get_default in H.
  destruct (Int256Tree.get k m) eqn:Case.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      epose (Int256Tree_Properties.fold1_get Z.add H 0 Case).
      rewrite e.
      simpl.
      rewrite (sum_starting_from_init_equals_sum_plus_init v).
      Set Printing All.
      assert((Z.sub
      (Z.add (@Int256Tree.fold1 Z Z Z.add (@Int256Tree.remove Z k m) Z0) v) v) = 
      (@Int256Tree.fold1 Z Z Z.add (@Int256Tree.remove Z k m) Z0)).
      lia.
      rewrite H0.
      apply sum_set_0_remove.
  - unfold HyperType.ht_default in H. subst.
    rewrite Z.sub_0_r.
    pose (Int256Tree_Properties.set_permutation 0 Case).
    repeat rewrite Int256Tree.fold1_spec.
    rewrite Int256Tree_Properties.fold1_permutation 
      with (l':=((k, 0) :: Int256Tree.elements m)); [|intros; lia|assumption].
    simpl. reflexivity.
Qed.


Lemma Int256Tree_sum_minus : 
  forall m k x,
    Int256Tree_Properties.sum m <= x
    ->
    Int256Tree_Properties.sum (Int256Tree.set k 0 m) <=
    x - (Int256Tree.get_default 0 k m).
    intros.
    rewrite sum_set_0_minus with (v:= Int256Tree.get_default 0 k m) by reflexivity.
    lia.
Qed.


End GenericProofs.

Ltac inv_runStateT_branching_with_me_transfer_cases :=
      repeat (
        try inv_runStateT_branching;
        let Case := fresh "SufficientFundsToTransferCase" in
        try match goal with
          | H : context[me_transfer _  _ _] |- _ => 
          unfold me_transfer, GenericMachineEnv.generic_machine_env in H;
          destruct (GenericMachineEnv.successful_transfer _ _ _ _) eqn:Case
        end
      ).

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

(* The following is reasonable to assume. *)
Definition address_accepts_funds_guaranteed_for_contract 
  mes d sender recipient amount :=
  if Int256.eq sender contract_address then true else
  address_accepts_funds mes d sender recipient amount.

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
      address_accepts_funds_guaranteed_for_contract
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
        (try (apply SingleTransferCheck.Crowdfunding_donate_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=(update_balances caller contract_address callvalue (ps_balance ps_before))) (address_accepts_funds:=address_accepts_funds_guaranteed_for_contract) (result:=u); [assumption | apply SSCase]);
        try (apply SingleTransferCheck.Crowdfunding_getFunds_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=(update_balances caller contract_address callvalue (ps_balance ps_before))) (address_accepts_funds:=address_accepts_funds_guaranteed_for_contract) (result:=u); [assumption | apply SSCase]);
        try (apply SingleTransferCheck.Crowdfunding_claim_opt_single_transfer with (d:=d_before) (coinbase:=coinbase) (timestamp:=ps_timestamp ps_before) (number:=ps_number ps_before) (blockhash:=ps_blockhash ps_before) (chainid:=chainid) (origin:=origin) (contract_address:=contract_address) (caller:=caller) (callvalue:=callvalue) (initial_balances:=(update_balances caller contract_address callvalue (ps_balance ps_before))) (address_accepts_funds:=address_accepts_funds_guaranteed_for_contract) (result:=u); [assumption | apply SSCase]))
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
                            (prf : sender <> contract_address /\ amount >= 0 /\  noOverflowOrUnderflowInTransfer sender recipient amount (ps_balance ps_before) = true)
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

Lemma addZeroBalance : forall ps_before caller contract_address,
GenericMachineEnv.current_balances contract_address
              (update_balances caller contract_address 0 (ps_balance ps_before)) []
              contract_address = (ps_balance ps_before) contract_address.
Proof.
  intros.
  unfold GenericMachineEnv.current_balances, update_balances, GenericMachineEnv.credits_to_address, GenericMachineEnv.debits_from_contract.
  rewrite Int256.eq_true.
  destruct (Int256.eq caller contract_address0) eqn:Case.
  - simpl. 
    repeat rewrite Z.add_0_r.
    repeat rewrite Z.sub_0_r.
    reflexivity.
  - rewrite Int256.eq_sym in Case.
    rewrite Case.
    repeat rewrite Z.add_0_r.
    repeat rewrite Z.sub_0_r.
    reflexivity.
Qed.

(* Start of Crowdfunding Proofs. *)

Definition Safe (P : global_abstract_data_type -> persistent_state -> Prop ) :=
   forall d ps, ReachableState d ps -> P d ps.

Definition balance_backed (d : global_abstract_data_type) (ps : persistent_state) : Prop := 
  (Crowdfunding_funded d) = false
  -> Int256Tree_Properties.sum (Crowdfunding_backers d)
     <= (ps_balance ps (contract_address)).

Lemma balance_backed_in_next_state : forall d_before d_after ps_before callvalue caller origin chainid coinbase,
     balance_backed d_before ps_before -> d_after = resetTransfers d_before -> (callvalue =? 0) = true -> negb (Int256.eq caller contract_address) = true -> balance_backed (resetTransfers d_before)
                 (next_persistent_state
                    (GenericMachineEnv.generic_machine_env coinbase 
                       (ps_timestamp ps_before) (ps_number ps_before)
                       (ps_blockhash ps_before) chainid origin contract_address caller
                       callvalue
                       (update_balances caller contract_address callvalue
                          (ps_balance ps_before)) address_accepts_funds_guaranteed_for_contract)
                    (resetTransfers d_before)).
Proof.
  intros.
  unfold resetTransfers; unfold balance_backed; simpl.
  unfold balance_backed in H.
  apply Z.eqb_eq in H1.
  rewrite H1.
  rewrite addZeroBalance.
  assumption.
Qed.

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
          match goal with
          | H : context[runStateT ?X ] |- _ => destruct (runStateT X) eqn:SSSCase end; [|inversion H0; assumption].
          destruct p.
          Transparent Crowdfunding_donate_opt.
          unfold Crowdfunding_donate_opt in SSSCase.
          inv_runStateT_branching; subst; try discriminate.
          - inversion H0. unfold next_persistent_state. simpl.
            unfold GenericMachineEnv.current_balances.
            unfold GenericMachineEnv.debits_from_contract.
            unfold GenericMachineEnv.credits_to_address.
            simpl.
            unfold balance_backed. simpl.
            repeat rewrite Z.add_0_r. rewrite Z.sub_0_r.
            rewrite Int256.eq_true.
            intros.
            unfold balance_backed in IHReachableState.
            apply IHReachableState in H1.
            unfold update_balances.
            rewrite Int256.eq_true.
            unfold GenericMachineEnv.generic_machine_env in Heqb0. simpl in Heqb0.
            apply Z.eqb_eq in Heqb0.
            destruct (Int256.eq contract_address caller) eqn:SSSCase;
            [
              apply Int256eq_true in SSSCase;
              unfold GenericMachineEnv.generic_machine_env in H5; simpl in H5;
              rewrite SSSCase in H5;
              clear -H5;
              rewrite Int256.eq_true in H5; 
              discriminate
            |].
            rewrite Int256Tree_sum_set_value_initially_zero; [|assumption].
            rewrite Int256.eq_sym, SSSCase.
            rewrite <- Z.add_le_mono_r.
            assumption.
        }
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
          match goal with
          | H : context[runStateT ?X ] |- _ => destruct (runStateT X) eqn:SSSCase end; [|inversion H0; assumption].
          destruct p.
          Transparent Crowdfunding_getFunds_opt.
          unfold Crowdfunding_getFunds_opt in SSSCase.
          inv_runStateT_branching; subst.
          2,3,4 : inversion H0; apply balance_backed_in_next_state with (d_after:=d_after); assumption.
          unfold balance_backed.
          intros.
          inv_runStateT_branching_with_me_transfer_cases; subst.
          - match goal with | H : (d_after, ps_after) = _ |- _ => inversion H end.
            subst. inversion H1.
          - rewrite Int256.eq_true in Heqb2. discriminate.
          - rewrite Int256.eq_false in Heqb2 by (unfold not; intros; discriminate). discriminate.
          - simpl in SSSCase1. inversion SSSCase1.
        }
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
          match goal with
          | H : context[runStateT ?X ] |- _ => destruct (runStateT X) eqn:SSSCase end; [|inversion H0; assumption].
          destruct p.
          Transparent Crowdfunding_claim_opt.
          unfold Crowdfunding_claim_opt in SSSCase.
          inv_runStateT_branching; subst.
          1,2 : inversion H0; apply balance_backed_in_next_state with (d_after:=d_after); assumption.
          inversion H0; subst.
          inv_runStateT_branching_with_me_transfer_cases; subst.
          simpl.
          all: simpl in SufficientFundsToTransferCase.
          - clear Heqb1.
            unfold balance_backed.
            unfold GenericMachineEnv.d_with_transfer.
            simpl.
            intros.
            apply IHReachableState in H1.
            unfold GenericMachineEnv.current_balances.
            rewrite Int256.eq_true.
            unfold GenericMachineEnv.debits_from_contract, GenericMachineEnv.credits_to_address.
            simpl.
            simpl in H5.
            destruct (Int256.eq caller contract_address) eqn:SCase; try discriminate.
            unfold update_balances.
            rewrite SCase.
            rewrite Int256.eq_sym in SCase.
            rewrite SCase.
            rewrite Int256.eq_true.
            Search callvalue 0.
            simpl in H11.
            rewrite Z.eqb_eq in H11.
            rewrite H11.
            repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
            apply Int256Tree_sum_minus.
            assumption.
          - rewrite Int256.eq_true in Heqb1. discriminate.
          - rewrite Int256.eq_false in Heqb1 by (unfold not; intros; discriminate). discriminate.
          - simpl in SSSCase1. inversion SSSCase1.
        }
    + unfold step in H0. simpl in H0. inversion H0.
      unfold balance_backed.
      unfold updateTimeAndBlock.
      simpl.
      assumption.
    + unfold step in H0. simpl in H0. inversion H0.
      unfold balance_backed.
      unfold update_ps_balance.
      simpl.
      destruct prf. destruct a.
      intros.
      apply IHReachableState in H1.
      unfold update_balances.
      destruct (Int256.eq sender recipient); try assumption.
      destruct (Int256.eq contract_address sender) eqn:SCase.
        * apply Int256eq_true in SCase. symmetry in SCase. contradiction.
        * destruct(Int256.eq contract_address recipient) eqn:SSCase.
          -- apply Int256eq_true in SSCase. rewrite <- SSCase. lia.
          -- assumption.
    + unfold step in H0. simpl in H0. inversion H0.
      assumption.
Qed.

Print Assumptions sufficient_funds_safe.

End Blockchain_Model.

End FunctionalCorrectness.
