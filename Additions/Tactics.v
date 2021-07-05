Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import DeepSpec.Runtime.
Require Import backend.MachineModel.
Require Import GenericMachineEnv.


Ltac deepsea_inversion :=
(* Could also be called: inv_runStateT_branching_with_me_transfer_cases *)
  repeat (
    try inv_runStateT_branching;
    let Case := fresh "TransferSuccessCase" in
    try match goal with
      | H : context[me_transfer ?me  _ _] |- _ => 
      unfold me_transfer, me, GenericMachineEnv.generic_machine_env in H;
      destruct (GenericMachineEnv.successful_transfer _ _ _ _) eqn:Case
    end
  ).


(* This is useful in Obj_____CodeProofs.v
Add:
Require Import Additions.Tactics.
*)
Ltac code_proofs_auto :=
    intros;
    unfold synth_func_obligation;
    repeat (split; auto)
.