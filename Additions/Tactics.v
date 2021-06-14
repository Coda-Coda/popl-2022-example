Require Import DeepSpec.lib.Monad.RunStateTInv.
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