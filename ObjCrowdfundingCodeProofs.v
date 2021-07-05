(* Skeleton by Edgser for Crowdfunding_Based_On_Scilla.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import Crowdfunding_Based_On_Scilla.EdsgerIdents.
Require Import Crowdfunding_Based_On_Scilla.DataTypes.
Require Import Crowdfunding_Based_On_Scilla.DataTypeOps.
Require Import Crowdfunding_Based_On_Scilla.DataTypeProofs.
Require Import Crowdfunding_Based_On_Scilla.LayerCROWDFUNDING.

Require Import Additions.Tactics.

Section EdsgerGen.

Existing Instance GlobalLayerSpec.
Existing Instances CROWDFUNDING_overlay_spec.

Context {memModelOps : MemoryModelOps mem}.

Lemma Crowdfunding_constructor_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_constructor Crowdfunding_constructor_wf
                    me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_constructor_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_constructor Crowdfunding_constructor_wf
                          me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_donate_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_donate Crowdfunding_donate_wf
                    me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_donate_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_donate Crowdfunding_donate_wf
                          me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_getFunds_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_getFunds Crowdfunding_getFunds_wf
                    me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_getFunds_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_getFunds Crowdfunding_getFunds_wf
                          me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_claim_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_claim Crowdfunding_claim_wf
                    me d.
Proof.
    code_proofs_auto.
Qed.

Lemma Crowdfunding_claim_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_claim Crowdfunding_claim_wf
                          me d.
Proof.
    code_proofs_auto.
Qed.

End EdsgerGen.
