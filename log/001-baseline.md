# 001 — Baseline

New repo `admitto`, forked from Trident post-pivot.

`lake build Trident.Proofs.Checker` → completes successfully.

Trusted base confirmed clean:
checkVectorAdd_sound depends on axioms: [propext, Classical.choice, Quot.sound]
— no sorryAx, no native_decide leakage.

The gate is sound. Dead chain (evalInstr_faithful, symEval_sound, ~93 sorries
in Soundness.lean lines 1223–1538) still present but unreferenced by the live
path. Next: purge it, then build the envelope.
