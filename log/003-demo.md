# 003 — Live demo: the shield catches a bad kernel

demo.sh runs the verified gate on two AI-style kernel proposals:

  Proposal 1 (correct vector-add)       → VERIFIED
  Proposal 2 (addf -> subf, computes a-b) → REJECTED

The wrong kernel differs by one character and computes a-b instead of a+b —
the kind of subtle error a reward-hacked generator emits and a tolerance
test can miss. The gate rejects it by proof, not by sampling.

Gate: checkVectorAdd (sound, axiom-clean).
Shield: shield_sound (induction over arbitrary proposal sequences, axiom-clean).
This is the whole thesis, running.
