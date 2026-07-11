# Admitto

A **general, machine-checked construction** for verified safety shields for AI
systems.

An untrusted AI component — a code generator, an agent — proposes actions. A
**sound gate** admits only actions proven to satisfy a specification, and a
**mechanized induction** proves that across *any* sequence of actions the AI
proposes, the system stays safe. The AI is universally quantified out of every
theorem: the guarantee does not depend on its behavior or capability.

The construction is defined once (`Admitto/Core.lean`) and instantiated across
three domains. Every theorem is checked by Lean's kernel with a trusted base of
only standard axioms — no `sorry`, no `native_decide`.

## The construction — proved once

`Admitto.Core.Shield` packages a shield as: a state, an action, a decidable
gate `admit`, an invariant `Safe`, a `step`, and two obligations (rejected
actions are no-ops; admitted actions preserve `Safe`). From these,
`Shield.sound` proves the safety induction — `Safe` is preserved across any
sequence of actions — **once**. Each domain below instantiates `Shield`; the
induction is reused, never re-proved.

## Three instances

| Domain | Gate | Guarantee | Theorem |
|---|---|---|---|
| AI-generated GPU kernels | `checkVectorAdd` (verified equivalence) | every installed kernel provably computes its spec | `kernelShield` / `shield_sound_via_core` |
| Agent capability-monotonicity | `admitOp` (computed effect) | granted resources never expand beyond the initial set | `sandboxShield` / `sandbox_sound_via_core` |
| Privilege-amplification prevention | `admitTyped` (level bound) | no resource's authority is amplified beyond its initial level | `typedShield` / `typed_sound_via_core` |

Each `*_via_core` theorem is derived from the single generic `Shield.sound`.

## Demos

- **Kernels** (`./demo.sh`): the shield admits a correct vector-add kernel and
  rejects a subtly-wrong one (`addf` → `subf`, computing a−b) — a one-character
  error a tolerance test can miss. Rejected by proof.
- **Agents** (`./agent_demo.sh`): an agent provisioned with `read` authority is
  admitted for reads and *rejected* for every amplification attempt
  (`read → write`, `read → exec`). Escalation blocked by proof.

## Validation

The typed capability model is differentially validated against real OS
filesystem permissions (`validate_agent.py`): for each (held-level, requested-op),
a real file is created with the corresponding permissions, the operation is
actually attempted, and the OS's allow/deny is compared to the model's verdict.
**Result: 9/9 agreement** on the comparable (cumulative-permission) domain. The
model's guarantees are about an abstraction validated against real system
behavior.

## What is proven, and what is not

- **Sound, capability-independent gates.** Each gate's soundness is a theorem, so
  its guarantee holds regardless of how capable the AI is — for the property it
  checks.
- **Scope is the spec.** A gate guarantees only its specified property. It says
  nothing about properties it does not specify (e.g. the gates do not address
  deception or misaligned goals — those are not formally specifiable).
- **Closure is assumed.** The shields govern the gated channel. That this is the
  *only* channel — no side channels, no human persuaded to act outside the gate —
  is an isolation property assumed here, standard for this class of system, and
  the irreducible limit of the approach.
- **World models.** The typed capability model is validated against real OS
  behavior (above). The kernel gate rests on a Triton kernel semantics whose
  differential validation against real execution is future work.

## Building

    lake build Admitto.Core                # the generic construction
    lake build Admitto.Envelope            # kernel shield instance
    lake build Admitto.Agents.Sandbox      # capability-monotonicity instance
    lake build Admitto.Agents.Typed        # amplification-prevention instance
    ./demo.sh          # kernel demo
    ./agent_demo.sh    # agent demo
    python3 validate_agent.py   # OS validation

## Background

The construction is the runtime-assurance / Simplex pattern (an untrusted
component wrapped by a verified one), instantiated with a **machine-checked**
gate and a **mechanized** safety induction — the composition that distinguishes
Admitto from prior work: runtime-assurance systems for AI use unsound (judged)
gates or paper-only proofs; verified checkers exist but are not composed into a
deployment-level safety induction for adversarially-generated actions, nor
generalized across domains. The kernel gate builds on Trident, a Lean 4 project
on formal semantics for Triton GPU kernels.
