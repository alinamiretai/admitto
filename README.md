# Admitto

A construction for **verified safety shields** for AI systems.

Admitto wraps an untrusted AI component — a code generator, an agent — in a
**sound, machine-checked gate** composed with a **mechanized safety induction**.
The gate admits only actions proven to satisfy a specification; the induction
proves that across *any* sequence of actions the AI proposes, the system stays
safe. The AI is universally quantified out of every theorem: the guarantee does
not depend on its behavior or capability.

Every theorem below is checked by Lean's kernel with a trusted base of only
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no
`native_decide`.

## The construction

A shield is three parts:

- **gate** — a decidable predicate `admit` that is *sound*: `admit action = true`
  implies the action satisfies the spec. Sound gates do not degrade as the AI
  gets more capable, because the guarantee is a theorem, not a classifier.
- **invariant** `Safe` — the property preserved across the system's lifetime.
- **induction** — a proof that starting `Safe`, gating every action with `admit`
  keeps the system `Safe` for any sequence of proposals.

The induction is generic over the gate. Each domain supplies a gate; the safety
proof is reused. Admitto demonstrates this across two domains and four gates.

## Instances

### 1. AI-generated GPU kernels — `Admitto/Envelope.lean`

An untrusted generator proposes Triton kernels. The gate is a machine-checked
equivalence checker (`checkVectorAdd`, sound by `checkVectorAdd_sound`): it
admits a kernel only if it *provably* computes vector-add for all inputs — no
testing, no tolerance, no sampling. `shield_sound` proves every installed kernel
meets the spec, over any sequence the generator emits.

Demo (`demo.sh`): the shield admits a correct kernel and rejects a subtly-wrong
one (`addf` → `subf`, computing a−b instead of a+b) — a one-character error a
tolerance test can miss. The gate rejects it by proof.

### 2. Agent capability-monotonicity — `Admitto/Agents/Sandbox.lean`

An untrusted agent proposes filesystem operations. The gate *computes* each
operation's effect on the permission state (rather than trusting the agent's
self-report), and admits an operation only if it does not expand the granted
set. `sandbox_sound` proves the agent's granted resources never grow beyond the
initial provision — for any sequence of operations.

Demo: the shield rejects a mid-sequence privilege-escalation attempt
(`grant "/etc/secrets"`); granted paths remain unchanged.

### 3. Privilege-amplification prevention — `Admitto/Agents/Typed.lean`

Capabilities carry *levels* (read < write < exec). The threat is *amplification*:
acquiring a higher level over a resource than provisioned. The gate admits an
acquisition only if the requested level is within the agent's initial grant.
`typed_sound` proves no resource's authority is ever amplified beyond its initial
level, across any sequence of operations.

Demo: an agent holding `read:/data` is refused `write:/data` and `exec:/data` —
amplification blocked by proof.

## What is proven, and what is not

Admitto states exactly what it guarantees.

- **Sound gate, capability-independent.** Each gate's soundness is a theorem, so
  its guarantee holds regardless of how capable the AI is — for the property it
  checks.
- **Scope is the spec.** A gate guarantees only its specified property: kernel
  equivalence, capability-monotonicity, no-amplification. It says nothing about
  properties it does not specify.
- **Closure is assumed, not proven.** The shields govern the gated channel (the
  install path, the operation interface). That this is the *only* channel — no
  side channels, and no human who can be persuaded to act outside the gate — is
  an isolation property assumed here, standard for this class of system, and the
  irreducible limit of the approach.
- **World model.** The kernel gate rests on a defined kernel semantics; the agent
  gates rest on an abstract permission/capability model. Differential validation
  of these models against real execution is ongoing work.
- **Numerics.** The kernel gate checks algebraic equivalence (structure), not
  floating-point rounding.

## Building

    lake build Admitto.Envelope          # kernel shield
    lake build Admitto.Agents.Sandbox    # capability-monotonicity shield
    lake build Admitto.Agents.Typed      # amplification-prevention shield
    ./demo.sh                            # kernel demo (VERIFIED / REJECTED)

## Background

The construction is the runtime-assurance / Simplex pattern (an untrusted
component wrapped by a verified one), instantiated with a **machine-checked**
gate and a **mechanized** safety induction — the composition that distinguishes
Admitto from prior work: runtime-assurance systems for AI use unsound (judged)
gates or paper-only proofs; verified checkers exist but are not composed into a
deployment-level safety induction for adversarially-generated actions. The
kernel gate builds on Trident, a Lean 4 project on symbolic verification of
Triton kernels.
