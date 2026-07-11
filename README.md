# Admitto

A machine-checked safety shield for AI-generated GPU kernels.

Admitto wraps an untrusted code generator (an LLM, an RL policy, any process
that emits Triton kernels) in a verified gate. Every proposed kernel is checked
against a specification before it enters the pipeline; only kernels *proven* to
compute the spec are admitted. The central theorem, `shield_sound`, establishes
by induction that for **any** sequence of kernels the generator emits, every
installed kernel provably meets its spec — and the generator is universally
quantified out, so the guarantee does not depend on its behavior or capability.

## The idea

Testing a generated kernel (e.g. `torch.allclose` against a reference) samples
inputs within a tolerance. Against a generator *optimizing to pass the test*,
the tolerance is an attack surface — a kernel can compute different arithmetic
that stays within tolerance on the sampled inputs. Admitto's gate is a sound
equivalence check: it accepts a kernel only if it provably computes the
specification for all inputs. There is no tolerance to exploit and no sampling
to overfit. The gate's guarantee is a theorem, so it does not degrade as the
generator gets more capable.

## What is proven

The trusted base is Lean's kernel plus three standard axioms — nothing more:

    #print axioms Admitto.shield_sound
    → [propext, Classical.choice, Quot.sound]

No `sorry`, no `native_decide`. The shield is exactly as trustworthy as the
verified gate beneath it, which is exactly as trustworthy as Lean itself.

### Structure

- `admit`                — the gate: a machine-checked equivalence checker
                           (`Trident.checkVectorAdd`, sound by `checkVectorAdd_sound`).
- `Safe`                 — the invariant: every installed kernel was admitted.
- `step_preserves_safe`  — the inductive step: whatever the generator proposes,
                           the gate keeps the pipeline `Safe`.
- `shield_sound`         — the main theorem: for any sequence of proposals,
                           starting `Safe`, the pipeline stays `Safe`.

## Scope and limitations

Admitto states exactly what it guarantees and no more.

- **Property.** The gate checks algebraic equivalence to a reference spec —
  the *structure* of the computation, not floating-point rounding. A
  tree-correct kernel with poor numerical behavior is admitted.
- **Fragment.** The current gate covers vector-add kernels. Kernels outside the
  supported fragment are simply not admitted (they are rejected, never wrongly
  accepted). Extending the fragment (matmul, loops via unrolling) is ongoing.
- **Layer.** Verification is at the level of the parsed kernel (TTIR-style),
  above the compiler. A miscompilation below this layer is out of scope.
- **Closure.** The shield governs the kernel-installation channel. That the
  gate is the *only* channel to the pipeline is an isolation property assumed
  here, not proven — standard for this class of system.
- **Semantics.** The guarantee is relative to the kernel semantics Admitto
  defines. Differential validation of that semantics against a reference
  execution is future work.

## Building

    lake build Admitto.Envelope

## Background

Admitto grew out of Trident, a project on symbolic verification of Triton
kernels in Lean 4. The verified equivalence checker is Trident's; Admitto adds
the gate/invariant/induction that turns a checker into a shield for an AI
system. The architecture is the Simplex / runtime-assurance pattern (an
untrusted component wrapped by a verified one) with a *machine-checked* gate and
a mechanized safety induction.
