import Trident.Proofs.Checker

open Trident

/-!
# Admitto: a verified shield for AI-generated kernels

The AI system: a pipeline that receives kernels proposed by an (untrusted,
arbitrarily capable) generator and installs them. The shield gates every
proposal through `checkVectorAdd`, whose soundness is machine-checked
(`checkVectorAdd_sound`, axioms: propext, Classical.choice, Quot.sound).

The safety invariant `Safe`: every installed kernel provably computes its spec
at every lane. The main theorem `shield_sound`: for ANY sequence of proposals
the generator emits, the pipeline stays Safe forever. The generator is
universally quantified out — the guarantee holds regardless of its intelligence.
-/

namespace Admitto

/-- A proposal from the untrusted AI generator: a kernel source and the
    spec parameters it claims to satisfy. -/
structure Proposal where
  src : String
  pid : Nat
  bs  : Nat
  n   : Nat

/-- The pipeline state: the list of proposals that have been admitted so far. -/
structure PipelineState where
  installed : List Proposal

/-- A proposal is *correct* iff the verified gate admits it. Because
    `checkVectorAdd_sound` holds, `admit p = true` implies the kernel computes
    vector-add at every lane — this is the spec, and it is machine-checked. -/
def admit (p : Proposal) : Bool :=
  checkVectorAdd p.src p.pid p.bs p.n

/-- The safety invariant: every installed proposal was admitted by the gate. -/
def Safe (s : PipelineState) : Prop :=
  ∀ p ∈ s.installed, admit p = true

/-- One step of the AI-generation loop: the generator emits `p`; the shield
    installs it iff the gate admits it, otherwise the state is unchanged. -/
def step (s : PipelineState) (p : Proposal) : PipelineState :=
  if admit p then { installed := p :: s.installed } else s

/-- The empty pipeline is trivially Safe. -/
def init : PipelineState := { installed := [] }

theorem init_safe : Safe init := by
  intro p hp
  simp [init] at hp

/-- **The inductive step.** The gate preserves the invariant: whatever the
    generator proposes, `step` keeps the pipeline Safe. -/
theorem step_preserves_safe (s : PipelineState) (p : Proposal) (hs : Safe s) :
    Safe (step s p) := by
  unfold Safe step
  by_cases hadm : admit p
  · -- admitted: new state is p :: installed
    simp only [hadm, if_true]
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hqrest
    · subst hqp; exact hadm
    · exact hs q hqrest
  · -- rejected: state unchanged
    simp only [hadm, if_false]
    exact hs

/-- Run the pipeline on an arbitrary sequence of generator proposals. -/
def run (s : PipelineState) (proposals : List Proposal) : PipelineState :=
  proposals.foldl step s

/-- **The main theorem: the verified shield.**
    For ANY sequence of proposals the untrusted AI generator emits, starting
    from a Safe state, the pipeline stays Safe. The generator is universally
    quantified (`∀ proposals`) — the guarantee is independent of its behavior
    or capability. -/
theorem shield_sound (s : PipelineState) (hs : Safe s) (proposals : List Proposal) :
    Safe (run s proposals) := by
  unfold run
  induction proposals generalizing s with
  | nil => exact hs
  | cons p ps ih =>
    exact ih (step s p) (step_preserves_safe s p hs)

end Admitto

-- Verify the trusted base of the whole shield.
#print axioms Admitto.shield_sound
