/-!
# Admitto.Core — the generic shield construction

Every Admitto shield is the same three parts: a state, a per-action `admit`
gate, an invariant `Safe`, and a `step` that applies an action only if admitted.
Given the single obligation that `admit`-ed actions preserve `Safe`, the shield
theorem — Safe is preserved across ANY sequence of actions — holds by induction.

This file proves that induction ONCE, generically. Each domain (kernels, agent
capabilities, ...) instantiates `Shield` with its own state/action/gate; the
safety proof is reused, not re-proved.
-/

namespace Admitto.Core

/-- A shield: a state type `σ`, an action type `α`, a decidable gate `admit`, an
    invariant `Safe`, and a `step`. The single proof obligation is `stepSafe`:
    an admitted action preserves the invariant; a rejected action leaves the
    state unchanged (so also preserves it). -/
structure Shield (σ : Type) (α : Type) where
  admit : σ → α → Bool
  Safe  : σ → Prop
  step  : σ → α → σ
  /-- Rejected actions are no-ops. -/
  step_reject : ∀ s a, admit s a = false → step s a = s
  /-- Admitted actions preserve the invariant. -/
  step_admit  : ∀ s a, Safe s → admit s a = true → Safe (step s a)

namespace Shield

variable {σ α : Type} (S : Shield σ α)

/-- The single inductive step: `step` preserves `Safe` regardless of the action. -/
theorem step_preserves (s : σ) (a : α) (hs : S.Safe s) : S.Safe (S.step s a) := by
  by_cases hadm : S.admit s a
  · exact S.step_admit s a hs hadm
  · rw [S.step_reject s a (by simpa using hadm)]; exact hs

/-- Run the shield on an arbitrary sequence of actions. -/
def run (s : σ) (actions : List α) : σ :=
  actions.foldl S.step s

/-- **The generic shield theorem.** For ANY sequence of actions, starting from a
    Safe state, the shield keeps the state Safe. Proved once; reused by every
    instance. The action source (the AI) is universally quantified out. -/
theorem sound (s : σ) (hs : S.Safe s) (actions : List α) :
    S.Safe (S.run s actions) := by
  unfold run
  induction actions generalizing s with
  | nil => exact hs
  | cons a as ih => exact ih (S.step s a) (S.step_preserves s a hs)

end Shield

end Admitto.Core
