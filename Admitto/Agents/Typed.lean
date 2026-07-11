import Admitto.Core
/-!
# Admitto.Agents.Typed — capability shield catching privilege amplification

Models capability *levels* (read < write < exec), not just resource presence.
The threat: an agent amplifies its authority — acquiring a higher level over a
resource than it was provisioned. The agent proposes operations that WOULD grant
itself authority; the gate admits an op only if the requested level does not
exceed the agent's INITIAL level for that resource. Thus the agent's held
authority genuinely evolves, but can never be amplified beyond its provision.

Spec (invariant `SafeAuth`): for every resource, the agent's held level never
exceeds its initial level.
Theorem `typed_sound`: for ANY sequence of operations, SafeAuth is preserved —
authority is never amplified beyond the initial grant. Agent quantified out.
-/

namespace Admitto.Agents.Typed

abbrev Resource := String

/-- Authority levels, ordered read < write < exec. -/
inductive Level where
  | read | write | exec
  deriving DecidableEq, Repr

def Level.rank : Level → Nat
  | .read => 0 | .write => 1 | .exec => 2

/-- `a.le b` : level a is no more powerful than b. -/
def Level.le (a b : Level) : Bool := a.rank ≤ b.rank

/-- The agent's authority: current level per resource, and the initial grant. -/
structure Auth where
  held    : List (Resource × Level)
  initial : List (Resource × Level)

/-- The agent's current level for a resource (none = no authority). -/
def levelOf (m : List (Resource × Level)) (r : Resource) : Option Level :=
  (m.find? (·.1 == r)).map (·.2)

/-- An operation: the agent asks to acquire `level` authority over `resource`.
    This is the escalation vector — the gate must bound it by the initial grant. -/
structure Op where
  resource : Resource
  level    : Level

/-- **The gate.** Admit iff the requested level does not exceed the agent's
    INITIAL level for that resource. Computed by the gate from the initial
    provision — the agent cannot forge it. This bounds all acquisition by the
    provision, blocking amplification. -/
def admitTyped (a : Auth) (o : Op) : Bool :=
  match levelOf a.initial o.resource with
  | some ilvl => o.level.le ilvl
  | none      => false

/-- The spec / invariant: every held level is within the initial grant. -/
def SafeAuth (a : Auth) : Prop :=
  ∀ r lvl, levelOf a.held r = some lvl →
    ∃ ilvl, levelOf a.initial r = some ilvl ∧ lvl.le ilvl = true

/-- One step: if admitted, the agent acquires the requested (resource, level) —
    prepended to `held`, so `levelOf` (which uses `find?`) now returns it.
    A rejected op is a no-op. The state GENUINELY changes on admit. -/
def stepTyped (a : Auth) (o : Op) : Auth :=
  if admitTyped a o then
    { a with held := (o.resource, o.level) :: a.held }
  else a

theorem stepTyped_preserves_safe (a : Auth) (o : Op) (hs : SafeAuth a) :
    SafeAuth (stepTyped a o) := by
  unfold SafeAuth stepTyped
  by_cases hadm : admitTyped a o
  · simp only [hadm, if_true]
    intro r lvl hlvl
    -- levelOf of the extended held list
    unfold levelOf at hlvl
    simp only [List.find?_cons] at hlvl
    by_cases hr : (o.resource == r) = true
    · -- the newly-acquired resource: its level is o.level, bounded by initial
      simp only [hr, if_true, Option.map_some] at hlvl
      -- hlvl : some o.level = some lvl  (up to the beq), so lvl = o.level
      have hlveq : lvl = o.level := by simpa using hlvl.symm
      -- admitTyped gave us: o.level ≤ initial level of o.resource
      unfold admitTyped at hadm
      have hreq : r = o.resource := by
        have := beq_iff_eq.mp hr; simpa using this.symm
      cases hinit : levelOf a.initial o.resource with
      | none => rw [hinit] at hadm; exact absurd hadm (by simp)
      | some ilvl =>
        rw [hinit] at hadm
        refine ⟨ilvl, ?_, ?_⟩
        · rw [hreq]; exact hinit
        · rw [hlveq]; exact hadm
    · -- an already-held resource: use the old invariant
      simp only [hr, if_false] at hlvl
      have : levelOf a.held r = some lvl := by unfold levelOf; exact hlvl
      exact hs r lvl this
  · simp only [hadm]
    exact hs

def runTyped (a : Auth) (ops : List Op) : Auth :=
  ops.foldl stepTyped a

/-- **Main theorem.** For ANY sequence of operations, SafeAuth is preserved:
    no resource's authority is ever amplified beyond the initial grant. -/
theorem typed_sound (a : Auth) (hs : SafeAuth a) (ops : List Op) :
    SafeAuth (runTyped a ops) := by
  unfold runTyped
  induction ops generalizing a with
  | nil => exact hs
  | cons o os ih => exact ih (stepTyped a o) (stepTyped_preserves_safe a o hs)

end Admitto.Agents.Typed

#print axioms Admitto.Agents.Typed.typed_sound

/-! ## Demo: the gate admits within-provision ops and rejects amplification -/

open Admitto.Agents.Typed

-- Agent provisioned with read authority over /data (and nothing more).
def demoAuth : Auth :=
  { held := [("/data", Level.read)], initial := [("/data", Level.read)] }

-- Within provision: re-acquiring read on /data → ADMITTED (true)
#eval admitTyped demoAuth { resource := "/data", level := Level.read }

-- Amplification: requesting WRITE on /data (holds only read) → REJECTED (false)
#eval admitTyped demoAuth { resource := "/data", level := Level.write }

-- Amplification to exec → REJECTED (false)
#eval admitTyped demoAuth { resource := "/data", level := Level.exec }

-- Unprovisioned resource → REJECTED (false)
#eval admitTyped demoAuth { resource := "/secrets", level := Level.read }

/-! ## The typed shield as an instance of the generic construction -/

open Admitto.Core

/-- The typed capability shield, packaged as a `Shield`. The two proof
    obligations are discharged from the existing lemmas: rejected ops are
    definitionally no-ops, and admitted ops preserve `SafeAuth` (which
    `stepTyped_preserves_safe` already proves for all ops). -/
def typedShield : Shield Auth Op where
  admit := admitTyped
  Safe  := SafeAuth
  step  := stepTyped
  step_reject := by
    intro s a h
    unfold stepTyped
    simp [h]
  step_admit := by
    intro s a hs _
    exact stepTyped_preserves_safe s a hs

/-- `typed_sound` is now literally the generic shield theorem, instantiated:
    the typed capability shield is an instance of the one Admitto construction. -/
theorem typed_sound_via_core (a : Auth) (hs : SafeAuth a) (ops : List Op) :
    SafeAuth (typedShield.run a ops) :=
  typedShield.sound a hs ops
