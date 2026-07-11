/-!
# Admitto.Agents.Sandbox — capability shield over a real action model

The previous capability shield (`Capability.lean`) trusted the agent's *declared*
grants. An adversarial agent lies: it labels an escalating action as benign. This
file fixes that. Actions are concrete filesystem operations with *effects the
gate computes* — the agent does not get to label its own escalation.

World model: the agent holds a set of granted paths. Operations act on paths.
The gate computes each operation's effect on the permission state and admits it
only if the effect does not expand the granted set. The agent proposes raw
operations; it cannot forge the effect analysis, because the gate derives it.

Invariant `SafeSandbox`: granted paths never exceed the initial grant.
Theorem `sandbox_sound`: for ANY sequence of operations the agent proposes,
its granted paths never expand — agent quantified out.
-/

namespace Admitto.Agents.Sandbox

/-- A filesystem path (abstract). -/
abbrev Path := String

/-- A concrete operation the agent can propose. The agent chooses the operation
    and its arguments — but NOT how the gate interprets its effect. -/
inductive Op where
  /-- Read from a path. Uses the read capability; grants nothing. -/
  | read  (p : Path)
  /-- Write to a path. Uses the write capability; grants nothing. -/
  | write (p : Path)
  /-- Delegate: attempt to add path `p` to the agent's granted set.
      THIS is the escalation vector — the gate must catch it. -/
  | grant (p : Path)
  deriving DecidableEq

/-- The sandbox state: the set of paths the agent is currently granted, and the
    initial grant it must never exceed. -/
structure Sandbox where
  granted : List Path
  initial : List Path

/-- The *effect* of an operation on the granted set, COMPUTED by the gate — not
    declared by the agent. `read`/`write` change nothing; `grant p` would add p. -/
def effect (s : Sandbox) (o : Op) : List Path :=
  match o with
  | .read _  => s.granted
  | .write _ => s.granted
  | .grant p => p :: s.granted

/-- What capability an operation *uses* — the path it touches. -/
def touches (o : Op) : Path :=
  match o with
  | .read p  => p
  | .write p => p
  | .grant p => p

/-- **The gate.** Admit an operation iff (a) the path it touches is already
    granted, and (b) its computed effect does not expand the granted set.
    The agent cannot forge either check — both are computed from the operation. -/
def admitOp (s : Sandbox) (o : Op) : Bool :=
  (touches o ∈ s.granted) && (effect s o).all (· ∈ s.granted)

/-- Invariant: the granted set never exceeds the initial grant. -/
def SafeSandbox (s : Sandbox) : Prop :=
  ∀ p ∈ s.granted, p ∈ s.initial

/-- One step: apply the operation's computed effect iff the gate admits it. -/
def stepOp (s : Sandbox) (o : Op) : Sandbox :=
  if admitOp s o then { s with granted := effect s o } else s

theorem stepOp_preserves_safe (s : Sandbox) (o : Op) (hs : SafeSandbox s) :
    SafeSandbox (stepOp s o) := by
  unfold SafeSandbox stepOp
  by_cases hadm : admitOp s o
  · simp only [hadm, if_true]
    intro p hp
    -- admitOp proved every path in (effect s o) is already granted
    have heff : (effect s o).all (· ∈ s.granted) = true := by
      simp only [admitOp, Bool.and_eq_true] at hadm
      exact hadm.2
    have hpg : p ∈ s.granted := by
      have h := List.all_eq_true.mp heff
      simpa using h p hp
    exact hs p hpg
  · simp only [hadm]
    exact hs

/-- Run the agent's proposed operation sequence. -/
def runOps (s : Sandbox) (ops : List Op) : Sandbox :=
  ops.foldl stepOp s

/-- **The main theorem: the verified sandbox capability shield.**
    For ANY sequence of operations the untrusted agent proposes, starting from a
    SafeSandbox state, the granted paths never expand beyond the initial grant.
    The agent is universally quantified out. Crucially, the agent proposes raw
    operations — it cannot forge the effect analysis, because the gate computes
    it. -/
theorem sandbox_sound (s : Sandbox) (hs : SafeSandbox s) (ops : List Op) :
    SafeSandbox (runOps s ops) := by
  unfold runOps
  induction ops generalizing s with
  | nil => exact hs
  | cons o os ih =>
    exact ih (stepOp s o) (stepOp_preserves_safe s o hs)

end Admitto.Agents.Sandbox

#print axioms Admitto.Agents.Sandbox.sandbox_sound
