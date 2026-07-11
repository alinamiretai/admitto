/-!
# Admitto.Agents.Capability — a verified capability-monotonicity shield

A second instance of the Admitto shield construction, in a new domain: agents.

The AI system: an agent that proposes actions. Each action may *use* capabilities
and may attempt to *grant* the agent new ones. An untrusted, arbitrarily capable
agent will try to escalate its own privileges (self-exfiltration, privilege
escalation). The shield gates every action through `admitAction`, which admits an
action only if it neither uses nor grants any capability the agent does not
already hold.

The safety invariant `SafeAgent`: the agent's held capabilities are always a
subset of what it started with. The main theorem `capability_sound`: for ANY
sequence of actions the agent proposes, its permissions never expand beyond the
initial set — forever. The agent is universally quantified out; the guarantee
holds regardless of its intelligence.

Same construction as `Admitto.shield_sound` (gate + invariant + induction), new
domain. The envelope is generic over the gate; this file supplies a new gate.
-/

namespace Admitto.Agents

/-- A capability the agent may hold, e.g. "read:/tmp", "net:egress". -/
abbrev Capability := String

/-- The set of capabilities the agent currently holds. -/
abbrev PermSet := List Capability

/-- An action the untrusted agent proposes: capabilities it wants to *use*, and
    capabilities it would *grant* itself. A privilege-escalating action grants
    itself something new. -/
structure AgentAction where
  uses   : List Capability
  grants : List Capability

/-- The agent's state: the capabilities it currently holds, and the initial set
    it was provisioned with (the bound it must never exceed). -/
structure AgentState where
  held    : PermSet
  initial : PermSet

/-- **The gate.** Admit an action iff it neither uses nor grants any capability
    the agent does not already hold. This is capability-monotonicity: no action
    can introduce a capability from outside the currently-held set. -/
def admitAction (s : AgentState) (a : AgentAction) : Bool :=
  a.uses.all (· ∈ s.held) && a.grants.all (· ∈ s.held)

/-- The safety invariant: the agent has never accumulated a capability beyond
    its initial provision. -/
def SafeAgent (s : AgentState) : Prop :=
  ∀ c ∈ s.held, c ∈ s.initial

/-- One step: the agent proposes `a`; if the gate admits it, its granted
    capabilities are added (they are provably already held, so nothing new
    actually enters); otherwise the state is unchanged. -/
def stepAgent (s : AgentState) (a : AgentAction) : AgentState :=
  if admitAction s a then { s with held := a.grants ++ s.held } else s

theorem stepAgent_preserves_safe (s : AgentState) (a : AgentAction)
    (hs : SafeAgent s) : SafeAgent (stepAgent s a) := by
  unfold SafeAgent stepAgent
  by_cases hadm : admitAction s a
  · simp only [hadm, if_true]
    intro c hc
    rcases List.mem_append.mp hc with hgrant | hheld
    · have hgrants : a.grants.all (· ∈ s.held) = true := by
        simp only [admitAction, Bool.and_eq_true] at hadm
        exact hadm.2
      have hcheld : c ∈ s.held := by
        have h := List.all_eq_true.mp hgrants
        simpa using h c hgrant
      exact hs c hcheld
    · exact hs c hheld
  · simp only [hadm]
    exact hs
/-- Run the agent loop on an arbitrary sequence of proposed actions. -/
def runAgent (s : AgentState) (actions : List AgentAction) : AgentState :=
  actions.foldl stepAgent s

/-- **The main theorem: the verified capability shield.**
    For ANY sequence of actions the untrusted agent proposes, starting from a
    SafeAgent state, the agent's capabilities never expand beyond its initial
    set. The agent is universally quantified (`∀ actions`) — the guarantee is
    independent of its behavior or capability. -/
theorem capability_sound (s : AgentState) (hs : SafeAgent s)
    (actions : List AgentAction) : SafeAgent (runAgent s actions) := by
  unfold runAgent
  induction actions generalizing s with
  | nil => exact hs
  | cons a as ih =>
    exact ih (stepAgent s a) (stepAgent_preserves_safe s a hs)

end Admitto.Agents

-- Verify the trusted base of the capability shield.
#print axioms Admitto.Agents.capability_sound
