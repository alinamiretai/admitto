# 004 — The shield generalizes: capability-monotonicity for agents

Admitto/Agents/Capability.lean builds. capability_sound type-checks:

  #print axioms Admitto.Agents.capability_sound
  → [propext, Quot.sound]

Second instance of the shield construction, new domain (agents, not kernels):

  admitAction              := gate — admit iff action uses/grants only held caps
  SafeAgent                := invariant — held caps ⊆ initial caps
  stepAgent_preserves_safe := inductive step
  capability_sound         := for ANY sequence of agent actions, capabilities
                              never expand beyond the initial set. Agent
                              quantified out.

Same construction as shield_sound (gate + invariant + induction), entirely
different domain and spec. The envelope is generic; a new gate slots in.

This demonstrates Admitto is not a kernel checker — it is a construction for
verified shields, instantiated in two domains: AI-generated code, and agent
capability-safety.
