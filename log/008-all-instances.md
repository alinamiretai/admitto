# 008 — All three shields are instances of one construction

The kernel shield now instantiates Core.Shield alongside the two agent shields:

  kernelShield  : Shield PipelineState Proposal   (AI-generated kernels)
  sandboxShield : Shield Sandbox Op               (capability monotonicity)
  typedShield   : Shield Auth Op                  (amplification prevention)

All three safety theorems (shield_sound_via_core, sandbox_sound_via_core,
typed_sound_via_core) are DERIVED from the single generic Shield.sound. The
safety induction is proved exactly once, in Admitto/Core.lean.

Admitto is now, structurally and by Lean's type system, one construction
instantiated across three domains — not four parallel proofs. Adding a domain =
supply (state, action, gate) + discharge two obligations; safety is automatic.
