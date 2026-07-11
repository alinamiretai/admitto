# 007 — Generality realized in code: one construction, proven instances

Admitto/Core.lean defines Shield (state, gate admit, invariant Safe, step, and
two obligations: rejected ops are no-ops, admitted ops preserve Safe) and proves
Shield.sound — the safety induction over arbitrary action sequences — ONCE.

Both agent shields are now instances:
  typedShield   : Shield Auth Op       (privilege-amplification prevention)
  sandboxShield : Shield Sandbox Op    (capability monotonicity)

Their safety theorems (typed_sound_via_core, sandbox_sound_via_core) are DERIVED
from Shield.sound, not re-proved. The induction exists once.

Adding a new domain = provide (state, action, gate) + discharge two small
obligations. The safety guarantee is then automatic.

"Admitto is a general construction" is now enforced by Lean's type system, not
asserted in prose. All axiom-clean [propext, Quot.sound].
