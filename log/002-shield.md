# 002 — The shield compiles

Admitto/Envelope.lean builds. `shield_sound` type-checks:

  For any sequence of proposals from an untrusted generator, starting from
  a Safe pipeline, run stays Safe. The generator is universally quantified.

Structure:
  admit p              := checkVectorAdd (the verified gate)
  Safe s               := every installed proposal was admitted
  step_preserves_safe  := the inductive step, via checkVectorAdd_sound
  shield_sound         := induction over arbitrary proposal sequences

This is a machine-checked safety induction over an AI code-generation loop,
built on a sound gate. First known instance.
