# 005 — Sandbox shield rejects live escalation

Admitto/Agents/Sandbox.lean: the gate computes an operation's effect on the
permission state (rather than trusting the agent's self-report), so an
adversarial agent cannot mislabel an escalating op as benign.

Demo (#eval):
  admitOp demoState (read "/tmp")            → true   (safe, admitted)
  admitOp demoState (grant "/etc/secrets")   → false  (escalation, rejected)
  runOps [read, grant "/etc/secrets", write] → granted = ["/tmp"]  (unchanged)

sandbox_sound axiom-clean [propext, Quot.sound].

Admitto now demonstrates the shield construction across two domains and three
gates: AI-generated kernels (shield_sound) and agent capabilities
(capability_sound, sandbox_sound). The construction is general; each domain
supplies a gate; the induction is reused.
