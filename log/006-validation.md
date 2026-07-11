# 006 — Validation: typed model matches real OS permissions

validate_agent.py differentially tests admitTyped against real filesystem
behavior: for each (held-level, requested-op), it creates a real file with the
corresponding chmod bits, actually attempts the operation, and compares the OS's
allow/deny to the model's ADMIT/DENY (via `lake exe admitto-agent`).

Result on the comparable (cumulative-permission) domain: 9/9 agreements.

  held   op     OS     model
  read   read   allow  ADMIT   ok
  read   write  deny   DENY    ok
  read   exec   deny   DENY    ok
  write  read   allow  ADMIT   ok
  write  write  allow  ADMIT   ok
  write  exec   deny   DENY    ok
  exec   *      allow  ADMIT   ok

The typed capability model is faithful to real OS permission semantics on the
cumulative hierarchy it abstracts. Unix independent-bit permissions
(exec-without-read) are explicitly outside the linear model's scope.

This closes the "world model faithfulness" gap for the typed shield: the model's
predictions match reality, so the machine-checked guarantee (typed_sound) is
about a validated abstraction, not an arbitrary one.
