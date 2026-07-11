#!/bin/bash
# Admitto agent shield demo: a verified gate blocks privilege amplification.
# An agent provisioned with limited authority proposes actions; the gate admits
# only those within its provision — by machine-checked proof.

run() {  # run() <resource> <held> <requested> <label>
  local verdict
  verdict=$(lake exe admitto-agent "$1" "$2" "$3" 2>/dev/null | tail -1)
  printf "  %-28s held=%-6s wants=%-6s  ->  %s\n" "$4" "$2" "$3" "$verdict"
}

echo "======================================================"
echo "  ADMITTO — verified capability shield for AI agents"
echo "======================================================"
echo
echo "An agent is provisioned with READ authority over /data."
echo "It proposes actions. The gate admits an action only if the"
echo "requested authority is within its provision — proven by"
echo "typed_sound (machine-checked, axiom-clean)."
echo
echo "--- Within provision (admitted) ---"
run "/data" read  read  "read /data (as provisioned)"
echo
echo "--- Privilege amplification (rejected) ---"
run "/data" read  write "escalate read -> write"
run "/data" read  exec  "escalate read -> exec"
echo
echo "--- A more-privileged agent (write) ---"
run "/data" write read  "read (below provision)"
run "/data" write write "write (as provisioned)"
run "/data" write exec  "escalate write -> exec"
echo
echo "======================================================"
echo "The gate admits authority within the provision and"
echo "rejects every amplification attempt — by proof, not"
echo "policy. An agent cannot escalate beyond what it was given."
echo "======================================================"
