import Admitto.Agents.Typed
open Admitto.Agents.Typed

/-- CLI: query the typed capability gate.
    usage: admitto-agent <resource> <held-level> <requested-level>
    levels: read | write | exec
    prints ADMIT or DENY. -/

def parseLevel (s : String) : Option Level :=
  match s with
  | "read"  => some .read
  | "write" => some .write
  | "exec"  => some .exec
  | _       => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [resource, heldS, reqS] =>
    let some held := parseLevel heldS
      | do IO.eprintln "held level must be read|write|exec"; return 2
    let some req := parseLevel reqS
      | do IO.eprintln "requested level must be read|write|exec"; return 2
    -- Agent provisioned with `held` authority over `resource`.
    let auth : Auth :=
      { held := [(resource, held)], initial := [(resource, held)] }
    let op : Op := { resource := resource, level := req }
    if admitTyped auth op then
      IO.println "ADMIT"
      return 0
    else
      IO.println "DENY"
      return 1
  | _ =>
    IO.eprintln "usage: admitto-agent <resource> <held-level> <requested-level>"
    return 2
