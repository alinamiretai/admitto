import Trident.Proofs.Checker
open Trident

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, pidS, bsS, nS] =>
    let src ← IO.FS.readFile path
    let some pid := pidS.toNat? | do IO.eprintln "pid must be a Nat"; return 1
    let some bs  := bsS.toNat?  | do IO.eprintln "bs must be a Nat";  return 1
    let some n   := nS.toNat?   | do IO.eprintln "n must be a Nat";   return 1
    if checkVectorAdd src pid bs n then
      IO.println s!"VERIFIED: {path} matches vector-add spec for all inputs (pid={pid}, bs={bs}, n={n})"
      return 0
    else
      IO.println s!"REJECTED: {path} did not verify at (pid={pid}, bs={bs}, n={n})"
      return 1
  | _ => IO.eprintln "usage: trident-check <file.ttir> <pid> <bs> <n>"; return 1
