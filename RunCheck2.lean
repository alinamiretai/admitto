import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.Soundness
import Trident.Proofs.Checker
import Trident.Proofs.VectorAddEquiv

open Trident
#eval symCheckVectorAddTutorial parsedVectorAdd 0 1024 1 2048 0
