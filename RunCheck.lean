import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.Soundness
import Trident.Proofs.Checker
import Trident.Common.Equiv

open Trident

def parsedVectorAddFixed : TritonKernel := [
  { result := "c1024_i32", op := .constant 1024,          args := [] },
  { result := "pid",       op := .get_program_id 0,        args := [] },
  { result := "offset",    op := .muli,                    args := ["pid", "c1024_i32"] },
  { result := "range",     op := .make_range (some 1024),  args := [] },
  { result := "voffset",   op := .splat [1024],            args := ["offset"] },
  { result := "idx",       op := .addi,                    args := ["voffset", "range"] },
  { result := "aptr",      op := .addptr,                  args := ["x_ptr", "idx"] },
  { result := "bptr",      op := .addptr,                  args := ["y_ptr", "idx"] },
  { result := "cptr",      op := .addptr,                  args := ["output_ptr", "idx"] },
  { result := "a",         op := .load,                    args := ["aptr"] },
  { result := "b",         op := .load,                    args := ["bptr"] },
  { result := "c",         op := .addf,                    args := ["a", "b"] },
  { result := "_",         op := .store,                   args := ["cptr", "c"] }
]

-- pid=0, all i < 1024
set_option maxRecDepth 100000 in
theorem checker_pid0 : ∀ i : Fin 1024,
    symCheckVectorAddTutorial parsedVectorAddFixed 0 1024 1 2048 i.val = true := by
  native_decide

-- pid=1, all i < 1024
set_option maxRecDepth 100000 in
theorem checker_pid1 : ∀ i : Fin 1024,
    symCheckVectorAddTutorial parsedVectorAddFixed 1 1024 1 2048 i.val = true := by
  native_decide

theorem checker_passes (pid i : Nat) (hpid : pid ≤ 1) (hi : i < 1024) :
    symCheckVectorAddTutorial parsedVectorAddFixed pid 1024 1 2048 i = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hpid with rfl | rfl
  · exact checker_pid0 ⟨i, hi⟩
  · exact checker_pid1 ⟨i, hi⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem parsedVectorAddFixed_correct
    (a b : List Int) (pid gs i : Nat)
    (hla : a.length = 2048) (hlb : b.length = 2048)
    (hpid : pid ≤ 1) (hi : i < 1024) :
    MachineState.readMem
      (evalKernel parsedVectorAddFixed (parsedInitState a b pid 1024 gs))
      (2 * 2048 + pid * 1024 + i) =
    a.getD (pid * 1024 + i) 0 + b.getD (pid * 1024 + i) 0 :=
  symCheckTutorial_sound parsedVectorAddFixed pid 1024 gs 2048 i
    (checker_passes pid i hpid hi) a b hla hlb (by omega)
