import Trident.Common.Memory

namespace Trident

structure SourceSemantics where
  State  : Type
  init   : List (List Int) → State
  output : State → List Int
  step   : State → State → Prop

structure TargetSemantics where
  init   : List (List Int) → Nat → Nat → Nat → MachineState
  output : MachineState → List Int
  exec   : MachineState → MachineState

structure ForwardSimulation
    (src : SourceSemantics)
    (tgt : TargetSemantics)
    (inputs : List (List Int))
    (pid bs gs : Nat) where
  matchStates : src.State → MachineState → Prop
  simInit     : matchStates (src.init inputs) (tgt.init inputs pid bs gs)
  simStep     : ∀ s1 t1 s2,
                  src.step s1 s2 →
                  matchStates s1 t1 →
                  ∃ t2, matchStates s2 t2
  simFinal    : ∀ s t,
                  matchStates s t →
                  src.output s = tgt.output t

def GlobalCorrectness
    (src    : SourceSemantics)
    (tgt    : TargetSemantics)
    (inputs : List (List Int))
    (bs gs  : Nat) : Prop :=
  ∀ pid < gs,
    ∃ _ : ForwardSimulation src tgt inputs pid bs gs,
      let finalTarget := tgt.exec (tgt.init inputs pid bs gs)
      let fullOutput  := src.output (src.init inputs)
      ∀ i < bs,
        finalTarget.readMem (pid * bs + i) =
        fullOutput.getD (pid * bs + i) 0

theorem global_from_tiles
    (fullOutput : List Int)
    (getBlock   : Nat → List Int)
    (bs gs      : Nat)
    (h_bs       : bs > 0)
    (h_tiles    : ∀ pid < gs, ∀ i < bs,
                    (getBlock pid).getD i 0 =
                    fullOutput.getD (pid * bs + i) 0)
    (i : Nat) (h_i : i < gs * bs) :
    (getBlock (i / bs)).getD (i % bs) 0 = fullOutput.getD i 0 := by
  have h_pid : i / bs < gs := by
    rw [Nat.div_lt_iff_lt_mul h_bs]; exact h_i
  have h_mod : i % bs < bs := Nat.mod_lt i h_bs
  have h := h_tiles (i / bs) h_pid (i % bs) h_mod
  have heq : i / bs * bs + i % bs = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i bs
  rw [heq] at h
  exact h

end Trident
