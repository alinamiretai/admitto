import Trident.Common.Smallstep
import Trident.Source.Specs.VectorAddSpec
import Trident.Target.Semantics
import Trident.Compiler

namespace Trident

open MachineState

def layoutMemory (a b : List Int) : Nat → Int := fun addr =>
  let n := a.length
  if addr < n         then a.getD addr 0
  else if addr < 2*n  then b.getD (addr - n) 0
  else                     0

def vectorAddInitState (a b : List Int) (pid bs gs : Nat) : MachineState :=
  let n := a.length
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := layoutMemory a b
  , env        := fun v => match v with
      | "a_base" => some (TritonValue.scalar 0)
      | "b_base" => some (TritonValue.scalar (Int.ofNat n))
      | "c_base" => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | "bsize"  => some (TritonValue.scalar (Int.ofNat bs))
      | _        => none }

def vectorAddSourceSem : SourceSemantics :=
  tensorExprSemantics TensorExpr.vectorAdd

def vectorAddTargetSem : TargetSemantics where
  init   := fun inputs pid bs gs =>
    match inputs with
    | [a, b] => vectorAddInitState a b pid bs gs
    | _      => vectorAddInitState [] [] pid bs gs
  output := fun s =>
    let n := match s.lookup "c_base" with
             | some (TritonValue.scalar v) => v.natAbs / 2
             | _ => 0
    (List.range s.block_size).map fun i =>
      s.readMem (2 * n + s.pid * s.block_size + i)
  exec   := fun s => evalKernel compiledVectorAdd s


theorem vectorAdd_correct
    (a b : List Int) (pid bs gs : Nat)
    (h_len : a.length = b.length)
    (h_bs  : bs > 0)
    (h_pid : pid < gs)
    (h_cov : gs * bs = a.length) :
    ∀ i < bs,
      let s  := vectorAddInitState a b pid bs gs
      let s' := evalKernel compiledVectorAdd s
      s'.readMem (2 * a.length + pid * bs + i) =
      (vectorAddSpec a b).getD (pid * bs + i) 0 := by
  intro i hi s s'
  have h_inbound : pid * bs + i < a.length := by
    have h1 : pid + 1 <= gs := Nat.succ_le_of_lt h_pid
    have h2 : (pid + 1) * bs <= gs * bs := Nat.mul_le_mul_right bs h1
    simp [Nat.add_mul] at h2
    omega
  have h_spec : (vectorAddSpec a b).getD (pid * bs + i) 0 =
      a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
    exact zipWith_add_getD a b (pid * bs + i) h_len
  rw [h_spec]

  have h_key :
      MachineState.readMem (evalKernel compiledVectorAdd (vectorAddInitState a b pid bs gs))
        (2 * a.length + pid * bs + i) =
      layoutMemory a b (pid * bs + i) +
      layoutMemory a b (a.length + pid * bs + i) := by
    unfold compiledVectorAdd evalKernel List.foldl
    unfold evalInstr evalOp vectorAddInitState MachineState.writeTile
    simp [MachineState.bind, MachineState.lookup, TritonValue.zipWith]
    generalize hA : (List.map (Int.natAbs ∘ (fun x => x + 2 * (Int.ofNat a.length)) ∘ (fun x => x + Int.ofNat pid * Int.ofNat bs) ∘ Int.ofNat) (List.range bs)) = addrs
    have addrs_eq : addrs = List.map (fun j => 2 * a.length + pid * bs + j) (List.range bs) := by
      rw [← hA]
      apply List.map_congr_left
      intro j hj
      simp [Function.comp]
      omega
    have h_addr : 2 * a.length + pid * bs + i = addrs.getD i 0 := by
      rw [addrs_eq]
      simp [List.getD, List.getElem?_eq_getElem
        (show i < (List.map (fun j => 2 * a.length + pid * bs + j) (List.range bs)).length by simp [hi]),
        List.getElem_map, List.getElem_range]
    rw [h_addr]
    have hnodup : addrs.Nodup := by
      rw [addrs_eq]
      refine nodup_map_injective (fun j => 2 * a.length + pid * bs + j) (List.range bs) ?_ List.nodup_range
      intro x y h
      simp only at h
      omega
    have haddrs_len : addrs.length = bs := by rw [addrs_eq]; simp
    rw [foldl_writeMem_readMem _ _ _ (by simp [haddrs_len]) hnodup i (by rw [addrs_eq]; simpa using hi)]
    simp only [MachineState.readMem, List.getD, List.getElem?_map]
    rw [getElem?_zip (by simp [hi]) (by simp [hi])]
    simp only [List.getElem_map, List.getElem_range, Option.map_some, Option.getD, Function.comp]
    congr 1
    · congr 1
      rw [Int.natAbs_eq_iff]
      left
      simp only [Int.natCast_add, Int.natCast_mul, Int.ofNat_eq_natCast]
      omega
    · congr 1
      rw [Int.natAbs_eq_iff]
      left
      simp only [Int.natCast_add, Int.natCast_mul, Int.ofNat_eq_natCast]
      omega

  dsimp [s', s]
  rw [h_key]
  simp [layoutMemory, h_inbound]

  -- Handle the remaining if-then-else conditions cleanly
  split
  · omega -- Branch 1: a.length + pid * bs + i < a.length is impossible
  · split
    · -- Branch 2: a.length + pid * bs + i < 2 * a.length is the valid block
      have h_idx : a.length + pid * bs + i - a.length = pid * bs + i := by omega
      rw [h_idx]
    · omega -- Branch 3: Index exceeding 2 * a.length is impossible due to h_inbound

theorem vectorAdd_global
    (a b : List Int) (bs gs : Nat)
    (h_len : a.length = b.length)
    (h_bs  : bs > 0)
    (h_cov : gs * bs = a.length) :
    ∀ pid, pid < gs → ∀ i, i < bs →
      MachineState.readMem (evalKernel compiledVectorAdd (vectorAddInitState a b pid bs gs))
        (2 * a.length + pid * bs + i) =
      (vectorAddSpec a b).getD (pid * bs + i) 0 := by
  intro pid h_pid i hi
  have h := vectorAdd_correct a b pid bs gs h_len h_bs h_pid h_cov
  exact h i hi

end Trident
