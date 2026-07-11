-- Trident.Common.Memory
-- The virtual GPU machine state.
-- Models one thread block's view of memory and registers.
--
-- CompCert equivalent: common/Memory.v
-- Key difference from CompCert: GPU memory is flat (no stack frames,
-- no heap allocation, no undefined behavior from C).
-- This makes our memory model significantly simpler.

import Trident.Common.Values

namespace Trident

/--
`MachineState` is the complete state of one GPU thread block mid-execution.

Fields:
  pid        — which block this is (0 .. grid_size - 1)
  block_size — number of elements this block processes (BLOCK_SIZE constexpr)
  grid_size  — total number of blocks launched
  memory     — flat virtual memory: address → integer value
  env        — SSA variable environment: name → value
-/
structure MachineState where
  pid        : Nat
  pid_y      : Nat := 0
  block_size : Nat
  grid_size  : Nat
  memory     : Nat → Int
  fmemory    : Nat → Float := fun _ => 0.0
  env        : String → Option TritonValue
  deriving Inhabited
namespace MachineState

-- ── Environment operations ────────────────────────────────────────────────────

/-- Look up an SSA variable -/
@[inline]
def lookup (s : MachineState) (v : String) : Option TritonValue :=
  s.env v

/-- Bind an SSA variable to a value, returning the updated state -/
@[inline]
def bind (s : MachineState) (v : String) (val : TritonValue) : MachineState :=
  { s with env := fun name => if name == v then some val else s.env name }

-- ── Memory operations ─────────────────────────────────────────────────────────

/-- Read one integer from virtual memory -/
@[inline]
def readMem (s : MachineState) (addr : Nat) : Int :=
  s.memory addr

/-- Write one integer to virtual memory -/
@[inline]
def writeMem (s : MachineState) (addr : Nat) (val : Int) : MachineState :=
  { s with memory := fun a => if a == addr then val else s.memory a }

/-- Write a full tile of values starting at base address -/
def writeTile (s : MachineState) (addrs : List Nat) (vals : List Int) : MachineState :=
  (addrs.zip vals).foldl (fun st (a, v) => st.writeMem a v) s

def readMemF (s : MachineState) (addr : Nat) : Float :=
  s.fmemory addr

def writeMemF (s : MachineState) (addr : Nat) (val : Float) : MachineState :=
  { s with fmemory := fun a => if a == addr then val else s.fmemory a }

def writeTileF (s : MachineState) (addrs : List Nat) (vals : List Float) : MachineState :=
  (addrs.zip vals).foldl (fun st (a, v) => st.writeMemF a v) s

-- ── Key lemmas ────────────────────────────────────────────────────────────────
-- These are the "machine lemmas" that simulation proofs use.
-- Named and proved here so Proofs/ files stay clean.

@[simp]
theorem bind_lookup_self (s : MachineState) (v : String) (val : TritonValue) :
    (s.bind v val).lookup v = some val := by
  simp [bind, lookup]

@[simp]
theorem bind_lookup_other (s : MachineState) (v w : String) (val : TritonValue)
    (h : v ≠ w) : (s.bind v val).lookup w = s.lookup w := by
  simp [bind, lookup]; intro heq; simp [heq] at h

@[simp]
theorem writeMem_readMem_self (s : MachineState) (addr : Nat) (val : Int) :
    (s.writeMem addr val).readMem addr = val := by
  simp [writeMem, readMem]

@[simp]
theorem writeMem_readMem_other (s : MachineState) (a b : Nat) (val : Int)
    (h : a ≠ b) : (s.writeMem a val).readMem b = s.readMem b := by
  simp [writeMem, readMem]; intro heq; simp [heq] at h

-- Binding does not affect memory
@[simp]
theorem bind_readMem (s : MachineState) (v : String) (val : TritonValue) (a : Nat) :
    (s.bind v val).readMem a = s.readMem a := by
  simp [bind, readMem]

-- writeMem does not affect the environment
@[simp]
theorem writeMem_lookup (s : MachineState) (addr : Nat) (val : Int) (v : String) :
    (s.writeMem addr val).lookup v = s.lookup v := by
  simp [writeMem, lookup]

end MachineState
-- General lemma: foldl writeMem over addresses not containing `addr` preserves readMem addr
theorem foldl_writeMem_not_mem
    (addrs : List Nat) (vals : List Int) (s : MachineState) (addr : Nat)
    (h : addr ∉ addrs) :
    (List.foldl (fun st (x : Nat × Int) => MachineState.writeMem st x.fst x.snd)
       s (addrs.zip vals)).readMem addr = s.readMem addr := by
  induction addrs generalizing vals s with
  | nil => simp
  | cons a as ih =>
    cases vals with
    | nil => simp
    | cons v vs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      simp only [List.mem_cons, not_or] at h
      rw [ih vs (s.writeMem a v) h.2]
      exact MachineState.writeMem_readMem_other s a addr v (Ne.symm h.1)

-- General lemma: foldl writeMem over a Nodup address list, reading at addrs[i], gives vals[i]
theorem foldl_writeMem_readMem
    (addrs : List Nat) (vals : List Int) (s : MachineState)
    (hlen : addrs.length = vals.length) (hnodup : addrs.Nodup)
    (i : Nat) (hi : i < addrs.length) :
    (List.foldl (fun st (x : Nat × Int) => MachineState.writeMem st x.fst x.snd)
       s (addrs.zip vals)).readMem (addrs.getD i 0) = vals.getD i 0 := by
  induction addrs generalizing vals s i with
  | nil => simp at hi
  | cons a as ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [List.nodup_cons] at hnodup
      cases i with
      | zero =>
        simp only [List.getD_cons_zero]
        rw [foldl_writeMem_not_mem as vs (s.writeMem a v) a hnodup.1]
        exact MachineState.writeMem_readMem_self s a v
      | succ n =>
        simp only [List.getD_cons_succ]
        simp only [List.length_cons] at hlen hi
        exact ih vs (s.writeMem a v) (by omega) hnodup.2 n (by omega)

-- General lemma: a strictly monotone/injective map of List.range is Nodup
theorem nodup_map_injective (f : Nat -> Nat) (l : List Nat)
    (h : forall x y, f x = f y -> x = y) (hl : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      simp only [List.mem_map] at hmem
      obtain ⟨x, hx, hfx⟩ := hmem
      exact hl.1 (h x a hfx ▸ hx)
    · exact ih hl.2

-- General lemma: getElem? of a zip, when both indices are in range
theorem getElem?_zip {α β : Type} {l1 : List α} {l2 : List β} {i : Nat}
    (h1 : i < l1.length) (h2 : i < l2.length) :
    (l1.zip l2)[i]? = some (l1[i]'h1, l2[i]'h2) := by
  rw [List.getElem?_eq_getElem (by simp; omega)]
  congr 1
  simp [List.getElem_zip]

-- splat(c) zipped with range then summed = map (c + ·) range
theorem replicate_zip_range (bs : Nat) (c : Int) :
    List.map (fun x : Int × Int => x.fst + x.snd)
      ((List.replicate bs c).zip (List.map Int.ofNat (List.range bs))) =
    List.map (fun j => c + Int.ofNat j) (List.range bs) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_replicate,
               List.getElem_map, List.getElem_range]

end Trident
