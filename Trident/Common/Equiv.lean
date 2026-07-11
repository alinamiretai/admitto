-- Trident.Common.Equiv
-- Layer 2: Semantic equivalence checker
-- Runs a parsed kernel against the proved reference on concrete inputs
-- and compares outputs. This is the bridge between Layer 1 (proofs)
-- and real .ttir files.

import Trident.Target.Semantics
import Trident.Compiler
import Trident.Proofs.VectorAddProof
import Trident.Proofs.ReductionProof

namespace Trident

/-- Init state for compiled reference kernel (uses a_base/b_base/c_base) -/
def refInitState (a b : List Int) (pid bs gs : Nat) : MachineState :=
  vectorAddInitState a b pid bs gs

/-- Init state for parsed real TTIR kernels (uses arg0/arg1/arg2 naming) -/
def parsedInitState (a b : List Int) (pid bs gs : Nat) : MachineState :=
  let n := a.length
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := layoutMemory a b
  , env        := fun v => match v with
      | "arg0"   => some (TritonValue.scalar 0)
      | "arg1"   => some (TritonValue.scalar (Int.ofNat n))
      | "arg2"   => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | "a_base" => some (TritonValue.scalar 0)
      | "b_base" => some (TritonValue.scalar (Int.ofNat n))
      | "c_base" => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | "bsize"  => some (TritonValue.scalar (Int.ofNat bs))
      | "x_ptr"      => some (TritonValue.scalar 0)
      | "y_ptr"      => some (TritonValue.scalar (Int.ofNat n))
      | "output_ptr" => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | "n_elements" => some (TritonValue.scalar (Int.ofNat n))
      | _        => none }

/-- Run reference kernel and extract output tile -/
def runRef (a b : List Int) (pid bs gs : Nat) : List Int :=
  let s  := refInitState a b pid bs gs
  let s' := evalKernel compiledVectorAdd s
  (List.range bs).map fun i =>
    s'.readMem (2 * a.length + pid * bs + i)

/-- Run parsed kernel and extract output tile -/
def runAndExtract (kernel : TritonKernel) (a b : List Int)
    (pid bs gs : Nat) : List Int :=
  let s  := parsedInitState a b pid bs gs
  let s' := evalKernel kernel s
  (List.range bs).map fun i =>
    s'.readMem (2 * a.length + pid * bs + i)

/--
  Check semantic equivalence between a parsed kernel and compiledVectorAdd
  by running both on several concrete inputs and comparing outputs.
  NOT a proof — a dynamic check that transfers proof confidence to new kernels.
-/
def checkVectorAddEquiv (parsed : TritonKernel) : Bool :=
  -- Use bs=1024 to match real Triton TTIR compiled with block_size=1024
  -- make_range uses s.block_size so we must match the compiled block size
  let bs := 1024
  let gs := 1
  let a1 := (List.range bs).map (fun i => Int.ofNat (i + 1))
  let b1 := (List.range bs).map (fun i => Int.ofNat (i * 2))
  let a2 := (List.range bs).map (fun _ => (0 : Int))
  let b2 := (List.range bs).map (fun _ => (0 : Int))
  let a3 := (List.range bs).map (fun i => Int.ofNat i)
  let b3 := (List.range bs).map (fun i => Int.ofNat (bs - i))
  let tests : List (List Int × List Int × Nat × Nat) := [
    (a1, b1, bs, gs),
    (a2, b2, bs, gs),
    (a3, b3, bs, gs),
  ]
  tests.all fun (a, b, bs, gs) =>
    let ref := runRef              a b 0 bs gs
    let got := runAndExtract parsed a b 0 bs gs
    ref == got

/-- Result type for the equivalence check -/
inductive EquivResult
  | equivalent                       : EquivResult
  | notEquivalent (msg : String)     : EquivResult
  | parseError                       : EquivResult

/-- Full check with result -/
def verifyAgainstVectorAdd (parsed : TritonKernel) : EquivResult :=
  if checkVectorAddEquiv parsed
  then .equivalent
  else .notEquivalent "outputs differ on test inputs"

/-- Init state for parsed real TTIR reduction kernels -/
def parsedReductionInitState (x : List Int) (pid bs gs : Nat) : MachineState :=
  let n := x.length
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr => if addr < n then x.getD addr 0 else 0
  , env        := fun v => match v with
      | "out_ptr"    => some (TritonValue.scalar (Int.ofNat n))
      | "n_elements" => some (TritonValue.scalar (Int.ofNat n))
      | "x_base"     => some (TritonValue.scalar 0)
      | "out_base"   => some (TritonValue.scalar (Int.ofNat n))
      | "bsize"      => some (TritonValue.scalar (Int.ofNat bs))
      | "x_ptr"      => some (TritonValue.scalar 0)
      | _            => none }

/-- Run reference reduction kernel -/
def runReductionRef (x : List Int) (pid bs gs : Nat) : Int :=
  let s  := { pid := pid, block_size := bs, grid_size := gs
            , memory := fun addr => if addr < x.length then x.getD addr 0 else 0
            , env := fun v => match v with
                | "x_base"  => some (TritonValue.scalar 0)
                | "out_base"=> some (TritonValue.scalar (Int.ofNat x.length))
                | "bsize"   => some (TritonValue.scalar (Int.ofNat bs))
                | _ => none }
  let s' := evalKernel compiledReduction s
  s'.readMem x.length

/-- Run parsed reduction kernel -/
def runReductionParsed (kernel : TritonKernel) (x : List Int) (pid bs gs : Nat) : Int :=
  let s  := parsedReductionInitState x pid bs gs
  let s' := evalKernel kernel s
  s'.readMem x.length

/-- Check reduction by comparing against the mathematical spec directly -/
def checkReductionEquiv (parsed : TritonKernel) : Bool :=
  let bs := 1024
  let gs := 1
  -- test: output should equal x.foldl (· + ·) 0
  let x1 := (List.range bs).map (fun i => Int.ofNat (i + 1))
  let x2 := (List.range bs).map (fun _ => (1 : Int))
  let x3 := (List.range bs).map (fun i => Int.ofNat i)
  let tests := [x1, x2, x3]
  tests.all fun x =>
    let expected := x.foldl (· + ·) 0
    let got := runReductionParsed parsed x 0 bs gs
    expected == got

def parsedMatmulInitState (a b : List Int) (m k n : Nat) (pid bs gs : Nat) : MachineState :=
  let aBase := 0
  let bBase := m * k
  let cBase := m * k + k * n
  { pid := pid
  , pid_y := 0
  , block_size := bs
  , grid_size := gs
  , memory := fun addr =>
      if addr < m * k then a.getD addr 0
      else if addr < m * k + k * n then b.getD (addr - m * k) 0
      else 0
  , env := fun name => match name with
      | "a_ptr"     => some (TritonValue.scalar (Int.ofNat aBase))
      | "b_ptr"     => some (TritonValue.scalar (Int.ofNat bBase))
      | "c_ptr"     => some (TritonValue.scalar (Int.ofNat cBase))
      | "M"         => some (TritonValue.scalar (Int.ofNat m))
      | "N"         => some (TritonValue.scalar (Int.ofNat n))
      | "K"         => some (TritonValue.scalar (Int.ofNat k))
      | "stride_am" => some (TritonValue.scalar (Int.ofNat k))
      | "stride_bk" => some (TritonValue.scalar (Int.ofNat n))
      | "stride_cm" => some (TritonValue.scalar (Int.ofNat n))
      | _           => none }

def checkMatmulEquiv (parsed : TritonKernel) : Bool :=
  let m := 128
  let k := 128
  let n := 128
  let a := (List.range (m * k)).map (fun i => Int.ofNat (i % 7 + 1))
  let b := (List.range (k * n)).map (fun i => Int.ofNat (i % 5 + 1))
  let s  := parsedMatmulInitState a b m k n 0 64 1
  let s' := evalKernel parsed s
  let cBase := m * k + k * n
  (List.range 64).all fun i =>
    (List.range 64).all fun j =>
      let expected := (List.range k).foldl
        (fun acc kk => acc + a.getD (i * k + kk) 0 * b.getD (kk * n + j) 0) 0
      s'.readMem (cBase + i * n + j) == expected
def parsedSoftmaxInitState (x : List Int) (ncols : Nat) (pid bs gs : Nat) : MachineState :=
  let inputBase := 0
  let outputBase := ncols
  { pid := pid
  , pid_y := 0
  , block_size := bs
  , grid_size := gs
  , memory := fun addr => if addr < ncols then x.getD addr 0 else 0
  , fmemory := fun addr => if addr < ncols then Float.ofInt (x.getD addr 0) else 0.0
  , env := fun name => match name with
      | "input_ptr"         => some (TritonValue.scalar (Int.ofNat inputBase))
      | "output_ptr"        => some (TritonValue.scalar (Int.ofNat outputBase))
      | "input_row_stride"  => some (TritonValue.scalar (Int.ofNat ncols))
      | "output_row_stride" => some (TritonValue.scalar (Int.ofNat ncols))
      | "n_cols"            => some (TritonValue.scalar (Int.ofNat ncols))
      | _ => none }

def checkSoftmaxEquiv (parsed : TritonKernel) : Bool :=
  let ncols := 16
  let x := (List.range ncols).map (fun i => Int.ofNat (i + 1))
  let s  := parsedSoftmaxInitState x ncols 0 16 1
  let s' := evalKernel parsed s
  let xf := x.map (fun v => Float.ofInt v)
  let maxVal := xf.foldl max (xf.headD 0.0)
  let expVals := xf.map (fun v => Float.exp (v - maxVal))
  let sumExp := expVals.foldl (· + ·) 0.0
  let expected := expVals.map (fun v => v / sumExp)
  (List.range ncols).all fun i =>
    Float.abs (s'.readMemF (ncols + i) - expected.getD i 0.0) < 0.0001

end Trident
