-- Trident.Proofs.ReductionProof
-- Reference kernel and symbolic verification for reduction (sum)
-- reduction(x) = x[0] + x[1] + ... + x[bs-1]

import Trident.Target.Semantics
import Trident.Common.Symbolic
import Trident.Common.Memory

namespace Trident

-- ── Reference Kernel ──────────────────────────────────────────────────────────

def compiledReduction : TritonKernel := [
  { result := "pid",    op := .get_program_id 0, args := [] },
  { result := "bstart", op := .muli,             args := ["pid", "bsize"] },
  { result := "range",  op := .make_range none,        args := [] },
  { result := "offset", op := .addi,             args := ["bstart", "range"] },
  { result := "xptrs",  op := .addptr,           args := ["x_base", "offset"] },
  { result := "xvals",  op := .load,             args := ["xptrs"] },
  { result := "sum",    op := .reduce_sum 0,     args := ["xvals"] },
  { result := "outptr", op := .addptr,           args := ["out_base", "pid"] },
  { result := "_",      op := .store,            args := ["outptr", "sum"] }
]

-- ── Symbolic Verification ─────────────────────────────────────────────────────

def symReductionInitState (pid bs gs n : Nat) : SymState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr =>
      if addr < n then Expr.var "x" addr
      else Expr.lit 0
  , env        := fun v => match v with
      | "x_base"   => some (SymValue.scalar (Expr.lit 0))
      | "out_base" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "bsize"    => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | _          => none }

/-- Reduction spec: output = sum of x[pid*bs .. pid*bs+bs) -/
def reductionSpecExpr (pid bs : Nat) : Expr :=
  Expr.reduceSum ((List.range bs).map (fun i => Expr.var "x" (pid * bs + i)))

/-- Normalize for reduction -/
def normalizeReduction (e : Expr) (n : Nat) : Expr :=
  normalizeExpr e (fun addr =>
    if addr < n then Expr.var "x" addr
    else Expr.lit 0)

/-- Symbolic check: does this kernel compute sum(x[i]) for ALL inputs? -/
def symCheckReduction (kernel : TritonKernel) (pid bs gs n : Nat) : Bool :=
  let s' := symEvalKernel kernel (symReductionInitState pid bs gs n)
  let raw  := s'.memory (n + pid)
  let norm := normalizeReduction raw n
  norm == reductionSpecExpr pid bs

end Trident
