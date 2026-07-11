-- Trident.Proofs.ReLUProof
-- Reference kernel and symbolic verification for ReLU
-- ReLU(x) = max(0, x)

import Trident.Target.Semantics
import Trident.Common.Symbolic
import Trident.Common.Memory

namespace Trident

-- ── Reference Kernel ──────────────────────────────────────────────────────────

def compiledReLU : TritonKernel := [
  { result := "pid",    op := .get_program_id 0, args := [] },
  { result := "bstart", op := .muli,             args := ["pid", "bsize"] },
  { result := "range",  op := .make_range none,        args := [] },
  { result := "offset", op := .addi,             args := ["bstart", "range"] },
  { result := "xptrs",  op := .addptr,           args := ["x_base", "offset"] },
  { result := "optrs",  op := .addptr,           args := ["out_base", "offset"] },
  { result := "xvals",  op := .load,             args := ["xptrs"] },
  { result := "zero",   op := .constant 0,       args := [] },
  { result := "zeros",  op := .splat [1024],            args := ["zero"] },
  { result := "ovals",  op := .maxsi,            args := ["zeros", "xvals"] },
  { result := "_",      op := .store,            args := ["optrs", "ovals"] }
]

-- ── Symbolic Verification ─────────────────────────────────────────────────────

/-- Initial symbolic state for ReLU: one input array x, one output -/
def symReLUInitState (pid bs gs n : Nat) : SymState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr =>
      if addr < n then Expr.var "x" addr
      else Expr.lit 0
  , env        := fun v => match v with
      | "x_base"   => some (SymValue.scalar (Expr.lit 0))
      | "out_base" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      -- real TTIR uses x_ptr/out_ptr as parameter names
      | "x_ptr"    => some (SymValue.scalar (Expr.lit 0))
      | "out_ptr"  => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "bsize"      => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | "n_elements" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | _            => none }

/-- ReLU spec: output[i] = max(0, x[i]) -/
def reLUSpecExpr (pid bs i : Nat) : Expr :=
  Expr.max (Expr.lit 0) (Expr.var "x" (pid * bs + i))

/-- Normalize for ReLU: resolve loads against x array -/
def normalizeReLU (e : Expr) (n : Nat) : Expr :=
  normalizeExpr e (fun addr =>
    if addr < n then Expr.var "x" addr
    else Expr.lit 0)

/-- Symbolic check: does this kernel compute max(0, x[i]) for ALL inputs? -/
def symCheckReLU (kernel : TritonKernel) (pid bs gs n i : Nat) : Bool :=
  let s' := symEvalKernel kernel (symReLUInitState pid bs gs n)
  let raw  := s'.memory (n + pid * bs + i)
  let norm := normalizeReLU raw n
  norm == reLUSpecExpr pid bs i

end Trident
