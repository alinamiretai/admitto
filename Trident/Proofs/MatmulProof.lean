-- Trident.Proofs.MatmulProof
-- Matrix multiply: C[i,j] = sum_k(A[i,k] * B[k,j])
-- Flat memory: A at [0,M*K), B at [M*K, M*K+K*N), C at [M*K+K*N,...)

import Trident.Target.Semantics
import Trident.Common.Symbolic
import Trident.Common.Memory

namespace Trident

-- ── Spec ─────────────────────────────────────────────────────────────────────

def matmulSpecExpr (i j K N : Nat) : Expr :=
  Expr.reduceSum ((List.range K).map fun k =>
    Expr.mul (Expr.var "A" (i * K + k)) (Expr.var "B" (k * N + j)))

-- ── Initial State ─────────────────────────────────────────────────────────────

def symMatmulInitState (pid_m pid_n M N K : Nat) : SymState :=
  { pid        := pid_m
  , block_size := M * K   -- M*K so make_range loads full tile
  , grid_size  := 1
  , memory     := fun addr =>
      if addr < M * K then Expr.var "A" addr
      else if addr < M * K + K * N then Expr.var "B" (addr - M * K)
      else Expr.lit 0
  , env        := fun v => match v with
      | "a_ptr"  => some (SymValue.scalar (Expr.lit 0))
      | "b_ptr"  => some (SymValue.scalar (Expr.lit (Int.ofNat (M * K))))
      | "c_ptr"  => some (SymValue.scalar (Expr.lit (Int.ofNat (M * K + K * N))))
      | "K_dim"  => some (SymValue.scalar (Expr.lit (Int.ofNat K)))
      | "MK"     => some (SymValue.scalar (Expr.lit (Int.ofNat (M * K))))
      | "KN"     => some (SymValue.scalar (Expr.lit (Int.ofNat (K * N))))
      | _        => none }

-- ── Reference Kernel ──────────────────────────────────────────────────────────
-- Loads full flat tiles of A (M*K elements) and B (K*N elements)
-- then computes C = dot(A_tile, B_tile)

def compiledMatmul2x2 : TritonKernel := [
  -- Load full A tile: M*K = 4 elements starting at a_ptr
  { result := "MK",      op := .constant 4,     args := [] },  -- M*K = 4
  { result := "a_range", op := .make_range,       args := [] },  -- [0,1,2,3]
  { result := "a_base",  op := .splat,           args := ["a_ptr"] },
  { result := "a_ptrs",  op := .addptr,          args := ["a_base", "a_range"] },
  { result := "A_tile",  op := .load,            args := ["a_ptrs"] },
  -- Load full B tile: K*N = 4 elements starting at b_ptr
  { result := "b_base",  op := .splat,           args := ["b_ptr"] },
  { result := "b_ptrs",  op := .addptr,          args := ["b_base", "a_range"] },
  { result := "B_tile",  op := .load,            args := ["b_ptrs"] },
  -- Matrix multiply
  { result := "acc",     op := .dot,             args := ["A_tile", "B_tile"] },
  -- Store C tile: M*N = 4 elements starting at c_ptr
  { result := "c_base",  op := .splat,           args := ["c_ptr"] },
  { result := "c_ptrs",  op := .addptr,          args := ["c_base", "a_range"] },
  { result := "_",       op := .store,           args := ["c_ptrs", "acc"] }
]

-- ── Symbolic Check ────────────────────────────────────────────────────────────

def normalizeMatmul (e : Expr) (M K N : Nat) : Expr :=
  normalizeExpr e (fun addr =>
    if addr < M * K then Expr.var "A" addr
    else if addr < M * K + K * N then Expr.var "B" (addr - M * K)
    else Expr.lit 0)

def symCheckMatmul (kernel : TritonKernel) (M N K i j : Nat) : Bool :=
  let s' := symEvalKernel kernel (symMatmulInitState 0 0 M N K)
  let C_base := M * K + K * N
  let addr := C_base + i * N + j
  let raw  := s'.memory addr
  let norm := normalizeMatmul raw M K N
  norm == matmulSpecExpr i j K N

end Trident
