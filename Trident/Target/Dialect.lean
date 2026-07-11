-- Trident.Target.Dialect
-- The Triton IR syntax: types, operations, and instruction format.
-- No external dependencies — pure Lean 4 inductive types.
--
-- CompCert equivalent: backend/RTL.v (the target IR definition)
--
-- This covers the full op vocabulary needed for:
--   vector ops, matmul, softmax, layer norm, flash attention

namespace Trident

-- ── Types ─────────────────────────────────────────────────────────────────────

inductive TritonType where
  | int    (width : Nat)
  | float  (width : Nat)
  | ptr    (elem : TritonType)
  | tensor (shape : List Nat) (elem : TritonType)
  deriving BEq, Repr

-- ── Operations ────────────────────────────────────────────────────────────────

inductive TritonOp where
  -- ── Grid ops ──
  | get_program_id (axis : Nat)
  | get_num_programs (axis : Nat)

  -- ── Range and pointer arithmetic ──
  | make_range (size : Option Nat)   -- was: | make_range
  | splat (shape : List Nat)
  | addptr                        -- pointer + offset (scalar or tiled)
  | expand_dims (axis : Nat)
  | broadcast (shape : List Nat)

  -- ── Memory ──
  | load                          -- load from pointer(s)
  | load_masked                   -- load with mask
  | store                         -- store to pointer(s)
  | store_masked                  -- store with mask

  -- ── Integer arithmetic ──
  | constant (val : Int)
  | constant_tensor (val : Int) (shape : List Nat)
  | addi | subi | muli
  | maxsi | minsi          -- element-wise integer max/min
  | divsi | divui
  | remsi | remui
  | andi  | ori  | xori
  | shli  | shrsi | shrui

  -- ── Float arithmetic ──
  | constantf (val : Float)
  | addf | subf | mulf | divf
  | negf | absf | sqrtf
  | truncf | extf | expf             -- float precision conversion

  -- ── Comparison ──
  | select                          -- conditional select
  | cmpi_eq | cmpi_ne
  | cmpi_slt | cmpi_sle
  | cmpi_sgt | cmpi_sge
  | cmpf_olt | cmpf_ole

  -- ── Reductions (needed for softmax, layer norm) ──
  | reduce_sum  (axis : Nat)
  | reduce_max  (axis : Nat)
  | reduce_min  (axis : Nat)

  -- ── Matrix ops (needed for matmul, flash attention) ──
  | dot                           -- matrix multiply accumulate

  -- ── Shape ops ──
  | reshape
  | trans                         -- transpose

  | loadf
  | storef
  | constant_tensorf (val : Float) (shape : List Nat)
  | copy                          -- var→var move: iter_arg init + scf.yield rebind
  deriving BEq, Repr

-- ── SSA Instruction ───────────────────────────────────────────────────────────

/--
One SSA instruction: binds `result` to `op` applied to `args`.
This is the unit of execution in Triton IR.
-/
structure TritonInstr where
  result : String
  op     : TritonOp
  args   : List String
  deriving Repr, BEq

/-- A complete Triton kernel: a list of SSA instructions -/
abbrev TritonKernel := List TritonInstr

/-- A structured for-loop: induction variable name, trip count, and a flat body kernel.
    iter_args are threaded through the state env (the body writes loop-carried vars, next iter reads).
    Kept SEPARATE from TritonInstr so the flat-kernel path and all 50 ops are untouched. -/
structure ForLoop where
  ivName : String
  trip   : Nat
  body   : TritonKernel

-- ── Signatures ────────────────────────────────────────────────────────────────
-- Type signatures for each op. Used by the parser for validation.

def TritonOp.arity : TritonOp → Nat
  | .get_program_id _ => 0
  | .get_num_programs _ => 0
  | .constant _       => 0
  | .constant_tensor _ _ => 0
  | .constantf _      => 0
  | .make_range _       => 0
  | .splat _           => 1
  | .copy              => 1
  | .expand_dims _    => 1
  | .load             => 1
  | .load_masked      => 2
  | .reduce_sum _     => 1
  | .reduce_max _     => 1
  | .reduce_min _     => 1
  | .reshape          => 1
  | .trans            => 1
  | .negf             => 1
  | .absf             => 1
  | .sqrtf            => 1
  | .truncf           => 1
  | .extf             => 1
  | .store            => 2
  | .store_masked     => 3
  | .addptr           => 2
  | .broadcast _       => 2
  | .addi | .subi | .muli   => 2
  | .maxsi | .minsi          => 2
  | .addf | .subf | .mulf   => 2
  | .divsi | .divui         => 2
  | .divf                   => 2
  | .remsi | .remui         => 2
  | .andi  | .ori  | .xori  => 2
  | .shli  | .shrsi | .shrui => 2
  | .select                  => 3
  | .cmpi_eq | .cmpi_ne     => 2
  | .cmpi_slt | .cmpi_sle   => 2
  | .cmpi_sgt | .cmpi_sge   => 2
  | .cmpf_olt | .cmpf_ole   => 2
  | .dot                    => 2
  | .expf => 1
  | .loadf => 2
  | .storef => 2
  | .constant_tensorf _ _ => 0



end Trident
