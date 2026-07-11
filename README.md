# Trident

A formal verification framework for Triton GPU kernels, in Lean 4.

Trident gives Triton IR (TTIR) an executable formal semantics, a symbolic evaluator, and a machine-checked proof that the two agree. On top of that foundation it verifies functional correctness of specific kernels: what the kernel computes, at every output lane, as a function of its inputs.

**Status:** research prototype. Two kernels verified (vector-add complete; matmul faithfulness complete, functional correctness in progress). The semantics has not been validated against the real Triton compiler — see [Limitations](#limitations), which is the most important section of this document.

---

## What it does

Given a `.ttir` file, Trident:

1. **Parses** it into a `TritonKernel` (a list of `TritonInstr`).
2. **Evaluates** it two ways — concretely (`evalKernel`, machine states with real values) and symbolically (`symEvalKernel`, states holding expression trees).
3. **Proves faithfulness**: the symbolic state's expressions, evaluated against the concrete memory, equal the concrete state's values. This is the `FaithfulWFI` invariant, threaded through every instruction.
4. **Proves correctness**: for a specific kernel, the value written to each output address equals a stated mathematical function of the inputs.

Steps 1–3 are largely generic. Step 4 is per-kernel and, for looped kernels, requires a hand-written loop invariant.

### The automated path

For straight-line kernels (no `scf.for`), verification is fully automatic:

```lean
theorem kernel_faithful_of_supported (K : TritonKernel)
    (hall : K.all instrSupported = true)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalKernel K s) (symEvalKernel K ss) mem
```

The premise `K.all instrSupported = true` is decidable — `native_decide` discharges it on any concrete parsed kernel. **Verifying a new straight-line kernel requires zero new Lean.** This is the part of the project that behaves like a tool rather than a proof.

Looped kernels are not automatic. Matmul's loop invariant is roughly 2,000 lines of bespoke Lean.

---

## What's proven

### Vector-add — complete

```lean
theorem checkVectorAdd_sound (src : String) (pid bs n : Nat)
    (hchk : checkVectorAdd src pid bs n = true)
    (k : TritonKernel) (hpk : parseKernel src = some k)
    (a b : List Int) (hla : a.length = n) (hlb : b.length = n)
    (i : Nat) (hi : i < bs) :
    MachineState.readMem (evalKernel k (parsedInitState a b pid bs 1)) (2 * n + pid * bs + i)
      = (if pid * bs + i < n then a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 else 0)
```

Every output lane, including the masked tail. Axiom-clean: `#print axioms` returns `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide` leakage into the trusted base.

### Matmul — faithfulness complete, correctness in progress

**Faithfulness (done).** The accumulator loop preserves the invariant across arbitrary trip counts:

```lean
theorem forLoop_matmul {c : MachineState} {sc : SymState} {mem : Nat → Int}
    (Md Kd Nd : Nat) (hKpos : 0 < Kd) (hNpos : 0 < Nd) (trip : Nat)
    (hinit : MatmulLoopInv … Md Kd Nd c sc mem) :
    MatmulLoopInv … Md Kd Nd
      (evalForLoop { ivName := "k", trip := trip, body := MatmulBody Md Kd Nd } c)
      (symEvalForLoop { ivName := "k", trip := trip, body := MatmulBody Md Kd Nd } sc) mem
```

All 18 body instructions — two masked tile loads, two broadcasts, the `[64,32]·[32,64]→[64,64]` contraction, two pointer advances, three iter-arg yields — dispatch into `FaithfulWFI`.

**Correctness (in progress).** Every semantic ingredient is proven; the composition is partly done.

Three results are worth calling out because they were discovered rather than assumed:

**The dot really is a contraction.** `evalOp .dot`'s index arithmetic was checked against the standard row-major definition, not eyeballed:

```lean
theorem dot_lane_value (m k1 n i j : Nat) (A B Acc : List Int)
    (hi : i < m) (hj : j < n) :
    <dot output>.getD (i * n + j) 0 = contract A B k1 n i j + Acc.getD (i * n + j) 0
```

No off-by-one, no transposition.

**The tail tile is correct *because* `arith.subi` is signed.** The k-bound mask compares `offs_k[kk] < K - t·32` over `Int`. When `t·32 > K` the right-hand side goes negative and no lane passes. Over `Nat` the subtraction would truncate to zero and the mask would admit *every* lane:

```lean
theorem mask_boundary (t Kd Kfull kk : Nat) :
    (Int.ofNat kk < Int.ofNat Kfull - Int.ofNat (t * Kd)) ↔ (t * Kd + kk < Kfull)
```

**Out-of-range columns agree by accident of `getD`.** Where the mask zeroes the kernel's operands, the specification reads past the end of `B` — and `List.getD`'s default is `0`. Both give zero. This requires `B.length = Kfull * N` and, notably, *nothing* about `A`'s length:

```lean
theorem masked_term_eq (A B : List Int) (M Kfull N i j t Kd kk : Nat)
    (hB : B.length = Kfull * N) (hiM : i < M) (hjN : j < N) : …
```

The minimal precondition fell out of the proof rather than being posited.

---

## Architecture

```
Trident/
  Common/
    Values.lean      TritonValue (scalar, tensor, fscalar, ftensor); WF1, WFn
    Memory.lean      MachineState (env, memory, pid, block_size, grid_size)
    Symbolic.lean    Expr, IntBinop, FExpr; SymValue; SymState; symEvalOp
    Equiv.lean       parsedInitState
  Target/
    Dialect.lean     TritonOp
    Semantics.lean   evalOp, evalInstr, evalKernel, evalForLoop
    Parser.lean      parseKernel, parseMatmulKernel
  Proofs/
    Soundness.lean   ~6,000 lines: the invariant, dispatch layer, matmul proofs
    Checker.lean     checkVectorAdd + checkVectorAdd_sound
    VectorAddProof.lean
```

### Core invariant

```lean
def FaithfulWFI (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  FaithfulWF s ss mem ∧ NoFloatState s
```

where `FaithfulWF` bundles `StatesFaithful` (symbolic evaluates to concrete, lane by lane), the memory-equality fact, and `WFState` (every bound tensor satisfies `shapeProd sh = vals.length`).

`WFState` uses `WFn`, a **rank-agnostic** well-formedness predicate. An earlier rank-1 version (`sh = [vals.length]`) was false for the 2-D tensors matmul needs; discovering this required rebuilding the invariant and every proof above it.

### Reusable machinery

The genuinely reusable output of the matmul work is a small combinator library:

| Lemma | What it gives |
|---|---|
| `generic_step` | Any supported instruction preserves `FaithfulWFI` |
| `kernel_faithful_of_supported` | Any all-supported straight-line kernel, via `native_decide` |
| `evalInstr_eq_bind` | Non-store op with `evalOp = some val` ⟹ `evalInstr = s.bind result val` |
| `env_carry` / `env_carry_kernel` | A block preserves every variable it never writes |
| `memory_carry_kernel` | A store-free block preserves memory |
| `loop_faithful_skeleton` | Fold-invariant preservation, arbitrary relation |
| `loop_indexed_skeleton` | Same, with an *iteration-indexed* relation `R : Nat → C → S → Prop` |
| `*_binds` family | The exact value each op writes, for straight-line chaining |

`loop_indexed_skeleton` exists because `loop_faithful_skeleton`'s fixed relation cannot express "after `t` iterations the accumulator holds the partial contraction over the first `t` tiles."

---

## Limitations

This section is the honest part. Every item below is a real gap, and the first two govern everything else.

### The parser type-erases

`parseKernel` maps f16 `tt.load` and `tt.dot` to the *integer* ops `.load` and `.dot`. The tutorial matmul is `f16 × f16 → f32` with `tf32` accumulation; as parsed, it is an integer kernel. Concretely: of 105 parsed instructions, 104 are integer and the one float op (`truncf`) has identity semantics.

So the matmul theorem is about an integer reading of a float kernel. That reading is coherent — an integer matmul has the same addressing, masking, tiling and loop structure, which is where miscompilations live — but it is not the program in the file.

### The semantics has never been validated against Triton

`evalOp` was written by hand from the Triton documentation and MLIR sources. It has never been executed against the real compiler on a single kernel. **Every theorem in this repository is conditional on a model nobody has checked**, including the author.

This is the highest-priority gap. Differential testing — run randomized kernels through both Triton and `evalOp`, compare — would either validate the semantics or produce a list of disagreements. Either outcome is more valuable than another verified kernel.

### Single program instance, disjoint buffers

Verification is for one `pid`. Nothing is said about grid coverage (is every output element written exactly once?) or races between programs. `layoutMatmul` places `A`, `B`, `C` in disjoint regions *by construction*, so aliasing bugs cannot appear.

### No float arithmetic

`FExpr` and `evalFExpr` exist as scaffolding. There is no IEEE-754 model, no rounding, no `tf32`, no reasoning about non-associative accumulation. Kernels whose *meaning* is float — softmax, layer-norm, attention — cannot be given a theorem at all under the current parser, because there is no integer reading of `exp`.

### Structurally invisible bug classes

Shared-memory overflow, register pressure, pipelining deadlock: these are properties of the *lowered* code, after Triton's backend allocates and schedules. Trident models TTIR, which sits above all of it. These are not extensions; they are a different project on a different IR.

### Loop invariants are hand-written

Matmul's invariant is ~2,000 lines. A second looped kernel would need its own. This is the standard deductive-verification bargain (Dafny, Why3, Frama-C all make it), but it means Trident does not currently *scale* to new looped kernels without a proof engineer.

### Known open corrections

Two errors in the in-progress value layer, found and not yet fixed:

- `AptrTile` ignores the `pid_m` offset and the `% M` wrap in `offs_am`. It is correct only for `pid_m = 0`. The fix ripples upward through `tile_load_value_A` and everything above it.
- `AccPartial_full` assumes `T · Kd = Kfull`. The kernel's trip count is `⌈K/32⌉`, giving `T · Kd ≥ Kfull`. The extra columns are masked and `B.getD` reads past the end, so the result still holds — but the lemma needs generalizing to the inequality.

### Trusted base

Four `sorry`s remain, all in dead code (an unused monolithic `evalInstr_faithful` superseded by the dispatch layer). They should be deleted. `checkVectorAdd_sound` is axiom-clean; the same check has not yet been run on the matmul theorems.

---

## Roadmap

1. **Finish matmul.** Complete the value walk, fix the two open corrections above, establish loop entry from the pre-block, compose `checkMatmul_sound`. Verify axiom-cleanliness.
2. **Hygiene.** Delete the dead `sorry`s. Split the 6,000-line `Soundness.lean`. Add CI.
3. **Fidelity.** *The load-bearing step.* Ingest real MLIR instead of string-matching. Preserve types. Differentially test `evalOp` against Triton on randomized kernels. Publish the disagreements.
4. **Artifact.** `checkTTIR file.ttir` as a command-line tool, usable without Lean.
5. **Then, and only then:** float structure (uninterpreted arithmetic, verified addressing), grid coverage, and whatever the differential test turns up.

Steps 1–4 are engineering. Everything after is research.

---

## Building

```bash
lake build                              # everything
lake build Trident.Proofs.Soundness     # the core
lake build Trident.Proofs.Checker       # the verified checkers
```

Requires Lean 4 (`nightly-2025-12-01`) via `elan`. No Mathlib dependency — the proofs use core `Nat`/`Int`/`List` lemmas only, which is why you will see `Nat.add_mul_div_right` rather than `omega` in places where `omega` cannot see inside an `Int.ofNat`.

Check the trusted base:

```lean
#print axioms checkVectorAdd_sound
-- [propext, Classical.choice, Quot.sound]
```

---

## Notes for anyone reading the proofs

Three traps cost real time and are worth knowing:

- **`Int.ofNat` splits definitionally.** `Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b` is `rfl`, not a rewrite target, and `omega` cannot see inside the cast. Pattern: prove the `Nat` identity, then lift with `rfl` or `show`.
- **`omega` cannot do variable products.** `i * Kfull` is nonlinear. Use structural `Nat` lemmas.
- **`set` breaks the straight-line walks.** Use explicit nested `evalInstr` terms.

The `binds`-family lemmas come in two flavours: `foo_binds` (existential, hides the output expression) and `foo_binds_explicit` (states it). The value layer needs the explicit form; the shape layer does not.

---

## License

TBD.
