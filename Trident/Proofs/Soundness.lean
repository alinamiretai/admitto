import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.VectorAddProof
import Trident.Common.Equiv


set_option linter.unusedSimpArgs false


namespace Trident
open TritonValue


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 1: Core definitions
-- ══════════════════════════════════════════════════════════════════════════════


-- The central invariant: machine state and symbolic state agree on memory and
-- every bound variable, under interpretation by `mem`.
def StatesFaithful (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
 s.pid = ss.pid
 ∧ s.block_size = ss.block_size
 ∧ s.grid_size = ss.grid_size
 ∧ (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
 ∧ (∀ v val, s.env v = some (scalar val) →
     ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
 ∧ (∀ v sh vals, s.env v = some (tensor sh vals) →
     ∃ g, ss.env v = some (SymValue.tensor sh g)
       ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
 ∧ (∀ v, s.env v = none → ss.env v = none)


-- Concreteness predicate: expression does not read from symbolic memory
@[simp] theorem shapeProd_pair (x y : Nat) : shapeProd [x, y] = x * y := by
  simp [shapeProd, List.foldl]

@[simp] theorem shapeProd_singleton (x : Nat) : shapeProd [x] = x := by
  simp [shapeProd]

def Expr.isConcrete : Expr → Bool
 | .lit _       => true
 | .var _ _     => false
 | .load _      => false
 | .add e1 e2   => e1.isConcrete && e2.isConcrete
 | .mul e1 e2   => e1.isConcrete && e2.isConcrete
 | .max e1 e2   => e1.isConcrete && e2.isConcrete
 | .reduceSum _ => false
 | .select c t e => c.isConcrete && t.isConcrete && e.isConcrete
 | .lt a b => a.isConcrete && b.isConcrete
 | .binop _ a b => a.isConcrete && b.isConcrete


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 2: Expression and list lemmas
-- ══════════════════════════════════════════════════════════════════════════════


-- Concrete expressions are memory-independent
theorem evalExpr_concrete (e : Expr) (mem1 mem2 : Nat → Int)
   (h : e.isConcrete = true) :
   evalExpr e mem1 = evalExpr e mem2 := by
 match e with
 | .lit n => simp [evalExpr]
 | .var _ _ => simp [Expr.isConcrete] at h
 | .load _ => simp [Expr.isConcrete] at h
 | .add e1 e2 =>
     simp [Expr.isConcrete, Bool.and_eq_true] at h
     simp [evalExpr, evalExpr_concrete e1 mem1 mem2 h.1,
                     evalExpr_concrete e2 mem1 mem2 h.2]
 | .mul e1 e2 =>
     simp [Expr.isConcrete, Bool.and_eq_true] at h
     simp [evalExpr, evalExpr_concrete e1 mem1 mem2 h.1,
                     evalExpr_concrete e2 mem1 mem2 h.2]
 | .max e1 e2 =>
     simp [Expr.isConcrete, Bool.and_eq_true] at h
     simp [evalExpr, evalExpr_concrete e1 mem1 mem2 h.1,
                     evalExpr_concrete e2 mem1 mem2 h.2]
 | .reduceSum _ => simp [Expr.isConcrete] at h
 | .select c t e =>
     simp [Expr.isConcrete, Bool.and_eq_true] at h
     simp [evalExpr, evalExpr_concrete c mem1 mem2 h.1.1,
                     evalExpr_concrete t mem1 mem2 h.1.2,
                     evalExpr_concrete e mem1 mem2 h.2]
 | .lt a b =>
     simp [Expr.isConcrete, Bool.and_eq_true] at h
     simp [evalExpr, evalExpr_concrete a mem1 mem2 h.1,
                     evalExpr_concrete b mem1 mem2 h.2]
 | .binop op a b =>
     simp [Expr.isConcrete, Bool.and_eq_true] at h
     have hae := evalExpr_concrete a mem1 mem2 h.1
     have hbe := evalExpr_concrete b mem1 mem2 h.2
     cases op <;> simp only [evalExpr, hae, hbe]


-- (List.range n).map ofNat getD
private theorem range_map_getD (n i : Nat) :
   (List.map Int.ofNat (List.range n)).getD i 0 =
   if i < n then Int.ofNat i else 0 := by
 rcases Nat.lt_or_ge i n with h | h
 · simp [List.getD, List.getElem?_map, List.getElem?_range, h]
 · simp [List.getD, List.length_map, List.length_range, Nat.not_lt.mpr h]


-- map (· + x) getD
private theorem map_add_getD (ys : List Int) (x : Int) (i : Nat)
   (h : i < ys.length) :
   (ys.map (· + x)).getD i 0 = ys.getD i 0 + x := by
 simp [List.getD, List.getElem?_map, h]


-- (xs.zip ys).map (fst + snd) getD, index in bounds for both
-- ── DESIGN DECISION (recorded 2026-06-29) ────────────────────────────────────
-- Elementwise tensor ops (addi/muli/addf/... tensor+tensor) currently MISMATCH
-- between concrete and symbolic evaluators:
--   concrete (Semantics.lean) guards on SHAPE equality  (sh == sh2)
--   symbolic (Symbolic.lean symAdd/symMul) has NO guard; binds with first length
-- This is a genuine faithfulness gap for shape-mismatched operands.
-- RESOLUTION (queued, do FIRST next session — edits trusted models):
--   Length-guard BOTH evaluators (elementwise faithfulness depends on element
--   count, not shape). Sound for well-typed TTIR where shape-match <=> length-match.
--   Add shape/length-compatibility validation to the PARSER as an ingest gate, so
--   the soundness theorem assumes well-typed input. Then prove addi/muli
--   tensor+tensor faithful uniformly (no per-kernel obligation).
-- The list helper below (zip_add_getD) is guard-independent and already validated.
-- ──────────────────────────────────────────────────────────────────────────────

-- (xs.zip ys).map (fst+snd) indexed = xs[i] + ys[i], by structural induction.
-- Guard-independent; used by the addi/addf tensor+tensor faithfulness proofs.
theorem zip_add_getD (a b : List Int) (i : Nat)
    (hi : i < a.length) (hab : a.length = b.length) :
    ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 = a.getD i 0 + b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases i with
      | zero => simp [List.zip_cons_cons]
      | succ j =>
        simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
        exact ih ys j (by simpa using hi) (by simpa using hab)

theorem zip_mul_getD (a b : List Int) (i : Nat)
    (hi : i < a.length) (hab : a.length = b.length) :
    ((a.zip b).map (fun p => p.fst * p.snd)).getD i 0 = a.getD i 0 * b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases i with
      | zero => simp [List.zip_cons_cons]
      | succ j =>
        simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
        exact ih ys j (by simpa using hi) (by simpa using hab)

theorem zip_lt_getD (a b : List Int) (i : Nat)
    (hi : i < a.length) (hab : a.length = b.length) :
    ((a.zip b).map (fun p => if p.fst < p.snd then (1:Int) else 0)).getD i 0 =
    (if a.getD i 0 < b.getD i 0 then 1 else 0) := by
  induction a generalizing b i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases i with
      | zero => simp [List.zip_cons_cons]
      | succ j =>
        simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
        exact ih ys j (by simpa using hi) (by simpa using hab)

theorem zip_mask_load_getD (addrs masks : List Int) (i : Nat) (rm : Int → Int)
    (hi : i < addrs.length) (hlen : addrs.length = masks.length) :
    ((addrs.zip masks).map (fun x => if (x.snd != 0) = true then rm x.fst else 0)).getD i 0 =
    (if (masks.getD i 0 != 0) = true then rm (addrs.getD i 0) else 0) := by
  induction addrs generalizing masks i with
  | nil => simp at hi
  | cons a as ih =>
    cases masks with
    | nil => simp at hlen
    | cons mk ms =>
      cases i with
      | zero => simp [List.zip_cons_cons]
      | succ j =>
        simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
        exact ih ms j (by simpa using hi) (by simpa using hlen)

-- ── produces-WF1 lemmas: tensor-producing ops yield rank-1 wellformed output ──
-- These discharge the WF1 hypotheses of elementwise faithfulness lemmas locally,
-- from whatever op produced each operand. No global invariant threading needed.

theorem make_range_produces_WF1 (sizeOpt : Option Nat) (args : List String) (s : MachineState)
    (sh : List Nat) (vals : List Int)
    (h : evalOp (.make_range sizeOpt) args s = some (tensor sh vals)) :
    (tensor sh vals).WF1 := by
  simp only [evalOp] at h
  injection h with h
  injection h with hsh hvals
  subst hsh; subst hvals
  simp only [TritonValue.WF1]
  simp [List.length_map, List.length_range]

theorem splat_produces_WF1_rank1 (n : Nat) (args : List String) (s : MachineState)
    (sh : List Nat) (vals : List Int)
    (h : evalOp (.splat [n]) args s = some (tensor sh vals)) :
    (tensor sh vals).WF1 := by
  simp only [evalOp] at h
  split at h
  · split at h
    · injection h with h
      injection h with hsh hvals
      subst hsh; subst hvals
      simp only [TritonValue.WF1]
      simp [List.length_replicate, List.foldl]
    · exact absurd h (by simp)
    · simp at h
  · simp at h

-- ── per-op faithfulness lemmas (standalone, for the driver dispatcher) ────────
-- Each proves one op faithful given StatesFaithful. Elementwise ones take WF1
-- operand hypotheses (discharged from produces-WF1 lemmas). Load goes through
-- the driver's load_faithful_mem separately.


private theorem zipWith_add_getD' (a b : List Int) (i : Nat)
   (ha : i < a.length) (hb : i < b.length) :
   ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 =
   a.getD i 0 + b.getD i 0 := by
 have hzip : i < (a.zip b).length := by simp [List.length_zip]; omega
 have hmap : i < ((a.zip b).map (fun p : Int × Int => p.fst + p.snd)).length := by simp [List.length_zip]; omega
 rw [show ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 =
     ((a.zip b).map (fun p => p.fst + p.snd))[i] from by
   simp [List.getD, List.getElem?_eq_getElem hmap]]
 rw [show a.getD i 0 = a[i] from by simp [List.getD, List.getElem?_eq_getElem ha]]
 rw [show b.getD i 0 = b[i] from by simp [List.getD, List.getElem?_eq_getElem hb]]
 simp [List.getElem_map, List.getElem_zip]


-- filterMap that keeps all elements (all masks nonzero) collapses to zip
theorem filterMap_kept_eq_zip
   (addrs vals masks : List Int) (hlen_av : addrs.length = vals.length)
   (hlen_am : addrs.length = masks.length)
   (hall : ∀ i, i < masks.length → masks.getD i 0 ≠ 0) :
   ((addrs.zip vals).zip masks).filterMap (fun (p : (Int × Int) × Int) =>
     if p.2 != 0 then some p.1 else none) = addrs.zip vals := by
 induction addrs generalizing vals masks with
 | nil => simp
 | cons a as ih =>
     cases vals with
     | nil => simp at hlen_av
     | cons v vs =>
         cases masks with
         | nil => simp at hlen_am
         | cons mk mks =>
             simp only [List.zip_cons_cons, List.filterMap_cons]
             have hne : mk ≠ 0 := by
               have := hall 0 (by simp); simpa using this
             have hbne : (mk != 0) = true := by
               simp only [bne_iff_ne, ne_eq]; exact hne
             simp only [hbne, ↓reduceIte]
             simp only [List.length_cons] at hlen_av hlen_am
             congr 1
             exact ih vs mks (by omega) (by omega) (fun i hi => by
               have := hall (i + 1) (by simp; omega)
               simpa using this)


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 3: Memory faithfulness lemmas
-- ══════════════════════════════════════════════════════════════════════════════


-- env is unaffected by writeTile
private theorem writeTile_env
   (s : MachineState) (addrs : List Nat) (vals : List Int) (var : String) :
   (s.writeTile addrs vals).env var = s.env var := by
 simp only [MachineState.writeTile]
 induction addrs.zip vals generalizing s with
 | nil => simp
 | cons hd tl ih =>
     simp only [List.foldl]
     exact ih (s.writeMem hd.fst hd.snd)


-- env is unaffected by symbolic foldl writeMem
private theorem symFoldl_writeMem_env
   (n : Nat) (gAddr : Nat → Nat) (gVal : Nat → Expr) (ss : SymState) (var : String) :
   (List.foldl (fun st i => st.writeMem (gAddr i) (gVal i)) ss (List.range n)).env var
   = ss.env var := by
 induction List.range n generalizing ss with
 | nil => simp
 | cons hd tl ih =>
     simp only [List.foldl]
     exact ih (ss.writeMem (gAddr hd) (gVal hd))


-- Symbolic foldl writeMem leaves an unwritten address unchanged
theorem sym_foldl_writeMem_not_mem
   (n : Nat) (gAddrs gVals : Nat → Expr) (ss : SymState) (addr : Nat)
   (h : ∀ i, i < n → (evalExpr (gAddrs i) (fun _ => 0)).natAbs ≠ addr) :
   (List.foldl (fun st i =>
       st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
     ss (List.range n)).memory addr = ss.memory addr := by
 suffices ∀ (idxs : List Nat) (st : SymState),
     (∀ i, i ∈ idxs → (evalExpr (gAddrs i) (fun _ => 0)).natAbs ≠ addr) →
     (List.foldl (fun st i =>
         st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
       st idxs).memory addr = st.memory addr by
   exact this (List.range n) ss (fun i hi => h i (List.mem_range.mp hi))
 intro idxs
 induction idxs with
 | nil => simp
 | cons idx rest ih =>
     intro st hne
     simp only [List.foldl_cons]
     rw [ih _ (fun i hi => hne i (List.mem_cons_of_mem _ hi))]
     simp only [SymState.writeMem]
     have hne_idx := hne idx (List.Mem.head _)
     simp [show (addr == (evalExpr (gAddrs idx) (fun _ => 0)).natAbs) = false from by
       simp [BEq.beq, Nat.beq_eq, hne_idx.symm]]


-- Core induction: symbolic and concrete foldl writeMem stay in sync
-- when addresses are concrete (memory-independent)
private theorem fold_mem_faithful_aux
   (idxs : List Nat)
   (gAddrs gVals : Nat → Expr) (cAddrs cVals : Nat → Int) (mem : Nat → Int)
   (hconcrete : ∀ i, i ∈ idxs → (gAddrs i).isConcrete = true)
   (haddr : ∀ i, i ∈ idxs → evalExpr (gAddrs i) mem = cAddrs i)
   (hval  : ∀ i, i ∈ idxs → evalExpr (gVals i) mem = cVals i)
   (s : MachineState) (ss : SymState)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) :
   ∀ addr, evalExpr
     ((List.foldl (fun st i =>
         st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
       ss idxs).memory addr) mem
     = (List.foldl (fun st i =>
         st.writeMem (cAddrs i).natAbs (cVals i))
       s idxs).memory addr := by
 induction idxs generalizing s ss with
 | nil => simpa
 | cons idx rest ih =>
     simp only [List.foldl_cons]
     have hconc     := hconcrete idx (List.Mem.head _)
     have haddr_idx := haddr idx (List.Mem.head _)
     have hval_idx  := hval  idx (List.Mem.head _)
     have haddr_zero : evalExpr (gAddrs idx) (fun _ => 0) = cAddrs idx := by
       rw [← haddr_idx]
       exact evalExpr_concrete (gAddrs idx) (fun _ => 0) mem hconc
     rw [haddr_zero]
     apply ih
     · intro i hi; exact hconcrete i (List.mem_cons_of_mem _ hi)
     · intro i hi; exact haddr     i (List.mem_cons_of_mem _ hi)
     · intro i hi; exact hval      i (List.mem_cons_of_mem _ hi)
     intro a
     simp only [SymState.writeMem, MachineState.writeMem]
     by_cases heq : a == (cAddrs idx).natAbs
     · simp [heq, hval_idx]
     · simp [heq, hmem a]


-- Masked (conditional) analog of fold_mem_faithful_aux: both sides write only where mask != 0.
-- Requires mask expressions concrete (so zero-mem eval = mem eval = concrete mask value).
theorem masked_fold_mem_faithful_aux
   (idxs : List Nat)
   (gAddrs gVals gMask : Nat → Expr) (cAddrs cVals cMask : Nat → Int) (mem : Nat → Int)
   (hAconc : ∀ i, i ∈ idxs → (gAddrs i).isConcrete = true)
   (hMconc : ∀ i, i ∈ idxs → (gMask i).isConcrete = true)
   (haddr : ∀ i, i ∈ idxs → evalExpr (gAddrs i) mem = cAddrs i)
   (hval  : ∀ i, i ∈ idxs → evalExpr (gVals i) mem = cVals i)
   (hmask : ∀ i, i ∈ idxs → evalExpr (gMask i) mem = cMask i)
   (s : MachineState) (ss : SymState)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) :
   ∀ addr, evalExpr
     ((List.foldl (fun st i =>
         if evalExpr (gMask i) (fun _ => 0) != 0 then
           st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i) else st)
       ss idxs).memory addr) mem
     = (List.foldl (fun st i =>
         if cMask i != 0 then st.writeMem (cAddrs i).natAbs (cVals i) else st)
       s idxs).memory addr := by
  induction idxs generalizing s ss with
  | nil => simpa
  | cons idx rest ih =>
    simp only [List.foldl_cons]
    have hAc := hAconc idx (List.Mem.head _)
    have hMc := hMconc idx (List.Mem.head _)
    have haddr_idx := haddr idx (List.Mem.head _)
    have hval_idx  := hval  idx (List.Mem.head _)
    have hmask_idx := hmask idx (List.Mem.head _)
    have haddr_zero : evalExpr (gAddrs idx) (fun _ => 0) = cAddrs idx := by
      rw [← haddr_idx]; exact evalExpr_concrete (gAddrs idx) (fun _ => 0) mem hAc
    have hmask_zero : evalExpr (gMask idx) (fun _ => 0) = cMask idx := by
      rw [← hmask_idx]; exact evalExpr_concrete (gMask idx) (fun _ => 0) mem hMc
    rw [haddr_zero, hmask_zero]
    by_cases hmk : cMask idx != 0
    · simp only [hmk, ↓reduceIte]
      apply ih
      · intro i hi; exact hAconc i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact hMconc i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact haddr  i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact hval   i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact hmask  i (List.mem_cons_of_mem _ hi)
      intro a
      simp only [SymState.writeMem, MachineState.writeMem]
      by_cases heq : a == (cAddrs idx).natAbs
      · simp [heq, hval_idx]
      · simp [heq, hmem a]
    · simp only [hmk, Bool.false_eq_true, ↓reduceIte]
      apply ih
      · intro i hi; exact hAconc i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact hMconc i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact haddr  i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact hval   i (List.mem_cons_of_mem _ hi)
      · intro i hi; exact hmask  i (List.mem_cons_of_mem _ hi)
      exact hmem

-- Public version ranging over List.range n
theorem range_fold_mem_faithful
   (n : Nat) (gAddrs gVals : Nat → Expr) (cAddrs cVals : Nat → Int) (mem : Nat → Int)
   (hconcrete : ∀ i, i < n → (gAddrs i).isConcrete = true)
   (haddr : ∀ i, i < n → evalExpr (gAddrs i) mem = cAddrs i)
   (hval  : ∀ i, i < n → evalExpr (gVals i) mem = cVals i) :
   ∀ (s : MachineState) (ss : SymState),
     (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) →
     ∀ addr, evalExpr
       ((List.foldl (fun st i =>
           st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
         ss (List.range n)).memory addr) mem
       = (List.foldl (fun st i =>
           st.writeMem (cAddrs i).natAbs (cVals i))
         s (List.range n)).memory addr := by
 intro s ss hmem addr
 apply fold_mem_faithful_aux (List.range n) gAddrs gVals cAddrs cVals mem
 · intro i hi; exact hconcrete i (List.mem_range.mp hi)
 · intro i hi; exact haddr     i (List.mem_range.mp hi)
 · intro i hi; exact hval      i (List.mem_range.mp hi)
 · exact hmem


theorem masked_range_fold_mem_faithful
   (n : Nat) (gAddrs gVals gMask : Nat → Expr) (cAddrs cVals cMask : Nat → Int) (mem : Nat → Int)
   (hAconc : ∀ i, i < n → (gAddrs i).isConcrete = true)
   (hMconc : ∀ i, i < n → (gMask i).isConcrete = true)
   (haddr : ∀ i, i < n → evalExpr (gAddrs i) mem = cAddrs i)
   (hval  : ∀ i, i < n → evalExpr (gVals i) mem = cVals i)
   (hmask : ∀ i, i < n → evalExpr (gMask i) mem = cMask i) :
   ∀ (s : MachineState) (ss : SymState),
     (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) →
     ∀ addr, evalExpr
       ((List.foldl (fun st i =>
           if evalExpr (gMask i) (fun _ => 0) != 0 then
             st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i) else st)
         ss (List.range n)).memory addr) mem
       = (List.foldl (fun st i =>
           if cMask i != 0 then st.writeMem (cAddrs i).natAbs (cVals i) else st)
         s (List.range n)).memory addr := by
  intro s ss hmem addr
  apply masked_fold_mem_faithful_aux (List.range n) gAddrs gVals gMask cAddrs cVals cMask mem
  · intro i hi; exact hAconc i (List.mem_range.mp hi)
  · intro i hi; exact hMconc i (List.mem_range.mp hi)
  · intro i hi; exact haddr  i (List.mem_range.mp hi)
  · intro i hi; exact hval   i (List.mem_range.mp hi)
  · intro i hi; exact hmask  i (List.mem_range.mp hi)
  · exact hmem

-- ── Store bridging + projection helpers ──────────────────────────────────────

theorem zip_foldl_eq_range (s : MachineState) (addrs vals : List Int)
    (hlen : addrs.length = vals.length) :
    List.foldl (fun st (x : Nat × Int) => st.writeMem x.1 x.2) s
      ((addrs.map Int.natAbs).zip vals) =
    List.foldl (fun st i => st.writeMem (addrs.getD i 0).natAbs (vals.getD i 0))
      s (List.range addrs.length) := by
  induction addrs generalizing s vals with
  | nil => simp
  | cons a as ih =>
      cases vals with
      | nil => simp at hlen
      | cons val vs =>
          simp only [List.length_cons, List.map_cons, List.zip_cons_cons,
                     List.foldl_cons, List.getD_cons_zero, List.range_succ_eq_map,
                     List.foldl_map, List.getD_cons_succ]
          rw [ih (s.writeMem a.natAbs val) vs (by simpa using hlen)]

theorem con_foldl_pid (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).pid = s.pid := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem con_foldl_bs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).block_size = s.block_size := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem con_foldl_gs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).grid_size = s.grid_size := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem con_foldl_env (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) (var : String) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).env var = s.env var := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_pid (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).pid = ss.pid := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_bs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).block_size = ss.block_size := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_gs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).grid_size = ss.grid_size := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_env (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) (var : String) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).env var = ss.env var := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 4: StatesFaithful binding lemmas
-- ══════════════════════════════════════════════════════════════════════════════


private theorem bind_scalar_faithful
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (r : String) (cval : Int) (sval : Expr) (he : evalExpr sval mem = cval) :
   StatesFaithful (s.bind r (scalar cval)) (ss.bind r (SymValue.scalar sval)) mem := by
 refine ⟨hp, hbs, hgs, hmem, ?_, ?_, ?_⟩
 · intro v val hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv
     have hval : cval = val := by
       have := Option.some.inj hv
       exact congrArg (fun x => match x with | scalar v => v | _ => 0) this
     exact ⟨sval, by simp [heq], hval ▸ he⟩
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hsc v val hv
 · intro v sh vals hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv; simp at hv
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hten v sh vals hv
 · intro v hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv; simp at hv
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hnone v hv


private theorem bind_tensor_faithful
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (r : String) (sh : List Nat) (cvals : List Int) (g : Nat → Expr)
   (hg : ∀ i, i < cvals.length → evalExpr (g i) mem = cvals.getD i 0) :
   StatesFaithful (s.bind r (tensor sh cvals))
                  (ss.bind r (SymValue.tensor sh g)) mem := by
 refine ⟨hp, hbs, hgs, hmem, ?_, ?_, ?_⟩
 · intro v val hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv; simp at hv
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hsc v val hv
 · intro v sh' vals' hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv
     obtain ⟨rfl, rfl⟩ : sh = sh' ∧ cvals = vals' := by
       have := Option.some.inj hv; cases this; simp
     exact ⟨g, by simp [heq], hg⟩
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hten v sh' vals' hv
 · intro v hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv; simp at hv
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hnone v hv


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 5: Per-opcode faithfulness helpers
--
-- load/store/cmpi_slt require side conditions that can't be established
-- generically in evalInstr_faithful (e.g. s.memory = mem, concrete addresses,
-- all masks nonzero). These helpers take those conditions as hypotheses and
-- are called directly from per-kernel step theorems.
-- ══════════════════════════════════════════════════════════════════════════════

theorem constant_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (v : Int) (h_op : instr.op = .constant v) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op]
  exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
    instr.result v (Expr.lit v) (by simp [evalExpr])

theorem get_program_id_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (h_op : instr.op = .get_program_id 0) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op]
  simp only [(by decide : (0 == 0) = true), ↓reduceIte]
  exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
    (by simp [evalExpr, hp])

theorem make_range_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (sizeOpt : Option Nat) (h_op : instr.op = .make_range sizeOpt) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op]
  rw [← hbs]
  have hlen : (List.map Int.ofNat (List.range (sizeOpt.getD s.block_size))).length
              = sizeOpt.getD s.block_size := by simp
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  rw [hlen] at hi
  simp only [evalExpr]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [List.getElem?_range, hi]

theorem dot_boundsA (m k1 i kk : Nat) (hi : i < m) (hkk : kk < k1) :
    i * k1 + kk < m * k1 := by
  calc i * k1 + kk < i * k1 + k1 := by omega
    _ = (i + 1) * k1 := by rw [Nat.succ_mul]
    _ ≤ m * k1 := Nat.mul_le_mul_right k1 hi

theorem dot_boundsB (k1 n kk j : Nat) (hkk : kk < k1) (hj : j < n) :
    kk * n + j < k1 * n := by
  calc kk * n + j < kk * n + n := by omega
    _ = (kk + 1) * n := by rw [Nat.succ_mul]
    _ ≤ k1 * n := Nat.mul_le_mul_right n hkk

theorem foldl_range_congr {α : Type} (K : Nat) (f g : α → Nat → α) (init : α)
    (hfg : ∀ acc k, k < K → f acc k = g acc k) :
    (List.range K).foldl f init = (List.range K).foldl g init := by
  have : ∀ (l : List Nat) (acc : α), (∀ k ∈ l, k < K) → l.foldl f acc = l.foldl g acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons x xs ih =>
      intro acc hmem
      simp only [List.foldl_cons]
      rw [hfg acc x (hmem x (by simp)), ih (g acc x) (fun k hk => hmem k (by simp [hk]))]
  exact this (List.range K) init (fun k hk => List.mem_range.mp hk)

theorem evalExpr_reduceSum_map_mul (mem : Nat → Int) (K : Nat)
    (fa fb : Nat → Expr) (ca cb : Nat → Int)
    (ha : ∀ k, k < K → evalExpr (fa k) mem = ca k)
    (hb : ∀ k, k < K → evalExpr (fb k) mem = cb k) :
    evalExpr (Expr.reduceSum ((List.range K).map (fun k => Expr.mul (fa k) (fb k)))) mem
    = (List.range K).foldl (fun acc k => acc + ca k * cb k) 0 := by
  simp only [evalExpr, List.foldl_map]
  apply foldl_range_congr K
  intro acc k hk
  simp only [evalExpr, ha k hk, hb k hk]

theorem broadcast_bounds (s0 s1 t0 t1 idx : Nat)
    (hs0pos : 0 < s0) (hs1pos : 0 < s1)
    (hidx : idx < t0 * t1) (ht0 : t0 = s0 ∨ s0 = 1) (ht1 : t1 = s1 ∨ s1 = 1) :
    (if s0 == 1 then 0 else idx / t1) * s1 + (if s1 == 1 then 0 else idx % t1) < s0 * s1 := by
  have ht1pos : 0 < t1 := by
    rcases Nat.eq_zero_or_pos t1 with h | h
    · rw [h, Nat.mul_zero] at hidx; exact absurd hidx (Nat.not_lt_zero _)
    · exact h
  have hj : (if s1 == 1 then 0 else idx % t1) < s1 := by
    by_cases h : s1 = 1
    · simp [h, hs1pos]
    · simp only [h, beq_iff_eq, if_neg]
      rcases ht1 with h1 | h1
      · subst h1; exact Nat.mod_lt _ hs1pos
      · exact absurd h1 h
  have hi : (if s0 == 1 then 0 else idx / t1) < s0 := by
    by_cases h : s0 = 1
    · simp [h, hs0pos]
    · simp only [h, beq_iff_eq, if_neg]
      have ht0' : t0 = s0 := by rcases ht0 with h0 | h0; exact h0; exact absurd h0 h
      subst ht0'
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hidx)
  calc (if s0 == 1 then 0 else idx / t1) * s1 + (if s1 == 1 then 0 else idx % t1)
      < (if s0 == 1 then 0 else idx / t1) * s1 + s1 := Nat.add_lt_add_left hj _
    _ = ((if s0 == 1 then 0 else idx / t1) + 1) * s1 := by rw [Nat.succ_mul]
    _ ≤ s0 * s1 := Nat.mul_le_mul_right s1 hi

theorem broadcast_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (s0 s1 t0 t1 : Nat) (v : String)
    (h_op : instr.op = .broadcast [t0, t1]) (h_args : instr.args = [v])
    (vals : List Int)
    (h_lv : s.env v = some (tensor [s0, s1] vals))
    (hwfn : (tensor [s0, s1] vals).WFn)
    (hs0 : 0 < s0) (hs1 : 0 < s1)
    (ht0 : t0 = s0 ∨ s0 = 1) (ht1 : t1 = s1 ∨ s1 = 1) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  obtain ⟨g, hsg, hcorr⟩ := hten v [s0, s1] vals h_lv
  have hlen : shapeProd [s0, s1] = vals.length := WFn_tensor_len [s0, s1] vals hwfn
  simp only [shapeProd, List.foldl, Nat.one_mul] at hlen
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, SymState.lookup, h_lv, hsg, symBroadcast]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  have hbound : (if s0 == 1 then 0 else i / t1) * s1 + (if s1 == 1 then 0 else i % t1) < vals.length := by
    rw [← hlen]; exact broadcast_bounds s0 s1 t0 t1 i hs0 hs1 hi ht0 ht1
  exact hcorr _ hbound

-- ── Loop-invariant skeleton: the mathematical core of scf.for faithfulness ──────
-- If each body iteration preserves the faithfulness relation R on the carried (concrete, symbolic)
-- state, the whole loop preserves R — for ARBITRARY trip count. Proved by induction on iterations.
-- This is parser/AST-independent; wiring the real loop body's per-op faithfulness into `hstep`
-- instantiates it for matmul's accumulation loop.
theorem loop_faithful_skeleton {C S : Type}
    (R : C → S → Prop)
    (cbody : Nat → C → C) (sbody : Nat → S → S)
    (trip : Nat)
    (hstep : ∀ k, k < trip → ∀ c sc, R c sc → R (cbody k c) (sbody k sc))
    (c0 : C) (s0 : S) (hinit : R c0 s0) :
    R ((List.range trip).foldl (fun c k => cbody k c) c0)
      ((List.range trip).foldl (fun sc k => sbody k sc) s0) := by
  have gen : ∀ (l : List Nat) (c : C) (sc : S),
      (∀ k ∈ l, k < trip) → R c sc →
      R (l.foldl (fun c k => cbody k c) c) (l.foldl (fun sc k => sbody k sc) sc) := by
    intro l
    induction l with
    | nil => intro c sc _ hR; exact hR
    | cons x xs ih =>
      intro c sc hmem hR
      simp only [List.foldl_cons]
      exact ih (cbody x c) (sbody x sc) (fun k hk => hmem k (by simp [hk]))
        (hstep x (hmem x (by simp)) c sc hR)
  exact gen (List.range trip) c0 s0 (fun k hk => List.mem_range.mp hk) hinit

-- An INDEXED loop invariant: R t holds after t iterations. Needed for the matmul value
-- invariant (accumulator after t tiles = AccPartial ... t), which loop_faithful_skeleton's
-- fixed relation cannot express. foldl over List.range visits 0,1,…,trip-1 in order, so
-- exactly k iterations have completed when the step with value k runs.
theorem loop_indexed_skeleton {C S : Type}
    (R : Nat → C → S → Prop)
    (cbody : Nat → C → C) (sbody : Nat → S → S)
    (trip : Nat)
    (hstep : ∀ k, k < trip → ∀ c sc, R k c sc → R (k + 1) (cbody k c) (sbody k sc))
    (c0 : C) (s0 : S) (hinit : R 0 c0 s0) :
    R trip ((List.range trip).foldl (fun c k => cbody k c) c0)
           ((List.range trip).foldl (fun sc k => sbody k sc) s0) := by
  have gen : ∀ n, n ≤ trip →
      R n ((List.range n).foldl (fun c k => cbody k c) c0)
          ((List.range n).foldl (fun sc k => sbody k sc) s0) := by
    intro n
    induction n with
    | zero => intro _; simpa using hinit
    | succ m ih =>
        intro hm
        have hRm := ih (Nat.le_of_succ_le hm)
        rw [List.range_succ, List.foldl_append, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        exact hstep m (Nat.lt_of_succ_le hm) _ _ hRm
  exact gen trip (Nat.le_refl trip)

-- ── for-loop faithfulness: wire the loop evaluators to the invariant skeleton ────
theorem forLoop_faithful (loop : ForLoop) {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hinit : StatesFaithful s ss mem)
    (hbody : ∀ k, k < loop.trip → ∀ c sc, StatesFaithful c sc mem →
      StatesFaithful
        (evalKernel loop.body (c.bind loop.ivName (TritonValue.scalar (Int.ofNat k))))
        (symEvalKernel loop.body (sc.bind loop.ivName (SymValue.scalar (Expr.lit (Int.ofNat k))))) mem) :
    StatesFaithful (evalForLoop loop s) (symEvalForLoop loop ss) mem := by
  unfold evalForLoop symEvalForLoop
  exact loop_faithful_skeleton (fun c sc => StatesFaithful c sc mem)
    (fun k st => evalKernel loop.body (st.bind loop.ivName (TritonValue.scalar (Int.ofNat k))))
    (fun k st => symEvalKernel loop.body (st.bind loop.ivName (SymValue.scalar (Expr.lit (Int.ofNat k)))))
    loop.trip hbody s ss hinit


theorem dot_faithful_acc
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (m k1 n : Nat) (a b acc : String)
    (h_op : instr.op = .dot) (h_args : instr.args = [a, b, acc])
    (valsA valsB valsAcc : List Int)
    (h_la : s.env a = some (tensor [m, k1] valsA))
    (h_lb : s.env b = some (tensor [k1, n] valsB))
    (h_lacc : s.env acc = some (tensor [m, n] valsAcc))
    (hwfA : (tensor [m, k1] valsA).WFn)
    (hwfB : (tensor [k1, n] valsB).WFn)
    (hwfAcc : (tensor [m, n] valsAcc).WFn)
    (hnpos : 0 < n) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  obtain ⟨gA, hsgA, hcorrA⟩ := hten a [m, k1] valsA h_la
  obtain ⟨gB, hsgB, hcorrB⟩ := hten b [k1, n] valsB h_lb
  obtain ⟨gAcc, hsgAcc, hcorrAcc⟩ := hten acc [m, n] valsAcc h_lacc
  have hlenA : m * k1 = valsA.length := by
    have := WFn_tensor_len [m, k1] valsA hwfA; simpa [shapeProd, List.foldl, Nat.one_mul] using this
  have hlenB : k1 * n = valsB.length := by
    have := WFn_tensor_len [k1, n] valsB hwfB; simpa [shapeProd, List.foldl, Nat.one_mul] using this
  have hlenAcc : m * n = valsAcc.length := by
    have := WFn_tensor_len [m, n] valsAcc hwfAcc; simpa [shapeProd, List.foldl, Nat.one_mul] using this
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, SymState.lookup, h_la, h_lb, h_lacc, hsgA, hsgB, hsgAcc,
    bne_self_eq_false, Bool.false_eq_true, if_false, Option.bind_some, Option.map_some, Option.getD_some]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro idx hidx
  simp only [List.length_map, List.length_range] at hidx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]
  simp only [Option.map_some, Option.getD_some]
  have hi : idx / n < m := by rw [Nat.div_lt_iff_lt_mul hnpos]; omega
  have hj : idx % n < n := Nat.mod_lt _ hnpos
  show evalExpr ((Expr.reduceSum _).add (gAcc idx)) mem = _
  simp only [evalExpr]
  have hsum := evalExpr_reduceSum_map_mul mem k1
      (fun kk => gA (idx / n * k1 + kk)) (fun kk => gB (kk * n + idx % n))
      (fun kk => valsA.getD (idx / n * k1 + kk) 0) (fun kk => valsB.getD (kk * n + idx % n) 0)
      (fun kk hkk => hcorrA _ (by rw [← hlenA]; exact dot_boundsA m k1 (idx/n) kk hi hkk))
      (fun kk hkk => hcorrB _ (by rw [← hlenB]; exact dot_boundsB k1 n kk (idx%n) hkk hj))
  have hacc : evalExpr (gAcc idx) mem = valsAcc.getD idx 0 :=
    hcorrAcc idx (by rw [← hlenAcc]; exact hidx)
  simp only [evalExpr] at hsum
  rw [hsum, hacc]

theorem dot_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (m k1 n : Nat) (a b : String)
    (h_op : instr.op = .dot) (h_args : instr.args = [a, b])
    (valsA valsB : List Int)
    (h_la : s.env a = some (tensor [m, k1] valsA))
    (h_lb : s.env b = some (tensor [k1, n] valsB))
    (hwfA : (tensor [m, k1] valsA).WFn)
    (hwfB : (tensor [k1, n] valsB).WFn)
    (hnpos : 0 < n) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  obtain ⟨gA, hsgA, hcorrA⟩ := hten a [m, k1] valsA h_la
  obtain ⟨gB, hsgB, hcorrB⟩ := hten b [k1, n] valsB h_lb
  have hlenA : m * k1 = valsA.length := by
    have := WFn_tensor_len [m, k1] valsA hwfA; simpa [shapeProd, List.foldl, Nat.one_mul] using this
  have hlenB : k1 * n = valsB.length := by
    have := WFn_tensor_len [k1, n] valsB hwfB; simpa [shapeProd, List.foldl, Nat.one_mul] using this
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, SymState.lookup, h_la, h_lb, hsgA, hsgB, bne_self_eq_false,
    Bool.false_eq_true, if_false, Option.bind_some, Option.map_none, Option.getD_none, Int.add_zero]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro idx hidx
  simp only [List.length_map, List.length_range] at hidx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]
  simp only [Option.map_some, Option.getD_some]
  have hi : idx / n < m := by
    rw [Nat.div_lt_iff_lt_mul hnpos]; omega
  have hj : idx % n < n := Nat.mod_lt _ hnpos
  exact evalExpr_reduceSum_map_mul mem k1
    (fun kk => gA (idx / n * k1 + kk)) (fun kk => gB (kk * n + idx % n))
    (fun kk => valsA.getD (idx / n * k1 + kk) 0) (fun kk => valsB.getD (kk * n + idx % n) 0)
    (fun kk hkk => hcorrA _ (by rw [← hlenA]; exact dot_boundsA m k1 (idx/n) kk hi hkk))
    (fun kk hkk => hcorrB _ (by rw [← hlenB]; exact dot_boundsB k1 n kk (idx%n) hkk hj))

theorem expand_dims_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem)
    (instr : TritonInstr) (axis : Nat) (v : String)
    (h_op : instr.op = .expand_dims axis) (h_args : instr.args = [v])
    (sh : List Nat) (vals : List Int)
    (h_lv : s.env v = some (tensor sh vals)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  obtain ⟨g, hsg, hcorr⟩ := hten v sh vals h_lv
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, SymState.lookup, h_lv, hsg, symExpandDims, Option.bind_some]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  exact hcorr

theorem splat_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (shape : List Nat) (v : String)
    (h_op : instr.op = .splat shape) (h_args : instr.args = [v])
    (x : Int) (h_lv : s.env v = some (scalar x)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨e, hse, heval⟩ := hsc v x h_lv
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_lv, Option.bind_some, SymState.lookup, hse]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_replicate] at hi
  simp only [evalExpr, heval]
  simp [List.getElem?_replicate, hi]

theorem addi_tt_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (hwa : (tensor sha xs).WFn) (hwb : (tensor shb ys).WFn) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ga, hsga, hega⟩ := hten a sha xs h_la
  obtain ⟨gb, hsgb, hegb⟩ := hten b shb ys h_lb
  simp only [TritonValue.WFn] at hwa hwb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsga, hsgb, symAdd]
  by_cases hshape : (sha == shb) = true
  · simp only [hshape, if_true, Option.bind_some]
    have hsheq : sha = shb := by simpa using hshape
    have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
    have hlen2 : xs.length = ((xs.zip ys).map (fun p => p.fst + p.snd)).length := by
      simp [List.length_zip, hlen]
    apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
    intro i hi
    rw [← hlen2] at hi
    simp only [evalExpr]
    rw [hega i hi, hegb i (hlen ▸ hi), zip_add_getD xs ys i hi hlen]
  · have hshape' : (sha == shb) = false := by simpa using hshape
    simp only [hshape', if_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩

theorem cmpi_slt_tt_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size) (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_slt) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (hwa : (tensor sha xs).WFn) (hwb : (tensor shb ys).WFn) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ga, hsga, hega⟩ := hten a sha xs h_la
  obtain ⟨gb, hsgb, hegb⟩ := hten b shb ys h_lb
  simp only [TritonValue.WFn] at hwa hwb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsga, hsgb]
  by_cases hshape : (sha == shb) = true
  · simp only [hshape, if_true, Option.bind_some]
    have hsheq : sha = shb := by simpa using hshape
    have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
    have hlen2 : xs.length =
        ((xs.zip ys).map (fun p => if p.fst < p.snd then (1:Int) else 0)).length := by
      simp [List.length_zip, hlen]
    apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
    intro i hi
    rw [← hlen2] at hi
    simp only [evalExpr]
    rw [hega i hi, hegb i (hlen ▸ hi), zip_lt_getD xs ys i hi hlen]
  · have hshape' : (sha == shb) = false := by simpa using hshape
    simp only [hshape', if_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩

theorem cmpi_slt_ss_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size) (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_slt) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsea, hex⟩ := hsc a x h_la
  obtain ⟨ey, hseb, hey⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsea, hseb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hp
  · simpa using hbs
  · simpa using hgs
  · intro addr; simpa using hmem addr
  · intro v val hv
    simp only [MachineState.bind] at hv
    by_cases hvr : (v == instr.result) = true
    · rw [if_pos hvr] at hv
      injection hv with hv
      refine ⟨Expr.lt ex ey, ?_, ?_⟩
      · simp only [SymState.bind]; rw [if_pos hvr]
      · simp only [evalExpr]; rw [hex, hey]; injection hv with hv
    · rw [if_neg hvr] at hv
      obtain ⟨e, he1, he2⟩ := hsc v val hv
      exact ⟨e, by simp only [SymState.bind]; rw [if_neg hvr]; exact he1, he2⟩
  · intro v sh vals hv
    simp only [MachineState.bind] at hv
    by_cases hvr : (v == instr.result) = true
    · rw [if_pos hvr] at hv; exact absurd hv (by simp)
    · rw [if_neg hvr] at hv
      obtain ⟨g, hg1, hg2⟩ := hten v sh vals hv
      exact ⟨g, by simp only [SymState.bind]; rw [if_neg hvr]; exact hg1, hg2⟩
  · intro v hv
    simp only [MachineState.bind] at hv
    by_cases hvr : (v == instr.result) = true
    · rw [if_pos hvr] at hv; exact absurd hv (by simp)
    · rw [if_neg hvr] at hv
      simp only [SymState.bind]; rw [if_neg hvr]; exact hnone v hv


theorem addf_tt_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (hwa : (tensor sha xs).WFn) (hwb : (tensor shb ys).WFn) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ga, hsga, hega⟩ := hten a sha xs h_la
  obtain ⟨gb, hsgb, hegb⟩ := hten b shb ys h_lb
  simp only [TritonValue.WFn] at hwa hwb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsga, hsgb, symAdd]
  by_cases hshape : (sha == shb) = true
  · simp only [hshape, if_true, Option.bind_some]
    have hsheq : sha = shb := by simpa using hshape
    have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
    have hlen2 : xs.length = ((xs.zip ys).map (fun p => p.fst + p.snd)).length := by
      simp [List.length_zip, hlen]
    apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
    intro i hi
    rw [← hlen2] at hi
    simp only [evalExpr]
    rw [hega i hi, hegb i (hlen ▸ hi), zip_add_getD xs ys i hi hlen]
  · have hshape' : (sha == shb) = false := by simpa using hshape
    simp only [hshape', if_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩


-- load [ptr]: s.memory = mem
theorem load_tensor_faithful_when_memory_unchanged
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone    : ∀ v, s.env v = none → ss.env v = none)
   (hmem_raw : s.memory = mem)
   (instr : TritonInstr) (p : String)
   (h_op : instr.op = .load) (h_args : instr.args = [p])
   (sh : List Nat) (addrs : List Int)
   (h_lp : s.lookup p = some (tensor sh addrs)) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  obtain ⟨gp, hsp, hgp⟩ := hten p sh addrs h_envp
  simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, h_args,
             MachineState.lookup, SymState.lookup, h_envp, hsp,
             List.head?, Option.getD]
  have hlen : (addrs.map fun a => s.readMem a.natAbs).length = addrs.length := by simp
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  rw [hlen] at hi
  simp only [evalExpr]
  rw [hgp i hi, ← hmem_raw]
  simp only [MachineState.readMem]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hi]

theorem zip_mask_load_fill_getD (addrs masks fills : List Int) (i : Nat) (rm : Int → Int)
    (hi : i < addrs.length) (hlm : addrs.length = masks.length) (hlf : addrs.length = fills.length) :
    (((addrs.zip masks).zip fills).map
        (fun x => if (x.fst.snd != 0) = true then rm x.fst.fst else x.snd)).getD i 0 =
    (if (masks.getD i 0 != 0) = true then rm (addrs.getD i 0) else fills.getD i 0) := by
  induction addrs generalizing masks fills i with
  | nil => simp at hi
  | cons a as ih =>
    cases masks with
    | nil => simp at hlm
    | cons mk ms =>
      cases fills with
      | nil => simp at hlf
      | cons fl fs =>
        cases i with
        | zero => simp [List.zip_cons_cons]
        | succ j =>
          simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
          exact ih ms fs j (by simpa using hi) (by simpa using hlm) (by simpa using hlf)

theorem load_tensor_masked_faithful
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size) (hgs : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (hmem_raw : s.memory = mem)
   (instr : TritonInstr) (p m : String)
   (h_op : instr.op = .load) (h_args : instr.args = [p, m])
   (sh shm : List Nat) (addrs masks : List Int)
   (h_lp : s.lookup p = some (tensor sh addrs))
   (h_lm : s.lookup m = some (tensor shm masks))
   (hlen : addrs.length = masks.length) (hsheq : sh = shm) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  have h_envm : s.env m = some (tensor shm masks) := h_lm
  obtain ⟨gp, hsp, hgp⟩ := hten p sh addrs h_envp
  obtain ⟨gm, hsm, hgm⟩ := hten m shm masks h_envm
  have hlenb : ([addrs.length] == [masks.length]) = true := by simp [hlen]
  have hmaplen : (List.map (fun x => if (x.snd != 0) = true then s.readMem x.fst.natAbs else 0)
      (addrs.zip masks)).length = addrs.length := by simp [List.length_zip, hlen]
  have hcguard : ((List.map (fun x => if (x.snd != 0) = true then s.readMem x.fst.natAbs else 0)
      (addrs.zip masks)).length == masks.length) = true := by
    simp [hmaplen, hlen]
  simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, h_args,
             MachineState.lookup, SymState.lookup, h_envp, h_envm, hsp, hsm,
             hlenb, hcguard, if_true]
  rw [if_pos (by simp [hsheq] : (sh == shm) = true)]
  simp only [hsheq, beq_self_eq_true, if_true]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  rw [hmaplen] at hi
  simp only [evalExpr]
  rw [hgm i (by rw [← hlen]; exact hi), hgp i hi]
  rw [zip_mask_load_getD addrs masks i (fun a => s.readMem a.natAbs) hi hlen]
  simp only [MachineState.readMem, ← hmem_raw]

theorem load_tensor_masked_fill_faithful
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size) (hgs : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (hmem_raw : s.memory = mem)
   (instr : TritonInstr) (p m f : String)
   (h_op : instr.op = .load) (h_args : instr.args = [p, m, f])
   (sh shm shf : List Nat) (addrs masks fills : List Int)
   (h_lp : s.lookup p = some (tensor sh addrs))
   (h_lm : s.lookup m = some (tensor shm masks))
   (h_lf : s.lookup f = some (tensor shf fills))
   (hlenm : addrs.length = masks.length) (hlenf : addrs.length = fills.length) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  have h_envm : s.env m = some (tensor shm masks) := h_lm
  have h_envf : s.env f = some (tensor shf fills) := h_lf
  obtain ⟨gp, hsp, hgp⟩ := hten p sh addrs h_envp
  obtain ⟨gm, hsm, hgm⟩ := hten m shm masks h_envm
  obtain ⟨gf, hsf, hgf⟩ := hten f shf fills h_envf
  simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, h_args,
             MachineState.lookup, SymState.lookup, h_envp, h_envm, h_envf, hsp, hsm, hsf,
             Option.bind_some]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map, List.length_zip] at hi
  have hi' : i < addrs.length :=
    Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _))
  simp only [evalExpr]
  rw [hgm i (by rw [← hlenm]; exact hi'), hgp i hi', hgf i (by rw [← hlenf]; exact hi')]
  rw [zip_mask_load_fill_getD addrs masks fills i (fun a => s.readMem a.natAbs) hi' hlenm hlenf]
  simp only [MachineState.readMem, ← hmem_raw]

theorem load_tensor_masked_faithful_when_all_true
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone    : ∀ v, s.env v = none → ss.env v = none)
   (hmem_raw : s.memory = mem)
   (instr : TritonInstr) (p m : String)
   (h_op  : instr.op   = .load) (h_args : instr.args = [p, m])
   (sh : List Nat) (addrs masks : List Int)
   (h_lp  : s.lookup p = some (tensor sh addrs))
   (h_lm  : s.lookup m = some (tensor sh masks))
   (hlen  : addrs.length = masks.length)
   (hall  : ∀ i, i < masks.length → masks.getD i 0 ≠ 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

-- ── Masked store: concrete filterMap-writeTile ≡ conditional range-fold ──────
-- The structural heart of masked store. Concrete filters (writes only mask-true addrs via
-- writeTile over the filtered list); this shows that equals a conditional fold over the full
-- range that skips masked-out indices. Pure concrete; the symbolic side is already this form.
theorem writeTile_cons (s : MachineState) (a : Nat) (v : Int) (as : List Nat) (vs : List Int) :
    s.writeTile (a :: as) (v :: vs) = (s.writeMem a v).writeTile as vs := by
  simp [MachineState.writeTile]

theorem cond_fold_succ (s : MachineState) (a v mk : Int) (as vs mks : List Int) :
    List.foldl (fun st i =>
      if (mk :: mks).getD i 0 != 0 then st.writeMem ((a::as).getD i 0).natAbs ((v::vs).getD i 0) else st)
      s (List.range (as.length + 1))
    =
    List.foldl (fun st i =>
      if mks.getD i 0 != 0 then st.writeMem (as.getD i 0).natAbs (vs.getD i 0) else st)
      (if mk != 0 then s.writeMem a.natAbs v else s) (List.range as.length) := by
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [List.getD_cons_zero, List.getD_cons_succ]

theorem masked_writeTile_eq_cond_fold (s : MachineState)
    (addrs vals masks : List Int)
    (hlen_av : addrs.length = vals.length) (hlen_am : addrs.length = masks.length) :
    s.writeTile
      ((((addrs.zip vals).zip masks).filterMap
        (fun p => if p.2 != 0 then some p.1 else none)).map (·.1.natAbs))
      ((((addrs.zip vals).zip masks).filterMap
        (fun p => if p.2 != 0 then some p.1 else none)).map (·.2))
    =
    List.foldl (fun st i =>
      if masks.getD i 0 != 0 then st.writeMem (addrs.getD i 0).natAbs (vals.getD i 0) else st)
      s (List.range addrs.length) := by
  induction addrs generalizing s vals masks with
  | nil => simp [MachineState.writeTile]
  | cons a as ih =>
    cases vals with
    | nil => simp at hlen_av
    | cons v vs =>
      cases masks with
      | nil => simp at hlen_am
      | cons mk mks =>
        simp only [List.length_cons] at hlen_av hlen_am
        rw [show (a::as).length = as.length + 1 from rfl, cond_fold_succ]
        simp only [List.zip_cons_cons, List.filterMap_cons]
        by_cases hmk : (mk != 0) = true
        · simp only [hmk, ↓reduceIte, List.map_cons]
          rw [writeTile_cons]
          exact ih (s.writeMem a.natAbs v) vs mks (by omega) (by omega)
        · simp only [hmk, Bool.false_eq_true, ↓reduceIte]
          exact ih s vs mks (by omega) (by omega)

-- ── Masked store: conditional-fold projection helpers (pid/bs/gs/env invariant) ──
theorem sym_cond_foldl_pid (n : Nat) (gM gA gV : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => if evalExpr (gM i) (fun _ => 0) != 0 then
       st.writeMem (evalExpr (gA i) (fun _ => 0)).natAbs (gV i) else st) ss (List.range n)).pid = ss.pid := by
  induction n generalizing ss with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : evalExpr (gM k) (fun _ => 0) != 0
    · simp only [h, ↓reduceIte, SymState.writeMem]; exact ih ss
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih ss

theorem sym_cond_foldl_block_size (n : Nat) (gM gA gV : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => if evalExpr (gM i) (fun _ => 0) != 0 then
       st.writeMem (evalExpr (gA i) (fun _ => 0)).natAbs (gV i) else st) ss (List.range n)).block_size = ss.block_size := by
  induction n generalizing ss with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : evalExpr (gM k) (fun _ => 0) != 0
    · simp only [h, ↓reduceIte, SymState.writeMem]; exact ih ss
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih ss

theorem sym_cond_foldl_grid_size (n : Nat) (gM gA gV : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => if evalExpr (gM i) (fun _ => 0) != 0 then
       st.writeMem (evalExpr (gA i) (fun _ => 0)).natAbs (gV i) else st) ss (List.range n)).grid_size = ss.grid_size := by
  induction n generalizing ss with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : evalExpr (gM k) (fun _ => 0) != 0
    · simp only [h, ↓reduceIte, SymState.writeMem]; exact ih ss
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih ss

theorem sym_cond_foldl_env (n : Nat) (gM gA gV : Nat → Expr) (ss : SymState) (var : String) :
    (List.foldl (fun st i => if evalExpr (gM i) (fun _ => 0) != 0 then
       st.writeMem (evalExpr (gA i) (fun _ => 0)).natAbs (gV i) else st) ss (List.range n)).env var = ss.env var := by
  induction n generalizing ss with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : evalExpr (gM k) (fun _ => 0) != 0
    · simp only [h, ↓reduceIte, SymState.writeMem]; exact ih ss
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih ss

theorem con_cond_foldl_pid (n : Nat) (cM cA cV : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => if cM i != 0 then
       st.writeMem (cA i).natAbs (cV i) else st) s (List.range n)).pid = s.pid := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : cM k != 0
    · simp only [h, ↓reduceIte, MachineState.writeMem]; exact ih s
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih s

theorem con_cond_foldl_block_size (n : Nat) (cM cA cV : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => if cM i != 0 then
       st.writeMem (cA i).natAbs (cV i) else st) s (List.range n)).block_size = s.block_size := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : cM k != 0
    · simp only [h, ↓reduceIte, MachineState.writeMem]; exact ih s
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih s

theorem con_cond_foldl_grid_size (n : Nat) (cM cA cV : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => if cM i != 0 then
       st.writeMem (cA i).natAbs (cV i) else st) s (List.range n)).grid_size = s.grid_size := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : cM k != 0
    · simp only [h, ↓reduceIte, MachineState.writeMem]; exact ih s
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih s

theorem con_cond_foldl_env (n : Nat) (cM cA cV : Nat → Int) (s : MachineState) (var : String) :
    (List.foldl (fun st i => if cM i != 0 then
       st.writeMem (cA i).natAbs (cV i) else st) s (List.range n)).env var = s.env var := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : cM k != 0
    · simp only [h, ↓reduceIte, MachineState.writeMem]; exact ih s
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih s

theorem store_tensor_faithful_when_memory_unchanged
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (p v : String)
   (h_op  : instr.op   = .store) (h_args : instr.args = [p, v])
   (sh : List Nat) (addrs vals : List Int)
   (h_lp  : s.lookup p = some (tensor sh addrs))
   (h_lv  : s.lookup v = some (tensor sh vals))
   (hlen  : addrs.length = vals.length)
   (gp gv : Nat → Expr)
   (hgp       : ss.env p = some (SymValue.tensor [addrs.length] gp))
   (hgv_corr  : ss.env v = some (SymValue.tensor sh gv))
   (hconcrete : ∀ i, i < addrs.length → (gp i).isConcrete = true)
   (haddr     : ∀ i, i < addrs.length → evalExpr (gp i) mem = addrs.getD i 0)
   (hval      : ∀ i, i < addrs.length → evalExpr (gv i) mem = vals.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  have h_envv : s.env v = some (tensor sh vals) := h_lv
  simp only [evalInstr, symEvalInstr, h_op, h_args,
             MachineState.lookup, SymState.lookup,
             h_envp, h_envv, hgp, hgv_corr]
  rw [MachineState.writeTile, zip_foldl_eq_range s addrs vals hlen]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sym_foldl_pid, con_foldl_pid]; exact hp
  · rw [sym_foldl_bs, con_foldl_bs]; exact hbs
  · rw [sym_foldl_gs, con_foldl_gs]; exact hgs
  · intro addr
    simp only [shapeProd_singleton]
    exact range_fold_mem_faithful addrs.length gp gv
      (fun i => addrs.getD i 0) (fun i => vals.getD i 0) mem
      hconcrete haddr hval s ss hmem addr
  · intro w val hw
    rw [con_foldl_env] at hw; rw [sym_foldl_env]; exact hsc w val hw
  · intro w sh' vals' hw
    rw [con_foldl_env] at hw; rw [sym_foldl_env]; exact hten w sh' vals' hw
  · intro w hw
    rw [con_foldl_env] at hw; rw [sym_foldl_env]; exact hnone w hw

theorem store_tensor_masked_faithful
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (p v m : String)
   (h_op  : instr.op = .store) (h_args : instr.args = [p, v, m])
   (sh shv shm : List Nat) (addrs vals masks : List Int)
   (h_lp : s.lookup p = some (tensor sh addrs))
   (h_lv : s.lookup v = some (tensor shv vals))
   (h_lm : s.lookup m = some (tensor shm masks))
   (hlen_av : addrs.length = vals.length) (hlen_am : addrs.length = masks.length)
   (hwfp : shapeProd sh = addrs.length)
   (gp gv gm : Nat → Expr)
   (hgp : ss.env p = some (SymValue.tensor sh gp))
   (hgv : ss.env v = some (SymValue.tensor shv gv))
   (hgm : ss.env m = some (SymValue.tensor shm gm))
   (hAconc : ∀ i, i < addrs.length → (gp i).isConcrete = true)
   (hMconc : ∀ i, i < addrs.length → (gm i).isConcrete = true)
   (haddr : ∀ i, i < addrs.length → evalExpr (gp i) mem = addrs.getD i 0)
   (hval  : ∀ i, i < addrs.length → evalExpr (gv i) mem = vals.getD i 0)
   (hmask : ∀ i, i < addrs.length → evalExpr (gm i) mem = masks.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  have h_envv : s.env v = some (tensor shv vals) := h_lv
  have h_envm : s.env m = some (tensor shm masks) := h_lm
  simp only [evalInstr, symEvalInstr, h_op, h_args,
             MachineState.lookup, SymState.lookup,
             h_envp, h_envv, h_envm, hgp, hgv, hgm]
  rw [masked_writeTile_eq_cond_fold s addrs vals masks hlen_av hlen_am]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sym_cond_foldl_pid, con_cond_foldl_pid]; exact hp
  · rw [sym_cond_foldl_block_size, con_cond_foldl_block_size]; exact hbs
  · rw [sym_cond_foldl_grid_size, con_cond_foldl_grid_size]; exact hgs
  · intro addr
    rw [hwfp]
    exact masked_range_fold_mem_faithful addrs.length gp gv gm
      (fun i => addrs.getD i 0) (fun i => vals.getD i 0) (fun i => masks.getD i 0) mem
      hAconc hMconc haddr hval hmask s ss hmem addr
  · intro w val hw
    rw [con_cond_foldl_env] at hw; rw [sym_cond_foldl_env]; exact hsc w val hw
  · intro w sh' vals' hw
    rw [con_cond_foldl_env] at hw; rw [sym_cond_foldl_env]; exact hten w sh' vals' hw
  · intro w hw
    rw [con_cond_foldl_env] at hw; rw [sym_cond_foldl_env]; exact hnone w hw

theorem store_tensor_masked_faithful_when_all_true
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (p v m : String)
   (h_op  : instr.op   = .store) (h_args : instr.args = [p, v, m])
   (sh : List Nat) (addrs vals masks : List Int)
   (h_lp    : s.lookup p = some (tensor sh addrs))
   (h_lv    : s.lookup v = some (tensor sh vals))
   (h_lm    : s.lookup m = some (tensor sh masks))
   (hlen_av : addrs.length = vals.length)
   (hlen_am : addrs.length = masks.length)
   (hall    : ∀ i, i < masks.length → masks.getD i 0 ≠ 0)
   (gp gv : Nat → Expr)
   (hgp       : ss.env p = some (SymValue.tensor [addrs.length] gp))
   (hgv_corr  : ss.env v = some (SymValue.tensor sh gv))
   (hconcrete : ∀ i, i < addrs.length → (gp i).isConcrete = true)
   (haddr     : ∀ i, i < addrs.length → evalExpr (gp i) mem = addrs.getD i 0)
   (hval      : ∀ i, i < addrs.length → evalExpr (gv i) mem = vals.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

theorem cmpi_slt_tensor_faithful_when_all_true
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor sh g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (a b : String)
   (h_op  : instr.op   = .cmpi_slt) (h_args : instr.args = [a, b])
   (sh : List Nat) (xs ys : List Int)
   (h_la  : s.lookup a = some (tensor sh xs))
   (h_lb  : s.lookup b = some (tensor sh ys))
   (hlen  : xs.length = ys.length)
   (hall  : ∀ i, i < xs.length → xs.getD i 0 < ys.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 6: evalInstr_faithful
-- ══════════════════════════════════════════════════════════════════════════════


set_option maxHeartbeats 4000000 in
theorem evalInstr_faithful (instr : TritonInstr)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  have hid : StatesFaithful s ss mem := ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩
  match h_op : instr.op with

  | .constant v =>
      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, MachineState.lookup]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
        instr.result v (Expr.lit v) (by simp [evalExpr])

  | .get_program_id axis =>
      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, MachineState.lookup]
      by_cases haxis : axis == 0
      · simp only [haxis, ↓reduceIte]
        exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
          (by simp [evalExpr, hp])
      · simp only [haxis, ↓reduceIte]; sorry

  | .make_range sizeOpt =>
      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op]
      rw [← hbs]
      have hlen : (List.map Int.ofNat (List.range (sizeOpt.getD s.block_size))).length
                  = sizeOpt.getD s.block_size := by simp
      apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
      intro i hi
      rw [hlen] at hi
      simp only [evalExpr]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      simp [List.getElem?_range, hi]

  | .splat shape =>
      match h_args : instr.args with
      | [v] =>
          cases h_lv : s.env v with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_lv, Option.bind_none, SymState.lookup, hnone v h_lv]
              exact hid
          | some val =>
              cases val with
              | scalar x =>
                  obtain ⟨e, hse, heval⟩ := hsc v x h_lv
                  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                    MachineState.lookup, h_lv, Option.bind_some, SymState.lookup, hse]
                  -- goal: StatesFaithful (s.bind r (tensor shape (replicate n x)))
                  --                      (ss.bind r (SymValue.tensor n (fun _ => e)))
                  -- Use conv to rewrite only the symbolic tensor n to (replicate n x).length
                  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                  intro i hi
                  simp only [List.length_replicate] at hi
                  -- goal: evalExpr e mem = (List.replicate n x)[i]?.getD 0
                  -- (replicate n x)[i] = x since i < n; evalExpr e mem = x by heval
                  simp only [evalExpr, heval]
                  simp [List.getElem?_replicate, hi]
              | fscalar _ => sorry
              | ftensor _ _ => sorry
              | tensor _ _ => sorry
      | _ => sorry

  | .copy =>
      match h_args : instr.args with
      | [v] =>
          cases h_lv : s.env v with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_lv, Option.bind_none, SymState.lookup, hnone v h_lv]
              exact hid
          | some val => sorry
      | _ => sorry
  | .addi =>
      match h_args : instr.args with
      | [a, b] =>
          cases h_la : s.env a with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_la, Option.bind_none, SymState.lookup,
                hnone a h_la, symAdd]; exact hid
          | some va =>
              cases h_lb : s.env b with
              | none =>
                  cases va with
                  | scalar x =>
                      obtain ⟨ea, hsa, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsa, hnone b h_lb, symAdd]; exact hid
                  | tensor sh xs =>
                      obtain ⟨g, hsg, _⟩ := hten a sh xs h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsg, hnone b h_lb, symAdd]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vb =>
                  cases va with
                  | scalar x =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsb, symAdd]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hea, heb])
                      | tensor sh ys =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨g, hsg, heg⟩ := hten b sh ys h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsg, symAdd]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [hea, heg i hi, map_add_getD ys x i hi]; omega
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor sh xs =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨g, hsg, heg⟩ := hten a sh xs h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsg, hsb, symAdd]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [heg i hi, heb, map_add_getD xs y i hi]
                      | tensor _ _ => sorry
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .addf =>
      match h_args : instr.args with
      | [a, b] =>
          cases h_la : s.env a with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_la, Option.bind_none, SymState.lookup,
                hnone a h_la, symAdd]; exact hid
          | some va =>
              cases h_lb : s.env b with
              | none =>
                  cases va with
                  | scalar x =>
                      obtain ⟨ea, hsa, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsa, hnone b h_lb, symAdd]; exact hid
                  | tensor sh xs =>
                      obtain ⟨g, hsg, _⟩ := hten a sh xs h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsg, hnone b h_lb, symAdd]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vb =>
                  cases va with
                  | scalar x =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsb, symAdd]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hea, heb])
                      | tensor sh ys =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨g, hsg, heg⟩ := hten b sh ys h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsg, symAdd]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [hea, heg i hi, map_add_getD ys x i hi]; omega
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor sh xs =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨g, hsg, heg⟩ := hten a sh xs h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsg, hsb, symAdd]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [heg i hi, heb, map_add_getD xs y i hi]
                      | tensor _ _ => sorry
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .muli =>
      match h_args : instr.args with
      | [a, b] =>
          cases h_la : s.env a with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_la, Option.bind_none, TritonValue.zipWith,
                SymState.lookup, hnone a h_la]; exact hid
          | some va =>
              cases h_lb : s.env b with
              | none =>
                  cases va with
                  | scalar x =>
                      obtain ⟨ea, hsa, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        TritonValue.zipWith, SymState.lookup, hsa, hnone b h_lb]; exact hid
                  | tensor sh xs =>
                      obtain ⟨g, hsg, _⟩ := hten a sh xs h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        TritonValue.zipWith, SymState.lookup, hsg, hnone b h_lb]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vb =>
                  cases va with
                  | scalar x =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            TritonValue.zipWith, SymState.lookup, hsa, hsb]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hea, heb])
                      | tensor _ _ => sorry
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .addptr =>
      match h_args : instr.args with
      | [p, o] =>
          cases h_lp : s.env p with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_lp, Option.bind_none, SymState.lookup, hnone p h_lp]
              exact hid
          | some vp =>
              cases h_lo : s.env o with
              | none =>
                  cases vp with
                  | scalar base =>
                      obtain ⟨ep, hsp, _⟩ := hsc p base h_lp
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_lp, h_lo, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsp, hnone o h_lo]; exact hid
                  | tensor sh1 bases =>
                      obtain ⟨g, hsg, _⟩ := hten p sh1 bases h_lp
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_lp, h_lo, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsg, hnone o h_lo]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vo =>
                  cases vp with
                  | scalar base =>
                      cases vo with
                      | scalar off =>
                          obtain ⟨ep, hsp, hep⟩ := hsc p base h_lp
                          obtain ⟨eo, hso, heo⟩ := hsc o off h_lo
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_lp, h_lo, Option.bind_some,
                            SymState.lookup, hsp, hso]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hep, heo])
                      | tensor sh offs =>
                          obtain ⟨ep, hsp, hep⟩ := hsc p base h_lp
                          obtain ⟨g, hsg, heg⟩ := hten o sh offs h_lo
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_lp, h_lo, Option.bind_some,
                            SymState.lookup, hsp, hsg]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [hep, heg i hi, map_add_getD offs base i hi]; omega
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .load          => sorry
  | .load_masked   => sorry
  | .store         => sorry
  | .store_masked  => sorry
  | .storef        => sorry
  | .cmpi_slt      => sorry
  | .cmpi_sge      => sorry
  | .cmpi_sgt      => sorry
  | .cmpi_sle      => sorry
  | .cmpi_ne       => sorry
  | .cmpi_eq       => sorry
  | .cmpf_ole      => sorry
  | .cmpf_olt      => sorry
  | .get_num_programs _ => sorry
  | .constantf _   => sorry
  | .loadf         => sorry
  | .andi          => sorry
  | .subf          => sorry
  | .divf          => sorry
  | .mulf          => sorry
  | .maxsi         => sorry
  | .minsi         => sorry
  | .remsi         => sorry
  | .remui         => sorry
  | .divsi         => sorry
  | .divui         => sorry
  | .subi          => sorry
  | .shli          => sorry
  | .shrsi         => sorry
  | .shrui         => sorry
  | .xori          => sorry
  | .ori           => sorry
  | .truncf        => sorry
  | .extf          => sorry
  | .sqrtf         => sorry
  | .absf          => sorry
  | .negf          => sorry
  | .select        => sorry
  | .dot           => sorry
  | .reduce_sum _  => sorry
  | .reduce_max _  => sorry
  | .reduce_min _  => sorry
  | .broadcast _   => sorry
  | .expand_dims _ => sorry
  | .expf          => sorry
  | .constant_tensor _ _ => sorry
  | .constant_tensorf _ _ => sorry
  | .trans         => sorry
  | .reshape       => sorry


set_option maxHeartbeats 2000000 in
theorem symEvalKernel_faithful (K : TritonKernel)
   (s : MachineState) (ss : SymState) (mem : Nat → Int)
   (h : StatesFaithful s ss mem) :
   StatesFaithful (evalKernel K s) (symEvalKernel K ss) mem := by
 induction K generalizing s ss with
 | nil => simp [evalKernel, symEvalKernel]; exact h
 | cons instr rest ih =>
     simp only [evalKernel, symEvalKernel, List.foldl]
     exact ih _ _ (evalInstr_faithful instr s ss mem h)


-- Generic soundness bridge: for any kernel K, any init states satisfying
-- StatesFaithful, the symbolic memory at any address evaluates to the
-- concrete memory value under the interpretation mem.
theorem symEval_sound (K : TritonKernel)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) (addr : Nat) :
    evalExpr ((symEvalKernel K ss).memory addr) mem =
    (evalKernel K s).memory addr :=
  (symEvalKernel_faithful K s ss mem h).2.2.2.1 addr


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 7: StatesFaithfulMem driver (sound load/store via strengthened invariant)
-- ══════════════════════════════════════════════════════════════════════════════

-- Strengthened invariant: faithful AND concrete memory still equals the symbolic
-- interpretation base `mem`. Holds from init through any non-store instruction.
-- A store exits this regime (memory diverges) — handled as a terminal transition.
def StatesFaithfulMem (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  StatesFaithful s ss mem ∧ s.memory = mem

theorem evalInstr_preserves_memory_of_ne_store
    (instr : TritonInstr) (s : MachineState)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef) :
    (evalInstr instr s).memory = s.memory := by
  unfold evalInstr
  split
  · exact absurd (by assumption) hns
  · exact absurd (by assumption) hnsf
  · cases evalOp instr.op instr.args s with
    | none => rfl
    | some val => rfl

theorem evalInstr_faithful_mem
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef)
    (hstep_or_load :
       (instr.op = .load → ∃ p sh addrs, instr.args = [p] ∧ s.lookup p = some (tensor sh addrs))
       ∧ (instr.op ≠ .load →
            (StatesFaithful s ss mem →
             StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem)))
    (h : StatesFaithfulMem s ss mem) :
    StatesFaithfulMem (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsf, hraw⟩ := h
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  by_cases hld : instr.op = .load
  · obtain ⟨p, sh, addrs, h_args, h_lp⟩ := hstep_or_load.1 hld
    refine ⟨load_tensor_faithful_when_memory_unchanged hp hbs hgs hmem hsc hten hnone
      hraw instr p hld h_args sh addrs h_lp, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s hns hnsf]; exact hraw
  · refine ⟨hstep_or_load.2 hld ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s hns hnsf]; exact hraw

theorem prefix_faithful_mem (K : TritonKernel)
    (hstep : ∀ (instr : TritonInstr), instr ∈ K →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                StatesFaithfulMem s ss mem →
                StatesFaithfulMem (evalInstr instr s) (symEvalInstr instr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithfulMem s ss mem) :
    StatesFaithfulMem (evalKernel K s) (symEvalKernel K ss) mem := by
  induction K generalizing s ss with
  | nil => simpa [evalKernel, symEvalKernel] using h
  | cons instr rest ih =>
      simp only [evalKernel, symEvalKernel, List.foldl]
      exact ih (fun i hi => hstep i (List.mem_cons_of_mem _ hi)) _ _
        (hstep instr (List.mem_cons_self ..) s ss mem h)

theorem evalKernel_append (xs ys : TritonKernel) (s : MachineState) :
    evalKernel (xs ++ ys) s = evalKernel ys (evalKernel xs s) := by
  simp only [evalKernel, List.foldl_append]

theorem symEvalKernel_append (xs ys : TritonKernel) (ss : SymState) :
    symEvalKernel (xs ++ ys) ss = symEvalKernel ys (symEvalKernel xs ss) := by
  simp only [symEvalKernel, List.foldl_append]

theorem kernel_faithful_terminal_store
    (pre : TritonKernel) (storeInstr : TritonInstr)
    (hpre_step : ∀ (instr : TritonInstr), instr ∈ pre →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                StatesFaithfulMem s ss mem →
                StatesFaithfulMem (evalInstr instr s) (symEvalInstr instr ss) mem)
    (hstore : ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                StatesFaithfulMem s ss mem →
                StatesFaithful (evalInstr storeInstr s) (symEvalInstr storeInstr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithfulMem s ss mem) :
    StatesFaithful (evalKernel (pre ++ [storeInstr]) s)
                   (symEvalKernel (pre ++ [storeInstr]) ss) mem := by
  rw [evalKernel_append, symEvalKernel_append]
  have hpre := prefix_faithful_mem pre hpre_step s ss mem h
  simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
  exact hstore _ _ _ hpre


theorem addptr_st_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (p o : String)
    (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (base : Int) (sho : List Nat) (offs : List Int)
    (h_lp : s.env p = some (scalar base)) (h_lo : s.env o = some (tensor sho offs)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨eb, hseb, hevalb⟩ := hsc p base h_lp
  obtain ⟨go, hsgo, hego⟩ := hten o sho offs h_lo
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_lp, h_lo, Option.bind_some, SymState.lookup, hseb, hsgo]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map] at hi
  simp only [evalExpr, hevalb]
  rw [hego i hi]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
  simp
  omega


theorem divsi_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .divsi) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey,
    TritonValue.zipWith, symBinop]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem remsi_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .remsi) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey,
    TritonValue.zipWith, symBinop]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem minsi_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .minsi) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey,
    symBinop]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem cmpi_sgt_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_sgt) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey,
    symBinop]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem subi_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .subi) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey,
    TritonValue.zipWith, symBinop]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem constant_tensor_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (val : Int) (shape : List Nat)
    (h_op : instr.op = .constant_tensor val shape) (h_args : instr.args = []) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_replicate] at hi
  simp only [evalExpr]
  simp [List.getElem?_replicate, hi]

theorem select_and_eq (x y : Int) :
    (if (x != 0) = true then (if (y != 0) = true then (1:Int) else 0) else 0) =
    (if (x != 0 && y != 0) = true then 1 else 0) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [hx, hy, bne_iff_ne]

theorem zip_and_getD (a b : List Int) (i : Nat)
    (hi : i < a.length) (hab : a.length = b.length) :
    ((a.zip b).map (fun p => if p.fst != 0 && p.snd != 0 then (1:Int) else 0)).getD i 0 =
    (if a.getD i 0 != 0 && b.getD i 0 != 0 then 1 else 0) := by
  induction a generalizing b i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
        exact ih ys j (by simpa using hi) (by simpa using hab)

theorem andi_tt_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size) (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .andi) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (hwa : (tensor sha xs).WFn) (hwb : (tensor shb ys).WFn) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ga, hsga, hega⟩ := hten a sha xs h_la
  obtain ⟨gb, hsgb, hegb⟩ := hten b shb ys h_lb
  simp only [TritonValue.WFn] at hwa hwb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsga, hsgb]
  by_cases hshape : (sha == shb) = true
  · simp only [hshape, if_true, Option.bind_some]
    have hsheq : sha = shb := by simpa using hshape
    have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
    have hlen2 : xs.length =
        ((xs.zip ys).map (fun p => if p.fst != 0 && p.snd != 0 then (1:Int) else 0)).length := by
      simp [List.length_zip, hlen]
    apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
    intro i hi
    rw [← hlen2] at hi
    simp only [evalExpr]
    rw [hega i hi, hegb i (hlen ▸ hi), zip_and_getD xs ys i hi hlen]
    exact select_and_eq (xs.getD i 0) (ys.getD i 0)
  · have hshape' : (sha == shb) = false := by simpa using hshape
    simp only [hshape', if_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩

theorem muli_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .muli) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey,
    TritonValue.zipWith]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]


theorem muli_tt_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .muli) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (hwa : (tensor sha xs).WFn) (hwb : (tensor shb ys).WFn) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ga, hsga, hega⟩ := hten a sha xs h_la
  obtain ⟨gb, hsgb, hegb⟩ := hten b shb ys h_lb
  simp only [TritonValue.WFn] at hwa hwb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsga, hsgb,
    TritonValue.zipWith]
  by_cases hshape : (sha == shb) = true
  · simp only [hshape, if_true, Option.bind_some]
    have hsheq : sha = shb := by simpa using hshape
    have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
    have hlen2 : xs.length = ((xs.zip ys).map (fun p => p.fst * p.snd)).length := by
      simp [List.length_zip, hlen]
    apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
    intro i hi
    rw [← hlen2] at hi
    simp only [evalExpr]
    rw [hega i hi, hegb i (hlen ▸ hi), zip_mul_getD xs ys i hi hlen]
  · have hshape' : (sha == shb) = false := by simpa using hshape
    simp only [hshape', if_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩


theorem load_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (hraw : s.memory = mem)
    (instr : TritonInstr) (p : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p])
    (addr : Int) (h_lp : s.env p = some (scalar addr)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ep, hsep, hevalp⟩ := hsc p addr h_lp
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_lp, Option.bind_some, SymState.lookup, hsep, List.head?, Option.getD]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalp, MachineState.readMem, hraw]


theorem addi_ss_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey, symAdd]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem addi_st_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (x : Int) (shb : List Nat) (ys : List Int)
    (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (tensor shb ys)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨gy, hsgy, hegy⟩ := hten b shb ys h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsgy, symAdd]
  have hlen : ys.length = (ys.map (· + x)).length := by simp
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map] at hi
  simp only [evalExpr, hevalx]
  rw [hegy i hi]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
  simp
  omega

theorem addi_ts_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (sha : List Nat) (xs : List Int) (y : Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨gx, hsgx, hegx⟩ := hten a sha xs h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsgx, hsey, symAdd]
  have hlen : xs.length = (xs.map (· + y)).length := by simp
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map] at hi
  simp only [evalExpr, hevaly]
  rw [hegx i hi]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
  simp

theorem addf_ss_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsey, symAdd]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalx, hevaly]

theorem addf_st_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (x : Int) (shb : List Nat) (ys : List Int)
    (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (tensor shb ys)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ex, hsex, hevalx⟩ := hsc a x h_la
  obtain ⟨gy, hsgy, hegy⟩ := hten b shb ys h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsex, hsgy, symAdd]
  have hlen : ys.length = (ys.map (· + x)).length := by simp
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map] at hi
  simp only [evalExpr, hevalx]
  rw [hegy i hi]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
  simp
  omega

theorem addf_ts_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (a b : String) (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (sha : List Nat) (xs : List Int) (y : Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (scalar y)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨gx, hsgx, hegx⟩ := hten a sha xs h_la
  obtain ⟨ey, hsey, hevaly⟩ := hsc b y h_lb
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_la, h_lb, Option.bind_some, SymState.lookup, hsgx, hsey, symAdd]
  have hlen : xs.length = (xs.map (· + y)).length := by simp
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  simp only [List.length_map] at hi
  simp only [evalExpr, hevaly]
  rw [hegx i hi]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
  simp


theorem addptr_ss_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (p o : String) (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (base off : Int) (h_lp : s.env p = some (scalar base)) (h_lo : s.env o = some (scalar off)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨ep, hsep, hevalp⟩ := hsc p base h_lp
  obtain ⟨eo, hseo, hevalo⟩ := hsc o off h_lo
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_lp, h_lo, Option.bind_some, SymState.lookup, hsep, hseo]
  apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
  simp only [evalExpr, hevalp, hevalo]

theorem addptr_tt_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor sh g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (p o : String) (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (shp sho : List Nat) (bases offs : List Int)
    (h_lp : s.env p = some (tensor shp bases)) (h_lo : s.env o = some (tensor sho offs))
    (hwp : (tensor shp bases).WFn) (hwo : (tensor sho offs).WFn) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨gp, hsgp, hegp⟩ := hten p shp bases h_lp
  obtain ⟨go, hsgo, hego⟩ := hten o sho offs h_lo
  simp only [TritonValue.WFn] at hwp hwo
  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
    MachineState.lookup, h_lp, h_lo, Option.bind_some, SymState.lookup, hsgp, hsgo]
  by_cases hshape : (shp == sho) = true
  · simp only [hshape, if_true, Option.bind_some]
    have hsheq : shp = sho := by simpa using hshape
    have hlen : bases.length = offs.length := by rw [← hwp, ← hwo, hsheq]
    have hlen2 : bases.length = ((bases.zip offs).map (fun p => p.fst + p.snd)).length := by
      simp [List.length_zip, hlen]
    apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
    intro i hi
    rw [← hlen2] at hi
    simp only [evalExpr]
    rw [hegp i hi, hego i (hlen ▸ hi), zip_add_getD bases offs i hi hlen]
  · have hshape' : (shp == sho) = false := by simpa using hshape
    simp only [hshape', if_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩


-- ── WF1 parallel invariant + combined driver (threads rank-1 WF for elementwise) ──
-- StatesFaithful is left UNTOUCHED. WFState rides alongside as a parallel invariant
-- so elementwise faithfulness lemmas can obtain operand WF1 at each step.

def WFState (s : MachineState) : Prop :=
  ∀ v sh vals, s.env v = some (tensor sh vals) → (tensor sh vals).WFn

theorem WFState_bind_tensor (s : MachineState) (r : String) (sh : List Nat) (vals : List Int)
    (hw : WFState s) (hwf : (tensor sh vals).WFn) :
    WFState (s.bind r (tensor sh vals)) := by
  intro v sh' vals' hv
  simp only [MachineState.bind] at hv
  by_cases hvr : (v == r) = true
  · rw [if_pos hvr] at hv
    injection hv with hv; injection hv with e1 e2; subst e1; subst e2; exact hwf
  · rw [if_neg hvr] at hv
    exact hw v sh' vals' hv

theorem WFState_bind_scalar (s : MachineState) (r : String) (x : Int)
    (hw : WFState s) :
    WFState (s.bind r (scalar x)) := by
  intro v sh' vals' hv
  simp only [MachineState.bind] at hv
  by_cases hvr : (v == r) = true
  · rw [if_pos hvr] at hv; simp at hv
  · rw [if_neg hvr] at hv
    exact hw v sh' vals' hv

def FaithfulWF (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  StatesFaithfulMem s ss mem ∧ WFState s

theorem prefix_faithful_wf (K : TritonKernel)
    (hstep : ∀ (instr : TritonInstr), instr ∈ K →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWF s ss mem →
                FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalKernel K s) (symEvalKernel K ss) mem := by
  induction K generalizing s ss with
  | nil => simpa [evalKernel, symEvalKernel] using h
  | cons instr rest ih =>
      simp only [evalKernel, symEvalKernel, List.foldl]
      exact ih (fun i hi => hstep i (List.mem_cons_of_mem _ hi)) _ _
        (hstep instr (List.mem_cons_self ..) s ss mem h)

theorem kernel_faithful_wf_terminal_store
    (pre : TritonKernel) (storeInstr : TritonInstr)
    (hpre_step : ∀ (instr : TritonInstr), instr ∈ pre →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWF s ss mem →
                FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem)
    (hstore : ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWF s ss mem →
                StatesFaithful (evalInstr storeInstr s) (symEvalInstr storeInstr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWF s ss mem) :
    StatesFaithful (evalKernel (pre ++ [storeInstr]) s)
                   (symEvalKernel (pre ++ [storeInstr]) ss) mem := by
  rw [evalKernel_append, symEvalKernel_append]
  have hpre := prefix_faithful_wf pre hpre_step s ss mem h
  simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
  exact hstore _ _ _ hpre


-- ── per-op COMBINED step lemmas (FaithfulWF -> FaithfulWF) ────────────────────
-- Lift each per-op faithful lemma to the combined invariant: StatesFaithfulMem
-- half via the faithful lemma + memory preservation; WFState half via bind.

theorem constant_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (v : Int) (h_op : instr.op = .constant v)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    refine ⟨constant_faithful hsf instr v h_op, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar v) := by
      simp only [evalInstr, h_op, evalOp]
    rw [hb]
    exact WFState_bind_scalar s instr.result v hwf

theorem get_program_id_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (h_op : instr.op = .get_program_id 0)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    refine ⟨get_program_id_faithful hsf instr h_op, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s
        = s.bind instr.result (scalar (Int.ofNat (if (0:Nat) == 0 then s.pid else s.pid_y))) := by
      simp only [evalInstr, h_op, evalOp]
    rw [hb]
    exact WFState_bind_scalar s instr.result _ hwf


theorem make_range_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (sizeOpt : Option Nat) (h_op : instr.op = .make_range sizeOpt)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    refine ⟨make_range_faithful hsf instr sizeOpt h_op, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s
        = s.bind instr.result
            (tensor [sizeOpt.getD s.block_size]
              (List.map Int.ofNat (List.range (sizeOpt.getD s.block_size)))) := by
      simp only [evalInstr, h_op, evalOp]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp [TritonValue.WFn, shapeProd, List.length_map, List.length_range]

theorem splat_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (n : Nat) (v : String)
    (h_op : instr.op = .splat [n]) (h_args : instr.args = [v])
    (x : Int) (h_lv : s.env v = some (scalar x))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨splat_scalar_faithful hp hbs hgs hmem hsc hten hnone instr [n] v h_op h_args x h_lv, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s
        = s.bind instr.result
            (tensor [n] (List.replicate ([n].foldl (· * ·) 1) x)) := by
      simp only [evalInstr, h_op, h_args, evalOp, MachineState.lookup, h_lv]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp [TritonValue.WFn, shapeProd, List.length_replicate]


theorem addi_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addi_tt_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha shb xs ys h_la h_lb hwa hwb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa hwb
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    by_cases hsh : sha == shb
    · rw [if_pos hsh]
      apply WFState_bind_tensor s instr.result _ _ hwf
      have hsheq : sha = shb := by simpa using hsh
      have hxy : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
      simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hxy, Nat.min_self]
    · rw [if_neg (by simpa using hsh)]
      exact hwf

theorem addf_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addf_tt_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha shb xs ys h_la h_lb hwa hwb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa hwb
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    by_cases hsh : sha == shb
    · rw [if_pos hsh]
      apply WFState_bind_tensor s instr.result _ _ hwf
      have hsheq : sha = shb := by simpa using hsh
      have hxy : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
      simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hxy, Nat.min_self]
    · rw [if_neg (by simpa using hsh)]
      exact hwf


theorem addptr_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p o : String)
    (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (base : Int) (sho : List Nat) (offs : List Int)
    (h_lp : s.env p = some (scalar base)) (h_lo : s.env o = some (tensor sho offs))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwo : (tensor sho offs).WFn := hwf o sho offs h_lo
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addptr_st_faithful hp hbs hgs hmem hsc hten hnone instr p o h_op h_args
      base sho offs h_lp h_lo, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwo
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, h_lo, Option.bind_some]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwo, List.length_map]


theorem load_masked_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p m : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p, m])
    (sh shm : List Nat) (addrs masks : List Int)
    (h_lp : s.env p = some (tensor sh addrs))
    (h_lm : s.env m = some (tensor shm masks))
    (hsheq : sh = shm)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sh addrs).WFn := hwf p sh addrs h_lp
  have hwm : (tensor shm masks).WFn := hwf m shm masks h_lm
  have hlen : addrs.length = masks.length := by
    simp only [TritonValue.WFn] at hwa hwm; rw [← hwa, ← hwm, hsheq]
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    have hmr : s.memory = mem := hraw
    refine ⟨load_tensor_masked_faithful hp hbs hgs hmem hsc hten hnone hmr instr p m h_op h_args
      sh shm addrs masks h_lp h_lm hlen hsheq, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa
    have hshmb : (sh == shm) = true := by simp [hsheq]
    have hb : evalInstr instr s = s.bind instr.result
        (tensor sh ((addrs.zip masks).map (fun x => if x.snd != 0 then s.readMem x.fst.natAbs else 0))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, h_lm, Option.bind_some,
        hshmb, if_true]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hlen, Nat.min_self]

theorem load_masked_fill_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p m f : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p, m, f])
    (sh shm shf : List Nat) (addrs masks fills : List Int)
    (h_lp : s.env p = some (tensor sh addrs))
    (h_lm : s.env m = some (tensor shm masks))
    (h_lf : s.env f = some (tensor shf fills))
    (hlenm : addrs.length = masks.length) (hlenf : addrs.length = fills.length)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sh addrs).WFn := hwf p sh addrs h_lp
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    have hmr : s.memory = mem := hraw
    refine ⟨load_tensor_masked_fill_faithful hp hbs hgs hmem hsc hten hnone hmr instr p m f h_op h_args
      sh shm shf addrs masks fills h_lp h_lm h_lf hlenm hlenf, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa
    have hb : evalInstr instr s = s.bind instr.result
        (tensor sh (((addrs.zip masks).zip fills).map
          (fun x => if x.fst.snd != 0 then s.readMem x.fst.fst.natAbs else x.snd))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, h_lm, h_lf,
        Option.bind_some]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    have hmf : masks.length = fills.length := by rw [← hlenm, ← hlenf]
    simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hlenm, hlenf, hmf, Nat.min_self]

theorem load_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p])
    (sh : List Nat) (addrs : List Int)
    (h_lp : s.env p = some (tensor sh addrs))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwp : (tensor sh addrs).WFn := hwf p sh addrs h_lp
  refine ⟨?_, ?_⟩
  · apply evalInstr_faithful_mem instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
    refine ⟨?_, ?_⟩
    · intro _
      exact ⟨p, sh, addrs, h_args, h_lp⟩
    · intro hnl; exact absurd h_op hnl
    · exact hsfm
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwp
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, Option.bind_some]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwp, List.length_map]


theorem muli_scalar_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .muli) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨muli_scalar_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      x y h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar (x * y)) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb,
        Option.bind_some, TritonValue.zipWith]
    rw [hb]
    exact WFState_bind_scalar s instr.result (x * y) hwf


-- Carry an env lookup forward past an instruction that binds a DIFFERENT result.
-- The workhorse for discharging operand lookups in explicit sequential chains.
theorem env_bind_ne (s : MachineState) (instr : TritonInstr) (w : String)
    (val : TritonValue) (hbind : evalInstr instr s = s.bind instr.result val)
    (hne : w ≠ instr.result) :
    (evalInstr instr s).env w = s.env w := by
  rw [hbind]; simp only [MachineState.bind]; rw [if_neg]; simpa using hne


-- ── binding-fact toolkit: what each op writes (for explicit sequential chains) ──
-- Each reads the operand lookups (as hyps) and states the exact bound value, one
-- layer up. Combined with env_bind_ne/carry_ne to thread operands through a chain.

theorem const_binds (s : MachineState) (r : String) (v : Int) :
    (evalInstr { result := r, op := .constant v, args := [] } s).env r = some (scalar v) := by
  simp only [evalInstr, evalOp, MachineState.bind]; simp

theorem gpid_binds (s : MachineState) (r : String) :
    (evalInstr { result := r, op := .get_program_id 0, args := [] } s).env r
      = some (scalar (Int.ofNat s.pid)) := by
  simp only [evalInstr, evalOp, MachineState.bind]; simp

theorem muli_binds (s : MachineState) (r a bb : String) (x y : Int)
    (ha : s.env a = some (scalar x)) (hb : s.env bb = some (scalar y)) :
    (evalInstr { result := r, op := .muli, args := [a, bb] } s).env r = some (scalar (x * y)) := by
  simp only [evalInstr, evalOp, MachineState.lookup, ha, hb, Option.bind_some,
    TritonValue.zipWith, MachineState.bind]; simp

theorem make_range_binds (s : MachineState) (r : String) (sz : Nat) :
    (evalInstr { result := r, op := .make_range (some sz), args := [] } s).env r
      = some (tensor [sz] (List.map Int.ofNat (List.range sz))) := by
  simp only [evalInstr, evalOp, MachineState.bind, Option.getD]; simp

theorem splat_binds (s : MachineState) (r v : String) (n : Nat) (x : Int)
    (hv : s.env v = some (scalar x)) :
    (evalInstr { result := r, op := .splat [n], args := [v] } s).env r
      = some (tensor [n] (List.replicate n x)) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hv, MachineState.bind]
  simp [List.foldl]

theorem splat_shaped_binds (s : MachineState) (r v : String) (shape : List Nat) (x : Int)
    (hv : s.env v = some (scalar x)) :
    (evalInstr { result := r, op := .splat shape, args := [v] } s).env r
      = some (tensor shape (List.replicate (shape.foldl (· * ·) 1) x)) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hv, MachineState.bind]
  simp

theorem subi_scalar_binds (s : MachineState) (r a bb : String) (x y : Int)
    (ha : s.env a = some (scalar x)) (hb : s.env bb = some (scalar y)) :
    (evalInstr { result := r, op := .subi, args := [a, bb] } s).env r
      = some (scalar (x - y)) := by
  simp only [evalInstr, evalOp, MachineState.lookup, ha, hb, MachineState.bind,
    Option.bind_some, TritonValue.zipWith]
  simp

theorem cmpi_slt_tt_binds (s : MachineState) (r a bb : String) (sh : List Nat) (xs ys : List Int)
    (ha : s.env a = some (tensor sh xs)) (hb : s.env bb = some (tensor sh ys)) :
    (evalInstr { result := r, op := .cmpi_slt, args := [a, bb] } s).env r
      = some (tensor sh ((xs.zip ys).map (fun p => if p.fst < p.snd then (1:Int) else 0))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, ha, hb, MachineState.bind,
    Option.bind_some, beq_self_eq_true, if_true]

theorem broadcast_binds (s : MachineState) (r v : String) (s0 s1 t0 t1 : Nat) (vals : List Int)
    (hv : s.env v = some (tensor [s0, s1] vals)) :
    (evalInstr { result := r, op := .broadcast [t0, t1], args := [v] } s).env r
      = some (tensor [t0, t1] ((List.range (t0 * t1)).map (fun idx =>
          vals.getD ((if s0 == 1 then 0 else idx / t1) * s1
                     + (if s1 == 1 then 0 else idx % t1)) 0))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hv, MachineState.bind, Option.bind_some]
  simp

theorem broadcast_binds_len (s : MachineState) (r v : String) (s0 s1 t0 t1 : Nat) (vals : List Int)
    (hv : s.env v = some (tensor [s0, s1] vals)) :
    ∃ out, (evalInstr { result := r, op := .broadcast [t0, t1], args := [v] } s).env r
      = some (tensor [t0, t1] out) ∧ out.length = t0 * t1 := by
  refine ⟨_, broadcast_binds s r v s0 s1 t0 t1 vals hv, ?_⟩
  simp

theorem copy_binds (s : MachineState) (r v : String) (val : TritonValue)
    (hv : s.env v = some val) :
    (evalInstr { result := r, op := .copy, args := [v] } s).env r = some val := by
  simp only [evalInstr, evalOp, MachineState.lookup, hv, MachineState.bind, Option.bind_some]
  simp

/-- Explicit form of the 3-arg masked load's output. load_fill_binds hides this behind an
    existential; the value walk needs the actual expression to apply tile_load_value_*. -/
theorem load_fill_binds_explicit (s : MachineState) (r p m f : String)
    (sh shm shf : List Nat) (addrs masks fills : List Int)
    (hp : s.env p = some (tensor sh addrs))
    (hm : s.env m = some (tensor shm masks))
    (hf : s.env f = some (tensor shf fills)) :
    (evalInstr { result := r, op := .load, args := [p, m, f] } s).env r
      = some (tensor sh (((addrs.zip masks).zip fills).map
          (fun x => if x.fst.snd != 0 then s.readMem x.fst.fst.natAbs else x.snd))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hp, hm, hf, MachineState.bind,
    Option.bind_some]
  simp

theorem load_fill_binds (s : MachineState) (r p m f : String)
    (sh shm shf : List Nat) (addrs masks fills : List Int)
    (hp : s.env p = some (tensor sh addrs))
    (hm : s.env m = some (tensor shm masks))
    (hf : s.env f = some (tensor shf fills))
    (hlenm : addrs.length = masks.length) (hlenf : addrs.length = fills.length) :
    ∃ out, (evalInstr { result := r, op := .load, args := [p, m, f] } s).env r
      = some (tensor sh out) ∧ out.length = addrs.length := by
  have hb : (evalInstr { result := r, op := .load, args := [p, m, f] } s).env r
      = some (tensor sh (((addrs.zip masks).zip fills).map
          (fun x => if x.fst.snd != 0 then s.readMem x.fst.fst.natAbs else x.snd))) := by
    simp only [evalInstr, evalOp, MachineState.lookup, hp, hm, hf, MachineState.bind,
      Option.bind_some]
    simp
  refine ⟨_, hb, ?_⟩
  have hmf : masks.length = fills.length := by rw [← hlenm, ← hlenf]
  simp [List.length_map, List.length_zip, hlenm, hlenf, hmf, Nat.min_self]

/-- Explicit form of the dot's output. dot_binds hides it behind an existential; the value
    walk needs the actual expression to apply acc_update_lane. -/
theorem dot_binds_explicit (s : MachineState) (r a b acc : String) (m k1 n : Nat)
    (valsA valsB valsAcc : List Int)
    (ha : s.env a = some (tensor [m, k1] valsA))
    (hb2 : s.env b = some (tensor [k1, n] valsB))
    (hacc : s.env acc = some (tensor [m, n] valsAcc)) :
    (evalInstr { result := r, op := .dot, args := [a, b, acc] } s).env r
      = some (tensor [m, n] ((List.range (m * n)).map (fun idx =>
          (List.range k1).foldl (fun accv kk =>
            accv + valsA.getD ((idx / n) * k1 + kk) 0 * valsB.getD (kk * n + (idx % n)) 0) 0
          + valsAcc.getD idx 0))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, ha, hb2, hacc, MachineState.bind,
    Option.bind_some]
  simp

theorem dot_binds (s : MachineState) (r a b acc : String) (m k1 n : Nat)
    (valsA valsB valsAcc : List Int)
    (ha : s.env a = some (tensor [m, k1] valsA))
    (hb2 : s.env b = some (tensor [k1, n] valsB))
    (hacc : s.env acc = some (tensor [m, n] valsAcc)) :
    ∃ out, (evalInstr { result := r, op := .dot, args := [a, b, acc] } s).env r
      = some (tensor [m, n] out) ∧ out.length = m * n := by
  have hb : (evalInstr { result := r, op := .dot, args := [a, b, acc] } s).env r
      = some (tensor [m, n] ((List.range (m * n)).map (fun idx =>
          (List.range k1).foldl (fun accv kk =>
            accv + valsA.getD ((idx / n) * k1 + kk) 0 * valsB.getD (kk * n + (idx % n)) 0) 0
          + valsAcc.getD idx 0))) := by
    simp only [evalInstr, evalOp, MachineState.lookup, ha, hb2, hacc, MachineState.bind,
      Option.bind_some]
    simp
  refine ⟨_, hb, ?_⟩
  simp

theorem addi_binds (s : MachineState) (r a bb : String) (sh : List Nat) (xs ys : List Int)
    (ha : s.env a = some (tensor sh xs)) (hb : s.env bb = some (tensor sh ys)) :
    (evalInstr { result := r, op := .addi, args := [a, bb] } s).env r
      = some (tensor sh ((xs.zip ys).map (fun p => p.fst + p.snd))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, ha, hb, Option.bind_some, MachineState.bind]
  rw [if_pos (by simp)]; simp

theorem addf_binds (s : MachineState) (r a bb : String) (sh : List Nat) (xs ys : List Int)
    (ha : s.env a = some (tensor sh xs)) (hb : s.env bb = some (tensor sh ys)) :
    (evalInstr { result := r, op := .addf, args := [a, bb] } s).env r
      = some (tensor sh ((xs.zip ys).map (fun p => p.fst + p.snd))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, ha, hb, Option.bind_some, MachineState.bind]
  rw [if_pos (by simp)]; simp

theorem addptr_binds (s : MachineState) (r p o : String) (base : Int) (sh : List Nat) (offs : List Int)
    (hp : s.env p = some (scalar base)) (ho : s.env o = some (tensor sh offs)) :
    (evalInstr { result := r, op := .addptr, args := [p, o] } s).env r
      = some (tensor sh (offs.map (· + base))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hp, ho, MachineState.bind]; simp

theorem addptr_tt_binds (s : MachineState) (r p o : String) (sh : List Nat) (bases offs : List Int)
    (hp : s.env p = some (tensor sh bases)) (ho : s.env o = some (tensor sh offs)) :
    (evalInstr { result := r, op := .addptr, args := [p, o] } s).env r
      = some (tensor sh ((bases.zip offs).map (fun x => x.fst + x.snd))) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hp, ho, MachineState.bind,
    Option.bind_some, beq_self_eq_true, if_true]

theorem load_binds (s : MachineState) (r p : String) (sh : List Nat) (addrs : List Int)
    (hp : s.env p = some (tensor sh addrs)) :
    (evalInstr { result := r, op := .load, args := [p] } s).env r
      = some (tensor sh (addrs.map fun a => s.readMem a.natAbs)) := by
  simp only [evalInstr, evalOp, MachineState.lookup, hp, MachineState.bind]; simp

-- Generic bind-fact: any non-store op whose evalOp succeeds binds its result.
-- Turns the `binds`-style value facts into the state form that env_bind_ne/carry_ne need.
theorem evalInstr_eq_bind (instr : TritonInstr) (s : MachineState) (val : TritonValue)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef)
    (hev : evalOp instr.op instr.args s = some val) :
    evalInstr instr s = s.bind instr.result val := by
  unfold evalInstr
  split
  · exact absurd (by assumption) hns
  · exact absurd (by assumption) hnsf
  · rw [hev]

-- env_carry: a non-store instruction never disturbs variables other than its own result.
-- Holds whether or not evalOp succeeds (on failure evalInstr is the identity), so no
-- bind-fact is needed. This is the workhorse for threading operand facts through a
-- straight-line body: carry any tracked variable past any step in one application.
theorem env_carry (instr : TritonInstr) (s : MachineState) (w : String)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef) (hne : w ≠ instr.result) :
    (evalInstr instr s).env w = s.env w := by
  cases hev : evalOp instr.op instr.args s with
  | none =>
      have hid : evalInstr instr s = s := by
        unfold evalInstr; split
        · exact absurd (by assumption) hns
        · exact absurd (by assumption) hnsf
        · rw [hev]
      rw [hid]
  | some val =>
      have hb : evalInstr instr s = s.bind instr.result val :=
        evalInstr_eq_bind instr s val hns hnsf hev
      rw [hb]; simp only [MachineState.bind]; rw [if_neg]; simpa using hne

-- env_carry_kernel: a whole straight-line block preserves any variable none of its
-- instructions writes. Collapses per-step threading into ONE application per variable
-- per segment, which is what makes the 18-step body composition tractable.
-- memory_carry_kernel: a straight-line block with no stores preserves memory.
-- The value walk needs this at every load (to rewrite readMem into layoutMatmul).
theorem memory_carry_kernel (K : TritonKernel) (s : MachineState)
    (hns : ∀ i ∈ K, i.op ≠ .store) (hnsf : ∀ i ∈ K, i.op ≠ .storef) :
    (evalKernel K s).memory = s.memory := by
  induction K generalizing s with
  | nil => simp [evalKernel]
  | cons i rest ih =>
      have hstep : (evalKernel rest (evalInstr i s)).memory = (evalInstr i s).memory :=
        ih (evalInstr i s)
          (fun j hj => hns j (List.mem_cons_of_mem _ hj))
          (fun j hj => hnsf j (List.mem_cons_of_mem _ hj))
      have hcar : (evalInstr i s).memory = s.memory :=
        evalInstr_preserves_memory_of_ne_store i s
          (hns i (List.mem_cons_self ..)) (hnsf i (List.mem_cons_self ..))
      show (evalKernel (i :: rest) s).memory = s.memory
      simp only [evalKernel, List.foldl_cons]
      exact hstep.trans hcar

theorem env_carry_kernel (K : TritonKernel) (s : MachineState) (w : String)
    (hns : ∀ i ∈ K, i.op ≠ .store) (hnsf : ∀ i ∈ K, i.op ≠ .storef)
    (hne : ∀ i ∈ K, w ≠ i.result) :
    (evalKernel K s).env w = s.env w := by
  induction K generalizing s with
  | nil => simp [evalKernel]
  | cons i rest ih =>
      have hstep : (evalKernel rest (evalInstr i s)).env w = (evalInstr i s).env w :=
        ih (evalInstr i s)
          (fun j hj => hns j (List.mem_cons_of_mem _ hj))
          (fun j hj => hnsf j (List.mem_cons_of_mem _ hj))
          (fun j hj => hne j (List.mem_cons_of_mem _ hj))
      have hcar : (evalInstr i s).env w = s.env w :=
        env_carry i s w (hns i (List.mem_cons_self ..))
          (hnsf i (List.mem_cons_self ..)) (hne i (List.mem_cons_self ..))
      show (evalKernel (i :: rest) s).env w = s.env w
      simp only [evalKernel, List.foldl_cons]
      exact hstep.trans hcar

theorem carry_ne (s : MachineState) (instr : TritonInstr) (w : String) (V : TritonValue)
    (val : TritonValue) (hbind : evalInstr instr s = s.bind instr.result val)
    (hne : w ≠ instr.result) (hw : s.env w = some V) :
    (evalInstr instr s).env w = some V := by
  rw [env_bind_ne s instr w val hbind hne]; exact hw


-- ── generic step infrastructure: degenerate operand cases collapse uniformly ──
-- When a non-store op produces none on BOTH concrete and symbolic sides, both
-- evalInstr/symEvalInstr are identity, so FaithfulWF is trivially preserved.
-- This discharges every ill-typed / absent-operand case across all generic steps.

theorem both_none_preserves_faithfulWF
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef)
    (hc : evalOp instr.op instr.args s = none)
    (hsym : symEvalOp instr.op instr.args ss = none)
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have he : evalInstr instr s = s := by
    unfold evalInstr
    split
    · exact absurd (by assumption) hns
    · exact absurd (by assumption) hnsf
    · rw [hc]
  have hse : symEvalInstr instr ss = ss := by
    unfold symEvalInstr
    split
    · exact absurd (by assumption) hns
    · rw [hsym]
  rw [he, hse]; exact h


-- ── NoFloat invariant: env contains no float values (integer-kernel scope) ────
-- StatesFaithful only relates scalar/tensor/none across concrete/symbolic; float
-- values are unconstrained, so generic steps need "operands non-float". This
-- invariant supplies it: established at init, preserved by every integer op.

def NoFloatState (s : MachineState) : Prop :=
  ∀ v tv, s.env v = some tv → (∃ x, tv = scalar x) ∨ (∃ sh xs, tv = tensor sh xs)

theorem NoFloatState_bind_scalar (s : MachineState) (r : String) (x : Int)
    (h : NoFloatState s) : NoFloatState (s.bind r (scalar x)) := by
  intro v tv hv
  simp only [MachineState.bind] at hv
  by_cases hvr : (v == r) = true
  · rw [if_pos hvr] at hv; left; exact ⟨x, by injection hv with hv; exact hv.symm⟩
  · rw [if_neg hvr] at hv; exact h v tv hv

theorem NoFloatState_bind_tensor (s : MachineState) (r : String) (sh : List Nat) (xs : List Int)
    (h : NoFloatState s) : NoFloatState (s.bind r (tensor sh xs)) := by
  intro v tv hv
  simp only [MachineState.bind] at hv
  by_cases hvr : (v == r) = true
  · rw [if_pos hvr] at hv; right; exact ⟨sh, xs, by injection hv with hv; exact hv.symm⟩
  · rw [if_neg hvr] at hv; exact h v tv hv


theorem muli_tt_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .muli) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨muli_tt_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha shb xs ys h_la h_lb hwa hwb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa hwb
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb,
      Option.bind_some, TritonValue.zipWith]
    by_cases hsh : sha == shb
    · rw [if_pos hsh]
      apply WFState_bind_tensor s instr.result _ _ hwf
      have hsheq : sha = shb := by simpa using hsh
      have hxy : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
      simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hxy, Nat.min_self]
    · rw [if_neg (by simpa using hsh)]
      exact hwf


theorem load_scalar_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p])
    (addr : Int) (h_lp : s.env p = some (scalar addr))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  refine ⟨⟨load_scalar_faithful hp hbs hgs hmem hsc hten hnone hraw instr p h_op h_args addr h_lp, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar (s.readMem addr.natAbs)) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, Option.bind_some]
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf


theorem cmpi_slt_tt_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_slt) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨cmpi_slt_tt_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha shb xs ys h_la h_lb hwa hwb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa hwb
    by_cases hsh : (sha == shb) = true
    · have hsheq : sha = shb := by simpa using hsh
      have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
      have hb : evalInstr instr s = s.bind instr.result
          (tensor sha ((xs.zip ys).map (fun p => if p.fst < p.snd then (1:Int) else 0))) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb,
          Option.bind_some, if_pos hsh]
      rw [hb]
      apply WFState_bind_tensor s instr.result _ _ hwf
      simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hlen, Nat.min_self]
    · have hsh' : (sha == shb) = false := by simpa using hsh
      have hid : evalInstr instr s = s := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
        rw [if_neg (by simp [hsh'])]
      rw [hid]; exact hwf

theorem andi_tt_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .andi) (h_args : instr.args = [a, b])
    (sha shb : List Nat) (xs ys : List Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨andi_tt_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha shb xs ys h_la h_lb hwa hwb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa hwb
    by_cases hsh : (sha == shb) = true
    · have hsheq : sha = shb := by simpa using hsh
      have hlen : xs.length = ys.length := by rw [← hwa, ← hwb, hsheq]
      have hb : evalInstr instr s = s.bind instr.result
          (tensor sha ((xs.zip ys).map (fun p => if p.fst != 0 && p.snd != 0 then (1:Int) else 0))) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb,
          Option.bind_some, if_pos hsh]
      rw [hb]
      apply WFState_bind_tensor s instr.result _ _ hwf
      simp only [TritonValue.WFn, hwa, List.length_map, List.length_zip, hlen, Nat.min_self]
    · have hsh' : (sha == shb) = false := by simpa using hsh
      have hid : evalInstr instr s = s := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
        rw [if_neg (by simp [hsh'])]
      rw [hid]; exact hwf

theorem cmpi_slt_ss_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_slt) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨cmpi_slt_ss_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      x y h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar (if x < y then 1 else 0)) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf

theorem addi_ss_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addi_ss_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      x y h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar (x + y)) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf

theorem addi_st_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (x : Int) (shb : List Nat) (ys : List Int)
    (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addi_st_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      x shb ys h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwb
    have hb : evalInstr instr s = s.bind instr.result (tensor shb (ys.map (· + x))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwb, List.length_map]

theorem addi_ts_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (sha : List Nat) (xs : List Int) (y : Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (scalar y))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addi_ts_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha xs y h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa
    have hb : evalInstr instr s = s.bind instr.result (tensor sha (xs.map (· + y))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwa, List.length_map]

theorem addf_ss_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (x y : Int) (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (scalar y))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addf_ss_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      x y h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar (x + y)) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf

theorem addf_st_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (x : Int) (shb : List Nat) (ys : List Int)
    (h_la : s.env a = some (scalar x)) (h_lb : s.env b = some (tensor shb ys))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwb : (tensor shb ys).WFn := hwf b shb ys h_lb
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addf_st_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      x shb ys h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwb
    have hb : evalInstr instr s = s.bind instr.result (tensor shb (ys.map (· + x))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwb, List.length_map]

theorem addf_ts_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (sha : List Nat) (xs : List Int) (y : Int)
    (h_la : s.env a = some (tensor sha xs)) (h_lb : s.env b = some (scalar y))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwa : (tensor sha xs).WFn := hwf a sha xs h_la
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addf_ts_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args
      sha xs y h_la h_lb, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwa
    have hb : evalInstr instr s = s.bind instr.result (tensor sha (xs.map (· + y))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, Option.bind_some]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, hwa, List.length_map]


theorem addptr_ss_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p o : String)
    (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (base off : Int) (h_lp : s.env p = some (scalar base)) (h_lo : s.env o = some (scalar off))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addptr_ss_faithful hp hbs hgs hmem hsc hten hnone instr p o h_op h_args
      base off h_lp h_lo, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result (scalar (base + off)) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, h_lo, Option.bind_some]
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf

theorem addptr_tt_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p o : String)
    (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (shp sho : List Nat) (bases offs : List Int)
    (h_lp : s.env p = some (tensor shp bases)) (h_lo : s.env o = some (tensor sho offs))
    (h : FaithfulWF s ss mem) :
    FaithfulWF (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsfm, hwf⟩ := h
  have hwp : (tensor shp bases).WFn := hwf p shp bases h_lp
  have hwo : (tensor sho offs).WFn := hwf o sho offs h_lo
  refine ⟨?_, ?_⟩
  · obtain ⟨hsf, hraw⟩ := hsfm
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    refine ⟨addptr_tt_faithful hp hbs hgs hmem hsc hten hnone instr p o h_op h_args
      shp sho bases offs h_lp h_lo hwp hwo, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    simp only [TritonValue.WFn] at hwp hwo
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, h_lo, Option.bind_some]
    by_cases hsh : shp == sho
    · rw [if_pos hsh]
      apply WFState_bind_tensor s instr.result _ _ hwf
      have hsheq : shp = sho := by simpa using hsh
      have hbo : bases.length = offs.length := by rw [← hwp, ← hwo, hsheq]
      simp only [TritonValue.WFn, hwp, List.length_map, List.length_zip, hbo, Nat.min_self]
    · rw [if_neg (by simpa using hsh)]
      exact hwf


-- ── FaithfulWFI: combined generic invariant (Faithful + WF1 + integer) ────────
-- The invariant for the GENERIC fold: adds NoFloatState so generic step lemmas can
-- discharge float-operand cases as vacuous. Threaded exactly like FaithfulWF.

def FaithfulWFI (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  FaithfulWF s ss mem ∧ NoFloatState s

-- Binding a scalar (concretely) and its literal (symbolically) preserves the full invariant.
-- Used at the loop head, where the induction variable is bound each iteration.
theorem faithfulWFI_bind_scalar {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (r : String) (n : Int) (h : FaithfulWFI s ss mem) :
    FaithfulWFI (s.bind r (scalar n)) (ss.bind r (SymValue.scalar (Expr.lit n))) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  refine ⟨⟨⟨bind_scalar_faithful hp hbs hgs hmem hsc hten hnone r n (Expr.lit n) (by simp [evalExpr]), ?_⟩, ?_⟩, ?_⟩
  · show (s.bind r (scalar n)).memory = mem
    simpa [MachineState.bind] using hraw
  · exact WFState_bind_scalar s r n hwf
  · exact NoFloatState_bind_scalar s r n hnf

theorem subi_scalar_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .subi) (h_args : instr.args = [a, b])
    (x y : Int) (hea : s.env a = some (scalar x)) (heb : s.env b = some (scalar y))
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have hb : evalInstr instr s = s.bind instr.result (scalar (x - y)) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
      Option.bind_some, TritonValue.zipWith]
  refine ⟨⟨⟨subi_scalar_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args x y hea heb, ?_⟩, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf

theorem divsi_scalar_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .divsi) (h_args : instr.args = [a, b])
    (x y : Int) (hea : s.env a = some (scalar x)) (heb : s.env b = some (scalar y))
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have hb : evalInstr instr s = s.bind instr.result (scalar (x / y)) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
      Option.bind_some, TritonValue.zipWith]
  refine ⟨⟨⟨divsi_scalar_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args x y hea heb, ?_⟩, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf

theorem remsi_scalar_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .remsi) (h_args : instr.args = [a, b])
    (x y : Int) (hea : s.env a = some (scalar x)) (heb : s.env b = some (scalar y))
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have hb : evalInstr instr s = s.bind instr.result (scalar (x % y)) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
      Option.bind_some, TritonValue.zipWith]
  refine ⟨⟨⟨remsi_scalar_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args x y hea heb, ?_⟩, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf

theorem minsi_scalar_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .minsi) (h_args : instr.args = [a, b])
    (x y : Int) (hea : s.env a = some (scalar x)) (heb : s.env b = some (scalar y))
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have hb : evalInstr instr s = s.bind instr.result (scalar (min x y)) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
      Option.bind_some]
  refine ⟨⟨⟨minsi_scalar_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args x y hea heb, ?_⟩, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf

theorem cmpi_sgt_scalar_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_sgt) (h_args : instr.args = [a, b])
    (x y : Int) (hea : s.env a = some (scalar x)) (heb : s.env b = some (scalar y))
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have hb : evalInstr instr s = s.bind instr.result (scalar (if x > y then 1 else 0)) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
      Option.bind_some]
  refine ⟨⟨⟨cmpi_sgt_scalar_faithful hp hbs hgs hmem hsc hten hnone instr a b h_op h_args x y hea heb, ?_⟩, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]; exact WFState_bind_scalar s instr.result _ hwf
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf


-- andi_step_generic: dispatch tensor-tensor bitwise-AND (mask combine) into FaithfulWFI.
-- Tensor-only productive path (matmul uses andi on [64,64] masks); other cases no-op.
theorem andi_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .andi) (h_args : instr.args = [a, b])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have noop : ∀ (hev : evalOp instr.op instr.args s = none)
                (hsv : symEvalOp instr.op instr.args ss = none),
      FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
    intro hev hsv
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [hev]
    have hsym : symEvalInstr instr ss = ss := by
      unfold symEvalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [hsv]
    rw [hid, hsym]; exact ⟨hfwf', hnf⟩
  cases hea : s.env a with
  | none =>
    have hsa := hnone a hea
    exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind])
               (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsa])
  | some va =>
    rcases hnf a va hea with ⟨x, hx⟩ | ⟨sha, xs, hx⟩
    · subst hx
      obtain ⟨ex, hsea, hevex⟩ := hsc a x hea
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
                   (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb])
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          obtain ⟨ey, hseb, hevey⟩ := hsc b y heb
          -- scalar-scalar andi IS productive: bind scalar (if x!=0&&y!=0 then 1 else 0)
          have hb : evalInstr instr s = s.bind instr.result
              (scalar (if x != 0 && y != 0 then (1:Int) else 0)) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
          · -- StatesFaithful
            simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
              MachineState.lookup, hea, heb, Option.bind_some, SymState.lookup, hsea, hseb]
            apply bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
            simp only [evalExpr, hevex, hevey]
            exact select_and_eq x y
          · rw [evalInstr_preserves_memory_of_ne_store instr s
                (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
                (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
            exact hraw
          · show WFState (evalInstr instr s); rw [hb]
            exact WFState_bind_scalar s instr.result _ hwf
          · show NoFloatState (evalInstr instr s); rw [hb]
            exact NoFloatState_bind_scalar s instr.result _ hnf
        · subst hy
          obtain ⟨gy, hseb, _⟩ := hten b shb ys heb
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hseb])
    · subst hx
      obtain ⟨gx, hsea, _⟩ := hten a sha xs hea
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
                   (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb])
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          obtain ⟨ey, hseb, _⟩ := hsc b y heb
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hseb])
        · subst hy
          refine ⟨andi_tt_step instr a b h_op h_args sha shb xs ys hea heb hfwf', ?_⟩
          by_cases hsh : sha == shb
          · have hb : evalInstr instr s = s.bind instr.result
                (tensor sha ((xs.zip ys).map (fun p => if p.fst != 0 && p.snd != 0 then (1:Int) else 0))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
                Option.bind_some, if_pos hsh]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · have hsh' : (sha == shb) = false := by simpa using hsh
            have hid : evalInstr instr s = s := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
              rw [if_neg (by simp [hsh'])]
            rw [hid]; exact hnf

-- constant_tensor_step_generic: dispatch nullary constant-tensor init into FaithfulWFI.
theorem constant_tensor_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (val : Int) (shape : List Nat)
    (h_op : instr.op = .constant_tensor val shape) (h_args : instr.args = [])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have hb : evalInstr instr s = s.bind instr.result
      (tensor shape (List.replicate (shape.foldl (· * ·) 1) val)) := by
    simp only [evalInstr, evalOp, h_op, h_args]
  refine ⟨⟨⟨constant_tensor_faithful hp hbs hgs hmem hsc hten hnone instr val shape h_op h_args, ?_⟩, ?_⟩, ?_⟩
  · rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, shapeProd, List.length_replicate]
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf

-- load_masked_fill_step_generic: dispatch 3-arg masked load (ptr, mask, fill) into FaithfulWFI.
-- Body's tile loads are 3-arg (fill = zero const tensor). Tensor operands productive; else noop.
theorem load_masked_fill_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p m f : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p, m, f])
    (sh shm shf : List Nat) (addrs masks fills : List Int)
    (h_lp : s.env p = some (tensor sh addrs))
    (h_lm : s.env m = some (tensor shm masks))
    (h_lf : s.env f = some (tensor shf fills))
    (hlenm : addrs.length = masks.length) (hlenf : addrs.length = fills.length)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  refine ⟨load_masked_fill_step instr p m f h_op h_args sh shm shf addrs masks fills
    h_lp h_lm h_lf hlenm hlenf hfwf, ?_⟩
  have hb : evalInstr instr s = s.bind instr.result
      (tensor sh (((addrs.zip masks).zip fills).map
        (fun x => if x.fst.snd != 0 then s.readMem x.fst.fst.natAbs else x.snd))) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lp, h_lm, h_lf, Option.bind_some]
  rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf

-- ── Matmul loop invariant: FaithfulWFI plus the iter-arg tensors' shapes ──────────
-- The scf.for carries three loop vars whose shapes are preserved each iteration:
--   a_ptrs : [64,32], b_ptrs : [32,64], accumulator : [64,64].
-- Recording these lets the body's broadcast/dot ops discharge their compat checks.
-- Matmul loop invariant. Carries:
--   * FaithfulWFI (symbolic tracks concrete, WF, no floats)
--   * the three iter-arg tensor shapes (a_ptrs [M,K], b_ptrs [K,N], accumulator [M,N])
--   * the four LOOP-INVARIANT pre-loop tensors the body reads:
--       amask [1,K] and bmask [K,1]  (cmpi_slt operands building the k-bound masks)
--       afill [M,K] and bfill [K,N]  (3-arg masked-load fill values, constant zero tensors)
-- All are re-established at the end of each iteration (yield copies rebind same-shaped values,
-- and the pre-loop values are never written in the body), so the invariant is inductive.
def MatmulLoopInv (aptr bptr accv amask bmask afill bfill astep : String) (M K N : Nat)
    (c : MachineState) (sc : SymState) (mem : Nat → Int) : Prop :=
  FaithfulWFI c sc mem
  ∧ (∃ vals, c.env aptr = some (tensor [M, K] vals))
  ∧ (∃ vals, c.env bptr = some (tensor [K, N] vals))
  ∧ (∃ vals, c.env accv = some (tensor [M, N] vals))
  ∧ (∃ vals, c.env amask = some (tensor [1, K] vals))
  ∧ (∃ vals, c.env bmask = some (tensor [K, 1] vals))
  ∧ (∃ vals, c.env afill = some (tensor [M, K] vals))
  ∧ (∃ vals, c.env bfill = some (tensor [K, N] vals))
  ∧ (∃ vals, c.env astep = some (tensor [M, K] vals))
  -- loop-invariant scalars the body reads (never written by it)
  ∧ (∃ x, c.env "c32_i32" = some (scalar x))
  ∧ (∃ x, c.env "K" = some (scalar x))
  ∧ (∃ x, c.env "stride_bk" = some (scalar x))

-- forLoop_faithful_wfi: threads the FULL invariant (FaithfulWFI) through the loop,
-- so loop bodies containing dot/broadcast (which need WFState for WFn facts) can dispatch.
theorem forLoop_faithful_wfi (loop : ForLoop) {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hinit : FaithfulWFI s ss mem)
    (hbody : ∀ k, k < loop.trip → ∀ c sc, FaithfulWFI c sc mem →
      FaithfulWFI
        (evalKernel loop.body (c.bind loop.ivName (TritonValue.scalar (Int.ofNat k))))
        (symEvalKernel loop.body (sc.bind loop.ivName (SymValue.scalar (Expr.lit (Int.ofNat k)))))
        mem) :
    FaithfulWFI (evalForLoop loop s) (symEvalForLoop loop ss) mem := by
  unfold evalForLoop symEvalForLoop
  exact loop_faithful_skeleton (fun c sc => FaithfulWFI c sc mem)
    (fun k st => evalKernel loop.body (st.bind loop.ivName (TritonValue.scalar (Int.ofNat k))))
    (fun k st => symEvalKernel loop.body (st.bind loop.ivName (SymValue.scalar (Expr.lit (Int.ofNat k)))))
    loop.trip hbody s ss hinit


theorem prefix_faithful_wfi (K : TritonKernel)
    (hstep : ∀ (instr : TritonInstr), instr ∈ K →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWFI s ss mem →
                FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalKernel K s) (symEvalKernel K ss) mem := by
  induction K generalizing s ss with
  | nil => simpa [evalKernel, symEvalKernel] using h
  | cons instr rest ih =>
      simp only [evalKernel, symEvalKernel, List.foldl]
      exact ih (fun i hi => hstep i (List.mem_cons_of_mem _ hi)) _ _
        (hstep instr (List.mem_cons_self ..) s ss mem h)

theorem kernel_faithful_wfi_terminal_store
    (pre : TritonKernel) (storeInstr : TritonInstr)
    (hpre_step : ∀ (instr : TritonInstr), instr ∈ pre →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWFI s ss mem →
                FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem)
    (hstore : ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWFI s ss mem →
                StatesFaithful (evalInstr storeInstr s) (symEvalInstr storeInstr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWFI s ss mem) :
    StatesFaithful (evalKernel (pre ++ [storeInstr]) s)
                   (symEvalKernel (pre ++ [storeInstr]) ss) mem := by
  rw [evalKernel_append, symEvalKernel_append]
  have hpre := prefix_faithful_wfi pre hpre_step s ss mem h
  simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
  exact hstore _ _ _ hpre


-- ── generic step lemmas: FaithfulWFI preserved from ARBITRARY state ───────────
-- The uniform hstep for the generic fold. Case-splits on operand types; NoFloat
-- makes float cases vacuous; real cases route through the _step lemmas; degenerate
-- (mixed/absent operands) collapse via both_none_preserves_faithfulWF.

theorem muli_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .muli) (h_args : instr.args = [a, b])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hea : s.env a with
  | none =>
    have hsa := hnone a hea
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsa]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind]]
    rw [hid]; exact hnf
  | some va =>
    rcases hnf a va hea with ⟨x, hx⟩ | ⟨sha, xs, hx⟩
    · subst hx
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        obtain ⟨ex, hsea, _⟩ := hsc a x hea
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none, TritonValue.zipWith])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none, TritonValue.zipWith]]
        rw [hid]; exact hnf
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          refine ⟨muli_scalar_step instr a b h_op h_args x y hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (scalar (x * y)) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
              Option.bind_some, TritonValue.zipWith]
          rw [hb]; exact NoFloatState_bind_scalar s instr.result (x*y) hnf
        · subst hy
          obtain ⟨ex, hsea, _⟩ := hsc a x hea
          obtain ⟨gy, hseb, _⟩ := hten b shb ys heb
          refine ⟨both_none_preserves_faithfulWF instr
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, TritonValue.zipWith])
            (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hseb]) hfwf', ?_⟩
          have hid : evalInstr instr s = s := by
            unfold evalInstr; split
            · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            · rw [show evalOp instr.op instr.args s = none from by
                rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, TritonValue.zipWith]]
          rw [hid]; exact hnf
    · subst hx
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        obtain ⟨gx, hsea, _⟩ := hten a sha xs hea
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none, TritonValue.zipWith])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none, TritonValue.zipWith]]
        rw [hid]; exact hnf
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          obtain ⟨gx, hsea, _⟩ := hten a sha xs hea
          obtain ⟨ey, hseb, _⟩ := hsc b y heb
          refine ⟨both_none_preserves_faithfulWF instr
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, TritonValue.zipWith])
            (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hseb]) hfwf', ?_⟩
          have hid : evalInstr instr s = s := by
            unfold evalInstr; split
            · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            · rw [show evalOp instr.op instr.args s = none from by
                rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, TritonValue.zipWith]]
          rw [hid]; exact hnf
        · subst hy
          refine ⟨muli_tt_step instr a b h_op h_args sha shb xs ys hea heb hfwf', ?_⟩
          by_cases hsh : sha == shb
          · have hb : evalInstr instr s = s.bind instr.result
                (tensor sha ((xs.zip ys).map (fun p => p.fst * p.snd))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
                Option.bind_some, TritonValue.zipWith, if_pos hsh]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · have hid : evalInstr instr s = s := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
                Option.bind_some, TritonValue.zipWith]
              rw [if_neg hsh]
            rw [hid]; exact hnf


theorem constant_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (v : Int) (h_op : instr.op = .constant v)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  refine ⟨constant_step instr v h_op hfwf, ?_⟩
  have hb : evalInstr instr s = s.bind instr.result (scalar v) := by
    simp only [evalInstr, h_op, evalOp]
  rw [hb]; exact NoFloatState_bind_scalar s instr.result v hnf

theorem get_program_id_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (h_op : instr.op = .get_program_id 0)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  refine ⟨get_program_id_step instr h_op hfwf, ?_⟩
  have hb : evalInstr instr s
      = s.bind instr.result (scalar (Int.ofNat (if (0:Nat) == 0 then s.pid else s.pid_y))) := by
    simp only [evalInstr, h_op, evalOp]
  rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf

theorem make_range_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (sizeOpt : Option Nat) (h_op : instr.op = .make_range sizeOpt)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  refine ⟨make_range_step instr sizeOpt h_op hfwf, ?_⟩
  have hb : evalInstr instr s
      = s.bind instr.result
          (tensor [sizeOpt.getD s.block_size]
            (List.map Int.ofNat (List.range (sizeOpt.getD s.block_size)))) := by
    simp only [evalInstr, h_op, evalOp]
  rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf


theorem copy_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (v : String)
    (h_op : instr.op = .copy) (h_args : instr.args = [v])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hev : s.env v with
  | none =>
    have hsv := hnone v hev
    have hb : evalInstr instr s = s := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_none]
    have hsb : symEvalInstr instr ss = ss := by
      simp only [symEvalInstr, symEvalOp, h_op, h_args, SymState.lookup, hsv]
    rw [hb, hsb]
    exact ⟨⟨⟨⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩, hraw⟩, hwf⟩, hnf⟩
  | some vv =>
    rcases hnf v vv hev with ⟨x, hx⟩ | ⟨shv, xs, hx⟩
    · subst hx
      obtain ⟨e, hse, heval⟩ := hsc v x hev
      have hb : evalInstr instr s = s.bind instr.result (scalar x) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_some]
      have hsb : symEvalInstr instr ss = ss.bind instr.result (SymValue.scalar e) := by
        simp only [symEvalInstr, symEvalOp, h_op, h_args, SymState.lookup, hse]
      rw [hb, hsb]
      refine ⟨⟨⟨bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result x e heval, ?_⟩,
              WFState_bind_scalar s instr.result x hwf⟩,
              NoFloatState_bind_scalar s instr.result x hnf⟩
      simp only [MachineState.bind]; exact hraw
    · subst hx
      obtain ⟨gx, hsv, hcorr⟩ := hten v shv xs hev
      have hwv : (tensor shv xs).WFn := hwf v shv xs hev
      have hb : evalInstr instr s = s.bind instr.result (tensor shv xs) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_some]
      have hsb : symEvalInstr instr ss = ss.bind instr.result (SymValue.tensor shv gx) := by
        simp only [symEvalInstr, symEvalOp, h_op, h_args, SymState.lookup, hsv]
      rw [hb, hsb]
      refine ⟨⟨⟨bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result shv xs gx hcorr, ?_⟩,
              WFState_bind_tensor s instr.result shv xs hwf hwv⟩,
              NoFloatState_bind_tensor s instr.result shv xs hnf⟩
      simp only [MachineState.bind]; exact hraw

theorem truncf_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (v : String)
    (h_op : instr.op = .truncf) (h_args : instr.args = [v])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hev : s.env v with
  | none =>
    have hsv := hnone v hev
    have hb : evalInstr instr s = s := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_none]
    have hsb : symEvalInstr instr ss = ss := by
      simp only [symEvalInstr, symEvalOp, h_op, h_args, SymState.lookup, hsv]
    rw [hb, hsb]
    exact ⟨⟨⟨⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩, hraw⟩, hwf⟩, hnf⟩
  | some vv =>
    rcases hnf v vv hev with ⟨x, hx⟩ | ⟨shv, xs, hx⟩
    · subst hx
      obtain ⟨e, hse, heval⟩ := hsc v x hev
      have hb : evalInstr instr s = s.bind instr.result (scalar x) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_some]
      have hsb : symEvalInstr instr ss = ss.bind instr.result (SymValue.scalar e) := by
        simp only [symEvalInstr, symEvalOp, h_op, h_args, SymState.lookup, hse]
      rw [hb, hsb]
      refine ⟨⟨⟨bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result x e heval, ?_⟩,
              WFState_bind_scalar s instr.result x hwf⟩,
              NoFloatState_bind_scalar s instr.result x hnf⟩
      simp only [MachineState.bind]; exact hraw
    · subst hx
      obtain ⟨gx, hsv, hcorr⟩ := hten v shv xs hev
      have hwv : (tensor shv xs).WFn := hwf v shv xs hev
      have hb : evalInstr instr s = s.bind instr.result (tensor shv xs) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_some]
      have hsb : symEvalInstr instr ss = ss.bind instr.result (SymValue.tensor shv gx) := by
        simp only [symEvalInstr, symEvalOp, h_op, h_args, SymState.lookup, hsv]
      rw [hb, hsb]
      refine ⟨⟨⟨bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result shv xs gx hcorr, ?_⟩,
              WFState_bind_tensor s instr.result shv xs hwf hwv⟩,
              NoFloatState_bind_tensor s instr.result shv xs hnf⟩
      simp only [MachineState.bind]; exact hraw

theorem splat_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (n : Nat) (v : String)
    (h_op : instr.op = .splat [n]) (h_args : instr.args = [v])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hev : s.env v with
  | none =>
    have hsv := hnone v hev
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsv]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev]]
    rw [hid]; exact hnf
  | some vv =>
    rcases hnf v vv hev with ⟨x, hx⟩ | ⟨shv, xs, hx⟩
    · subst hx
      refine ⟨splat_step instr n v h_op h_args x hev hfwf', ?_⟩
      have hb : evalInstr instr s = s.bind instr.result (tensor [n] (List.replicate n x)) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, List.foldl, Nat.one_mul]
      rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
    · subst hx
      obtain ⟨gx, hsv, _⟩ := hten v shv xs hev
      refine ⟨both_none_preserves_faithfulWF instr
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev])
        (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsv]) hfwf', ?_⟩
      have hid : evalInstr instr s = s := by
        unfold evalInstr; split
        · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        · rw [show evalOp instr.op instr.args s = none from by
            rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev]]
      rw [hid]; exact hnf


-- splat_step_generic_shaped: splat to an ARBITRARY shape (rank-2 needed by matmul body).
-- splat_scalar_faithful is already shape-parametric; this wraps it into FaithfulWFI.
theorem splat_step_generic_shaped
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (shape : List Nat) (v : String)
    (h_op : instr.op = .splat shape) (h_args : instr.args = [v])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hev : s.env v with
  | none =>
    have hsv := hnone v hev
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsv]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev]]
    rw [hid]; exact hnf
  | some vv =>
    rcases hnf v vv hev with ⟨x, hx⟩ | ⟨shv, xs, hx⟩
    · subst hx
      have hb : evalInstr instr s = s.bind instr.result
          (tensor shape (List.replicate (shape.foldl (· * ·) 1) x)) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hev, Option.bind_some]
      refine ⟨⟨⟨splat_scalar_faithful hp hbs hgs hmem hsc hten hnone instr shape v h_op h_args x hev, ?_⟩, ?_⟩, ?_⟩
      · rw [evalInstr_preserves_memory_of_ne_store instr s
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
        exact hraw
      · show WFState (evalInstr instr s)
        rw [hb]
        apply WFState_bind_tensor s instr.result _ _ hwf
        simp only [TritonValue.WFn, shapeProd, List.length_replicate]
      · show NoFloatState (evalInstr instr s)
        rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
    · subst hx
      obtain ⟨gx, hsv, _⟩ := hten v shv xs hev
      refine ⟨both_none_preserves_faithfulWF instr
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev])
        (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsv]) hfwf', ?_⟩
      have hid : evalInstr instr s = s := by
        unfold evalInstr; split
        · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        · rw [show evalOp instr.op instr.args s = none from by
            rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hev]]
      rw [hid]; exact hnf

theorem load_masked_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p m : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p, m])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have noop : ∀ (hev : evalOp instr.op instr.args s = none)
                (hsv : symEvalOp instr.op instr.args ss = none),
      FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
    intro hev hsv
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [hev]
    have hsym : symEvalInstr instr ss = ss := by
      unfold symEvalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [hsv]
    rw [hid, hsym]; exact ⟨hfwf', hnf⟩
  cases hep : s.env p with
  | none =>
    have hsp := hnone p hep
    exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, Option.none_bind])
               (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsp])
  | some vp =>
    rcases hnf p vp hep with ⟨addr, hx⟩ | ⟨sh, addrs, hx⟩
    · subst hx
      obtain ⟨ep, hsep, _⟩ := hsc p addr hep
      cases hem : s.env m with
      | none =>
        have hsm := hnone m hem
        exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, hem, Option.bind_some, Option.bind_none])
                   (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hsm])
      | some vm =>
        rcases hnf m vm hem with ⟨ymk, hy⟩ | ⟨shm, masks, hy⟩
        · subst hy
          obtain ⟨em, hsem, _⟩ := hsc m ymk hem
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, hem, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hsem])
        · subst hy
          obtain ⟨gm, hsem, _⟩ := hten m shm masks hem
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, hem, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hsem])
    · subst hx
      obtain ⟨gp, hsep, _⟩ := hten p sh addrs hep
      cases hem : s.env m with
      | none =>
        have hsm := hnone m hem
        exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, hem, Option.bind_some, Option.bind_none])
                   (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hsm])
      | some vm =>
        rcases hnf m vm hem with ⟨ymk, hy⟩ | ⟨shm, masks, hy⟩
        · subst hy
          obtain ⟨em, hsem, _⟩ := hsc m ymk hem
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, hem, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hsem])
        · subst hy
          obtain ⟨gm, hsem, _⟩ := hten m shm masks hem
          by_cases hshm : sh == shm
          · -- shapes match: productive masked load
            have hsheq : sh = shm := by simpa using hshm
            refine ⟨load_masked_step instr p m h_op h_args sh shm addrs masks hep hem hsheq hfwf', ?_⟩
            have hb : evalInstr instr s = s.bind instr.result
                (tensor sh ((addrs.zip masks).map (fun x => if x.snd != 0 then s.readMem x.fst.natAbs else 0))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, hem, Option.bind_some,
                hshm, if_true]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · -- shapes mismatch: guarded masked load no-ops on both sides
            have hshmb : (sh == shm) = false := by simpa using hshm
            exact noop
              (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, hem,
                    Option.bind_some, hshmb, Bool.false_eq_true, ↓reduceIte])
              (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hsem,
                    hshmb, Bool.false_eq_true, ↓reduceIte])

theorem load_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hep : s.env p with
  | none =>
    have hsp := hnone p hep
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsp, List.head?, Option.getD]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep]]
    rw [hid]; exact hnf
  | some vp =>
    rcases hnf p vp hep with ⟨addr, hx⟩ | ⟨sh, addrs, hx⟩
    · subst hx
      refine ⟨load_scalar_step instr p h_op h_args addr hep hfwf', ?_⟩
      have hb : evalInstr instr s = s.bind instr.result (scalar (s.readMem addr.natAbs)) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, Option.bind_some]
      rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf
    · subst hx
      refine ⟨load_step instr p h_op h_args sh addrs hep hfwf', ?_⟩
      have hb : evalInstr instr s
          = s.bind instr.result (tensor sh (addrs.map fun a => s.readMem a.natAbs)) := by
        simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, Option.bind_some]
      rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf


theorem cmpi_slt_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .cmpi_slt) (h_args : instr.args = [a, b])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  have noop : ∀ (hev : evalOp instr.op instr.args s = none)
                (hsv : symEvalOp instr.op instr.args ss = none),
      FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
    intro hev hsv
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [hev]
    have hsym : symEvalInstr instr ss = ss := by
      unfold symEvalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [hsv]
    rw [hid, hsym]; exact ⟨hfwf', hnf⟩
  cases hea : s.env a with
  | none =>
    have hsa := hnone a hea
    exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind])
               (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsa])
  | some va =>
    rcases hnf a va hea with ⟨x, hx⟩ | ⟨sha, xs, hx⟩
    · subst hx
      obtain ⟨ex, hsea, _⟩ := hsc a x hea
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
                   (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb])
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          refine ⟨cmpi_slt_ss_step instr a b h_op h_args x y hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (scalar (if x < y then 1 else 0)) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf
        · subst hy
          obtain ⟨gy, hseb, _⟩ := hten b shb ys heb
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hseb])
    · subst hx
      obtain ⟨gx, hsea, _⟩ := hten a sha xs hea
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
                   (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb])
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          obtain ⟨ey, hseb, _⟩ := hsc b y heb
          exact noop (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some])
                     (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hseb])
        · subst hy
          refine ⟨cmpi_slt_tt_step instr a b h_op h_args sha shb xs ys hea heb hfwf', ?_⟩
          by_cases hsh : sha == shb
          · have hb : evalInstr instr s = s.bind instr.result
                (tensor sha ((xs.zip ys).map (fun p => if p.fst < p.snd then (1:Int) else 0))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
                Option.bind_some, if_pos hsh]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · have hsh' : (sha == shb) = false := by simpa using hsh
            have hid : evalInstr instr s = s := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
              rw [if_neg (by simp [hsh'])]
            rw [hid]; exact hnf

theorem addi_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addi) (h_args : instr.args = [a, b])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hea : s.env a with
  | none =>
    have hsa := hnone a hea
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsa, symAdd]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind]]
    rw [hid]; exact hnf
  | some va =>
    rcases hnf a va hea with ⟨x, hx⟩ | ⟨sha, xs, hx⟩
    · subst hx
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        obtain ⟨ex, hsea, _⟩ := hsc a x hea
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb, symAdd]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none]]
        rw [hid]; exact hnf
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          refine ⟨addi_ss_step instr a b h_op h_args x y hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (scalar (x + y)) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf
        · subst hy
          refine ⟨addi_st_step instr a b h_op h_args x shb ys hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (tensor shb (ys.map (· + x))) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
    · subst hx
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        obtain ⟨gx, hsea, _⟩ := hten a sha xs hea
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb, symAdd]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none]]
        rw [hid]; exact hnf
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          refine ⟨addi_ts_step instr a b h_op h_args sha xs y hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (tensor sha (xs.map (· + y))) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
        · subst hy
          refine ⟨addi_step instr a b h_op h_args sha shb xs ys hea heb hfwf', ?_⟩
          by_cases hsh : sha == shb
          · have hb : evalInstr instr s = s.bind instr.result
                (tensor sha ((xs.zip ys).map (fun p => p.fst + p.snd))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
                Option.bind_some, if_pos hsh]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · have hid : evalInstr instr s = s := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
              rw [if_neg hsh]
            rw [hid]; exact hnf

theorem addf_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (a b : String)
    (h_op : instr.op = .addf) (h_args : instr.args = [a, b])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hea : s.env a with
  | none =>
    have hsa := hnone a hea
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsa, symAdd]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, Option.none_bind]]
    rw [hid]; exact hnf
  | some va =>
    rcases hnf a va hea with ⟨x, hx⟩ | ⟨sha, xs, hx⟩
    · subst hx
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        obtain ⟨ex, hsea, _⟩ := hsc a x hea
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb, symAdd]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none]]
        rw [hid]; exact hnf
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          refine ⟨addf_ss_step instr a b h_op h_args x y hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (scalar (x + y)) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf
        · subst hy
          refine ⟨addf_st_step instr a b h_op h_args x shb ys hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (tensor shb (ys.map (· + x))) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
    · subst hx
      cases heb : s.env b with
      | none =>
        have hsb := hnone b heb
        obtain ⟨gx, hsea, _⟩ := hten a sha xs hea
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsea, hsb, symAdd]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hea, heb, Option.bind_some, Option.bind_none]]
        rw [hid]; exact hnf
      | some vb =>
        rcases hnf b vb heb with ⟨y, hy⟩ | ⟨shb, ys, hy⟩
        · subst hy
          refine ⟨addf_ts_step instr a b h_op h_args sha xs y hea heb hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (tensor sha (xs.map (· + y))) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
        · subst hy
          refine ⟨addf_step instr a b h_op h_args sha shb xs ys hea heb hfwf', ?_⟩
          by_cases hsh : sha == shb
          · have hb : evalInstr instr s = s.bind instr.result
                (tensor sha ((xs.zip ys).map (fun p => p.fst + p.snd))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb,
                Option.bind_some, if_pos hsh]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · have hid : evalInstr instr s = s := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hea, heb, Option.bind_some]
              rw [if_neg hsh]
            rw [hid]; exact hnf


theorem addptr_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (p o : String)
    (h_op : instr.op = .addptr) (h_args : instr.args = [p, o])
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  have hfwf' := hfwf
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  cases hep : s.env p with
  | none =>
    have hsp := hnone p hep
    refine ⟨both_none_preserves_faithfulWF instr
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, Option.none_bind])
      (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsp]) hfwf', ?_⟩
    have hid : evalInstr instr s = s := by
      unfold evalInstr; split
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
      · rw [show evalOp instr.op instr.args s = none from by
          rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, Option.none_bind]]
    rw [hid]; exact hnf
  | some vp =>
    rcases hnf p vp hep with ⟨base, hx⟩ | ⟨shp, bases, hx⟩
    · subst hx
      cases heo : s.env o with
      | none =>
        have hso := hnone o heo
        obtain ⟨ep, hsep, _⟩ := hsc p base hep
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, heo, Option.bind_some, Option.bind_none])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hso]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, heo, Option.bind_some, Option.bind_none]]
        rw [hid]; exact hnf
      | some vo =>
        rcases hnf o vo heo with ⟨off, hy⟩ | ⟨sho, offs, hy⟩
        · subst hy
          refine ⟨addptr_ss_step instr p o h_op h_args base off hep heo hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (scalar (base + off)) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, heo, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_scalar s instr.result _ hnf
        · subst hy
          refine ⟨addptr_step instr p o h_op h_args base sho offs hep heo hfwf', ?_⟩
          have hb : evalInstr instr s = s.bind instr.result (tensor sho (offs.map (· + base))) := by
            simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, heo, Option.bind_some]
          rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
    · subst hx
      cases heo : s.env o with
      | none =>
        have hso := hnone o heo
        obtain ⟨gp, hsep, _⟩ := hten p shp bases hep
        refine ⟨both_none_preserves_faithfulWF instr
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, heo, Option.bind_some, Option.bind_none])
          (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hso]) hfwf', ?_⟩
        have hid : evalInstr instr s = s := by
          unfold evalInstr; split
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
          · rw [show evalOp instr.op instr.args s = none from by
              rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, heo, Option.bind_some, Option.bind_none]]
        rw [hid]; exact hnf
      | some vo =>
        rcases hnf o vo heo with ⟨off, hy⟩ | ⟨sho, offs, hy⟩
        · subst hy
          obtain ⟨gp, hsep, _⟩ := hten p shp bases hep
          obtain ⟨eo, hseo, _⟩ := hsc o off heo
          refine ⟨both_none_preserves_faithfulWF instr
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            (by rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, heo, Option.bind_some])
            (by rw [h_op, h_args]; simp only [symEvalOp, SymState.lookup, hsep, hseo]) hfwf', ?_⟩
          have hid : evalInstr instr s = s := by
            unfold evalInstr; split
            · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            · exact absurd (by assumption) (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
            · rw [show evalOp instr.op instr.args s = none from by
                rw [h_op, h_args]; simp only [evalOp, MachineState.lookup, hep, heo, Option.bind_some]]
          rw [hid]; exact hnf
        · subst hy
          refine ⟨addptr_tt_step instr p o h_op h_args shp sho bases offs hep heo hfwf', ?_⟩
          by_cases hsh : shp == sho
          · have hb : evalInstr instr s = s.bind instr.result
                (tensor shp ((bases.zip offs).map (fun q => q.fst + q.snd))) := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, heo,
                Option.bind_some, if_pos hsh]
            rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf
          · have hid : evalInstr instr s = s := by
              simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, hep, heo, Option.bind_some]
              rw [if_neg hsh]
            rw [hid]; exact hnf


-- ── backward faithfulness: symbolic tensor -> concrete tensor (via NoFloat) ────
-- StatesFaithful relates concrete->symbolic; this recovers the reverse for tensors
-- by elimination (concrete can't be none/scalar without forcing symbolic to match;
-- float ruled out by NoFloat). Used to extract store operands from the computable
-- symbolic post-prefix state.

-- ══════════════════════════════════════════════════════════════════════════════
-- GENERIC OP-DISPATCHER: verify any kernel of supported ops with NO per-kernel proof.
-- InstrSupported encodes the ten supported op+arg patterns; generic_step dispatches to the
-- matching *_step_generic. Decidable, so "∀ instr ∈ K, InstrSupported instr" is discharged by
-- `decide` on a concrete parsed kernel — replacing hand-written per-kernel hstep FOREVER.
-- ══════════════════════════════════════════════════════════════════════════════
def instrSupported (instr : TritonInstr) : Bool :=
  match instr.op, instr.args with
  | .constant _, _ => true
  | .get_program_id 0, _ => true
  | .muli, [_, _] => true
  | .make_range _, _ => true
  | .splat [_], [_] => true
  | .addi, [_, _] => true
  | .addf, [_, _] => true
  | .addptr, [_, _] => true
  | .cmpi_slt, [_, _] => true
  | .load, [_] => true
  | .load, [_, _] => true
  | .copy, [_] => true
  | _, _ => false

theorem generic_step
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr)
    (hsupp : instrSupported instr = true)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  unfold instrSupported at hsupp
  split at hsupp <;>
    first
    | exact constant_step_generic instr _ (by assumption) h
    | exact get_program_id_step_generic instr (by assumption) h
    | exact muli_step_generic instr _ _ (by assumption) (by assumption) h
    | exact make_range_step_generic instr _ (by assumption) h
    | exact splat_step_generic instr _ _ (by assumption) (by assumption) h
    | exact addi_step_generic instr _ _ (by assumption) (by assumption) h
    | exact addf_step_generic instr _ _ (by assumption) (by assumption) h
    | exact addptr_step_generic instr _ _ (by assumption) (by assumption) h
    | exact cmpi_slt_step_generic instr _ _ (by assumption) (by assumption) h
    | exact load_step_generic instr _ (by assumption) (by assumption) h
    | exact load_masked_step_generic instr _ _ (by assumption) (by assumption) h
    | exact copy_step_generic instr _ (by assumption) (by assumption) h
    | exact absurd hsupp (by simp)

-- KERNEL DRIVER: any kernel whose instructions are ALL supported preserves FaithfulWFI.
-- The premise (K.all instrSupported = true) is machine-checkable by native_decide on a concrete
-- parsed kernel — so verifying a new .ttir needs NO new Lean proof, just this driver + decide.
theorem kernel_faithful_of_supported (K : TritonKernel)
    (hall : K.all instrSupported = true)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalKernel K s) (symEvalKernel K ss) mem := by
  apply prefix_faithful_wfi K _ s ss mem h
  intro instr hmem_instr s' ss' mem' hf
  have hsupp : instrSupported instr = true := by
    rw [List.all_eq_true] at hall
    exact hall instr hmem_instr
  exact generic_step instr hsupp hf

-- TOP-LEVEL VERIFICATION: any kernel that splits as (supported prefix) ++ [faithful store] is
-- sound. hpre_all is native_decide-able on a concrete parsed kernel; hstore is supplied by
-- store_tensor_masked_faithful (masked) or store_tensor_faithful_when_memory_unchanged (unmasked).
-- The PREFIX needs NO per-kernel proof — generic_step dispatches every supported instruction.
-- This is the "verify any .ttir without writing a new proof" entry point.
theorem verify_kernel
    (pre : TritonKernel) (storeInstr : TritonInstr)
    (hpre_all : pre.all instrSupported = true)
    (hstore : ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                FaithfulWFI s ss mem →
                StatesFaithful (evalInstr storeInstr s) (symEvalInstr storeInstr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : FaithfulWFI s ss mem) :
    StatesFaithful (evalKernel (pre ++ [storeInstr]) s)
                   (symEvalKernel (pre ++ [storeInstr]) ss) mem := by
  apply kernel_faithful_wfi_terminal_store pre storeInstr _ hstore s ss mem h
  intro instr hmem_instr s' ss' mem' hf
  have hsupp : instrSupported instr = true := by
    rw [List.all_eq_true] at hpre_all
    exact hpre_all instr hmem_instr
  exact generic_step instr hsupp hf

-- ── Generic store-concreteness: decidable check that a named symbolic tensor is all-concrete ──
def symTensorAllConcrete (ss : SymState) (name : String) (n : Nat) : Bool :=
  match ss.env name with
  | some (SymValue.tensor k g) => (k == [n]) && (List.range n).all (fun j => (g j).isConcrete)
  | _ => false

theorem symTensorAllConcrete_elim (ss : SymState) (name : String) (n : Nat)
    (hchk : symTensorAllConcrete ss name n = true) :
    ∃ g, ss.env name = some (SymValue.tensor [n] g) ∧ ∀ i, i < n → (g i).isConcrete = true := by
  unfold symTensorAllConcrete at hchk
  cases hc : ss.env name with
  | none => rw [hc] at hchk; simp at hchk
  | some val =>
    cases val with
    | scalar x => rw [hc] at hchk; simp at hchk
    | fscalar x => rw [hc] at hchk; simp at hchk
    | ftensor _ _ => rw [hc] at hchk; simp at hchk
    | tensor k g =>
      rw [hc] at hchk
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hchk
      obtain ⟨hk, hall⟩ := hchk
      subst hk
      exact ⟨g, rfl, fun i hi => hall i hi⟩

theorem faithful_tensor_backward
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (h : StatesFaithful s ss mem) (hnf : NoFloatState s)
    (v : String) (n : Nat) (g : Nat → Expr)
    (hsv : ss.env v = some (SymValue.tensor [n] g)) :
    ∃ sh vals, s.env v = some (tensor sh vals) := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  cases hev : s.env v with
  | none =>
    rw [hnone v hev] at hsv; exact absurd hsv (by simp)
  | some cv =>
    rcases hnf v cv hev with ⟨x, hx⟩ | ⟨sh, vals, hx⟩
    · subst hx
      obtain ⟨e, hse, _⟩ := hsc v x hev
      rw [hse] at hsv; exact absurd hsv (by simp)
    · subst hx; exact ⟨sh, vals, rfl⟩


-- ── extract a symbolic tensor binding from a decidable shape fact ─────────────
-- SymValue has exactly two constructors (scalar | tensor). Given a native_decide-able
-- fact that env[name] is a tensor of length `len`, recover the binding with a named
-- symbolic function g. Used to obtain store operands from the closed post-prefix state.

theorem extract_tensor (ss : SymState) (name : String) (len : Nat)
    (hfact : (match ss.env name with | some (SymValue.tensor n _) => n == [len] | _ => false) = true) :
    ∃ g, ss.env name = some (SymValue.tensor [len] g) := by
  cases hc : ss.env name with
  | none => rw [hc] at hfact; simp at hfact
  | some v =>
    cases v with
    | scalar x => rw [hc] at hfact; simp at hfact
    | fscalar x => rw [hc] at hfact; simp at hfact
    | ftensor _ _ => rw [hc] at hfact; simp at hfact
    | tensor n g =>
      rw [hc] at hfact
      simp only [beq_iff_eq] at hfact
      subst hfact
      exact ⟨g, rfl⟩


#check @symEval_sound

-- THE BRIDGE: from FaithfulWFI + decidable concreteness of the store's pointer/value/mask operands,
-- produce terminal-store faithfulness. Generic over operand names — NO per-kernel proof. The
-- ── Broadcast compatibility (typed-dispatch, mirrors symTensorAllConcrete) ──
-- Reads v's recorded rank-2 shape [s0,s1] from the symbolic state and checks that
-- broadcasting to [t0,t1] is valid (each dim matches or source dim is 1) and positive.
def broadcastCompatible (ss : SymState) (v : String) (t0 t1 : Nat) : Bool :=
  match ss.env v with
  | some (SymValue.tensor k _) =>
      match k with
      | [s0, s1] => ((t0 == s0) || (s0 == 1)) && ((t1 == s1) || (s1 == 1)) && (0 < s0) && (0 < s1)
      | _ => false
  | _ => false

theorem broadcastCompatible_elim (ss : SymState) (v : String) (t0 t1 : Nat)
    (hchk : broadcastCompatible ss v t0 t1 = true) :
    ∃ s0 s1 g, ss.env v = some (SymValue.tensor [s0, s1] g)
      ∧ 0 < s0 ∧ 0 < s1 ∧ (t0 = s0 ∨ s0 = 1) ∧ (t1 = s1 ∨ s1 = 1) := by
  unfold broadcastCompatible at hchk
  cases hc : ss.env v with
  | none => rw [hc] at hchk; simp at hchk
  | some val =>
    cases val with
    | scalar x => rw [hc] at hchk; simp at hchk
    | fscalar x => rw [hc] at hchk; simp at hchk
    | ftensor _ _ => rw [hc] at hchk; simp at hchk
    | tensor k g =>
      rw [hc] at hchk
      cases k with
      | nil => simp at hchk
      | cons s0 rest =>
        cases rest with
        | nil => simp at hchk
        | cons s1 rest2 =>
          cases rest2 with
          | cons _ _ => simp at hchk
          | nil =>
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
              decide_eq_true_eq, Nat.lt_iff_add_one_le] at hchk
            obtain ⟨⟨⟨ht0, ht1⟩, hs0⟩, hs1⟩ := hchk
            refine ⟨s0, s1, g, rfl, ?_, ?_, ?_, ?_⟩
            · omega
            · omega
            · exact ht0
            · exact ht1

-- broadcast_step_generic: dispatches a compatible rank-2 broadcast into FaithfulWFI.
-- Compatibility (positivity + dim-match) is supplied as concrete hypotheses; the checker
-- discharges them by native_decide on the parsed kernel's concrete shapes.
theorem broadcast_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (t0 t1 : Nat) (v : String)
    (h_op : instr.op = .broadcast [t0, t1]) (h_args : instr.args = [v])
    (s0 s1 : Nat) (vals : List Int)
    (h_lv : s.env v = some (tensor [s0, s1] vals))
    (hs0 : 0 < s0) (hs1 : 0 < s1)
    (ht0 : t0 = s0 ∨ s0 = 1) (ht1 : t1 = s1 ∨ s1 = 1)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  have hwfn : (tensor [s0, s1] vals).WFn := hwf v [s0, s1] vals h_lv
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- StatesFaithful of the result
    refine ⟨broadcast_faithful hsf instr s0 s1 t0 t1 v h_op h_args vals h_lv hwfn hs0 hs1 ht0 ht1, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · -- WFState of the result
    show WFState (evalInstr instr s)
    obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
    obtain ⟨g, hsg, hcorr⟩ := hten v [s0, s1] vals h_lv
    have hb : evalInstr instr s = s.bind instr.result
        (tensor [t0, t1] ((List.range (t0 * t1)).map (fun i =>
          vals.getD ((if s0 == 1 then 0 else i / t1) * s1 + (if s1 == 1 then 0 else i % t1)) 0))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lv, Option.bind_some]
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, shapeProd, List.foldl, Nat.one_mul,
      List.length_map, List.length_range]
  · -- NoFloatState of the result
    show NoFloatState (evalInstr instr s)
    have hb : evalInstr instr s = s.bind instr.result
        (tensor [t0, t1] ((List.range (t0 * t1)).map (fun i =>
          vals.getD ((if s0 == 1 then 0 else i / t1) * s1 + (if s1 == 1 then 0 else i % t1)) 0))) := by
      simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lv, Option.bind_some]
    rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf

-- expand_dims_step_generic: inserts a size-1 axis; data unchanged, shapeProd preserved.
-- Unconditional (any tensor can gain a size-1 axis), like copy.
theorem expand_dims_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (axis : Nat) (v : String)
    (h_op : instr.op = .expand_dims axis) (h_args : instr.args = [v])
    (sh : List Nat) (vals : List Int)
    (h_lv : s.env v = some (tensor sh vals))
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  have hwfn : (tensor sh vals).WFn := hwf v sh vals h_lv
  have hshlen : shapeProd sh = vals.length := WFn_tensor_len sh vals hwfn
  have hb : evalInstr instr s = s.bind instr.result
      (tensor (sh.take axis ++ [1] ++ sh.drop axis) vals) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_lv, Option.bind_some]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- StatesFaithful
    refine ⟨expand_dims_faithful hsf instr axis v h_op h_args sh vals h_lv, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · -- WFState
    show WFState (evalInstr instr s)
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    show shapeProd (sh.take axis ++ [1] ++ sh.drop axis) = vals.length
    rw [← hshlen]
    simp only [shapeProd, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.mul_one]
    rw [← List.foldl_append, List.take_append_drop]
  · -- NoFloatState
    show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf

-- dotCompatible: reads a,b,acc recorded shapes; checks a=[m,k], b=[k,n], acc=[m,n] align + 0<n.
def dotCompatible (ss : SymState) (a b acc : String) : Bool :=
  match ss.env a, ss.env b, ss.env acc with
  | some (SymValue.tensor sa _), some (SymValue.tensor sb _), some (SymValue.tensor sc _) =>
      match sa, sb, sc with
      | [m, k1], [k2, n], [m2, n2] =>
          (k1 == k2) && (m == m2) && (n == n2) && (0 < n)
      | _, _, _ => false
  | _, _, _ => false

theorem dotCompatible_elim (ss : SymState) (a b acc : String)
    (hchk : dotCompatible ss a b acc = true) :
    ∃ m k1 n gA gB gAcc,
      ss.env a = some (SymValue.tensor [m, k1] gA)
      ∧ ss.env b = some (SymValue.tensor [k1, n] gB)
      ∧ ss.env acc = some (SymValue.tensor [m, n] gAcc)
      ∧ 0 < n := by
  unfold dotCompatible at hchk
  cases hca : ss.env a with
  | none => rw [hca] at hchk; simp at hchk
  | some va =>
    cases hcb : ss.env b with
    | none => rw [hca, hcb] at hchk; simp at hchk
    | some vb =>
      cases hcc : ss.env acc with
      | none => rw [hca, hcb, hcc] at hchk; simp at hchk
      | some vc =>
        cases va with
        | scalar _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | fscalar _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | ftensor _ _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | tensor sa gA =>
        cases vb with
        | scalar _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | fscalar _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | ftensor _ _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | tensor sb gB =>
        cases vc with
        | scalar _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | fscalar _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | ftensor _ _ => rw [hca, hcb, hcc] at hchk; simp at hchk
        | tensor sc gAcc =>
          rw [hca, hcb, hcc] at hchk
          match sa, sb, sc, hchk with
          | [m, k1], [k2, n], [m2, n2], hchk =>
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
            obtain ⟨⟨⟨hk, hm⟩, hn⟩, hnpos⟩ := hchk
            subst hk; subst hm; subst hn
            exact ⟨m, k1, n, gA, gB, gAcc, rfl, rfl, rfl, hnpos⟩
          | [], _, _, hchk => simp at hchk
          | _::_::_::_, _, _, hchk => simp at hchk
          | [_], _, _, hchk => simp at hchk
          | _, [], _, hchk => simp at hchk
          | _, [_], _, hchk => simp at hchk
          | _, _::_::_::_, _, hchk => simp at hchk
          | _, _, [], hchk => simp at hchk
          | _, _, [_], hchk => simp at hchk
          | _, _, _::_::_::_, hchk => simp at hchk

-- dot_step_generic: matmul-with-accumulator dispatch into FaithfulWFI.
-- Shapes a=[m,k1], b=[k1,n], acc=[m,n] supplied as hypotheses (checker native_decides them).
theorem dot_step_generic
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr) (m k1 n : Nat) (a b acc : String)
    (h_op : instr.op = .dot) (h_args : instr.args = [a, b, acc])
    (valsA valsB valsAcc : List Int)
    (h_la : s.env a = some (tensor [m, k1] valsA))
    (h_lb : s.env b = some (tensor [k1, n] valsB))
    (h_lacc : s.env acc = some (tensor [m, n] valsAcc))
    (hnpos : 0 < n)
    (h : FaithfulWFI s ss mem) :
    FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hfwf, hnf⟩ := h
  obtain ⟨hsfm, hwf⟩ := hfwf
  obtain ⟨hsf, hraw⟩ := hsfm
  have hwfA : (tensor [m, k1] valsA).WFn := hwf a [m, k1] valsA h_la
  have hwfB : (tensor [k1, n] valsB).WFn := hwf b [k1, n] valsB h_lb
  have hwfAcc : (tensor [m, n] valsAcc).WFn := hwf acc [m, n] valsAcc h_lacc
  have hb : evalInstr instr s = s.bind instr.result
      (tensor [m, n] ((List.range (m * n)).map fun idx =>
        let i := idx / n; let j := idx % n
        ((List.range k1).foldl (fun acc' kk =>
          acc' + (valsA.getD (i * k1 + kk) 0) * (valsB.getD (kk * n + j) 0)) 0)
        + ((some valsAcc).map (·.getD idx 0)).getD 0)) := by
    simp only [evalInstr, evalOp, h_op, h_args, MachineState.lookup, h_la, h_lb, h_lacc,
      Option.bind_some, bne_self_eq_false, Bool.false_eq_true, if_false, ↓reduceIte]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨dot_faithful_acc hsf instr m k1 n a b acc h_op h_args valsA valsB valsAcc
      h_la h_lb h_lacc hwfA hwfB hwfAcc hnpos, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)
        (by rw [h_op]; exact fun hc => TritonOp.noConfusion hc)]
    exact hraw
  · show WFState (evalInstr instr s)
    rw [hb]
    apply WFState_bind_tensor s instr.result _ _ hwf
    simp only [TritonValue.WFn, shapeProd, List.foldl, Nat.one_mul,
      List.length_map, List.length_range]
  · show NoFloatState (evalInstr instr s)
    rw [hb]; exact NoFloatState_bind_tensor s instr.result _ _ hnf

-- concreteness checks (symTensorAllConcrete) are native_decide-able on a concrete parsed kernel.
theorem masked_store_faithful_of_concrete
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (storeInstr : TritonInstr) (p v m : String)
    (h_op : storeInstr.op = .store) (h_args : storeInstr.args = [p, v, m])
    (n : Nat)
    (hf : FaithfulWFI s ss mem)
    (hpc : symTensorAllConcrete ss p n = true)
    (hmc : symTensorAllConcrete ss m n = true)
    (hvfact : (match ss.env v with | some (SymValue.tensor k _) => k == [n] | _ => false) = true) :
    StatesFaithful (evalInstr storeInstr s) (symEvalInstr storeInstr ss) mem := by
  obtain ⟨⟨⟨hsf, hraw⟩, hwf⟩, hnf⟩ := hf
  obtain ⟨hp, hbs, hgs, hmem_f, hsc, hten, hnone⟩ := hsf
  obtain ⟨gp, hgp_sym, hgp_conc⟩ := symTensorAllConcrete_elim ss p n hpc
  obtain ⟨gm, hgm_sym, hgm_conc⟩ := symTensorAllConcrete_elim ss m n hmc
  obtain ⟨gv, hgv_sym⟩ := extract_tensor ss v n hvfact
  have hsf' : StatesFaithful s ss mem := ⟨hp, hbs, hgs, hmem_f, hsc, hten, hnone⟩
  obtain ⟨shp, addrs, hp_con⟩ := faithful_tensor_backward hsf' hnf p n gp hgp_sym
  obtain ⟨shm, masks, hm_con⟩ := faithful_tensor_backward hsf' hnf m n gm hgm_sym
  obtain ⟨shv, vals, hv_con⟩ := faithful_tensor_backward hsf' hnf v n gv hgv_sym
  obtain ⟨gp', hgp'_sym, hgp'_corr⟩ := hten p shp addrs hp_con
  obtain ⟨gm', hgm'_sym, hgm'_corr⟩ := hten m shm masks hm_con
  obtain ⟨gv', hgv'_sym, hgv'_corr⟩ := hten v shv vals hv_con
  have hpt := Option.some.inj (hgp_sym.symm.trans hgp'_sym)
  injection hpt with hlp_shape hgp_eq
  have hmt := Option.some.inj (hgm_sym.symm.trans hgm'_sym)
  injection hmt with hlm_shape hgm_eq
  have hvt := Option.some.inj (hgv_sym.symm.trans hgv'_sym)
  injection hvt with hlv_shape hgv_eq
  -- hlp_shape : [n] = shp, etc. Recover n = length via WFn (shapeProd shp = addrs.length).
  have hp_wfn : shapeProd shp = addrs.length := WFn_tensor_len shp addrs (hwf p shp addrs hp_con)
  have hm_wfn : shapeProd shm = masks.length := WFn_tensor_len shm masks (hwf m shm masks hm_con)
  have hv_wfn : shapeProd shv = vals.length := WFn_tensor_len shv vals (hwf v shv vals hv_con)
  have hlp_eq : n = addrs.length := by rw [← hp_wfn, ← hlp_shape]; simp [shapeProd]
  have hlm_eq : n = masks.length := by rw [← hm_wfn, ← hlm_shape]; simp [shapeProd]
  have hlv_eq : n = vals.length := by rw [← hv_wfn, ← hlv_shape]; simp [shapeProd]
  have hav : addrs.length = vals.length := by rw [← hlp_eq, ← hlv_eq]
  have ham : addrs.length = masks.length := by rw [← hlp_eq, ← hlm_eq]
  apply store_tensor_masked_faithful hp hbs hgs hmem_f hsc hten hnone
    storeInstr p v m h_op h_args shp shv shm addrs vals masks hp_con hv_con hm_con hav ham
    hp_wfn gp' gv' gm' hgp'_sym hgv'_sym hgm'_sym
  · intro i hi
    rw [← hgp_eq]; exact hgp_conc i (by rw [hlp_eq]; exact hi)
  · intro i hi
    rw [← hgm_eq]; exact hgm_conc i (by rw [hlp_eq]; exact hi)
  · intro i hi; exact hgp'_corr i hi
  · intro i hi; rw [hav] at hi; exact hgv'_corr i hi
  · intro i hi; rw [ham] at hi; exact hgm'_corr i hi

-- ══════════════════════════════════════════════════════════════════════════════
-- ★ THE ONE COMMAND ★ verify_kernel_masked: a masked kernel (pre ++ [store]) is faithful for ALL
-- inputs when two DECIDABLE checks pass — pre.all instrSupported, and the store's operands concrete
-- at the post-prefix state. Both native_decide-able. NO per-kernel proof.
-- ══════════════════════════════════════════════════════════════════════════════
theorem verify_kernel_masked
    (pre : TritonKernel) (storeInstr : TritonInstr) (p val m : String) (n : Nat)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h_op : storeInstr.op = .store) (h_args : storeInstr.args = [p, val, m])
    (hpre_all : pre.all instrSupported = true)
    (hpc : symTensorAllConcrete (symEvalKernel pre ss) p n = true)
    (hmc : symTensorAllConcrete (symEvalKernel pre ss) m n = true)
    (hvfact : (match (symEvalKernel pre ss).env val with | some (SymValue.tensor k _) => k == [n] | _ => false) = true)
    (h : FaithfulWFI s ss mem) :
    StatesFaithful (evalKernel (pre ++ [storeInstr]) s)
                   (symEvalKernel (pre ++ [storeInstr]) ss) mem := by
  have hpre_step : ∀ (instr : TritonInstr), instr ∈ pre →
      ∀ (s' : MachineState) (ss' : SymState) (mem' : Nat → Int),
        FaithfulWFI s' ss' mem' →
        FaithfulWFI (evalInstr instr s') (symEvalInstr instr ss') mem' := by
    intro instr hmem_instr s' ss' mem' hf
    have hsupp : instrSupported instr = true := by
      rw [List.all_eq_true] at hpre_all; exact hpre_all instr hmem_instr
    exact generic_step instr hsupp hf
  have hpost : FaithfulWFI (evalKernel pre s) (symEvalKernel pre ss) mem :=
    prefix_faithful_wfi pre hpre_step s ss mem h
  rw [evalKernel_append, symEvalKernel_append]
  simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
  exact masked_store_faithful_of_concrete storeInstr p val m h_op h_args n hpost hpc hmc hvfact

-- ── Body walk segment 1: steps 1-4 (muli, subi, splat[1,K], cmpi_slt) ───────────
-- Threads FaithfulWFI through 4 steps and produces the shape fact for a_52 : [1,Kd],
-- which is the operand of the first broadcast (step 5).
theorem matmul_body_seg1
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Kd : Nat)
    (xk xc xK : Int)
    (hk   : c.env "k" = some (scalar xk))
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (amvals : List Int) (hamask : c.env "a_ptrs_18" = some (tensor [1, Kd] amvals))
    (hlen_am : amvals.length = 1 * Kd)
    (hfw : FaithfulWFI c sc mem) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    FaithfulWFI (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c))))
                (symEvalInstr I4 (symEvalInstr I3 (symEvalInstr I2 (symEvalInstr I1 sc)))) mem
    ∧ ∃ vals, (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c)))).env "a_52"
                = some (tensor [1, Kd] vals) := by
  intro I1 I2 I3 I4
  -- step 1: muli  (a := k * c32_i32), scalar
  have f1 : FaithfulWFI (evalInstr I1 c) (symEvalInstr I1 sc) mem :=
    muli_step_generic I1 "k" "c32_i32" rfl rfl hfw
  have e1_a : (evalInstr I1 c).env "a" = some (scalar (xk * xc)) :=
    muli_binds c "a" "k" "c32_i32" xk xc hk hc32
  have e1_K : (evalInstr I1 c).env "K" = some (scalar xK) :=
    (env_carry I1 c "K" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hKv
  have e1_am : (evalInstr I1 c).env "a_ptrs_18" = some (tensor [1, Kd] amvals) :=
    (env_carry I1 c "a_ptrs_18" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hamask
  -- step 2: subi  (a_50 := K - a), scalar
  have f2 : FaithfulWFI (evalInstr I2 (evalInstr I1 c)) (symEvalInstr I2 (symEvalInstr I1 sc)) mem :=
    subi_scalar_step_generic I2 "K" "a" rfl rfl xK (xk * xc) e1_K e1_a f1
  have e2_a50 : (evalInstr I2 (evalInstr I1 c)).env "a_50" = some (scalar (xK - xk * xc)) :=
    subi_scalar_binds (evalInstr I1 c) "a_50" "K" "a" xK (xk * xc) e1_K e1_a
  have e2_am : (evalInstr I2 (evalInstr I1 c)).env "a_ptrs_18" = some (tensor [1, Kd] amvals) :=
    (env_carry I2 (evalInstr I1 c) "a_ptrs_18" (by simp [I2]) (by simp [I2]) (by simp [I2])).trans e1_am
  -- step 3: splat[1,Kd]  (a_51 := splat a_50)
  have f3 : FaithfulWFI (evalInstr I3 (evalInstr I2 (evalInstr I1 c)))
      (symEvalInstr I3 (symEvalInstr I2 (symEvalInstr I1 sc))) mem :=
    splat_step_generic_shaped I3 [1, Kd] "a_50" rfl rfl f2
  have e3_a51 : (evalInstr I3 (evalInstr I2 (evalInstr I1 c))).env "a_51"
      = some (tensor [1, Kd] (List.replicate ([1, Kd].foldl (· * ·) 1) (xK - xk * xc))) :=
    splat_shaped_binds (evalInstr I2 (evalInstr I1 c)) "a_51" "a_50" [1, Kd] (xK - xk * xc) e2_a50
  have e3_am : (evalInstr I3 (evalInstr I2 (evalInstr I1 c))).env "a_ptrs_18"
      = some (tensor [1, Kd] amvals) :=
    (env_carry I3 (evalInstr I2 (evalInstr I1 c)) "a_ptrs_18" (by simp [I3]) (by simp [I3]) (by simp [I3])).trans e2_am
  -- step 4: cmpi_slt  (a_52 := a_ptrs_18 < a_51), both [1,Kd]
  have f4 : FaithfulWFI (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c))))
      (symEvalInstr I4 (symEvalInstr I3 (symEvalInstr I2 (symEvalInstr I1 sc)))) mem :=
    cmpi_slt_step_generic I4 "a_ptrs_18" "a_51" rfl rfl f3
  exact ⟨f4, _, cmpi_slt_tt_binds (evalInstr I3 (evalInstr I2 (evalInstr I1 c))) "a_52"
      "a_ptrs_18" "a_51" [1, Kd] amvals _ e3_am e3_a51⟩


-- ── Body walk segment 2: steps 5-6 (broadcast[M,K], 3-arg masked load) ──────────
-- Consumes a_52 : [1,Kd] (from seg1) and the invariant's aptr/afill : [M,K].
-- Produces a_54 : [M,K] — the dot's first operand.
theorem matmul_body_seg2
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd : Nat)
    (hKpos : 0 < Kd)
    (a52vals : List Int) (ha52 : c.env "a_52" = some (tensor [1, Kd] a52vals))
    (aptrvals : List Int) (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (afillvals : List Int) (hafill : c.env "cst_0" = some (tensor [Md, Kd] afillvals))
    (hlen_aptr : aptrvals.length = Md * Kd)
    (hlen_afill : afillvals.length = Md * Kd)
    (hfw : FaithfulWFI c sc mem) :
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    FaithfulWFI (evalInstr I6 (evalInstr I5 c)) (symEvalInstr I6 (symEvalInstr I5 sc)) mem
    ∧ ∃ vals, (evalInstr I6 (evalInstr I5 c)).env "a_54" = some (tensor [Md, Kd] vals) := by
  intro I5 I6
  -- step 5: broadcast [1,Kd] → [Md,Kd]  (s0=1 so t0 free; s1=Kd=t1)
  have f5 : FaithfulWFI (evalInstr I5 c) (symEvalInstr I5 sc) mem :=
    broadcast_step_generic I5 Md Kd "a_52" rfl rfl 1 Kd a52vals ha52
      Nat.one_pos hKpos (Or.inr rfl) (Or.inl rfl) hfw
  have e5_a53 : (evalInstr I5 c).env "a_53"
      = some (tensor [Md, Kd] ((List.range (Md * Kd)).map (fun idx =>
          a52vals.getD ((if (1:Nat) == 1 then 0 else idx / Kd) * Kd
                        + (if Kd == 1 then 0 else idx % Kd)) 0))) :=
    broadcast_binds c "a_53" "a_52" 1 Kd Md Kd a52vals ha52
  have e5_aptr : (evalInstr I5 c).env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals) :=
    (env_carry I5 c "a_ptrs_47" (by simp [I5]) (by simp [I5]) (by simp [I5])).trans haptr
  have e5_afill : (evalInstr I5 c).env "cst_0" = some (tensor [Md, Kd] afillvals) :=
    (env_carry I5 c "cst_0" (by simp [I5]) (by simp [I5]) (by simp [I5])).trans hafill
  -- broadcast output length
  have hlen_a53 : ((List.range (Md * Kd)).map (fun idx =>
          a52vals.getD ((if (1:Nat) == 1 then 0 else idx / Kd) * Kd
                        + (if Kd == 1 then 0 else idx % Kd)) 0)).length = Md * Kd := by simp
  -- step 6: 3-arg masked load (ptr [Md,Kd], mask [Md,Kd], fill [Md,Kd])
  have f6 : FaithfulWFI (evalInstr I6 (evalInstr I5 c)) (symEvalInstr I6 (symEvalInstr I5 sc)) mem :=
    load_masked_fill_step_generic I6 "a_ptrs_47" "a_53" "cst_0" rfl rfl
      [Md, Kd] [Md, Kd] [Md, Kd] aptrvals _ afillvals e5_aptr e5_a53 e5_afill
      (by rw [hlen_aptr, hlen_a53]) (by rw [hlen_aptr, hlen_afill]) f5
  refine ⟨f6, ?_⟩
  obtain ⟨out, hout, _⟩ := load_fill_binds (evalInstr I5 c) "a_54" "a_ptrs_47" "a_53" "cst_0"
    [Md, Kd] [Md, Kd] [Md, Kd] aptrvals _ afillvals e5_aptr e5_a53 e5_afill
    (by rw [hlen_aptr, hlen_a53]) (by rw [hlen_aptr, hlen_afill])
  exact ⟨out, hout⟩


-- ── Body walk segment 3: steps 7-10 (splat[K,1], cmpi_slt, broadcast[K,N], load) ─
-- B-tile mirror of segs 1+2. Reads a_50 (the scalar k-bound, from seg1), the invariant's
-- bmask (b_ptrs : [Kd,1]), bptr (b_ptrs_48 : [Kd,Nd]), bfill (cst : [Kd,Nd]).
-- Produces b_57 : [Kd,Nd] — the dot's second operand.
theorem matmul_body_seg3
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd)
    (xa50 : Int) (ha50 : c.env "a_50" = some (scalar xa50))
    (bmvals : List Int) (hbmask : c.env "b_ptrs" = some (tensor [Kd, 1] bmvals))
    (bptrvals : List Int) (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (bfillvals : List Int) (hbfill : c.env "cst" = some (tensor [Kd, Nd] bfillvals))
    (hlen_bm : bmvals.length = Kd * 1)
    (hlen_bptr : bptrvals.length = Kd * Nd)
    (hlen_bfill : bfillvals.length = Kd * Nd)
    (hfw : FaithfulWFI c sc mem) :
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],       args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,            args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd],  args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load,                args := ["b_ptrs_48", "b_56", "cst"] }
    FaithfulWFI (evalInstr I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 c))))
                (symEvalInstr I10 (symEvalInstr I9 (symEvalInstr I8 (symEvalInstr I7 sc)))) mem
    ∧ ∃ vals, (evalInstr I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 c)))).env "b_57"
                = some (tensor [Kd, Nd] vals) := by
  intro I7 I8 I9 I10
  -- step 7: splat [Kd,1]
  have f7 : FaithfulWFI (evalInstr I7 c) (symEvalInstr I7 sc) mem :=
    splat_step_generic_shaped I7 [Kd, 1] "a_50" rfl rfl hfw
  have e7_b : (evalInstr I7 c).env "b"
      = some (tensor [Kd, 1] (List.replicate ([Kd, 1].foldl (· * ·) 1) xa50)) :=
    splat_shaped_binds c "b" "a_50" [Kd, 1] xa50 ha50
  have e7_bm : (evalInstr I7 c).env "b_ptrs" = some (tensor [Kd, 1] bmvals) :=
    (env_carry I7 c "b_ptrs" (by simp [I7]) (by simp [I7]) (by simp [I7])).trans hbmask
  have e7_bptr : (evalInstr I7 c).env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals) :=
    (env_carry I7 c "b_ptrs_48" (by simp [I7]) (by simp [I7]) (by simp [I7])).trans hbptr
  have e7_bfill : (evalInstr I7 c).env "cst" = some (tensor [Kd, Nd] bfillvals) :=
    (env_carry I7 c "cst" (by simp [I7]) (by simp [I7]) (by simp [I7])).trans hbfill
  -- step 8: cmpi_slt (b_55 := b_ptrs < b), both [Kd,1]
  have f8 : FaithfulWFI (evalInstr I8 (evalInstr I7 c)) (symEvalInstr I8 (symEvalInstr I7 sc)) mem :=
    cmpi_slt_step_generic I8 "b_ptrs" "b" rfl rfl f7
  have e8_b55 : (evalInstr I8 (evalInstr I7 c)).env "b_55"
      = some (tensor [Kd, 1] ((bmvals.zip (List.replicate ([Kd, 1].foldl (· * ·) 1) xa50)).map
          (fun p => if p.fst < p.snd then (1:Int) else 0))) :=
    cmpi_slt_tt_binds (evalInstr I7 c) "b_55" "b_ptrs" "b" [Kd, 1] bmvals _ e7_bm e7_b
  have e8_bptr : (evalInstr I8 (evalInstr I7 c)).env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals) :=
    (env_carry I8 (evalInstr I7 c) "b_ptrs_48" (by simp [I8]) (by simp [I8]) (by simp [I8])).trans e7_bptr
  have e8_bfill : (evalInstr I8 (evalInstr I7 c)).env "cst" = some (tensor [Kd, Nd] bfillvals) :=
    (env_carry I8 (evalInstr I7 c) "cst" (by simp [I8]) (by simp [I8]) (by simp [I8])).trans e7_bfill
  -- step 9: broadcast [Kd,1] → [Kd,Nd]  (s1=1 so t1 free; s0=Kd=t0)
  have f9 : FaithfulWFI (evalInstr I9 (evalInstr I8 (evalInstr I7 c)))
      (symEvalInstr I9 (symEvalInstr I8 (symEvalInstr I7 sc))) mem :=
    broadcast_step_generic I9 Kd Nd "b_55" rfl rfl Kd 1 _ e8_b55
      hKpos Nat.one_pos (Or.inl rfl) (Or.inr rfl) f8
  have e9_b56 := broadcast_binds (evalInstr I8 (evalInstr I7 c)) "b_56" "b_55" Kd 1 Kd Nd _ e8_b55
  have e9_bptr : (evalInstr I9 (evalInstr I8 (evalInstr I7 c))).env "b_ptrs_48"
      = some (tensor [Kd, Nd] bptrvals) :=
    (env_carry I9 (evalInstr I8 (evalInstr I7 c)) "b_ptrs_48" (by simp [I9]) (by simp [I9]) (by simp [I9])).trans e8_bptr
  have e9_bfill : (evalInstr I9 (evalInstr I8 (evalInstr I7 c))).env "cst"
      = some (tensor [Kd, Nd] bfillvals) :=
    (env_carry I9 (evalInstr I8 (evalInstr I7 c)) "cst" (by simp [I9]) (by simp [I9]) (by simp [I9])).trans e8_bfill
  have hlen_b56 : ((List.range (Kd * Nd)).map (fun idx =>
      (((bmvals.zip (List.replicate ([Kd, 1].foldl (· * ·) 1) xa50)).map
        (fun p => if p.fst < p.snd then (1:Int) else 0))).getD
          ((if Kd == 1 then 0 else idx / Nd) * 1 + (if (1:Nat) == 1 then 0 else idx % Nd)) 0)).length
      = Kd * Nd := by simp
  -- step 10: 3-arg masked load (all [Kd,Nd])
  have f10 : FaithfulWFI (evalInstr I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 c))))
      (symEvalInstr I10 (symEvalInstr I9 (symEvalInstr I8 (symEvalInstr I7 sc)))) mem :=
    load_masked_fill_step_generic I10 "b_ptrs_48" "b_56" "cst" rfl rfl
      [Kd, Nd] [Kd, Nd] [Kd, Nd] bptrvals _ bfillvals e9_bptr e9_b56 e9_bfill
      (by rw [hlen_bptr, hlen_b56]) (by rw [hlen_bptr, hlen_bfill]) f9
  refine ⟨f10, ?_⟩
  obtain ⟨out, hout, _⟩ := load_fill_binds (evalInstr I9 (evalInstr I8 (evalInstr I7 c)))
    "b_57" "b_ptrs_48" "b_56" "cst" [Kd, Nd] [Kd, Nd] [Kd, Nd] bptrvals _ bfillvals
    e9_bptr e9_b56 e9_bfill (by rw [hlen_bptr, hlen_b56]) (by rw [hlen_bptr, hlen_bfill])
  exact ⟨out, hout⟩


-- ── Body walk segment 4: step 11 (dot) ──────────────────────────────────────────
-- The contraction: a_54 [Md,Kd] · b_57 [Kd,Nd] + accumulator_49 [Md,Nd] → accumulator_58 [Md,Nd].
-- Operand shapes come from segs 2/3 and the loop invariant's accumulator conjunct.
theorem matmul_body_seg4
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hNpos : 0 < Nd)
    (avals : List Int) (ha : c.env "a_54" = some (tensor [Md, Kd] avals))
    (bvals : List Int) (hb : c.env "b_57" = some (tensor [Kd, Nd] bvals))
    (accvals : List Int) (hacc : c.env "accumulator_49" = some (tensor [Md, Nd] accvals))
    (hfw : FaithfulWFI c sc mem) :
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    FaithfulWFI (evalInstr I11 c) (symEvalInstr I11 sc) mem
    ∧ ∃ vals, (evalInstr I11 c).env "accumulator_58" = some (tensor [Md, Nd] vals) := by
  intro I11
  have f11 : FaithfulWFI (evalInstr I11 c) (symEvalInstr I11 sc) mem :=
    dot_step_generic I11 Md Kd Nd "a_54" "b_57" "accumulator_49" rfl rfl
      avals bvals accvals ha hb hacc hNpos hfw
  refine ⟨f11, ?_⟩
  obtain ⟨out, hout, _⟩ := dot_binds c "accumulator_58" "a_54" "b_57" "accumulator_49"
    Md Kd Nd avals bvals accvals ha hb hacc
  exact ⟨out, hout⟩


-- ── Body walk segment 5 (full): steps 12-18, with invariant re-establishment ─────
-- Proves FaithfulWFI through the 7 steps AND that the three iter-args are re-bound at
-- their invariant shapes (the yield copies), making MatmulLoopInv inductive.
theorem matmul_body_seg5
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (aptrvals : List Int) (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (cst1vals : List Int) (hcst1 : c.env "cst_1" = some (tensor [Md, Kd] cst1vals))
    (bptrvals : List Int) (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (xsb xc32 : Int)
    (hsb : c.env "stride_bk" = some (scalar xsb))
    (hc32 : c.env "c32_i32" = some (scalar xc32))
    (accvals : List Int) (hacc58 : c.env "accumulator_58" = some (tensor [Md, Nd] accvals))
    (hfw : FaithfulWFI c sc mem) :
    let J1 : TritonInstr := { result := "a_ptrs_59", op := .addptr, args := ["a_ptrs_47", "cst_1"] }
    let J2 : TritonInstr := { result := "b_ptrs_60", op := .muli, args := ["stride_bk", "c32_i32"] }
    let J3 : TritonInstr := { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] }
    let J4 : TritonInstr := { result := "b_ptrs_62", op := .addptr, args := ["b_ptrs_48", "b_ptrs_61"] }
    let J5 : TritonInstr := { result := "a_ptrs_47", op := .copy, args := ["a_ptrs_59"] }
    let J6 : TritonInstr := { result := "b_ptrs_48", op := .copy, args := ["b_ptrs_62"] }
    let J7 : TritonInstr := { result := "accumulator_49", op := .copy, args := ["accumulator_58"] }
    let cEnd := evalInstr J7 (evalInstr J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c))))))
    let scEnd := symEvalInstr J7 (symEvalInstr J6 (symEvalInstr J5 (symEvalInstr J4 (symEvalInstr J3 (symEvalInstr J2 (symEvalInstr J1 sc))))))
    FaithfulWFI cEnd scEnd mem
    ∧ (∃ v, cEnd.env "a_ptrs_47" = some (tensor [Md, Kd] v))
    ∧ (∃ v, cEnd.env "b_ptrs_48" = some (tensor [Kd, Nd] v))
    ∧ (∃ v, cEnd.env "accumulator_49" = some (tensor [Md, Nd] v)) := by
  intro J1 J2 J3 J4 J5 J6 J7 cEnd scEnd
  -- FaithfulWFI chain
  have f1 : FaithfulWFI (evalInstr J1 c) (symEvalInstr J1 sc) mem :=
    addptr_step_generic J1 "a_ptrs_47" "cst_1" rfl rfl hfw
  have f2 : FaithfulWFI (evalInstr J2 (evalInstr J1 c)) (symEvalInstr J2 (symEvalInstr J1 sc)) mem :=
    muli_step_generic J2 "stride_bk" "c32_i32" rfl rfl f1
  have f3 := splat_step_generic_shaped J3 [Kd, Nd] "b_ptrs_60" rfl rfl f2
  have f4 := addptr_step_generic J4 "b_ptrs_48" "b_ptrs_61" rfl rfl f3
  have f5 := copy_step_generic J5 "a_ptrs_59" rfl rfl f4
  have f6 := copy_step_generic J6 "b_ptrs_62" rfl rfl f5
  have f7 := copy_step_generic J7 "accumulator_58" rfl rfl f6
  -- Shape facts, threaded forward (explicit states; no `set`)
  have e1_a59 := addptr_tt_binds c "a_ptrs_59" "a_ptrs_47" "cst_1" [Md, Kd] aptrvals cst1vals haptr hcst1
  have e1_bptr := (env_carry J1 c "b_ptrs_48" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hbptr
  have e1_sb := (env_carry J1 c "stride_bk" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hsb
  have e1_c32 := (env_carry J1 c "c32_i32" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hc32
  have e1_acc := (env_carry J1 c "accumulator_58" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hacc58
  have e2_b60 := muli_binds (evalInstr J1 c) "b_ptrs_60" "stride_bk" "c32_i32" xsb xc32 e1_sb e1_c32
  have e2_a59 := (env_carry J2 (evalInstr J1 c) "a_ptrs_59" (by simp [J2]) (by simp [J2]) (by simp [J2])).trans e1_a59
  have e2_bptr := (env_carry J2 (evalInstr J1 c) "b_ptrs_48" (by simp [J2]) (by simp [J2]) (by simp [J2])).trans e1_bptr
  have e2_acc := (env_carry J2 (evalInstr J1 c) "accumulator_58" (by simp [J2]) (by simp [J2]) (by simp [J2])).trans e1_acc
  have e3_b61 := splat_shaped_binds (evalInstr J2 (evalInstr J1 c)) "b_ptrs_61" "b_ptrs_60" [Kd, Nd] (xsb * xc32) e2_b60
  have e3_a59 := (env_carry J3 (evalInstr J2 (evalInstr J1 c)) "a_ptrs_59" (by simp [J3]) (by simp [J3]) (by simp [J3])).trans e2_a59
  have e3_bptr := (env_carry J3 (evalInstr J2 (evalInstr J1 c)) "b_ptrs_48" (by simp [J3]) (by simp [J3]) (by simp [J3])).trans e2_bptr
  have e3_acc := (env_carry J3 (evalInstr J2 (evalInstr J1 c)) "accumulator_58" (by simp [J3]) (by simp [J3]) (by simp [J3])).trans e2_acc
  have e4_b62 := addptr_tt_binds (evalInstr J3 (evalInstr J2 (evalInstr J1 c))) "b_ptrs_62" "b_ptrs_48" "b_ptrs_61" [Kd, Nd] bptrvals _ e3_bptr e3_b61
  have e4_a59 := (env_carry J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c))) "a_ptrs_59" (by simp [J4]) (by simp [J4]) (by simp [J4])).trans e3_a59
  have e4_acc := (env_carry J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c))) "accumulator_58" (by simp [J4]) (by simp [J4]) (by simp [J4])).trans e3_acc
  have e5_a47 := copy_binds (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c)))) "a_ptrs_47" "a_ptrs_59" _ e4_a59
  have e5_b62 := (env_carry J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c)))) "b_ptrs_62" (by simp [J5]) (by simp [J5]) (by simp [J5])).trans e4_b62
  have e5_acc := (env_carry J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c)))) "accumulator_58" (by simp [J5]) (by simp [J5]) (by simp [J5])).trans e4_acc
  have e6_b48 := copy_binds (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c))))) "b_ptrs_48" "b_ptrs_62" _ e5_b62
  have e6_a47 := (env_carry J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c))))) "a_ptrs_47" (by simp [J6]) (by simp [J6]) (by simp [J6])).trans e5_a47
  have e6_acc := (env_carry J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c))))) "accumulator_58" (by simp [J6]) (by simp [J6]) (by simp [J6])).trans e5_acc
  have e7_acc49 := copy_binds (evalInstr J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c)))))) "accumulator_49" "accumulator_58" _ e6_acc
  have e7_a47 := (env_carry J7 (evalInstr J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c)))))) "a_ptrs_47" (by simp [J7]) (by simp [J7]) (by simp [J7])).trans e6_a47
  have e7_b48 := (env_carry J7 (evalInstr J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 c)))))) "b_ptrs_48" (by simp [J7]) (by simp [J7]) (by simp [J7])).trans e6_b48
  exact ⟨f7, ⟨_, e7_a47⟩, ⟨_, e7_b48⟩, ⟨_, e7_acc49⟩⟩

-- Bridge: evalKernel on a concrete 4-element list unfolds to nested evalInstr.
-- (Sanity check that the segment lemmas' nested form matches evalKernel's foldl form.)
theorem evalKernel_six (i1 i2 i3 i4 i5 i6 : TritonInstr) (s : MachineState) :
    evalKernel [i1, i2, i3, i4, i5, i6] s
      = evalInstr i6 (evalInstr i5 (evalInstr i4 (evalInstr i3 (evalInstr i2 (evalInstr i1 s))))) := by
  simp [evalKernel]

theorem evalKernel_ten (i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 : TritonInstr) (s : MachineState) :
    evalKernel [i1, i2, i3, i4, i5, i6, i7, i8, i9, i10] s
      = evalInstr i10 (evalInstr i9 (evalInstr i8 (evalInstr i7
          (evalInstr i6 (evalInstr i5 (evalInstr i4 (evalInstr i3 (evalInstr i2 (evalInstr i1 s))))))))) := by
  simp [evalKernel]

theorem evalKernel_four (i1 i2 i3 i4 : TritonInstr) (s : MachineState) :
    evalKernel [i1, i2, i3, i4] s = evalInstr i4 (evalInstr i3 (evalInstr i2 (evalInstr i1 s))) := by
  simp [evalKernel]

theorem symEvalKernel_four (i1 i2 i3 i4 : TritonInstr) (ss : SymState) :
    symEvalKernel [i1, i2, i3, i4] ss
      = symEvalInstr i4 (symEvalInstr i3 (symEvalInstr i2 (symEvalInstr i1 ss))) := by
  simp [symEvalKernel]


-- ── Composition step: seg1 ++ seg2 (body steps 1-6) ──────────────────────────────
-- Validates the carry mechanics: seg2's operand facts (a_ptrs_47, cst_0) are transported
-- across seg1's four instructions with a single env_carry_kernel each.
theorem matmul_body_seg12
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd : Nat)
    (hKpos : 0 < Kd)
    (xk xc xK : Int)
    (hk   : c.env "k" = some (scalar xk))
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (amvals : List Int) (hamask : c.env "a_ptrs_18" = some (tensor [1, Kd] amvals))
    (hlen_am : amvals.length = 1 * Kd)
    (aptrvals : List Int) (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (afillvals : List Int) (hafill : c.env "cst_0" = some (tensor [Md, Kd] afillvals))
    (hlen_aptr : aptrvals.length = Md * Kd)
    (hlen_afill : afillvals.length = Md * Kd)
    (hfw : FaithfulWFI c sc mem) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let cA := evalKernel [I1, I2, I3, I4] c
    let scA := symEvalKernel [I1, I2, I3, I4] sc
    FaithfulWFI (evalInstr I6 (evalInstr I5 cA)) (symEvalInstr I6 (symEvalInstr I5 scA)) mem
    ∧ ∃ vals, (evalInstr I6 (evalInstr I5 cA)).env "a_54" = some (tensor [Md, Kd] vals) := by
  intro I1 I2 I3 I4 I5 I6 cA scA
  -- seg1 gives FaithfulWFI at cA and the shape of a_52
  have hseg1 := matmul_body_seg1 (c := c) (sc := sc) (mem := mem) Kd xk xc xK hk hc32 hKv amvals hamask hlen_am hfw
  simp only at hseg1
  obtain ⟨f4, a52vals, ha52⟩ := hseg1
  -- transport a_ptrs_47 and cst_0 across seg1's four instructions
  have hcarry_aptr : cA.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals) := by
    show (evalKernel [I1, I2, I3, I4] c).env "a_ptrs_47" = _
    rw [env_carry_kernel [I1, I2, I3, I4] c "a_ptrs_47"
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4])]
    exact haptr
  have hcarry_afill : cA.env "cst_0" = some (tensor [Md, Kd] afillvals) := by
    show (evalKernel [I1, I2, I3, I4] c).env "cst_0" = _
    rw [env_carry_kernel [I1, I2, I3, I4] c "cst_0"
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4])]
    exact hafill
  -- FaithfulWFI at cA, in evalKernel form
  have fA : FaithfulWFI cA scA mem := by
    show FaithfulWFI (evalKernel [I1, I2, I3, I4] c) (symEvalKernel [I1, I2, I3, I4] sc) mem
    rw [evalKernel_four, symEvalKernel_four]
    exact f4
  -- a_52's shape at cA, in evalKernel form
  have ha52A : cA.env "a_52" = some (tensor [1, Kd] a52vals) := by
    show (evalKernel [I1, I2, I3, I4] c).env "a_52" = _
    rw [evalKernel_four]; exact ha52
  -- apply seg2 at cA
  exact matmul_body_seg2 (c := cA) (sc := scA) (mem := mem) Md Kd hKpos
    a52vals ha52A aptrvals hcarry_aptr afillvals hcarry_afill hlen_aptr hlen_afill fA


-- ── Composition: seg1 ++ seg2 ++ seg3 (body steps 1-10) ──────────────────────────
-- Carries into seg3: a_50 (scalar k-bound, from seg1 step 2), b_ptrs, b_ptrs_48, cst.
theorem matmul_body_seg123
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd)
    (xk xc xK : Int)
    (hk   : c.env "k" = some (scalar xk))
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (amvals : List Int) (hamask : c.env "a_ptrs_18" = some (tensor [1, Kd] amvals))
    (hlen_am : amvals.length = 1 * Kd)
    (aptrvals : List Int) (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (afillvals : List Int) (hafill : c.env "cst_0" = some (tensor [Md, Kd] afillvals))
    (hlen_aptr : aptrvals.length = Md * Kd) (hlen_afill : afillvals.length = Md * Kd)
    (bmvals : List Int) (hbmask : c.env "b_ptrs" = some (tensor [Kd, 1] bmvals))
    (bptrvals : List Int) (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (bfillvals : List Int) (hbfill : c.env "cst" = some (tensor [Kd, Nd] bfillvals))
    (hlen_bm : bmvals.length = Kd * 1)
    (hlen_bptr : bptrvals.length = Kd * Nd) (hlen_bfill : bfillvals.length = Kd * Nd)
    (hfw : FaithfulWFI c sc mem) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let cB := evalKernel [I1, I2, I3, I4, I5, I6] c
    let scB := symEvalKernel [I1, I2, I3, I4, I5, I6] sc
    FaithfulWFI (evalInstr I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 cB))))
                (symEvalInstr I10 (symEvalInstr I9 (symEvalInstr I8 (symEvalInstr I7 scB)))) mem
    ∧ ∃ vals, (evalInstr I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 cB)))).env "b_57"
                = some (tensor [Kd, Nd] vals) := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 cB scB
  -- seg12 gives FaithfulWFI and a_54's shape at cB (in nested form)
  have h12 := matmul_body_seg12 (c := c) (sc := sc) (mem := mem) Md Kd hKpos xk xc xK
    hk hc32 hKv amvals hamask hlen_am aptrvals haptr afillvals hafill hlen_aptr hlen_afill hfw
  simp only at h12
  obtain ⟨f6, a54vals, ha54⟩ := h12
  -- FaithfulWFI at cB in evalKernel form
  have fB : FaithfulWFI cB scB mem := by
    show FaithfulWFI (evalKernel [I1,I2,I3,I4,I5,I6] c) (symEvalKernel [I1,I2,I3,I4,I5,I6] sc) mem
    simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
    simpa [evalKernel, symEvalKernel] using f6
  -- carries across the six instructions
  have hcarry : ∀ (w : String), (w ≠ "a") → (w ≠ "a_50") → (w ≠ "a_51") → (w ≠ "a_52") →
      (w ≠ "a_53") → (w ≠ "a_54") → cB.env w = c.env w := by
    intro w h1 h2 h3 h4 h5 h6
    show (evalKernel [I1,I2,I3,I4,I5,I6] c).env w = c.env w
    exact env_carry_kernel [I1,I2,I3,I4,I5,I6] c w
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6, h1,h2,h3,h4,h5,h6])
  -- a_50 survives (produced by I2, then untouched by I3..I6)
  have ha50_c : (evalKernel [I1, I2] c).env "a_50" = some (scalar (xK - xk * xc)) := by
    simp only [evalKernel, List.foldl_cons, List.foldl_nil]
    have e1_a := muli_binds c "a" "k" "c32_i32" xk xc hk hc32
    have e1_K := (env_carry I1 c "K" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hKv
    exact subi_scalar_binds (evalInstr I1 c) "a_50" "K" "a" xK (xk * xc) e1_K e1_a
  have ha50_B : cB.env "a_50" = some (scalar (xK - xk * xc)) := by
    show (evalKernel [I1,I2,I3,I4,I5,I6] c).env "a_50" = _
    have hsplit : ([I1,I2,I3,I4,I5,I6] : TritonKernel) = [I1,I2] ++ [I3,I4,I5,I6] := by simp
    rw [hsplit, evalKernel_append]
    rw [env_carry_kernel [I3,I4,I5,I6] (evalKernel [I1,I2] c) "a_50"
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h <;> subst h <;> simp [I3,I4,I5,I6])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h <;> subst h <;> simp [I3,I4,I5,I6])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h <;> subst h <;> simp [I3,I4,I5,I6])]
    exact ha50_c
  -- b-side operands survive all six
  have hbm_B := (hcarry "b_ptrs" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbmask
  have hbp_B := (hcarry "b_ptrs_48" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbptr
  have hbf_B := (hcarry "cst" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbfill
  exact matmul_body_seg3 (c := cB) (sc := scB) (mem := mem) Kd Nd hKpos hNpos
    (xK - xk * xc) ha50_B bmvals hbm_B bptrvals hbp_B bfillvals hbf_B
    hlen_bm hlen_bptr hlen_bfill fB


-- ── Composition: segs 1-4 (body steps 1-11, through the dot) ─────────────────────
-- Carries into seg4: a_54 (from seg2, survives I7..I10), accumulator_49 (untouched so far).
-- b_57 comes straight from seg3's conclusion.
theorem matmul_body_seg1234
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd)
    (xk xc xK : Int)
    (hk   : c.env "k" = some (scalar xk))
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (amvals : List Int) (hamask : c.env "a_ptrs_18" = some (tensor [1, Kd] amvals))
    (hlen_am : amvals.length = 1 * Kd)
    (aptrvals : List Int) (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (afillvals : List Int) (hafill : c.env "cst_0" = some (tensor [Md, Kd] afillvals))
    (hlen_aptr : aptrvals.length = Md * Kd) (hlen_afill : afillvals.length = Md * Kd)
    (bmvals : List Int) (hbmask : c.env "b_ptrs" = some (tensor [Kd, 1] bmvals))
    (bptrvals : List Int) (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (bfillvals : List Int) (hbfill : c.env "cst" = some (tensor [Kd, Nd] bfillvals))
    (hlen_bm : bmvals.length = Kd * 1)
    (hlen_bptr : bptrvals.length = Kd * Nd) (hlen_bfill : bfillvals.length = Kd * Nd)
    (accvals : List Int) (hacc : c.env "accumulator_49" = some (tensor [Md, Nd] accvals))
    (hfw : FaithfulWFI c sc mem) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    let cC := evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c
    let scC := symEvalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] sc
    FaithfulWFI (evalInstr I11 cC) (symEvalInstr I11 scC) mem
    ∧ ∃ vals, (evalInstr I11 cC).env "accumulator_58" = some (tensor [Md, Nd] vals) := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 cC scC
  have h123 := matmul_body_seg123 (c := c) (sc := sc) (mem := mem) Md Kd Nd hKpos hNpos
    xk xc xK hk hc32 hKv amvals hamask hlen_am aptrvals haptr afillvals hafill
    hlen_aptr hlen_afill bmvals hbmask bptrvals hbptr bfillvals hbfill
    hlen_bm hlen_bptr hlen_bfill hfw
  simp only at h123
  obtain ⟨f10, b57vals, hb57⟩ := h123
  have fC : FaithfulWFI cC scC mem := by
    show FaithfulWFI (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c)
                     (symEvalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] sc) mem
    simpa [evalKernel, symEvalKernel] using f10
  have hb57C : cC.env "b_57" = some (tensor [Kd, Nd] b57vals) := by
    show (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c).env "b_57" = _
    simpa [evalKernel] using hb57
  -- a_54 : produced by I6; survives I7..I10
  have ha54_6 : ∃ v, (evalKernel [I1,I2,I3,I4,I5,I6] c).env "a_54" = some (tensor [Md, Kd] v) := by
    have h12 := matmul_body_seg12 (c := c) (sc := sc) (mem := mem) Md Kd hKpos xk xc xK
      hk hc32 hKv amvals hamask hlen_am aptrvals haptr afillvals hafill hlen_aptr hlen_afill hfw
    simp only at h12
    obtain ⟨_, v, hv⟩ := h12
    exact ⟨v, by simpa [evalKernel] using hv⟩
  obtain ⟨a54vals, ha54_6'⟩ := ha54_6
  have ha54C : cC.env "a_54" = some (tensor [Md, Kd] a54vals) := by
    show (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c).env "a_54" = _
    have hsplit : ([I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] : TritonKernel)
        = [I1,I2,I3,I4,I5,I6] ++ [I7,I8,I9,I10] := by simp
    rw [hsplit, evalKernel_append]
    rw [env_carry_kernel [I7,I8,I9,I10] (evalKernel [I1,I2,I3,I4,I5,I6] c) "a_54"
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h <;> subst h <;> simp [I7,I8,I9,I10])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h <;> subst h <;> simp [I7,I8,I9,I10])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h <;> subst h <;> simp [I7,I8,I9,I10])]
    exact ha54_6'
  -- accumulator_49 : untouched by all ten
  have haccC : cC.env "accumulator_49" = some (tensor [Md, Nd] accvals) := by
    show (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c).env "accumulator_49" = _
    rw [env_carry_kernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c "accumulator_49"
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10])]
    exact hacc
  exact matmul_body_seg4 (c := cC) (sc := scC) (mem := mem) Md Kd Nd hNpos
    a54vals ha54C b57vals hb57C accvals haccC fC



-- ── Composition: all five segments (the full 18-instruction body) ────────────────
-- Every carry into seg5 is a variable untouched by I1..I11, except accumulator_58
-- which seg4 produces. Concludes with FaithfulWFI and the three iter-arg shapes restored.
theorem matmul_body_all
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd)
    (xk xc xK xsb : Int)
    (hk   : c.env "k" = some (scalar xk))
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (hsb  : c.env "stride_bk" = some (scalar xsb))
    (amvals : List Int) (hamask : c.env "a_ptrs_18" = some (tensor [1, Kd] amvals))
    (hlen_am : amvals.length = 1 * Kd)
    (aptrvals : List Int) (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (afillvals : List Int) (hafill : c.env "cst_0" = some (tensor [Md, Kd] afillvals))
    (hlen_aptr : aptrvals.length = Md * Kd) (hlen_afill : afillvals.length = Md * Kd)
    (bmvals : List Int) (hbmask : c.env "b_ptrs" = some (tensor [Kd, 1] bmvals))
    (bptrvals : List Int) (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (bfillvals : List Int) (hbfill : c.env "cst" = some (tensor [Kd, Nd] bfillvals))
    (hlen_bm : bmvals.length = Kd * 1)
    (hlen_bptr : bptrvals.length = Kd * Nd) (hlen_bfill : bfillvals.length = Kd * Nd)
    (accvals : List Int) (hacc : c.env "accumulator_49" = some (tensor [Md, Nd] accvals))
    (cst1vals : List Int) (hcst1 : c.env "cst_1" = some (tensor [Md, Kd] cst1vals))
    (hfw : FaithfulWFI c sc mem) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    let J1 : TritonInstr := { result := "a_ptrs_59", op := .addptr, args := ["a_ptrs_47", "cst_1"] }
    let J2 : TritonInstr := { result := "b_ptrs_60", op := .muli, args := ["stride_bk", "c32_i32"] }
    let J3 : TritonInstr := { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] }
    let J4 : TritonInstr := { result := "b_ptrs_62", op := .addptr, args := ["b_ptrs_48", "b_ptrs_61"] }
    let J5 : TritonInstr := { result := "a_ptrs_47", op := .copy, args := ["a_ptrs_59"] }
    let J6 : TritonInstr := { result := "b_ptrs_48", op := .copy, args := ["b_ptrs_62"] }
    let J7 : TritonInstr := { result := "accumulator_49", op := .copy, args := ["accumulator_58"] }
    let cD := evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c
    let scD := symEvalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] sc
    let cEnd := evalInstr J7 (evalInstr J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 cD))))))
    let scEnd := symEvalInstr J7 (symEvalInstr J6 (symEvalInstr J5 (symEvalInstr J4 (symEvalInstr J3 (symEvalInstr J2 (symEvalInstr J1 scD))))))
    FaithfulWFI cEnd scEnd mem
    ∧ (∃ v, cEnd.env "a_ptrs_47" = some (tensor [Md, Kd] v))
    ∧ (∃ v, cEnd.env "b_ptrs_48" = some (tensor [Kd, Nd] v))
    ∧ (∃ v, cEnd.env "accumulator_49" = some (tensor [Md, Nd] v)) := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 J1 J2 J3 J4 J5 J6 J7 cD scD cEnd scEnd
  have h1234 := matmul_body_seg1234 (c := c) (sc := sc) (mem := mem) Md Kd Nd hKpos hNpos
    xk xc xK hk hc32 hKv amvals hamask hlen_am aptrvals haptr afillvals hafill
    hlen_aptr hlen_afill bmvals hbmask bptrvals hbptr bfillvals hbfill
    hlen_bm hlen_bptr hlen_bfill accvals hacc hfw
  simp only at h1234
  obtain ⟨f11, acc58vals, hacc58⟩ := h1234
  have fD : FaithfulWFI cD scD mem := by
    show FaithfulWFI (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c)
                     (symEvalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] sc) mem
    simpa [evalKernel, symEvalKernel] using f11
  have hacc58D : cD.env "accumulator_58" = some (tensor [Md, Nd] acc58vals) := by
    show (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c).env "accumulator_58" = _
    simpa [evalKernel] using hacc58
  -- everything seg5 needs beyond accumulator_58 is untouched by I1..I11
  have hcarry : ∀ (w : String),
      w ≠ "a" → w ≠ "a_50" → w ≠ "a_51" → w ≠ "a_52" → w ≠ "a_53" → w ≠ "a_54" →
      w ≠ "b" → w ≠ "b_55" → w ≠ "b_56" → w ≠ "b_57" → w ≠ "accumulator_58" →
      cD.env w = c.env w := by
    intro w n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    show (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c).env w = c.env w
    exact env_carry_kernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c w
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11])
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h
          <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11, n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11])
  have haptrD := (hcarry "a_ptrs_47" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans haptr
  have hcst1D := (hcarry "cst_1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcst1
  have hbptrD := (hcarry "b_ptrs_48" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbptr
  have hsbD := (hcarry "stride_bk" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsb
  have hc32D := (hcarry "c32_i32" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc32
  exact matmul_body_seg5 (c := cD) (sc := scD) (mem := mem) Md Kd Nd
    aptrvals haptrD cst1vals hcst1D bptrvals hbptrD xsb xc hsbD hc32D acc58vals hacc58D fD

-- ── matmul_body_preserves: the loop body preserves MatmulLoopInv ─────────────────
-- Packages matmul_body_all against the invariant. Length facts are derived from WFState
-- (part of FaithfulWFI) rather than assumed. The invariant's pre-loop tensors survive the
-- body untouched; the three iter-args are restored by the yield copies.
theorem matmul_body_preserves
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd)
    (xk xc xK xsb : Int)
    (hk   : c.env "k" = some (scalar xk))
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (hsb  : c.env "stride_bk" = some (scalar xsb))
    (hinv : MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
              "cst_0" "cst" "cst_1" Md Kd Nd c sc mem) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    let J1 : TritonInstr := { result := "a_ptrs_59", op := .addptr, args := ["a_ptrs_47", "cst_1"] }
    let J2 : TritonInstr := { result := "b_ptrs_60", op := .muli, args := ["stride_bk", "c32_i32"] }
    let J3 : TritonInstr := { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] }
    let J4 : TritonInstr := { result := "b_ptrs_62", op := .addptr, args := ["b_ptrs_48", "b_ptrs_61"] }
    let J5 : TritonInstr := { result := "a_ptrs_47", op := .copy, args := ["a_ptrs_59"] }
    let J6 : TritonInstr := { result := "b_ptrs_48", op := .copy, args := ["b_ptrs_62"] }
    let J7 : TritonInstr := { result := "accumulator_49", op := .copy, args := ["accumulator_58"] }
    let body : TritonKernel := [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,J1,J2,J3,J4,J5,J6,J7]
    FaithfulWFI (evalKernel body c) (symEvalKernel body sc) mem
    ∧ (∃ v, (evalKernel body c).env "a_ptrs_47" = some (tensor [Md, Kd] v))
    ∧ (∃ v, (evalKernel body c).env "b_ptrs_48" = some (tensor [Kd, Nd] v))
    ∧ (∃ v, (evalKernel body c).env "accumulator_49" = some (tensor [Md, Nd] v)) := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 J1 J2 J3 J4 J5 J6 J7 body
  obtain ⟨hfw, ⟨aptrvals, haptr⟩, ⟨bptrvals, hbptr⟩, ⟨accvals, hacc⟩,
          ⟨amvals, hamask⟩, ⟨bmvals, hbmask⟩, ⟨afillvals, hafill⟩,
          ⟨bfillvals, hbfill⟩, ⟨cst1vals, hcst1⟩,
          ⟨xc_i, hc32_i⟩, ⟨xK_i, hKv_i⟩, ⟨xsb_i, hsb_i⟩⟩ := hinv
  -- derive the length facts from WFState (inside FaithfulWFI)
  have hwf : WFState c := hfw.1.2
  have hlen_am : amvals.length = 1 * Kd := by
    have := hwf "a_ptrs_18" [1, Kd] amvals hamask
    simp only [TritonValue.WFn, shapeProd_pair] at this; omega
  have hlen_aptr : aptrvals.length = Md * Kd := by
    have := hwf "a_ptrs_47" [Md, Kd] aptrvals haptr
    simp only [TritonValue.WFn, shapeProd_pair] at this; omega
  have hlen_afill : afillvals.length = Md * Kd := by
    have := hwf "cst_0" [Md, Kd] afillvals hafill
    simp only [TritonValue.WFn, shapeProd_pair] at this; omega
  have hlen_bm : bmvals.length = Kd * 1 := by
    have := hwf "b_ptrs" [Kd, 1] bmvals hbmask
    simp only [TritonValue.WFn, shapeProd_pair] at this; omega
  have hlen_bptr : bptrvals.length = Kd * Nd := by
    have := hwf "b_ptrs_48" [Kd, Nd] bptrvals hbptr
    simp only [TritonValue.WFn, shapeProd_pair] at this; omega
  have hlen_bfill : bfillvals.length = Kd * Nd := by
    have := hwf "cst" [Kd, Nd] bfillvals hbfill
    simp only [TritonValue.WFn, shapeProd_pair] at this; omega
  -- apply the full-body composition
  have hall := matmul_body_all (c := c) (sc := sc) (mem := mem) Md Kd Nd hKpos hNpos
    xk xc xK xsb hk hc32 hKv hsb amvals hamask hlen_am aptrvals haptr afillvals hafill
    hlen_aptr hlen_afill bmvals hbmask bptrvals hbptr bfillvals hbfill
    hlen_bm hlen_bptr hlen_bfill accvals hacc cst1vals hcst1 hfw
  simp only at hall
  -- bridge nested evalInstr form to evalKernel form
  obtain ⟨fEnd, ha47, hb48, hacc49⟩ := hall
  refine ⟨?_, ?_, ?_, ?_⟩
  · show FaithfulWFI (evalKernel body c) (symEvalKernel body sc) mem
    simpa [body, evalKernel, symEvalKernel] using fEnd
  · obtain ⟨v, hv⟩ := ha47; exact ⟨v, by simpa [body, evalKernel] using hv⟩
  · obtain ⟨v, hv⟩ := hb48; exact ⟨v, by simpa [body, evalKernel] using hv⟩
  · obtain ⟨v, hv⟩ := hacc49; exact ⟨v, by simpa [body, evalKernel] using hv⟩

-- The parsed matmul loop body as a named kernel (18 instructions), parameterized by tile dims.
def MatmulBody (Md Kd Nd : Nat) : TritonKernel :=
  [ { result := "a",    op := .muli,              args := ["k", "c32_i32"] },
    { result := "a_50", op := .subi,              args := ["K", "a"] },
    { result := "a_51", op := .splat [1, Kd],     args := ["a_50"] },
    { result := "a_52", op := .cmpi_slt,          args := ["a_ptrs_18", "a_51"] },
    { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] },
    { result := "a_54", op := .load,              args := ["a_ptrs_47", "a_53", "cst_0"] },
    { result := "b",    op := .splat [Kd, 1],     args := ["a_50"] },
    { result := "b_55", op := .cmpi_slt,          args := ["b_ptrs", "b"] },
    { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] },
    { result := "b_57", op := .load,              args := ["b_ptrs_48", "b_56", "cst"] },
    { result := "accumulator_58", op := .dot,     args := ["a_54", "b_57", "accumulator_49"] },
    { result := "a_ptrs_59", op := .addptr,       args := ["a_ptrs_47", "cst_1"] },
    { result := "b_ptrs_60", op := .muli,         args := ["stride_bk", "c32_i32"] },
    { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] },
    { result := "b_ptrs_62", op := .addptr,       args := ["b_ptrs_48", "b_ptrs_61"] },
    { result := "a_ptrs_47", op := .copy,         args := ["a_ptrs_59"] },
    { result := "b_ptrs_48", op := .copy,         args := ["b_ptrs_62"] },
    { result := "accumulator_49", op := .copy,    args := ["accumulator_58"] } ]

-- ── matmul_body_step: one loop iteration preserves MatmulLoopInv ─────────────────
-- At the loop head the induction variable is bound; every invariant conjunct and the three
-- ambient scalars survive that bind (all names differ from "k"). matmul_body_preserves then
-- gives FaithfulWFI + the three iter-arg shapes at the body's end, and the six pre-loop
-- tensors are carried across the body (none of them is ever a result).
theorem matmul_body_step
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd)
    (xc xK xsb : Int)
    (hc32 : c.env "c32_i32" = some (scalar xc))
    (hKv  : c.env "K" = some (scalar xK))
    (hsb  : c.env "stride_bk" = some (scalar xsb))
    (hinv : MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
              "cst_0" "cst" "cst_1" Md Kd Nd c sc mem)
    (kk : Nat) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    let J1 : TritonInstr := { result := "a_ptrs_59", op := .addptr, args := ["a_ptrs_47", "cst_1"] }
    let J2 : TritonInstr := { result := "b_ptrs_60", op := .muli, args := ["stride_bk", "c32_i32"] }
    let J3 : TritonInstr := { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] }
    let J4 : TritonInstr := { result := "b_ptrs_62", op := .addptr, args := ["b_ptrs_48", "b_ptrs_61"] }
    let J5 : TritonInstr := { result := "a_ptrs_47", op := .copy, args := ["a_ptrs_59"] }
    let J6 : TritonInstr := { result := "b_ptrs_48", op := .copy, args := ["b_ptrs_62"] }
    let J7 : TritonInstr := { result := "accumulator_49", op := .copy, args := ["accumulator_58"] }
    let body : TritonKernel := [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,J1,J2,J3,J4,J5,J6,J7]
    MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
      "cst_0" "cst" "cst_1" Md Kd Nd
      (evalKernel body (c.bind "k" (TritonValue.scalar (Int.ofNat kk))))
      (symEvalKernel body (sc.bind "k" (SymValue.scalar (Expr.lit (Int.ofNat kk))))) mem := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 J1 J2 J3 J4 J5 J6 J7 body
  obtain ⟨hfw, ⟨aptrvals, haptr⟩, ⟨bptrvals, hbptr⟩, ⟨accvals, hacc⟩,
          ⟨amvals, hamask⟩, ⟨bmvals, hbmask⟩, ⟨afillvals, hafill⟩,
          ⟨bfillvals, hbfill⟩, ⟨cst1vals, hcst1⟩,
          ⟨xc_i, hc32_i⟩, ⟨xK_i, hKv_i⟩, ⟨xsb_i, hsb_i⟩⟩ := hinv
  -- the bound state
  have hfw' : FaithfulWFI (c.bind "k" (TritonValue.scalar (Int.ofNat kk)))
      (sc.bind "k" (SymValue.scalar (Expr.lit (Int.ofNat kk)))) mem :=
    faithfulWFI_bind_scalar "k" (Int.ofNat kk) hfw
  have hk' : (c.bind "k" (TritonValue.scalar (Int.ofNat kk))).env "k"
      = some (scalar (Int.ofNat kk)) := by simp [MachineState.bind]
  have hc32' := by
    show (c.bind "k" (TritonValue.scalar (Int.ofNat kk))).env "c32_i32" = some (scalar xc)
    simpa [MachineState.bind] using hc32
  have hKv' := by
    show (c.bind "k" (TritonValue.scalar (Int.ofNat kk))).env "K" = some (scalar xK)
    simpa [MachineState.bind] using hKv
  have hsb' := by
    show (c.bind "k" (TritonValue.scalar (Int.ofNat kk))).env "stride_bk" = some (scalar xsb)
    simpa [MachineState.bind] using hsb
  -- the invariant's nine conjuncts at the bound state
  have hinv' : MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
      "cst_0" "cst" "cst_1" Md Kd Nd
      (c.bind "k" (TritonValue.scalar (Int.ofNat kk)))
      (sc.bind "k" (SymValue.scalar (Expr.lit (Int.ofNat kk)))) mem := by
    exact ⟨hfw',
      ⟨aptrvals, by simpa [MachineState.bind] using haptr⟩,
      ⟨bptrvals, by simpa [MachineState.bind] using hbptr⟩,
      ⟨accvals,  by simpa [MachineState.bind] using hacc⟩,
      ⟨amvals,   by simpa [MachineState.bind] using hamask⟩,
      ⟨bmvals,   by simpa [MachineState.bind] using hbmask⟩,
      ⟨afillvals, by simpa [MachineState.bind] using hafill⟩,
      ⟨bfillvals, by simpa [MachineState.bind] using hbfill⟩,
      ⟨cst1vals, by simpa [MachineState.bind] using hcst1⟩,
      ⟨xc_i,  by simpa [MachineState.bind] using hc32_i⟩,
      ⟨xK_i,  by simpa [MachineState.bind] using hKv_i⟩,
      ⟨xsb_i, by simpa [MachineState.bind] using hsb_i⟩⟩
  -- body preserves FaithfulWFI + restores the iter-args
  have hpres := matmul_body_preserves (c := c.bind "k" (TritonValue.scalar (Int.ofNat kk)))
    (sc := sc.bind "k" (SymValue.scalar (Expr.lit (Int.ofNat kk)))) (mem := mem)
    Md Kd Nd hKpos hNpos (Int.ofNat kk) xc xK xsb hk' hc32' hKv' hsb' hinv'
  simp only at hpres
  obtain ⟨fEnd, ha47, hb48, hacc49⟩ := hpres
  -- the six pre-loop tensors are never written by the body
  have hcarry : ∀ (w : String),
      w ≠ "a" → w ≠ "a_50" → w ≠ "a_51" → w ≠ "a_52" → w ≠ "a_53" → w ≠ "a_54" →
      w ≠ "b" → w ≠ "b_55" → w ≠ "b_56" → w ≠ "b_57" → w ≠ "accumulator_58" →
      w ≠ "a_ptrs_59" → w ≠ "b_ptrs_60" → w ≠ "b_ptrs_61" → w ≠ "b_ptrs_62" →
      w ≠ "a_ptrs_47" → w ≠ "b_ptrs_48" → w ≠ "accumulator_49" →
      (evalKernel body (c.bind "k" (TritonValue.scalar (Int.ofNat kk)))).env w
        = (c.bind "k" (TritonValue.scalar (Int.ofNat kk))).env w := by
    intro w n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18
    exact env_carry_kernel body _ w
      (by intro i hi
          simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
          <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,J1,J2,J3,J4,J5,J6,J7])
      (by intro i hi
          simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
          <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,J1,J2,J3,J4,J5,J6,J7])
      (by intro i hi
          simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
          <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,J1,J2,J3,J4,J5,J6,J7,
                    n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13,n14,n15,n16,n17,n18])
  have ham := (hcarry "a_ptrs_18" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                (by simpa [MachineState.bind] using hamask)
  have hbm := (hcarry "b_ptrs" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                (by simpa [MachineState.bind] using hbmask)
  have haf := (hcarry "cst_0" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                (by simpa [MachineState.bind] using hafill)
  have hbf := (hcarry "cst" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                (by simpa [MachineState.bind] using hbfill)
  have hc1 := (hcarry "cst_1" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                (by simpa [MachineState.bind] using hcst1)
  have hsc32 := (hcarry "c32_i32" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  (by simpa [MachineState.bind] using hc32_i)
  have hsK := (hcarry "K" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  (by simpa [MachineState.bind] using hKv_i)
  have hssb := (hcarry "stride_bk" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
                  (by simpa [MachineState.bind] using hsb_i)
  exact ⟨fEnd, ha47, hb48, hacc49, ⟨amvals, ham⟩, ⟨bmvals, hbm⟩, ⟨afillvals, haf⟩,
         ⟨bfillvals, hbf⟩, ⟨cst1vals, hc1⟩, ⟨xc_i, hsc32⟩, ⟨xK_i, hsK⟩, ⟨xsb_i, hssb⟩⟩

-- ── forLoop_matmul: the accumulator loop preserves MatmulLoopInv ─────────────────
-- Instantiates loop_faithful_skeleton with R := MatmulLoopInv, discharging the per-iteration
-- step with matmul_body_step. The invariant is self-sufficient (it carries the ambient
-- scalars), so no external hypotheses are needed inside the loop.
theorem forLoop_matmul
    {c : MachineState} {sc : SymState} {mem : Nat → Int} (Md Kd Nd : Nat)
    (hKpos : 0 < Kd) (hNpos : 0 < Nd) (trip : Nat)
    (hinit : MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
              "cst_0" "cst" "cst_1" Md Kd Nd c sc mem) :
    MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
      "cst_0" "cst" "cst_1" Md Kd Nd
      (evalForLoop { ivName := "k", trip := trip, body := MatmulBody Md Kd Nd } c)
      (symEvalForLoop { ivName := "k", trip := trip, body := MatmulBody Md Kd Nd } sc) mem := by
  unfold evalForLoop symEvalForLoop
  refine loop_faithful_skeleton
    (fun cc scc => MatmulLoopInv "a_ptrs_47" "b_ptrs_48" "accumulator_49" "a_ptrs_18" "b_ptrs"
      "cst_0" "cst" "cst_1" Md Kd Nd cc scc mem)
    (fun kk st => evalKernel (MatmulBody Md Kd Nd) (st.bind "k" (TritonValue.scalar (Int.ofNat kk))))
    (fun kk st => symEvalKernel (MatmulBody Md Kd Nd) (st.bind "k" (SymValue.scalar (Expr.lit (Int.ofNat kk)))))
    trip ?_ c sc hinit
  intro kk _ cc scc hR
  have hR' := hR
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨xc, hc32⟩, ⟨xK, hKv⟩, ⟨xsb, hsb⟩⟩ := hR
  have hstep := matmul_body_step (c := cc) (sc := scc) (mem := mem) Md Kd Nd hKpos hNpos
    xc xK xsb hc32 hKv hsb hR' kk
  simpa [MatmulBody] using hstep

-- ══════════════════════════════════════════════════════════════════════════════
-- Matmul VALUE semantics: the dot really computes a contraction, lane by lane.
-- ══════════════════════════════════════════════════════════════════════════════

theorem range_map_getD_gen (N idx : Nat) (f : Nat → Int) (h : idx < N) :
    ((List.range N).map f).getD idx 0 = f idx := by
  simp [List.getD, List.getElem?_map, List.getElem?_range, h]

/-- The mathematical contraction: C[i,j] = Σ_{kk<k1} A[i,kk] · B[kk,j] (row-major). -/
def contract (A B : List Int) (k1 n i j : Nat) : Int :=
  (List.range k1).foldl
    (fun s kk => s + (A.getD (i * k1 + kk) 0) * (B.getD (kk * n + j) 0)) 0

/-- The matrix row that tile lane `i` of program `pidm` addresses.

    The kernel builds  offs_am = (pid_m * Md + range Md) % M.  Lanes whose unwrapped row
    would fall past the bottom of the matrix WRAP around; the store mask (offs_am < M)
    discards them. Modelling the wrap here is what lets the theorem cover every program
    in the grid, not just those whose tile lies entirely inside the matrix. -/
def AptrRow (pidm Md M i : Nat) : Nat := (pidm * Md + i) % M

theorem lane_div (i j n : Nat) (hj : j < n) : (i * n + j) / n = i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  rw [Nat.add_comm (i * n) j, Nat.add_mul_div_right j i hn, Nat.div_eq_of_lt hj, Nat.zero_add]

theorem lane_mod (i j n : Nat) (hj : j < n) : (i * n + j) % n = j := by
  rw [Nat.add_comm (i * n) j, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hj

theorem lane_lt (i j m n : Nat) (hi : i < m) (hj : j < n) : i * n + j < m * n := by
  have h1 : i + 1 ≤ m := hi
  have : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right n h1
  have h2 : i * n + n = (i + 1) * n := by
    simp [Nat.succ_mul]
  omega

theorem dot_lane_value (m k1 n i j : Nat) (A B Acc : List Int)
    (hi : i < m) (hj : j < n) :
    ((List.range (m * n)).map (fun idx =>
        (List.range k1).foldl (fun acc' kk =>
          acc' + (A.getD ((idx / n) * k1 + kk) 0) * (B.getD (kk * n + (idx % n)) 0)) 0
        + Acc.getD idx 0)).getD (i * n + j) 0
      = contract A B k1 n i j + Acc.getD (i * n + j) 0 := by
  rw [range_map_getD_gen (m * n) (i * n + j) _ (lane_lt i j m n hi hj)]
  rw [lane_div i j n hj, lane_mod i j n hj]
  simp [contract]

-- ══════════════════════════════════════════════════════════════════════════════
-- Matmul memory layout + the value-domain invariant (what the kernel must compute)
-- ══════════════════════════════════════════════════════════════════════════════

/-- Row-major layout: A (M×K) at [0, M*K), B (K×N) next, C (M×N) after that. -/
def layoutMatmul (A B : List Int) (M K N : Nat) : Nat → Int := fun addr =>
  if addr < M * K then A.getD addr 0
  else if addr < M * K + K * N then B.getD (addr - M * K) 0
  else 0

/-- Address of A[i,k] under layoutMatmul (a_ptr = 0, stride_am = K). -/
def addrA (K i k : Nat) : Nat := i * K + k

/-- Address of B[k,j] (b_ptr = M*K, stride_bk = N). -/
def addrB (M K N k j : Nat) : Nat := M * K + k * N + j

/-- Address of C[i,j] (c_ptr = M*K + K*N, stride_cm = N). -/
def addrC (M K N i j : Nat) : Nat := M * K + K * N + i * N + j

/-- Reading A[i,k] out of the laid-out memory gives back A's entry. -/
theorem layoutMatmul_A (A B : List Int) (M K N i k : Nat)
    (hi : i < M) (hk : k < K) :
    layoutMatmul A B M K N (addrA K i k) = A.getD (i * K + k) 0 := by
  have hlt : i * K + k < M * K := lane_lt i k M K hi hk
  simp [layoutMatmul, addrA, hlt]

/-- Reading B[k,j] gives back B's entry (offset by the A region). -/
theorem layoutMatmul_B (A B : List Int) (M K N k j : Nat)
    (hk : k < K) (hj : j < N) :
    layoutMatmul A B M K N (addrB M K N k j) = B.getD (k * N + j) 0 := by
  have hkn : k * N + j < K * N := lane_lt k j K N hk hj
  have hassoc : M * K + k * N + j = M * K + (k * N + j) := by
    rw [Nat.add_assoc]
  have h1 : ¬ (M * K + k * N + j < M * K) := by
    rw [hassoc]; exact Nat.not_lt.mpr (Nat.le_add_right _ _)
  have h2 : M * K + k * N + j < M * K + K * N := by
    rw [hassoc]; exact Nat.add_lt_add_left hkn _
  have hsub : M * K + k * N + j - M * K = k * N + j := by
    rw [hassoc, Nat.add_sub_cancel_left]
  simp [layoutMatmul, addrB, h1, h2, hsub]

/-- Partial contraction over the first `t` k-tiles of width `Kd`, for TILE LANE `i` --
    which addresses matrix row `AptrRow pidm Md M i`. -/
def AccPartial (A B : List Int) (pidm Md M Kfull N i j t Kd : Nat) : Int :=
  (List.range (t * Kd)).foldl
    (fun s kk => s + (A.getD (AptrRow pidm Md M i * Kfull + kk) 0) * (B.getD (kk * N + j) 0)) 0

/-- After all `T` tiles (T*Kd = Kfull), tile lane `i` holds the contraction for matrix
    row `AptrRow pidm Md M i`. This is the sentence the whole proof is aiming at. -/
theorem AccPartial_full (A B : List Int) (pidm Md M Kfull N i j T Kd : Nat)
    (hT : T * Kd = Kfull) :
    AccPartial A B pidm Md M Kfull N i j T Kd
      = contract A B Kfull N (AptrRow pidm Md M i) j := by
  simp [AccPartial, contract, hT]

-- ══════════════════════════════════════════════════════════════════════════════
-- The ADDRESS invariant: the pointer tensors hold exactly tile t's addresses.
-- ══════════════════════════════════════════════════════════════════════════════

/-- a_ptrs at iteration t, lane (i,kk).

    The kernel builds  offs_am = (pid_m*Md + range Md) % M  and then
      a_ptrs[i,kk] = a_ptr + offs_am[i] * stride_am + offs_k[kk]
    With the row-major layout (a_ptr = 0, stride_am = Kfull) this is the address of
    A[row i of this program's tile, column t*Kd + kk], where the row index WRAPS:
      row = (pid_m * Md + i) % M
    Rows produced by the wrap are computed but discarded by the store mask (offs_am < M).
    Modelling the wrap here is what lets the theorem cover the ragged edge of the grid. -/
def AptrTile (pidm Md M Kfull Kd t : Nat) (i kk : Nat) : Int :=
  Int.ofNat (AptrRow pidm Md M i * Kfull + (t * Kd + kk))

/-- b_ptrs at iteration t: lane (kk,j) holds the address of B[t*Kd+kk, j]. -/
def BptrTile (M Kfull N Kd t : Nat) (kk j : Nat) : Int :=
  Int.ofNat (M * Kfull + (t * Kd + kk) * N + j)

/-- Advancing every lane by Kd moves the A-pointers from tile t to tile t+1.
    The row index is untouched, so the wrap plays no part here. -/
theorem AptrTile_step (pidm Md M Kfull Kd t i kk : Nat) :
    AptrTile pidm Md M Kfull Kd t i kk + Int.ofNat Kd
      = AptrTile pidm Md M Kfull Kd (t + 1) i kk := by
  have hnat : AptrRow pidm Md M i * Kfull + (t * Kd + kk) + Kd
      = AptrRow pidm Md M i * Kfull + ((t + 1) * Kd + kk) := by
    have h : (t + 1) * Kd = t * Kd + Kd := by simp [Nat.succ_mul]
    rw [h]; omega
  show Int.ofNat (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) + Int.ofNat Kd
      = Int.ofNat (AptrRow pidm Md M i * Kfull + ((t + 1) * Kd + kk))
  rw [← hnat]
  rfl

/-- Advancing b_ptrs by N*Kd on every lane moves it from tile t to tile t+1. -/
theorem BptrTile_step (M Kfull N Kd t kk j : Nat) :
    BptrTile M Kfull N Kd t kk j + Int.ofNat (N * Kd) = BptrTile M Kfull N Kd (t + 1) kk j := by
  have hstep : (t + 1) * Kd + kk = (t * Kd + kk) + Kd := by
    have h : (t + 1) * Kd = t * Kd + Kd := by simp [Nat.succ_mul]
    rw [h]; omega
  have hmul : ((t * Kd + kk) + Kd) * N = (t * Kd + kk) * N + N * Kd := by
    rw [Nat.add_mul, Nat.mul_comm Kd N]
  have hnat : M * Kfull + (t * Kd + kk) * N + j + N * Kd
      = M * Kfull + ((t + 1) * Kd + kk) * N + j := by
    rw [hstep, hmul]; omega
  show Int.ofNat (M * Kfull + (t * Kd + kk) * N + j) + Int.ofNat (N * Kd)
      = Int.ofNat (M * Kfull + ((t + 1) * Kd + kk) * N + j)
  rw [← hnat]
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- tile_load_value: the masked load turns tile-t addresses into tile-t data.
-- This is the bridge between the ADDRESS invariant and the VALUE invariant.
-- ══════════════════════════════════════════════════════════════════════════════

/-- The A-tile load. Lane (i,kk) of the loaded tile holds A[row, t*Kd+kk] when that column
    is in range, and the (zero) fill otherwise, where `row = AptrRow pidm Md M i` is the
    WRAPPED matrix row this tile lane addresses.

    Note the row bound is now free: `x % M < M` for any `x`, given `0 < M`. So the caller
    no longer has to supply `i < M` -- which is exactly what lets the theorem cover tiles
    that run past the bottom of the matrix. Those lanes read wrapped rows; the store mask
    discards them. -/
theorem tile_load_value_A
    (A B : List Int) (pidm M Kfull N Md Kd t i kk : Nat)
    (addrs masks fills : List Int)
    (hi : i < Md) (hkk : kk < Kd)
    (hMpos : 0 < M)
    (hlm : addrs.length = masks.length) (hlf : addrs.length = fills.length)
    (hlen : addrs.length = Md * Kd)
    (haddr : addrs.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
    (hmask : masks.getD (i * Kd + kk) 0 = (if t * Kd + kk < Kfull then 1 else 0))
    (hfill : fills.getD (i * Kd + kk) 0 = 0) :
    (((addrs.zip masks).zip fills).map
        (fun x => if (x.fst.snd != 0) = true
                  then layoutMatmul A B M Kfull N x.fst.fst.natAbs
                  else x.snd)).getD (i * Kd + kk) 0
      = (if t * Kd + kk < Kfull
         then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0) := by
  have hlane : i * Kd + kk < addrs.length := by
    rw [hlen]; exact lane_lt i kk Md Kd hi hkk
  have hrowM : AptrRow pidm Md M i < M := Nat.mod_lt _ hMpos
  rw [zip_mask_load_fill_getD addrs masks fills (i * Kd + kk)
        (fun a => layoutMatmul A B M Kfull N a.natAbs) hlane hlm hlf]
  rw [hmask, haddr, hfill]
  by_cases hc : t * Kd + kk < Kfull
  · simp only [hc, if_true]
    have : ((1 : Int) != 0) = true := by decide
    simp only [this, if_true]
    simp only [AptrTile]
    exact layoutMatmul_A A B M Kfull N (AptrRow pidm Md M i) (t * Kd + kk) hrowM hc
  · simp only [hc, if_false]
    have : ((0 : Int) != 0) = false := by decide
    simp only [this, Bool.false_eq_true, if_false]

/-- The B-tile load. Lane (kk,j) is B[t*Kd+kk, j] when that row is in range, else 0. -/
theorem tile_load_value_B
    (A B : List Int) (M Kfull N Kd Nd t kk j : Nat)
    (addrs masks fills : List Int)
    (hkk : kk < Kd) (hj : j < Nd)
    (hjN : j < N)
    (hlm : addrs.length = masks.length) (hlf : addrs.length = fills.length)
    (hlen : addrs.length = Kd * Nd)
    (haddr : addrs.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
    (hmask : masks.getD (kk * Nd + j) 0 = (if t * Kd + kk < Kfull then 1 else 0))
    (hfill : fills.getD (kk * Nd + j) 0 = 0) :
    (((addrs.zip masks).zip fills).map
        (fun x => if (x.fst.snd != 0) = true
                  then layoutMatmul A B M Kfull N x.fst.fst.natAbs
                  else x.snd)).getD (kk * Nd + j) 0
      = (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0) := by
  have hlane : kk * Nd + j < addrs.length := by
    rw [hlen]; exact lane_lt kk j Kd Nd hkk hj
  rw [zip_mask_load_fill_getD addrs masks fills (kk * Nd + j)
        (fun a => layoutMatmul A B M Kfull N a.natAbs) hlane hlm hlf]
  rw [hmask, haddr, hfill]
  by_cases hc : t * Kd + kk < Kfull
  · simp only [hc, if_true]
    have h1 : ((1 : Int) != 0) = true := by decide
    simp only [h1, if_true]
    simp only [BptrTile]
    exact layoutMatmul_B A B M Kfull N (t * Kd + kk) j hc hjN
  · simp only [hc, if_false]
    have h0 : ((0 : Int) != 0) = false := by decide
    simp only [h0, Bool.false_eq_true, if_false]

-- ══════════════════════════════════════════════════════════════════════════════
-- AccPartial's inductive step: one more tile adds that tile's contribution.
-- ══════════════════════════════════════════════════════════════════════════════

/-- foldl over range (a+b) = foldl over range a, then over the shifted range b. -/
theorem foldl_range_add (f : Int → Nat → Int) (a b : Nat) (init : Int) :
    (List.range (a + b)).foldl f init
      = (List.range b).foldl (fun s i => f s (a + i)) ((List.range a).foldl f init) := by
  induction b generalizing init with
  | zero => simp
  | succ n ih =>
      have hr : List.range (a + (n + 1)) = List.range (a + n) ++ [a + n] := by
        rw [← Nat.add_assoc]
        exact List.range_succ
      rw [hr, List.foldl_append]
      rw [ih]
      rw [List.range_succ, List.foldl_append]
      simp

/-- Adding one k-tile of width Kd grows AccPartial by that tile's contribution. -/
theorem AccPartial_succ (A B : List Int) (pidm Md M Kfull N i j t Kd : Nat) :
    AccPartial A B pidm Md M Kfull N i j (t + 1) Kd
      = (List.range Kd).foldl
          (fun s kk => s + (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
                         * (B.getD ((t * Kd + kk) * N + j) 0))
          (AccPartial A B pidm Md M Kfull N i j t Kd) := by
  have hsplit : (t + 1) * Kd = t * Kd + Kd := by simp [Nat.succ_mul]
  simp only [AccPartial, hsplit]
  rw [foldl_range_add]

-- ══════════════════════════════════════════════════════════════════════════════
-- The masked tile product agrees with the spec's product, term by term.
-- Out-of-range columns: the kernel zeroes them via the mask; the spec reads past the
-- end of A (and B), where getD's default is 0. Both give 0 -- provided A and B have
-- exactly the dimensions the spec claims.
-- ══════════════════════════════════════════════════════════════════════════════

/-- Reading past the end of a list gives the default. -/
theorem getD_oob (l : List Int) (i : Nat) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD, List.getElem?_eq_none h]

theorem masked_term_eq (A B : List Int) (pidm Md M Kfull N i j t Kd kk : Nat)
    (hB : B.length = Kfull * N)
    (hjN : j < N) :
    (if t * Kd + kk < Kfull
     then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0)
      * (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0)
      = (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
        * (B.getD ((t * Kd + kk) * N + j) 0) := by
  by_cases hc : t * Kd + kk < Kfull
  · simp [hc]
  · -- out of range: the spec's B-read is past the end of B, so it is 0
    simp only [hc, if_false, Int.zero_mul]
    have hge : Kfull ≤ t * Kd + kk := Nat.not_lt.mp hc
    have hBoob : B.length ≤ (t * Kd + kk) * N + j := by
      rw [hB]
      calc Kfull * N ≤ (t * Kd + kk) * N := Nat.mul_le_mul_right N hge
      _ ≤ (t * Kd + kk) * N + j := Nat.le_add_right _ _
    rw [getD_oob B _ hBoob]
    exact (Int.mul_zero _).symm

-- ══════════════════════════════════════════════════════════════════════════════
-- MatmulValueInv: what the pointers and the accumulator HOLD after t iterations.
-- Stated separately from MatmulLoopInv (which is about shapes) so the shape walk
-- stays untouched; the two compose.
-- ══════════════════════════════════════════════════════════════════════════════

/-- After `t` iterations: the pointer tensors address tile `t`, and the accumulator holds
    the partial contraction over the first `t` tiles. -/
def MatmulValueInv (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat) (c : MachineState) : Prop :=
  (∃ av, c.env "a_ptrs_47" = some (tensor [Md, Kd] av)
      ∧ av.length = Md * Kd
      ∧ ∀ i kk, i < Md → kk < Kd →
          av.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
  ∧ (∃ bv, c.env "b_ptrs_48" = some (tensor [Kd, Nd] bv)
      ∧ bv.length = Kd * Nd
      ∧ ∀ kk j, kk < Kd → j < Nd → bv.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
  ∧ (∃ cv, c.env "accumulator_49" = some (tensor [Md, Nd] cv)
      ∧ cv.length = Md * Nd
      ∧ ∀ i j, i < Md → j < Nd →
          cv.getD (i * Nd + j) 0 = AccPartial A B pidm Md M Kfull N i j t Kd)

/-- At loop entry (t = 0) the accumulator is the zero tensor and the partial sum is 0. -/
theorem AccPartial_zero (A B : List Int) (pidm Md M Kfull N i j Kd : Nat) :
    AccPartial A B pidm Md M Kfull N i j 0 Kd = 0 := by
  simp [AccPartial]

/-- At t = 0 the A-pointer addresses column kk of the tile's row i. -/
theorem AptrTile_zero (pidm Md M Kfull Kd i kk : Nat) :
    AptrTile pidm Md M Kfull Kd 0 i kk
      = Int.ofNat (AptrRow pidm Md M i * Kfull + kk) := by
  simp [AptrTile]

/-- At t = 0 the B-pointer addresses row kk, column j. -/
theorem BptrTile_zero (M Kfull N Kd kk j : Nat) :
    BptrTile M Kfull N Kd 0 kk j = Int.ofNat (M * Kfull + kk * N + j) := by
  simp [BptrTile]

-- ══════════════════════════════════════════════════════════════════════════════
-- Per-lane value lemmas for the mask chain (splat -> cmpi -> broadcast).
-- ══════════════════════════════════════════════════════════════════════════════

/-- A splat's every lane is the splatted scalar. -/
theorem splat_lane (shape : List Nat) (x : Int) (idx : Nat)
    (h : idx < shape.foldl (· * ·) 1) :
    (List.replicate (shape.foldl (· * ·) 1) x).getD idx 0 = x := by
  simp [List.getD, List.getElem?_replicate, h]

/-- Broadcasting a [1,c] row to [r,c]: lane (i,j) is the source's lane j. -/
theorem broadcast_row_lane (src : List Int) (r c i j : Nat)
    (hi : i < r) (hj : j < c) :
    ((List.range (r * c)).map (fun idx =>
        src.getD ((if (1:Nat) == 1 then 0 else idx / c) * c
                  + (if c == 1 then 0 else idx % c)) 0)).getD (i * c + j) 0
      = src.getD (if c == 1 then 0 else j) 0 := by
  rw [range_map_getD_gen (r * c) (i * c + j) _ (lane_lt i j r c hi hj)]
  simp only [beq_self_eq_true, if_true, Nat.zero_mul, Nat.zero_add]
  by_cases hc : c == 1
  · simp [hc]
  · simp only [hc, if_false, Bool.false_eq_true]
    rw [lane_mod i j c hj]

/-- Broadcasting a [r,1] column to [r,c]: lane (i,j) is the source's lane i. -/
theorem broadcast_col_lane (src : List Int) (r c i j : Nat)
    (hi : i < r) (hj : j < c) (hr : ¬ (r == 1)) :
    ((List.range (r * c)).map (fun idx =>
        src.getD ((if r == 1 then 0 else idx / c) * 1
                  + (if (1:Nat) == 1 then 0 else idx % c)) 0)).getD (i * c + j) 0
      = src.getD i 0 := by
  rw [range_map_getD_gen (r * c) (i * c + j) _ (lane_lt i j r c hi hj)]
  simp only [hr, if_false, Bool.false_eq_true, beq_self_eq_true, if_true, Nat.add_zero,
             Nat.mul_one]
  rw [lane_div i j c hj]

-- ══════════════════════════════════════════════════════════════════════════════
-- THE MASK BOUNDARY. The kernel computes the k-bound over Int:
--     mask lane kk  =  (offs_k[kk] < K - t*Kd)   with offs_k[kk] = kk
-- The spec wants   t*Kd + kk < Kfull.  These agree -- and crucially the comparison is
-- over Int, so when t*Kd > Kfull the RHS goes NEGATIVE and no lane passes. Over Nat the
-- subtraction would truncate to 0 and the mask would wrongly admit every lane.
-- This is exactly why the tail tile is handled correctly.
-- ══════════════════════════════════════════════════════════════════════════════

theorem mask_boundary (t Kd Kfull kk : Nat) :
    (Int.ofNat kk < Int.ofNat Kfull - Int.ofNat (t * Kd)) ↔ (t * Kd + kk < Kfull) := by
  constructor
  · intro h
    have h' : Int.ofNat (t * Kd + kk) < Int.ofNat Kfull := by
      show Int.ofNat (t * Kd) + Int.ofNat kk < Int.ofNat Kfull
      omega
    exact Int.ofNat_lt.mp h'
  · intro h
    have h' : Int.ofNat (t * Kd + kk) < Int.ofNat Kfull := Int.ofNat_lt.mpr h
    have h'' : Int.ofNat (t * Kd) + Int.ofNat kk < Int.ofNat Kfull := h'
    omega

/-- The mask value the kernel produces at lane kk, as the spec sees it. -/
theorem mask_lane_value (t Kd Kfull kk : Nat) :
    (if Int.ofNat kk < Int.ofNat Kfull - Int.ofNat (t * Kd) then (1:Int) else 0)
      = (if t * Kd + kk < Kfull then 1 else 0) := by
  by_cases h : t * Kd + kk < Kfull
  · rw [if_pos ((mask_boundary t Kd Kfull kk).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((mask_boundary t Kd Kfull kk).mp hc)), if_neg h]

/-- Lane value of a tensor-tensor cmpi_slt. -/
theorem cmpi_lane (xs ys : List Int) (idx : Nat)
    (hi : idx < xs.length) (hlen : xs.length = ys.length) :
    ((xs.zip ys).map (fun p => if p.fst < p.snd then (1:Int) else 0)).getD idx 0
      = (if xs.getD idx 0 < ys.getD idx 0 then 1 else 0) :=
  zip_lt_getD xs ys idx hi hlen

-- ══════════════════════════════════════════════════════════════════════════════
-- The A-mask chain: splat -> cmpi -> broadcast produces exactly the spec's k-bound mask.
--   a_51 = splat[1,Kd] (K - t*Kd)      every lane = K - t*Kd
--   a_52 = cmpi_slt offs_k a_51        lane kk = (kk < K - t*Kd)  over Int
--   a_53 = broadcast[Md,Kd] a_52       lane (i,kk) = a_52[kk]
-- Result: a_53[i*Kd+kk] = if t*Kd+kk < Kfull then 1 else 0.
-- ══════════════════════════════════════════════════════════════════════════════

/-- The cmpi step of the A-mask: offs_k[kk] < (K - t*Kd) is the spec's k-bound. -/
theorem amask_cmpi_lane (offs : List Int) (Kfull t Kd kk : Nat)
    (hlen : offs.length = 1 * Kd) (hkk : kk < Kd)
    (hoffs : offs.getD kk 0 = Int.ofNat kk) :
    ((offs.zip (List.replicate ([1, Kd].foldl (· * ·) 1)
        (Int.ofNat Kfull - Int.ofNat (t * Kd)))).map
        (fun p => if p.fst < p.snd then (1:Int) else 0)).getD kk 0
      = (if t * Kd + kk < Kfull then 1 else 0) := by
  have hrep : ([1, Kd].foldl (· * ·) 1) = Kd := by simp [List.foldl]
  have hlen1 : offs.length = Kd := by rw [hlen]; simp
  have hlenr : offs.length =
      (List.replicate ([1, Kd].foldl (· * ·) 1) (Int.ofNat Kfull - Int.ofNat (t * Kd))).length := by
    simp [hrep, hlen1]
  have hklt : kk < offs.length := by rw [hlen1]; exact hkk
  rw [cmpi_lane offs _ kk hklt hlenr]
  rw [hoffs]
  rw [splat_lane [1, Kd] (Int.ofNat Kfull - Int.ofNat (t * Kd)) kk (by rw [hrep]; exact hkk)]
  exact mask_lane_value t Kd Kfull kk

-- The B-mask chain. Structurally identical to the A side, but the source is b_ptrs
-- (offs_k as [Kd,1]) and the splat is [Kd,1], so the broadcast replicates the COLUMN.
theorem bmask_cmpi_lane (offs : List Int) (Kfull t Kd kk : Nat)
    (hlen : offs.length = Kd * 1) (hkk : kk < Kd)
    (hoffs : offs.getD kk 0 = Int.ofNat kk) :
    ((offs.zip (List.replicate ([Kd, 1].foldl (· * ·) 1)
        (Int.ofNat Kfull - Int.ofNat (t * Kd)))).map
        (fun p => if p.fst < p.snd then (1:Int) else 0)).getD kk 0
      = (if t * Kd + kk < Kfull then 1 else 0) := by
  have hrep : ([Kd, 1].foldl (· * ·) 1) = Kd := by simp [List.foldl]
  have hlen1 : offs.length = Kd := by rw [hlen]; simp
  have hlenr : offs.length =
      (List.replicate ([Kd, 1].foldl (· * ·) 1) (Int.ofNat Kfull - Int.ofNat (t * Kd))).length := by
    simp [hrep, hlen1]
  have hklt : kk < offs.length := by rw [hlen1]; exact hkk
  rw [cmpi_lane offs _ kk hklt hlenr]
  rw [hoffs]
  rw [splat_lane [Kd, 1] (Int.ofNat Kfull - Int.ofNat (t * Kd)) kk (by rw [hrep]; exact hkk)]
  exact mask_lane_value t Kd Kfull kk

-- ══════════════════════════════════════════════════════════════════════════════
-- The dot step in the VALUE domain: contracting the two loaded tiles grows AccPartial
-- by exactly one tile. Combines dot_lane_value, the tile-load lemmas, masked_term_eq
-- and AccPartial_succ.
-- ══════════════════════════════════════════════════════════════════════════════

/-- The contraction of the two masked tiles equals the spec's tile contribution. -/
theorem tile_contraction_eq
    (A B : List Int) (pidm Md M Kfull N Kd Nd t i j : Nat)
    (aTile bTile : List Int)
    (hB : B.length = Kfull * N)
    (hjN : j < N)
    (hA_tile : ∀ kk, kk < Kd →
        aTile.getD (i * Kd + kk) 0
          = (if t * Kd + kk < Kfull
             then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0))
    (hB_tile : ∀ kk, kk < Kd →
        bTile.getD (kk * Nd + j) 0
          = (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0)) :
    (List.range Kd).foldl
      (fun acc' kk => acc' + (aTile.getD (i * Kd + kk) 0) * (bTile.getD (kk * Nd + j) 0)) 0
    = (List.range Kd).foldl
      (fun s kk => s + (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
                     * (B.getD ((t * Kd + kk) * N + j) 0)) 0 := by
  -- the two folds agree term by term on range Kd
  have hterm : ∀ kk, kk < Kd →
      (aTile.getD (i * Kd + kk) 0) * (bTile.getD (kk * Nd + j) 0)
        = (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
          * (B.getD ((t * Kd + kk) * N + j) 0) := by
    intro kk hkk
    rw [hA_tile kk hkk, hB_tile kk hkk]
    exact masked_term_eq A B pidm Md M Kfull N i j t Kd kk hB hjN
  -- fold congruence over range
  have hgen : ∀ (l : List Nat), (∀ kk ∈ l, kk < Kd) → ∀ init,
      l.foldl (fun acc' kk => acc' + (aTile.getD (i * Kd + kk) 0) * (bTile.getD (kk * Nd + j) 0)) init
        = l.foldl (fun s kk => s + (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
                                 * (B.getD ((t * Kd + kk) * N + j) 0)) init := by
    intro l
    induction l with
    | nil => intro _ init; rfl
    | cons x xs ih =>
        intro hmem init
        simp only [List.foldl_cons]
        rw [hterm x (hmem x (List.mem_cons_self ..))]
        exact ih (fun k hk => hmem k (List.mem_cons_of_mem _ hk)) _
  exact hgen (List.range Kd) (fun kk hkk => List.mem_range.mp hkk) 0

-- ══════════════════════════════════════════════════════════════════════════════
-- Loop-invariant constants the value walk needs. Established once at loop entry.
--   a_ptrs_18 : [1,Kd]   lane kk = kk   (expand_dims 0 of make_range Kd)
--   b_ptrs    : [Kd,1]   lane kk = kk   (expand_dims 1 of the same)
--   cst_1     : [Md,Kd]  every lane = Kd     (constant_tensor Kd [Md,Kd])
--   stride_bk = N        (row-major B; the spec's layout assumption, stated honestly)
-- ══════════════════════════════════════════════════════════════════════════════

def MatmulConsts (A B : List Int) (M Kfull N Md Kd Nd : Nat) (c : MachineState) : Prop :=
  -- memory holds the two input matrices in row-major layout (no stores in the body,
  -- so this is loop-invariant). Connects readMem to layoutMatmul_A / layoutMatmul_B.
  (c.memory = layoutMatmul A B M Kfull N)
  ∧ (∃ ov, c.env "a_ptrs_18" = some (tensor [1, Kd] ov)
      ∧ ov.length = Kd ∧ ∀ kk, kk < Kd → ov.getD kk 0 = Int.ofNat kk)
  ∧ (∃ ov, c.env "b_ptrs" = some (tensor [Kd, 1] ov)
      ∧ ov.length = Kd ∧ ∀ kk, kk < Kd → ov.getD kk 0 = Int.ofNat kk)
  ∧ (∃ sv, c.env "cst_1" = some (tensor [Md, Kd] sv)
      ∧ sv.length = Md * Kd ∧ ∀ idx, idx < Md * Kd → sv.getD idx 0 = Int.ofNat Kd)
  ∧ (c.env "stride_bk" = some (scalar (Int.ofNat N)))
  ∧ (c.env "c32_i32" = some (scalar (Int.ofNat Kd)))
  ∧ (∃ fv, c.env "cst_0" = some (tensor [Md, Kd] fv)
      ∧ fv.length = Md * Kd ∧ ∀ idx, idx < Md * Kd → fv.getD idx 0 = 0)
  ∧ (∃ fv, c.env "cst" = some (tensor [Kd, Nd] fv)
      ∧ fv.length = Kd * Nd ∧ ∀ idx, idx < Kd * Nd → fv.getD idx 0 = 0)

/-- make_range n has lane i = i. -/
theorem make_range_lane (n i : Nat) (h : i < n) :
    (List.map Int.ofNat (List.range n)).getD i 0 = Int.ofNat i := by
  rw [range_map_getD]
  simp [h]

/-- constant_tensor's every lane is the constant. -/
theorem const_tensor_lane (shape : List Nat) (v : Int) (idx : Nat)
    (h : idx < shape.foldl (· * ·) 1) :
    (List.replicate (shape.foldl (· * ·) 1) v).getD idx 0 = v :=
  splat_lane shape v idx h

-- ══════════════════════════════════════════════════════════════════════════════
-- The A-tile value chain: I1..I6 produce a_54 holding tile t of A.
--   I1 a      = k * c32          = t * Kd
--   I2 a_50   = K - a            = Kfull - t*Kd     (over Int)
--   I3 a_51   = splat[1,Kd] a_50
--   I4 a_52   = cmpi_slt a_ptrs_18 a_51             lane kk = (t*Kd+kk < Kfull)
--   I5 a_53   = broadcast[Md,Kd] a_52               lane (i,kk) = a_52[kk]
--   I6 a_54   = load a_ptrs_47 a_53 cst_0           lane (i,kk) = A[i, t*Kd+kk] or 0
-- ══════════════════════════════════════════════════════════════════════════════

theorem atile_mask_lane
    (Md Kd Kfull t : Nat) (offs : List Int)
    (hoffs_len : offs.length = Kd)
    (hoffs : ∀ kk, kk < Kd → offs.getD kk 0 = Int.ofNat kk)
    (i kk : Nat) (hi : i < Md) (hkk : kk < Kd) :
    ((List.range (Md * Kd)).map (fun idx =>
        ((offs.zip (List.replicate ([1, Kd].foldl (· * ·) 1)
            (Int.ofNat Kfull - Int.ofNat (t * Kd)))).map
            (fun q => if q.fst < q.snd then (1:Int) else 0)).getD
          ((if (1:Nat) == 1 then 0 else idx / Kd) * Kd
           + (if Kd == 1 then 0 else idx % Kd)) 0)).getD (i * Kd + kk) 0
      = (if t * Kd + kk < Kfull then 1 else 0) := by
  rw [broadcast_row_lane _ Md Kd i kk hi hkk]
  by_cases hc : Kd == 1
  · -- Kd = 1, so the only lane is kk = 0
    have hKd1 : Kd = 1 := by simpa using hc
    have hkk0 : kk = 0 := by omega
    simp only [hc, if_true]
    subst hkk0
    exact amask_cmpi_lane offs Kfull t Kd 0 (by rw [hoffs_len]; simp) hkk (hoffs 0 hkk)
  · simp only [hc, if_false, Bool.false_eq_true]
    exact amask_cmpi_lane offs Kfull t Kd kk (by rw [hoffs_len]; simp) hkk (hoffs kk hkk)

/-- The B-mask, read at lane (kk,j). Broadcast replicates the COLUMN, so lane (kk,j)
    is the cmpi's lane kk -- independent of j, as it must be. -/
theorem btile_mask_lane
    (Kd Nd Kfull t : Nat) (offs : List Int)
    (hoffs_len : offs.length = Kd)
    (hoffs : ∀ kk, kk < Kd → offs.getD kk 0 = Int.ofNat kk)
    (hKd : ¬ (Kd == 1))
    (kk j : Nat) (hkk : kk < Kd) (hj : j < Nd) :
    ((List.range (Kd * Nd)).map (fun idx =>
        ((offs.zip (List.replicate ([Kd, 1].foldl (· * ·) 1)
            (Int.ofNat Kfull - Int.ofNat (t * Kd)))).map
            (fun q => if q.fst < q.snd then (1:Int) else 0)).getD
          ((if Kd == 1 then 0 else idx / Nd) * 1
           + (if (1:Nat) == 1 then 0 else idx % Nd)) 0)).getD (kk * Nd + j) 0
      = (if t * Kd + kk < Kfull then 1 else 0) := by
  rw [broadcast_col_lane _ Kd Nd kk j hkk hj hKd]
  exact bmask_cmpi_lane offs Kfull t Kd kk (by rw [hoffs_len]; simp) hkk (hoffs kk hkk)

/-- The A-pointer advance: adding the all-Kd tensor moves every lane to tile t+1. -/
theorem aptr_advance_lane
    (pidm M Kfull Kd Md t : Nat) (bases steps : List Int)
    (hbase : ∀ i kk, i < Md → kk < Kd →
        bases.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
    (hstep : ∀ idx, idx < Md * Kd → steps.getD idx 0 = Int.ofNat Kd)
    (hlen : bases.length = steps.length)
    (hblen : bases.length = Md * Kd)
    (i kk : Nat) (hi : i < Md) (hkk : kk < Kd) :
    ((bases.zip steps).map (fun x => x.fst + x.snd)).getD (i * Kd + kk) 0
      = AptrTile pidm Md M Kfull Kd (t + 1) i kk := by
  have hlane : i * Kd + kk < bases.length := by
    rw [hblen]; exact lane_lt i kk Md Kd hi hkk
  rw [zip_add_getD bases steps (i * Kd + kk) hlane hlen]
  rw [hbase i kk hi hkk, hstep (i * Kd + kk) (by rw [← hblen]; exact hlane)]
  exact AptrTile_step pidm Md M Kfull Kd t i kk

/-- An additive fold's seed distributes out:  foldl (·+g·) init l = init + foldl (·+g·) 0 l.
    Bridges dot_lane_value (fold from 0, then add the accumulator) to AccPartial_succ
    (fold seeded with the accumulator). -/
theorem foldl_add_seed (g : Nat → Int) (l : List Nat) (init : Int) :
    l.foldl (fun s kk => s + g kk) init = init + l.foldl (fun s kk => s + g kk) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (init + g x), ih (0 + g x)]
      omega

/-- The B-pointer advance: adding splat(stride_bk * c32) = splat(N*Kd) moves every lane
    to tile t+1. This is where the row-major assumption (stride_bk = N) is used. -/
theorem bptr_advance_lane
    (M Kfull N Kd Nd t : Nat) (bases steps : List Int)
    (hbase : ∀ kk j, kk < Kd → j < Nd →
        bases.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
    (hstep : ∀ idx, idx < Kd * Nd → steps.getD idx 0 = Int.ofNat (N * Kd))
    (hlen : bases.length = steps.length)
    (hblen : bases.length = Kd * Nd)
    (kk j : Nat) (hkk : kk < Kd) (hj : j < Nd) :
    ((bases.zip steps).map (fun x => x.fst + x.snd)).getD (kk * Nd + j) 0
      = BptrTile M Kfull N Kd (t + 1) kk j := by
  have hlane : kk * Nd + j < bases.length := by
    rw [hblen]; exact lane_lt kk j Kd Nd hkk hj
  rw [zip_add_getD bases steps (kk * Nd + j) hlane hlen]
  rw [hbase kk j hkk hj, hstep (kk * Nd + j) (by rw [← hblen]; exact hlane)]
  exact BptrTile_step M Kfull N Kd t kk j

/-- The dot's accumulator update at lane (i,j): AccPartial t grows to AccPartial (t+1). -/
theorem acc_update_lane
    (A B : List Int) (pidm Md M Kfull N Kd Nd t i j : Nat)
    (aTile bTile accIn : List Int)
    (hB : B.length = Kfull * N)
    (hi : i < Md) (hj : j < Nd) (hjN : j < N)
    (hA_tile : ∀ kk, kk < Kd →
        aTile.getD (i * Kd + kk) 0
          = (if t * Kd + kk < Kfull
             then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0))
    (hB_tile : ∀ kk, kk < Kd →
        bTile.getD (kk * Nd + j) 0
          = (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0))
    (hacc : accIn.getD (i * Nd + j) 0 = AccPartial A B pidm Md M Kfull N i j t Kd) :
    ((List.range (Md * Nd)).map (fun idx =>
        (List.range Kd).foldl (fun acc' kk =>
          acc' + (aTile.getD ((idx / Nd) * Kd + kk) 0) * (bTile.getD (kk * Nd + (idx % Nd)) 0)) 0
        + accIn.getD idx 0)).getD (i * Nd + j) 0
      = AccPartial A B pidm Md M Kfull N i j (t + 1) Kd := by
  -- read the lane: contraction of the tiles, plus the incoming accumulator
  rw [dot_lane_value Md Kd Nd i j aTile bTile accIn hi hj]
  rw [hacc]
  -- the tile contraction equals the spec's tile term
  have hcontr : contract aTile bTile Kd Nd i j
      = (List.range Kd).foldl
          (fun s kk => s + (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
                         * (B.getD ((t * Kd + kk) * N + j) 0)) 0 := by
    rw [contract]
    exact tile_contraction_eq A B pidm Md M Kfull N Kd Nd t i j aTile bTile hB hjN hA_tile hB_tile
  rw [hcontr]
  -- AccPartial (t+1) is the same fold, seeded with AccPartial t
  rw [AccPartial_succ A B pidm Md M Kfull N i j t Kd]
  rw [foldl_add_seed (fun kk => (A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0)
                              * (B.getD ((t * Kd + kk) * N + j) 0))
        (List.range Kd) (AccPartial A B pidm Md M Kfull N i j t Kd)]
  omega

-- ══════════════════════════════════════════════════════════════════════════════
-- VALUE WALK, segment A: I1..I6 produce a_54 holding tile t of A, lane by lane.
-- ══════════════════════════════════════════════════════════════════════════════

theorem value_seg_A
    {c : MachineState} (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat)
    (hMpos : 0 < M)
    (hconst : MatmulConsts A B M Kfull N Md Kd Nd c)
    (aptrvals : List Int)
    (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (haptr_len : aptrvals.length = Md * Kd)
    (haptr_lane : ∀ i kk, i < Md → kk < Kd →
        aptrvals.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
    (hk : c.env "k" = some (scalar (Int.ofNat t)))
    (hKv : c.env "K" = some (scalar (Int.ofNat Kfull))) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    ∃ tile,
      (evalInstr I6 (evalInstr I5 (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c)))))).env "a_54"
        = some (tensor [Md, Kd] tile)
      ∧ ∀ i kk, i < Md → kk < Kd →
          tile.getD (i * Kd + kk) 0
            = (if t * Kd + kk < Kfull then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0) := by
  intro I1 I2 I3 I4 I5 I6
  obtain ⟨hmem, ⟨offs, hoffs_env, hoffs_len, hoffs_lane⟩, _hb, _hc1,
          _hsb, hc32, ⟨fills, hfill_env, hfill_len, hfill_lane⟩, _hbf⟩ := hconst
  have e1_a := muli_binds c "a" "k" "c32_i32" _ _ hk hc32
  have e1_K := (env_carry I1 c "K" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hKv
  have e1_offs := (env_carry I1 c "a_ptrs_18" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hoffs_env
  have e1_aptr := (env_carry I1 c "a_ptrs_47" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans haptr
  have e1_fill := (env_carry I1 c "cst_0" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hfill_env
  have e2_a50 := subi_scalar_binds (evalInstr I1 c) "a_50" "K" "a" _ _ e1_K e1_a
  have e2_offs := (env_carry I2 _ "a_ptrs_18" (by simp [I2]) (by simp [I2]) (by simp [I2])).trans e1_offs
  have e2_aptr := (env_carry I2 _ "a_ptrs_47" (by simp [I2]) (by simp [I2]) (by simp [I2])).trans e1_aptr
  have e2_fill := (env_carry I2 _ "cst_0" (by simp [I2]) (by simp [I2]) (by simp [I2])).trans e1_fill
  have e3_a51 := splat_shaped_binds (evalInstr I2 (evalInstr I1 c)) "a_51" "a_50" [1, Kd] _ e2_a50
  have e3_offs := (env_carry I3 _ "a_ptrs_18" (by simp [I3]) (by simp [I3]) (by simp [I3])).trans e2_offs
  have e3_aptr := (env_carry I3 _ "a_ptrs_47" (by simp [I3]) (by simp [I3]) (by simp [I3])).trans e2_aptr
  have e3_fill := (env_carry I3 _ "cst_0" (by simp [I3]) (by simp [I3]) (by simp [I3])).trans e2_fill
  have e4_a52 := cmpi_slt_tt_binds (evalInstr I3 (evalInstr I2 (evalInstr I1 c)))
      "a_52" "a_ptrs_18" "a_51" [1, Kd] offs _ e3_offs e3_a51
  have e4_aptr := (env_carry I4 _ "a_ptrs_47" (by simp [I4]) (by simp [I4]) (by simp [I4])).trans e3_aptr
  have e4_fill := (env_carry I4 _ "cst_0" (by simp [I4]) (by simp [I4]) (by simp [I4])).trans e3_fill
  have e5_a53 := broadcast_binds (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c))))
      "a_53" "a_52" 1 Kd Md Kd _ e4_a52
  have e5_aptr := (env_carry I5 _ "a_ptrs_47" (by simp [I5]) (by simp [I5]) (by simp [I5])).trans e4_aptr
  have e5_fill := (env_carry I5 _ "cst_0" (by simp [I5]) (by simp [I5]) (by simp [I5])).trans e4_fill
  -- memory at the load point is still the layout
  have hmem5 : (evalInstr I5 (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c))))).memory
      = layoutMatmul A B M Kfull N := by
    have hk5 : (evalKernel [I1, I2, I3, I4, I5] c).memory = c.memory :=
      memory_carry_kernel [I1, I2, I3, I4, I5] c
        (by intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with h|h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4, I5])
        (by intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with h|h|h|h|h <;> subst h <;> simp [I1, I2, I3, I4, I5])
    have hunfold : evalKernel [I1, I2, I3, I4, I5] c
        = evalInstr I5 (evalInstr I4 (evalInstr I3 (evalInstr I2 (evalInstr I1 c)))) := by
      simp [evalKernel]
    rw [← hunfold, hk5]; exact hmem
  refine ⟨_, load_fill_binds_explicit _ "a_54" "a_ptrs_47" "a_53" "cst_0"
      [Md, Kd] [Md, Kd] [Md, Kd] aptrvals _ fills e5_aptr e5_a53 e5_fill, ?_⟩
  intro i kk hi hkk
  simp only [MachineState.readMem, hmem5]
  exact tile_load_value_A A B pidm M Kfull N Md Kd t i kk aptrvals _ fills hi hkk hMpos
    (by rw [haptr_len]; simp) (by rw [haptr_len, hfill_len]) haptr_len
    (haptr_lane i kk hi hkk)
    (atile_mask_lane Md Kd Kfull t offs hoffs_len hoffs_lane i kk hi hkk)
    (hfill_lane (i * Kd + kk) (lane_lt i kk Md Kd hi hkk))

-- ══════════════════════════════════════════════════════════════════════════════
-- VALUE WALK, segment B: I7..I10 produce b_57 holding tile t of B, lane by lane.
-- Reuses a_50 (the scalar k-bound) from segment A. Requires Kd ≠ 1: broadcast_col_lane
-- needs it, since the broadcast index formula special-cases size-1 leading dims.
-- ══════════════════════════════════════════════════════════════════════════════

theorem value_seg_B
    {c : MachineState} (A B : List Int) (M Kfull N Md Kd Nd t : Nat)
    (hKd1 : ¬ (Kd == 1))
    (hmem : c.memory = layoutMatmul A B M Kfull N)
    (offs : List Int)
    (hoffs_env : c.env "b_ptrs" = some (tensor [Kd, 1] offs))
    (hoffs_len : offs.length = Kd)
    (hoffs_lane : ∀ kk, kk < Kd → offs.getD kk 0 = Int.ofNat kk)
    (fills : List Int)
    (hfill_env : c.env "cst" = some (tensor [Kd, Nd] fills))
    (hfill_len : fills.length = Kd * Nd)
    (hfill_lane : ∀ idx, idx < Kd * Nd → fills.getD idx 0 = 0)
    (bptrvals : List Int)
    (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (hbptr_len : bptrvals.length = Kd * Nd)
    (hbptr_lane : ∀ kk j, kk < Kd → j < Nd →
        bptrvals.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
    (ha50 : c.env "a_50" = some (scalar (Int.ofNat Kfull - Int.ofNat t * Int.ofNat Kd))) :
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    ∃ tile,
      (evalInstr I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 c)))).env "b_57"
        = some (tensor [Kd, Nd] tile)
      ∧ ∀ kk j, kk < Kd → j < Nd → j < N →
          tile.getD (kk * Nd + j) 0
            = (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0) := by
  intro I7 I8 I9 I10
  have e7_b := splat_shaped_binds c "b" "a_50" [Kd, 1] _ ha50
  have e7_offs := (env_carry I7 c "b_ptrs" (by simp [I7]) (by simp [I7]) (by simp [I7])).trans hoffs_env
  have e7_bptr := (env_carry I7 c "b_ptrs_48" (by simp [I7]) (by simp [I7]) (by simp [I7])).trans hbptr
  have e7_fill := (env_carry I7 c "cst" (by simp [I7]) (by simp [I7]) (by simp [I7])).trans hfill_env
  have e8_b55 := cmpi_slt_tt_binds (evalInstr I7 c) "b_55" "b_ptrs" "b" [Kd, 1] offs _ e7_offs e7_b
  have e8_bptr := (env_carry I8 (evalInstr I7 c) "b_ptrs_48" (by simp [I8]) (by simp [I8]) (by simp [I8])).trans e7_bptr
  have e8_fill := (env_carry I8 (evalInstr I7 c) "cst" (by simp [I8]) (by simp [I8]) (by simp [I8])).trans e7_fill
  have e9_b56 := broadcast_binds (evalInstr I8 (evalInstr I7 c)) "b_56" "b_55" Kd 1 Kd Nd _ e8_b55
  have e9_bptr := (env_carry I9 (evalInstr I8 (evalInstr I7 c)) "b_ptrs_48" (by simp [I9]) (by simp [I9]) (by simp [I9])).trans e8_bptr
  have e9_fill := (env_carry I9 (evalInstr I8 (evalInstr I7 c)) "cst" (by simp [I9]) (by simp [I9]) (by simp [I9])).trans e8_fill
  have hmem9 : (evalInstr I9 (evalInstr I8 (evalInstr I7 c))).memory
      = layoutMatmul A B M Kfull N := by
    have hk : (evalKernel [I7, I8, I9] c).memory = c.memory :=
      memory_carry_kernel [I7, I8, I9] c
        (by intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with h|h|h <;> subst h <;> simp [I7, I8, I9])
        (by intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with h|h|h <;> subst h <;> simp [I7, I8, I9])
    have hunfold : evalKernel [I7, I8, I9] c
        = evalInstr I9 (evalInstr I8 (evalInstr I7 c)) := by simp [evalKernel]
    rw [← hunfold, hk]; exact hmem
  refine ⟨_, load_fill_binds_explicit _ "b_57" "b_ptrs_48" "b_56" "cst"
      [Kd, Nd] [Kd, Nd] [Kd, Nd] bptrvals _ fills e9_bptr e9_b56 e9_fill, ?_⟩
  intro kk j hkk hj hjN
  simp only [MachineState.readMem, hmem9]
  exact tile_load_value_B A B M Kfull N Kd Nd t kk j bptrvals _ fills hkk hj hjN
    (by rw [hbptr_len]; simp) (by rw [hbptr_len, hfill_len]) hbptr_len
    (hbptr_lane kk j hkk hj)
    (btile_mask_lane Kd Nd Kfull t offs hoffs_len hoffs_lane hKd1 kk j hkk hj)
    (hfill_lane (kk * Nd + j) (lane_lt kk j Kd Nd hkk hj))

-- ══════════════════════════════════════════════════════════════════════════════
-- VALUE WALK, segment C: I11 (the dot) and J1..J4 (the pointer advances).
-- The accumulator grows from AccPartial t to AccPartial (t+1); the two pointer
-- tensors move from tile t to tile t+1.
-- ══════════════════════════════════════════════════════════════════════════════

theorem value_seg_C_dot
    {c : MachineState} (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat)
    (hB : B.length = Kfull * N)
    (aTile bTile accIn : List Int)
    (ha : c.env "a_54" = some (tensor [Md, Kd] aTile))
    (hb : c.env "b_57" = some (tensor [Kd, Nd] bTile))
    (hacc : c.env "accumulator_49" = some (tensor [Md, Nd] accIn))
    (hA_lane : ∀ i kk, i < Md → kk < Kd →
        aTile.getD (i * Kd + kk) 0
          = (if t * Kd + kk < Kfull then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0))
    (hB_lane : ∀ kk j, kk < Kd → j < Nd → j < N →
        bTile.getD (kk * Nd + j) 0
          = (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0))
    (hacc_lane : ∀ i j, i < Md → j < Nd →
        accIn.getD (i * Nd + j) 0 = AccPartial A B pidm Md M Kfull N i j t Kd) :
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    ∃ out, (evalInstr I11 c).env "accumulator_58" = some (tensor [Md, Nd] out)
        ∧ out.length = Md * Nd
        ∧ ∀ i j, i < Md → j < Nd → j < N →
            out.getD (i * Nd + j) 0 = AccPartial A B pidm Md M Kfull N i j (t + 1) Kd := by
  intro I11
  refine ⟨_, dot_binds_explicit c "accumulator_58" "a_54" "b_57" "accumulator_49"
      Md Kd Nd aTile bTile accIn ha hb hacc, ?_, ?_⟩
  · simp
  intro i j hi hj hjN
  exact acc_update_lane A B pidm Md M Kfull N Kd Nd t i j aTile bTile accIn hB hi hj hjN
    (fun kk hkk => hA_lane i kk hi hkk)
    (fun kk hkk => hB_lane kk j hkk hj hjN)
    (hacc_lane i j hi hj)

/-- J1: a_ptrs_59 := a_ptrs_47 + cst_1, advancing the A-pointers to tile t+1. -/
theorem value_seg_C_aptr
    {c : MachineState} (pidm M Kfull Kd Md t : Nat)
    (bases steps : List Int)
    (hbase_env : c.env "a_ptrs_47" = some (tensor [Md, Kd] bases))
    (hbase_len : bases.length = Md * Kd)
    (hbase_lane : ∀ i kk, i < Md → kk < Kd →
        bases.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
    (hstep_env : c.env "cst_1" = some (tensor [Md, Kd] steps))
    (hstep_len : steps.length = Md * Kd)
    (hstep_lane : ∀ idx, idx < Md * Kd → steps.getD idx 0 = Int.ofNat Kd) :
    let J1 : TritonInstr := { result := "a_ptrs_59", op := .addptr, args := ["a_ptrs_47", "cst_1"] }
    ∃ out, (evalInstr J1 c).env "a_ptrs_59" = some (tensor [Md, Kd] out)
        ∧ out.length = Md * Kd
        ∧ ∀ i kk, i < Md → kk < Kd →
            out.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd (t + 1) i kk := by
  intro J1
  refine ⟨_, addptr_tt_binds c "a_ptrs_59" "a_ptrs_47" "cst_1" [Md, Kd] bases steps
      hbase_env hstep_env, ?_, ?_⟩
  · simp [List.length_map, List.length_zip, hbase_len, hstep_len]
  intro i kk hi hkk
  exact aptr_advance_lane pidm M Kfull Kd Md t bases steps hbase_lane hstep_lane
    (by rw [hbase_len, hstep_len]) hbase_len i kk hi hkk

/-- J2..J4: b_ptrs_48 += splat(stride_bk * c32_i32) = splat(N * Kd), advancing the
    B-pointers to tile t+1. This is where the row-major assumption (stride_bk = N) enters. -/
theorem value_seg_C_bptr
    {c : MachineState} (M Kfull N Kd Nd t : Nat)
    (bases : List Int)
    (hbase_env : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bases))
    (hbase_len : bases.length = Kd * Nd)
    (hbase_lane : ∀ kk j, kk < Kd → j < Nd →
        bases.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
    (hsb : c.env "stride_bk" = some (scalar (Int.ofNat N)))
    (hc32 : c.env "c32_i32" = some (scalar (Int.ofNat Kd))) :
    let J2 : TritonInstr := { result := "b_ptrs_60", op := .muli, args := ["stride_bk", "c32_i32"] }
    let J3 : TritonInstr := { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] }
    let J4 : TritonInstr := { result := "b_ptrs_62", op := .addptr, args := ["b_ptrs_48", "b_ptrs_61"] }
    ∃ out, (evalInstr J4 (evalInstr J3 (evalInstr J2 c))).env "b_ptrs_62"
              = some (tensor [Kd, Nd] out)
        ∧ out.length = Kd * Nd
        ∧ ∀ kk j, kk < Kd → j < Nd →
            out.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd (t + 1) kk j := by
  intro J2 J3 J4
  -- J2: the scalar step N * Kd
  have e2_b60 := muli_binds c "b_ptrs_60" "stride_bk" "c32_i32" _ _ hsb hc32
  have e2_bases := (env_carry J2 c "b_ptrs_48" (by simp [J2]) (by simp [J2]) (by simp [J2])).trans hbase_env
  -- J3: splat it to [Kd,Nd]
  have e3_b61 := splat_shaped_binds (evalInstr J2 c) "b_ptrs_61" "b_ptrs_60" [Kd, Nd] _ e2_b60
  have e3_bases := (env_carry J3 (evalInstr J2 c) "b_ptrs_48" (by simp [J3]) (by simp [J3]) (by simp [J3])).trans e2_bases
  -- J4: add it
  have hrep : ([Kd, Nd].foldl (· * ·) 1) = Kd * Nd := by simp [List.foldl]
  refine ⟨_, addptr_tt_binds (evalInstr J3 (evalInstr J2 c)) "b_ptrs_62" "b_ptrs_48" "b_ptrs_61"
      [Kd, Nd] bases _ e3_bases e3_b61, ?_, ?_⟩
  · simp [List.length_map, List.length_zip, hbase_len, hrep]
  intro kk j hkk hj
  refine bptr_advance_lane M Kfull N Kd Nd t bases _ hbase_lane ?_ ?_ hbase_len kk j hkk hj
  · intro idx hidx
    rw [splat_lane [Kd, Nd] (Int.ofNat N * Int.ofNat Kd) idx (by rw [hrep]; exact hidx)]
    rfl
  · rw [hbase_len]; simp [hrep]

-- ══════════════════════════════════════════════════════════════════════════════
-- VALUE WALK, composition: segments A and B (I1..I10). Both tiles loaded.
-- a_54's lane facts survive I7..I10 -- the tensor is untouched, so env_carry_kernel
-- transports the equality and the lane fact rides along.
-- ══════════════════════════════════════════════════════════════════════════════

theorem value_seg_AB
    {c : MachineState} (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat)
    (hKd1 : ¬ (Kd == 1)) (hMpos : 0 < M)
    (hconst : MatmulConsts A B M Kfull N Md Kd Nd c)
    (aptrvals : List Int)
    (haptr : c.env "a_ptrs_47" = some (tensor [Md, Kd] aptrvals))
    (haptr_len : aptrvals.length = Md * Kd)
    (haptr_lane : ∀ i kk, i < Md → kk < Kd →
        aptrvals.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
    (bptrvals : List Int)
    (hbptr : c.env "b_ptrs_48" = some (tensor [Kd, Nd] bptrvals))
    (hbptr_len : bptrvals.length = Kd * Nd)
    (hbptr_lane : ∀ kk j, kk < Kd → j < Nd →
        bptrvals.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
    (hk : c.env "k" = some (scalar (Int.ofNat t)))
    (hKv : c.env "K" = some (scalar (Int.ofNat Kfull))) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let cAB := evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c
    (∃ aT, cAB.env "a_54" = some (tensor [Md, Kd] aT)
        ∧ ∀ i kk, i < Md → kk < Kd →
            aT.getD (i * Kd + kk) 0
              = (if t * Kd + kk < Kfull then A.getD (AptrRow pidm Md M i * Kfull + (t * Kd + kk)) 0 else 0))
    ∧ (∃ bT, cAB.env "b_57" = some (tensor [Kd, Nd] bT)
        ∧ ∀ kk j, kk < Kd → j < Nd → j < N →
            bT.getD (kk * Nd + j) 0
              = (if t * Kd + kk < Kfull then B.getD ((t * Kd + kk) * N + j) 0 else 0)) := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 cAB
  have hconst' := hconst
  obtain ⟨hmem, _hoffs, ⟨boffs, hboffs_env, hboffs_len, hboffs_lane⟩, _hc1,
          hsb, hc32, _haf, ⟨bfills, hbfill_env, hbfill_len, hbfill_lane⟩⟩ := hconst
  -- segment A, then bridge to evalKernel form
  obtain ⟨aT, haT_env, haT_lane⟩ := value_seg_A A B pidm M Kfull N Md Kd Nd t hMpos hconst'
      aptrvals haptr haptr_len haptr_lane hk hKv
  have haT_env6 : (evalKernel [I1, I2, I3, I4, I5, I6] c).env "a_54"
      = some (tensor [Md, Kd] aT) := by
    rw [evalKernel_six]; exact haT_env
  -- a_50 at c6: produced by I2, untouched by I3..I6
  have ha50_c6 : (evalKernel [I1,I2,I3,I4,I5,I6] c).env "a_50"
      = some (scalar (Int.ofNat Kfull - Int.ofNat t * Int.ofNat Kd)) := by
    have hsplit : ([I1,I2,I3,I4,I5,I6] : TritonKernel) = [I1,I2] ++ [I3,I4,I5,I6] := by simp
    rw [hsplit, evalKernel_append]
    rw [env_carry_kernel [I3,I4,I5,I6] (evalKernel [I1,I2] c) "a_50"
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h <;> subst h <;> simp [I3,I4,I5,I6])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h <;> subst h <;> simp [I3,I4,I5,I6])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h <;> subst h <;> simp [I3,I4,I5,I6])]
    simp only [evalKernel, List.foldl_cons, List.foldl_nil]
    have e1_a := muli_binds c "a" "k" "c32_i32" _ _ hk hc32
    have e1_K := (env_carry I1 c "K" (by simp [I1]) (by simp [I1]) (by simp [I1])).trans hKv
    exact subi_scalar_binds (evalInstr I1 c) "a_50" "K" "a" _ _ e1_K e1_a
  -- the consts and b-side operands survive I1..I6
  have hcarry6 : ∀ (w : String),
      w ≠ "a" → w ≠ "a_50" → w ≠ "a_51" → w ≠ "a_52" → w ≠ "a_53" → w ≠ "a_54" →
      (evalKernel [I1,I2,I3,I4,I5,I6] c).env w = c.env w := by
    intro w n1 n2 n3 n4 n5 n6
    exact env_carry_kernel [I1,I2,I3,I4,I5,I6] c w
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6, n1,n2,n3,n4,n5,n6])
  have hmem6 : (evalKernel [I1,I2,I3,I4,I5,I6] c).memory = layoutMatmul A B M Kfull N := by
    have hk6 := memory_carry_kernel [I1,I2,I3,I4,I5,I6] c
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6])
    rw [hk6]; exact hmem
  have hboffs6 := (hcarry6 "b_ptrs" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hboffs_env
  have hbfill6 := (hcarry6 "cst" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbfill_env
  have hbptr6 := (hcarry6 "b_ptrs_48" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbptr
  -- segment B at c6
  obtain ⟨bT, hbT_env, hbT_lane⟩ := value_seg_B A B M Kfull N Md Kd Nd t hKd1 hmem6
      boffs hboffs6 hboffs_len hboffs_lane bfills hbfill6 hbfill_len hbfill_lane
      bptrvals hbptr6 hbptr_len hbptr_lane ha50_c6
  -- bridge the ten-instruction block
  have hcAB : cAB = evalInstr I10 (evalInstr I9 (evalInstr I8
      (evalInstr I7 (evalKernel [I1,I2,I3,I4,I5,I6] c)))) := by
    show evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c = _
    rw [evalKernel_ten, evalKernel_six]
  refine ⟨⟨aT, ?_, haT_lane⟩, ⟨bT, by rw [hcAB]; exact hbT_env, hbT_lane⟩⟩
  -- a_54 survives I7..I10
  rw [hcAB]
  have hsurv : (evalInstr I10 (evalInstr I9 (evalInstr I8
      (evalInstr I7 (evalKernel [I1,I2,I3,I4,I5,I6] c))))).env "a_54"
      = (evalKernel [I1,I2,I3,I4,I5,I6] c).env "a_54" := by
    have h7 := env_carry I7 (evalKernel [I1,I2,I3,I4,I5,I6] c) "a_54" (by simp [I7]) (by simp [I7]) (by simp [I7])
    have h8 := env_carry I8 (evalInstr I7 (evalKernel [I1,I2,I3,I4,I5,I6] c)) "a_54" (by simp [I8]) (by simp [I8]) (by simp [I8])
    have h9 := env_carry I9 (evalInstr I8 (evalInstr I7 (evalKernel [I1,I2,I3,I4,I5,I6] c))) "a_54" (by simp [I9]) (by simp [I9]) (by simp [I9])
    have h10 := env_carry I10 (evalInstr I9 (evalInstr I8 (evalInstr I7 (evalKernel [I1,I2,I3,I4,I5,I6] c)))) "a_54" (by simp [I10]) (by simp [I10]) (by simp [I10])
    exact h10.trans (h9.trans (h8.trans h7))
  rw [hsurv]; exact haT_env6

-- ══════════════════════════════════════════════════════════════════════════════
-- VALUE WALK: I1..I11 -- both tiles loaded and contracted into the accumulator.
-- ══════════════════════════════════════════════════════════════════════════════

theorem value_seg_ABC
    {c : MachineState} (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat)
    (hKd1 : ¬ (Kd == 1)) (hMpos : 0 < M) (hB : B.length = Kfull * N)
    (hconst : MatmulConsts A B M Kfull N Md Kd Nd c)
    (hinv : MatmulValueInv A B pidm M Kfull N Md Kd Nd t c)
    (hk : c.env "k" = some (scalar (Int.ofNat t)))
    (hKv : c.env "K" = some (scalar (Int.ofNat Kfull))) :
    let I1 : TritonInstr := { result := "a",    op := .muli,          args := ["k", "c32_i32"] }
    let I2 : TritonInstr := { result := "a_50", op := .subi,          args := ["K", "a"] }
    let I3 : TritonInstr := { result := "a_51", op := .splat [1, Kd], args := ["a_50"] }
    let I4 : TritonInstr := { result := "a_52", op := .cmpi_slt,      args := ["a_ptrs_18", "a_51"] }
    let I5 : TritonInstr := { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] }
    let I6 : TritonInstr := { result := "a_54", op := .load, args := ["a_ptrs_47", "a_53", "cst_0"] }
    let I7  : TritonInstr := { result := "b",    op := .splat [Kd, 1],      args := ["a_50"] }
    let I8  : TritonInstr := { result := "b_55", op := .cmpi_slt,           args := ["b_ptrs", "b"] }
    let I9  : TritonInstr := { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] }
    let I10 : TritonInstr := { result := "b_57", op := .load, args := ["b_ptrs_48", "b_56", "cst"] }
    let I11 : TritonInstr := { result := "accumulator_58", op := .dot,
                               args := ["a_54", "b_57", "accumulator_49"] }
    let cABC := evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c
    ∃ out, cABC.env "accumulator_58" = some (tensor [Md, Nd] out)
        ∧ out.length = Md * Nd
        ∧ ∀ i j, i < Md → j < Nd → j < N →
            out.getD (i * Nd + j) 0 = AccPartial A B pidm Md M Kfull N i j (t + 1) Kd := by
  intro I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 cABC
  obtain ⟨⟨av, haptr, haptr_len, haptr_lane⟩, ⟨bv, hbptr, hbptr_len, hbptr_lane⟩,
          ⟨cv, hacc, hacc_len, hacc_lane⟩⟩ := hinv
  -- the ten-instruction block
  obtain ⟨⟨aT, haT_env, haT_lane⟩, ⟨bT, hbT_env, hbT_lane⟩⟩ :=
    value_seg_AB A B pidm M Kfull N Md Kd Nd t hKd1 hMpos hconst av haptr haptr_len haptr_lane
      bv hbptr hbptr_len hbptr_lane hk hKv
  -- accumulator_49 is untouched by I1..I10
  have hacc10 : (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c).env "accumulator_49"
      = some (tensor [Md, Nd] cv) := by
    rw [env_carry_kernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] c "accumulator_49"
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10])]
    exact hacc
  -- the dot
  have hstep := value_seg_C_dot A B pidm M Kfull N Md Kd Nd t hB aT bT cv
      haT_env hbT_env hacc10 haT_lane hbT_lane hacc_lane
  simp only at hstep
  obtain ⟨out, hout_env, hout_len, hout_lane⟩ := hstep
  refine ⟨out, ?_, hout_len, hout_lane⟩
  show (evalKernel [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] c).env "accumulator_58" = _
  have hsplit : ([I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11] : TritonKernel)
      = [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10] ++ [I11] := by simp
  rw [hsplit, evalKernel_append]
  simp only [evalKernel, List.foldl_cons, List.foldl_nil]
  exact hout_env

/-- MatmulBody splits into the contraction block and the advance/yield block. -/
theorem MatmulBody_split (Md Kd Nd : Nat) :
    MatmulBody Md Kd Nd =
      [ { result := "a",    op := .muli,              args := ["k", "c32_i32"] },
        { result := "a_50", op := .subi,              args := ["K", "a"] },
        { result := "a_51", op := .splat [1, Kd],     args := ["a_50"] },
        { result := "a_52", op := .cmpi_slt,          args := ["a_ptrs_18", "a_51"] },
        { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] },
        { result := "a_54", op := .load,              args := ["a_ptrs_47", "a_53", "cst_0"] },
        { result := "b",    op := .splat [Kd, 1],     args := ["a_50"] },
        { result := "b_55", op := .cmpi_slt,          args := ["b_ptrs", "b"] },
        { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] },
        { result := "b_57", op := .load,              args := ["b_ptrs_48", "b_56", "cst"] },
        { result := "accumulator_58", op := .dot,     args := ["a_54", "b_57", "accumulator_49"] } ]
      ++
      [ { result := "a_ptrs_59", op := .addptr,       args := ["a_ptrs_47", "cst_1"] },
        { result := "b_ptrs_60", op := .muli,         args := ["stride_bk", "c32_i32"] },
        { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] },
        { result := "b_ptrs_62", op := .addptr,       args := ["b_ptrs_48", "b_ptrs_61"] },
        { result := "a_ptrs_47", op := .copy,         args := ["a_ptrs_59"] },
        { result := "b_ptrs_48", op := .copy,         args := ["b_ptrs_62"] },
        { result := "accumulator_49", op := .copy,    args := ["accumulator_58"] } ] := by
  rfl

/-- Carrying a variable across the contraction block (I1..I11). One application per
    variable instead of an eleven-way rcases each time. -/
theorem carry_across_contraction (Md Kd Nd : Nat) (s : MachineState) (w : String)
    (h1 : w ≠ "a") (h2 : w ≠ "a_50") (h3 : w ≠ "a_51") (h4 : w ≠ "a_52")
    (h5 : w ≠ "a_53") (h6 : w ≠ "a_54") (h7 : w ≠ "b") (h8 : w ≠ "b_55")
    (h9 : w ≠ "b_56") (h10 : w ≠ "b_57") (h11 : w ≠ "accumulator_58") :
    (evalKernel
      [ { result := "a",    op := .muli,              args := ["k", "c32_i32"] },
        { result := "a_50", op := .subi,              args := ["K", "a"] },
        { result := "a_51", op := .splat [1, Kd],     args := ["a_50"] },
        { result := "a_52", op := .cmpi_slt,          args := ["a_ptrs_18", "a_51"] },
        { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] },
        { result := "a_54", op := .load,              args := ["a_ptrs_47", "a_53", "cst_0"] },
        { result := "b",    op := .splat [Kd, 1],     args := ["a_50"] },
        { result := "b_55", op := .cmpi_slt,          args := ["b_ptrs", "b"] },
        { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] },
        { result := "b_57", op := .load,              args := ["b_ptrs_48", "b_56", "cst"] },
        { result := "accumulator_58", op := .dot,     args := ["a_54", "b_57", "accumulator_49"] } ]
      s).env w = s.env w := by
  apply env_carry_kernel
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- Memory is unchanged across the contraction block (no stores). -/
theorem memory_across_contraction (Md Kd Nd : Nat) (s : MachineState) :
    (evalKernel
      [ { result := "a",    op := .muli,              args := ["k", "c32_i32"] },
        { result := "a_50", op := .subi,              args := ["K", "a"] },
        { result := "a_51", op := .splat [1, Kd],     args := ["a_50"] },
        { result := "a_52", op := .cmpi_slt,          args := ["a_ptrs_18", "a_51"] },
        { result := "a_53", op := .broadcast [Md, Kd], args := ["a_52"] },
        { result := "a_54", op := .load,              args := ["a_ptrs_47", "a_53", "cst_0"] },
        { result := "b",    op := .splat [Kd, 1],     args := ["a_50"] },
        { result := "b_55", op := .cmpi_slt,          args := ["b_ptrs", "b"] },
        { result := "b_56", op := .broadcast [Kd, Nd], args := ["b_55"] },
        { result := "b_57", op := .load,              args := ["b_ptrs_48", "b_56", "cst"] },
        { result := "accumulator_58", op := .dot,     args := ["a_54", "b_57", "accumulator_49"] } ]
      s).memory = s.memory := by
  apply memory_carry_kernel
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp
-- ══════════════════════════════════════════════════════════════════════════════
-- VALUE WALK, the J-block: J1..J7 advance the pointers and rebind the three iter-args,
-- producing MatmulValueInv at t+1 from the post-contraction state.
-- ══════════════════════════════════════════════════════════════════════════════

theorem value_seg_J
    {d : MachineState} (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat)
    (av : List Int)
    (haptr : d.env "a_ptrs_47" = some (tensor [Md, Kd] av))
    (haptr_len : av.length = Md * Kd)
    (haptr_lane : ∀ i kk, i < Md → kk < Kd →
        av.getD (i * Kd + kk) 0 = AptrTile pidm Md M Kfull Kd t i kk)
    (cst1 : List Int)
    (hcst1 : d.env "cst_1" = some (tensor [Md, Kd] cst1))
    (hcst1_len : cst1.length = Md * Kd)
    (hcst1_lane : ∀ idx, idx < Md * Kd → cst1.getD idx 0 = Int.ofNat Kd)
    (bv : List Int)
    (hbptr : d.env "b_ptrs_48" = some (tensor [Kd, Nd] bv))
    (hbptr_len : bv.length = Kd * Nd)
    (hbptr_lane : ∀ kk j, kk < Kd → j < Nd →
        bv.getD (kk * Nd + j) 0 = BptrTile M Kfull N Kd t kk j)
    (hsb : d.env "stride_bk" = some (scalar (Int.ofNat N)))
    (hc32 : d.env "c32_i32" = some (scalar (Int.ofNat Kd)))
    (acc58 : List Int)
    (hacc58 : d.env "accumulator_58" = some (tensor [Md, Nd] acc58))
    (hacc58_len : acc58.length = Md * Nd)
    (hacc58_lane : ∀ i j, i < Md → j < Nd →
        acc58.getD (i * Nd + j) 0 = AccPartial A B pidm Md M Kfull N i j (t + 1) Kd) :
    let J1 : TritonInstr := { result := "a_ptrs_59", op := .addptr, args := ["a_ptrs_47", "cst_1"] }
    let J2 : TritonInstr := { result := "b_ptrs_60", op := .muli, args := ["stride_bk", "c32_i32"] }
    let J3 : TritonInstr := { result := "b_ptrs_61", op := .splat [Kd, Nd], args := ["b_ptrs_60"] }
    let J4 : TritonInstr := { result := "b_ptrs_62", op := .addptr, args := ["b_ptrs_48", "b_ptrs_61"] }
    let J5 : TritonInstr := { result := "a_ptrs_47", op := .copy, args := ["a_ptrs_59"] }
    let J6 : TritonInstr := { result := "b_ptrs_48", op := .copy, args := ["b_ptrs_62"] }
    let J7 : TritonInstr := { result := "accumulator_49", op := .copy, args := ["accumulator_58"] }
    MatmulValueInv A B pidm M Kfull N Md Kd Nd (t + 1)
      (evalInstr J7 (evalInstr J6 (evalInstr J5 (evalInstr J4
        (evalInstr J3 (evalInstr J2 (evalInstr J1 d))))))) := by
  intro J1 J2 J3 J4 J5 J6 J7
  -- J1: a_ptrs_59 at tile t+1
  obtain ⟨a59, ha59_env, ha59_len, ha59_lane⟩ :=
    value_seg_C_aptr pidm M Kfull Kd Md t av cst1 haptr haptr_len haptr_lane hcst1 hcst1_len hcst1_lane
  -- carries across J1
  have hbptr_1 := (env_carry J1 d "b_ptrs_48" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hbptr
  have hsb_1 := (env_carry J1 d "stride_bk" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hsb
  have hc32_1 := (env_carry J1 d "c32_i32" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hc32
  have hacc_1 := (env_carry J1 d "accumulator_58" (by simp [J1]) (by simp [J1]) (by simp [J1])).trans hacc58
  -- J2..J4: b_ptrs_62 at tile t+1
  obtain ⟨b62, hb62_env, hb62_len, hb62_lane⟩ :=
    value_seg_C_bptr M Kfull N Kd Nd t bv hbptr_1 hbptr_len hbptr_lane hsb_1 hc32_1
  -- carries across J2..J4
  have ha59_4 : (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d)))).env "a_ptrs_59"
      = some (tensor [Md, Kd] a59) := by
    have h2 := env_carry J2 (evalInstr J1 d) "a_ptrs_59" (by simp [J2]) (by simp [J2]) (by simp [J2])
    have h3 := env_carry J3 (evalInstr J2 (evalInstr J1 d)) "a_ptrs_59" (by simp [J3]) (by simp [J3]) (by simp [J3])
    have h4 := env_carry J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d))) "a_ptrs_59" (by simp [J4]) (by simp [J4]) (by simp [J4])
    exact (h4.trans (h3.trans h2)).trans ha59_env
  have hacc_4 : (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d)))).env "accumulator_58"
      = some (tensor [Md, Nd] acc58) := by
    have h2 := env_carry J2 (evalInstr J1 d) "accumulator_58" (by simp [J2]) (by simp [J2]) (by simp [J2])
    have h3 := env_carry J3 (evalInstr J2 (evalInstr J1 d)) "accumulator_58" (by simp [J3]) (by simp [J3]) (by simp [J3])
    have h4 := env_carry J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d))) "accumulator_58" (by simp [J4]) (by simp [J4]) (by simp [J4])
    exact (h4.trans (h3.trans h2)).trans hacc_1
  -- J5: a_ptrs_47 := a_ptrs_59
  have h5_a47 := copy_binds (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d))))
      "a_ptrs_47" "a_ptrs_59" _ ha59_4
  have h5_b62 := (env_carry J5 _ "b_ptrs_62" (by simp [J5]) (by simp [J5]) (by simp [J5])).trans hb62_env
  have h5_acc := (env_carry J5 _ "accumulator_58" (by simp [J5]) (by simp [J5]) (by simp [J5])).trans hacc_4
  -- J6: b_ptrs_48 := b_ptrs_62
  have h6_b48 := copy_binds (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d)))))
      "b_ptrs_48" "b_ptrs_62" _ h5_b62
  have h6_a47 := (env_carry J6 _ "a_ptrs_47" (by simp [J6]) (by simp [J6]) (by simp [J6])).trans h5_a47
  have h6_acc := (env_carry J6 _ "accumulator_58" (by simp [J6]) (by simp [J6]) (by simp [J6])).trans h5_acc
  -- J7: accumulator_49 := accumulator_58
  have h7_acc49 := copy_binds (evalInstr J6 (evalInstr J5 (evalInstr J4 (evalInstr J3 (evalInstr J2 (evalInstr J1 d))))))
      "accumulator_49" "accumulator_58" _ h6_acc
  have h7_a47 := (env_carry J7 _ "a_ptrs_47" (by simp [J7]) (by simp [J7]) (by simp [J7])).trans h6_a47
  have h7_b48 := (env_carry J7 _ "b_ptrs_48" (by simp [J7]) (by simp [J7]) (by simp [J7])).trans h6_b48
  exact ⟨⟨a59, h7_a47, ha59_len, ha59_lane⟩,
         ⟨b62, h7_b48, hb62_len, hb62_lane⟩,
         ⟨acc58, h7_acc49, hacc58_len, hacc58_lane⟩⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- matmul_value_step: the body takes MatmulValueInv t to MatmulValueInv (t+1).
-- ══════════════════════════════════════════════════════════════════════════════

theorem matmul_value_step
    {c : MachineState} (A B : List Int) (pidm M Kfull N Md Kd Nd t : Nat)
    (hKd1 : ¬ (Kd == 1)) (hMpos : 0 < M) (hB : B.length = Kfull * N)
    -- the tile must fit inside the matrix
    (hMd : Md ≤ M) (hNd : Nd ≤ N)
    (hconst : MatmulConsts A B M Kfull N Md Kd Nd c)
    (hinv : MatmulValueInv A B pidm M Kfull N Md Kd Nd t c)
    (hk : c.env "k" = some (scalar (Int.ofNat t)))
    (hKv : c.env "K" = some (scalar (Int.ofNat Kfull))) :
    MatmulValueInv A B pidm M Kfull N Md Kd Nd (t + 1) (evalKernel (MatmulBody Md Kd Nd) c) := by
  have hconst' := hconst
  have hinv' := hinv
  obtain ⟨hmem, _ho, _hbo, ⟨cst1, hcst1_env, hcst1_len, hcst1_lane⟩,
          hsb, hc32, _haf, _hbf⟩ := hconst
  obtain ⟨⟨av, haptr, haptr_len, haptr_lane⟩, ⟨bv, hbptr, hbptr_len, hbptr_lane⟩,
          ⟨cv, hacc, hacc_len, hacc_lane⟩⟩ := hinv
  -- head: the contraction block
  have hABC := value_seg_ABC A B pidm M Kfull N Md Kd Nd t hKd1 hMpos hB hconst' hinv' hk hKv
  obtain ⟨acc58, hacc58_env, hacc58_len, hacc58_lane⟩ := hABC
  -- five carries across the contraction block
  have haptr_P := (carry_across_contraction Md Kd Nd c "a_ptrs_47"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans haptr
  have hcst1_P := (carry_across_contraction Md Kd Nd c "cst_1"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcst1_env
  have hbptr_P := (carry_across_contraction Md Kd Nd c "b_ptrs_48"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbptr
  have hsb_P := (carry_across_contraction Md Kd Nd c "stride_bk"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsb
  have hc32_P := (carry_across_contraction Md Kd Nd c "c32_i32"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc32
  -- tail: the J-block, applied at the post-contraction state
  have hJ := value_seg_J A B pidm M Kfull N Md Kd Nd t av haptr_P haptr_len haptr_lane
      cst1 hcst1_P hcst1_len hcst1_lane bv hbptr_P hbptr_len hbptr_lane
      hsb_P hc32_P acc58 hacc58_env hacc58_len
      (fun i j hi hj => hacc58_lane i j hi hj (Nat.lt_of_lt_of_le hj hNd))
  -- stitch: MatmulBody = contraction ++ J-block
  rw [MatmulBody_split, evalKernel_append]
  simp only [evalKernel, List.foldl_cons, List.foldl_nil]
  exact hJ


end Trident
