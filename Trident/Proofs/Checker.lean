import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.Soundness
import Trident.Target.Parser
import Trident.Common.Equiv

namespace Trident
open TritonValue

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 1: Expr.beq soundness
-- ══════════════════════════════════════════════════════════════════════════════

mutual
  def exprBeqEq : (e1 e2 : Expr) → Expr.beq e1 e2 = true → e1 = e2
    | .lit a,        .lit b,        h => by simp [Expr.beq] at h; exact congrArg Expr.lit h
    | .var s1 i1,    .var s2 i2,    h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        obtain ⟨hs, hi⟩ := h; subst hs
        exact congrArg (Expr.var s1) (by exact_mod_cast hi)
    | .add a1 a2, .add b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a1 b1 h.1; have h2 := exprBeqEq a2 b2 h.2
        subst h1; subst h2; rfl
    | .mul a1 a2, .mul b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a1 b1 h.1; have h2 := exprBeqEq a2 b2 h.2
        subst h1; subst h2; rfl
    | .max a1 a2, .max b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a1 b1 h.1; have h2 := exprBeqEq a2 b2 h.2
        subst h1; subst h2; rfl
    | .load a, .load b, h => by
        simp [Expr.beq] at h
        have h1 := exprBeqEq a b h; subst h1; rfl
    | .reduceSum as, .reduceSum bs, h => by
        simp [Expr.beq] at h
        have h1 := exprListBeqEq as bs h; subst h1; rfl
    | .binop o1 a1 b1, .binop o2 a2 b2, h => by
        simp only [Expr.beq, Bool.and_eq_true] at h
        obtain ⟨⟨ho, ha⟩, hb⟩ := h
        have ha' := exprBeqEq a1 a2 ha
        have hb' := exprBeqEq b1 b2 hb
        subst ha'; subst hb'
        cases o1 <;> cases o2 <;> first | rfl | (exact absurd ho (by decide))
    | .lit _,        .binop _ _ _, h => by simp [Expr.beq] at h
    | .var _ _,      .binop _ _ _, h => by simp [Expr.beq] at h
    | .add _ _,      .binop _ _ _, h => by simp [Expr.beq] at h
    | .mul _ _,      .binop _ _ _, h => by simp [Expr.beq] at h
    | .max _ _,      .binop _ _ _, h => by simp [Expr.beq] at h
    | .load _,       .binop _ _ _, h => by simp [Expr.beq] at h
    | .reduceSum _,  .binop _ _ _, h => by simp [Expr.beq] at h
    | .select _ _ _, .binop _ _ _, h => by simp [Expr.beq] at h
    | .lt _ _,       .binop _ _ _, h => by simp [Expr.beq] at h
    | .binop _ _ _,  .lit _,       h => by simp [Expr.beq] at h
    | .binop _ _ _,  .var _ _,     h => by simp [Expr.beq] at h
    | .binop _ _ _,  .add _ _,     h => by simp [Expr.beq] at h
    | .binop _ _ _,  .mul _ _,     h => by simp [Expr.beq] at h
    | .binop _ _ _,  .max _ _,     h => by simp [Expr.beq] at h
    | .binop _ _ _,  .load _,      h => by simp [Expr.beq] at h
    | .binop _ _ _,  .reduceSum _, h => by simp [Expr.beq] at h
    | .binop _ _ _,  .select _ _ _, h => by simp [Expr.beq] at h
    | .binop _ _ _,  .lt _ _,      h => by simp [Expr.beq] at h
    | .lit _,       .var _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .add _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .mul _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .max _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .load _,      h => by simp [Expr.beq] at h
    | .lit _,       .reduceSum _, h => by simp [Expr.beq] at h
    | .var _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .var _ _,     .add _ _,     h => by simp [Expr.beq] at h
    | .var _ _,     .mul _ _,     h => by simp [Expr.beq] at h
    | .var _ _,     .max _ _,     h => by simp [Expr.beq] at h
    | .var _ _,     .load _,      h => by simp [Expr.beq] at h
    | .var _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .add _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .add _ _,     .var _ _,     h => by simp [Expr.beq] at h
    | .add _ _,     .mul _ _,     h => by simp [Expr.beq] at h
    | .add _ _,     .max _ _,     h => by simp [Expr.beq] at h
    | .add _ _,     .load _,      h => by simp [Expr.beq] at h
    | .add _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .mul _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .mul _ _,     .var _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,     .add _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,     .max _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,     .load _,      h => by simp [Expr.beq] at h
    | .mul _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .max _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .max _ _,     .var _ _,     h => by simp [Expr.beq] at h
    | .max _ _,     .add _ _,     h => by simp [Expr.beq] at h
    | .max _ _,     .mul _ _,     h => by simp [Expr.beq] at h
    | .max _ _,     .load _,      h => by simp [Expr.beq] at h
    | .max _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .load _,      .lit _,       h => by simp [Expr.beq] at h
    | .load _,      .var _ _,     h => by simp [Expr.beq] at h
    | .load _,      .add _ _,     h => by simp [Expr.beq] at h
    | .load _,      .mul _ _,     h => by simp [Expr.beq] at h
    | .load _,      .max _ _,     h => by simp [Expr.beq] at h
    | .load _,      .reduceSum _, h => by simp [Expr.beq] at h
    | .reduceSum _,  .lit _,      h => by simp [Expr.beq] at h
    | .reduceSum _,  .var _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .add _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .mul _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .max _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .load _,     h => by simp [Expr.beq] at h
    | .select c1 t1 e1, .select c2 t2 e2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have hc := exprBeqEq c1 c2 h.1.1
        have ht := exprBeqEq t1 t2 h.1.2
        have he := exprBeqEq e1 e2 h.2
        subst hc; subst ht; subst he; rfl
    | .lt a1 b1, .lt a2 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have ha := exprBeqEq a1 a2 h.1; have hb := exprBeqEq b1 b2 h.2
        subst ha; subst hb; rfl
    | .lit _,        .select _ _ _, h => by simp [Expr.beq] at h
    | .var _ _,      .select _ _ _, h => by simp [Expr.beq] at h
    | .add _ _,      .select _ _ _, h => by simp [Expr.beq] at h
    | .mul _ _,      .select _ _ _, h => by simp [Expr.beq] at h
    | .max _ _,      .select _ _ _, h => by simp [Expr.beq] at h
    | .load _,       .select _ _ _, h => by simp [Expr.beq] at h
    | .reduceSum _,  .select _ _ _, h => by simp [Expr.beq] at h
    | .select _ _ _, .lit _,        h => by simp [Expr.beq] at h
    | .select _ _ _, .var _ _,      h => by simp [Expr.beq] at h
    | .select _ _ _, .add _ _,      h => by simp [Expr.beq] at h
    | .select _ _ _, .mul _ _,      h => by simp [Expr.beq] at h
    | .select _ _ _, .max _ _,      h => by simp [Expr.beq] at h
    | .select _ _ _, .load _,       h => by simp [Expr.beq] at h
    | .select _ _ _, .reduceSum _,  h => by simp [Expr.beq] at h
    | .lit _,        .lt _ _,     h => by simp [Expr.beq] at h
    | .var _ _,      .lt _ _,     h => by simp [Expr.beq] at h
    | .add _ _,      .lt _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,      .lt _ _,     h => by simp [Expr.beq] at h
    | .max _ _,      .lt _ _,     h => by simp [Expr.beq] at h
    | .load _,       .lt _ _,     h => by simp [Expr.beq] at h
    | .reduceSum _,  .lt _ _,     h => by simp [Expr.beq] at h
    | .select _ _ _, .lt _ _,     h => by simp [Expr.beq] at h
    | .lt _ _,       .lit _,      h => by simp [Expr.beq] at h
    | .lt _ _,       .var _ _,    h => by simp [Expr.beq] at h
    | .lt _ _,       .add _ _,    h => by simp [Expr.beq] at h
    | .lt _ _,       .mul _ _,    h => by simp [Expr.beq] at h
    | .lt _ _,       .max _ _,    h => by simp [Expr.beq] at h
    | .lt _ _,       .load _,     h => by simp [Expr.beq] at h
    | .lt _ _,       .reduceSum _, h => by simp [Expr.beq] at h
    | .lt _ _,       .select _ _ _, h => by simp [Expr.beq] at h

  def exprListBeqEq : (as bs : List Expr) → ExprList.beq as bs = true → as = bs
    | [],    [],    _ => rfl
    | [],    _::_,  h => by simp [ExprList.beq] at h
    | _::_,  [],    h => by simp [ExprList.beq] at h
    | a::as, b::bs, h => by
        simp [ExprList.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a b h.1; have h2 := exprListBeqEq as bs h.2
        subst h1; subst h2; rfl
end

theorem Expr.beq_eq (e1 e2 : Expr) (h : Expr.beq e1 e2 = true) : e1 = e2 :=
  exprBeqEq e1 e2 h

theorem beq_evalExpr (e1 e2 : Expr) (mem : Nat → Int) (h : (e1 == e2) = true) :
    evalExpr e1 mem = evalExpr e2 mem := by
  have heq := Expr.beq_eq e1 e2 h; subst heq; rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 2: normalizeExpr preserves evalExpr (sorry -- nested inductive)
-- ══════════════════════════════════════════════════════════════════════════════

private theorem foldl_map_normalize (es : List Expr) (mem : Nat → Int) (symMem : Nat → Expr)
    (hpoint : ∀ e ∈ es, evalExpr (normalizeExpr e symMem) mem = evalExpr e mem) :
    ∀ acc, (es.map (fun e => normalizeExpr e symMem)).foldl (fun acc e => acc + evalExpr e mem) acc =
    es.foldl (fun acc e => acc + evalExpr e mem) acc := by
  induction es with
  | nil => intro acc; rfl
  | cons e rest ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      rw [hpoint e (List.mem_cons_self ..)]
      exact ih (fun e' he' => hpoint e' (List.mem_cons_of_mem _ he')) (acc + evalExpr e mem)

theorem normalizeExpr_correct (e : Expr) (mem : Nat → Int) (symMem : Nat → Expr)
    (h : ∀ addr, evalExpr (symMem addr) mem = mem addr) :
    evalExpr (normalizeExpr e symMem) mem = evalExpr e mem := by
  match e with
  | .lit n => simp [normalizeExpr, evalExpr]
  | .var s i => simp [normalizeExpr, evalExpr]
  | .add e1 e2 =>
      have ih1 := normalizeExpr_correct e1 mem symMem h
      have ih2 := normalizeExpr_correct e2 mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr e1 symMem with
      | lit a =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr e2 symMem with
          | lit b => rw [h2] at ih2; simp only [evalExpr] at ih2 ⊢; omega
          | var s i => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | select _ _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | lt _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | binop _ _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | select _ _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | lt _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | binop _ _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
  | .mul e1 e2 =>
      have ih1 := normalizeExpr_correct e1 mem symMem h
      have ih2 := normalizeExpr_correct e2 mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr e1 symMem with
      | lit a =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr e2 symMem with
          | lit b => rw [h2] at ih2; simp only [evalExpr] at ih2 ⊢; rw [← ih1, ← ih2]
          | var s i => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | select _ _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | lt _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | binop _ _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | select _ _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | lt _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | binop _ _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
  | .max e1 e2 =>
      have ih1 := normalizeExpr_correct e1 mem symMem h
      have ih2 := normalizeExpr_correct e2 mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr e1 symMem with
      | lit a =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr e2 symMem with
          | lit b => rw [h2] at ih2; simp only [evalExpr] at ih2 ⊢; rw [← ih1, ← ih2]
          | var s i => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | select _ _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | lt _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | binop _ _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | select _ _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | lt _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | binop _ _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
  | .binop op a b =>
      have ih1 := normalizeExpr_correct a mem symMem h
      have ih2 := normalizeExpr_correct b mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr a symMem with
      | lit x =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr b symMem with
          | lit y =>
              rw [h2] at ih2; simp only [evalExpr] at ih2
              cases op <;> simp only [evalExpr, ← ih1, ← ih2]
          | var s i => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | select _ _ _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | lt _ _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
          | binop _ _ _ => rw [h2] at ih2; cases op <;> simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | select _ _ _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | lt _ _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
      | binop _ _ _ => rw [h1] at ih1; cases op <;> simp [evalExpr, ih1, ih2]
  | .reduceSum es =>
      simp only [normalizeExpr, evalExpr]
      exact foldl_map_normalize es mem symMem
        (fun e he => normalizeExpr_correct e mem symMem h) 0
  | .load addr =>
      have ih := normalizeExpr_correct addr mem symMem h
      simp only [normalizeExpr]
      cases hn : normalizeExpr addr symMem with
      | lit k => rw [hn] at ih; simp only [evalExpr] at ih ⊢; rw [← h, ← ih]
      | var s i => rw [hn] at ih; simp [evalExpr, ih]
      | add _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | mul _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | max _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | load _ => rw [hn] at ih; simp [evalExpr, ih]
      | reduceSum _ => rw [hn] at ih; simp [evalExpr, ih]
      | select _ _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | lt _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | binop _ _ _ => rw [hn] at ih; simp [evalExpr, ih]
  | .select c t e =>
      have ihc := normalizeExpr_correct c mem symMem h
      have iht := normalizeExpr_correct t mem symMem h
      have ihe := normalizeExpr_correct e mem symMem h
      simp only [normalizeExpr]
      cases hc : normalizeExpr c symMem with
      | lit k =>
          rw [hc] at ihc; simp only [evalExpr] at ihc
          by_cases hk : k != 0
          · simp only [hk, if_true]
            simp only [evalExpr, ← ihc, hk, if_true]; exact iht
          · simp only [hk, if_false]
            simp only [evalExpr, ← ihc, hk, if_false]; exact ihe
      | var s i => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | add _ _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | mul _ _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | max _ _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | load _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | reduceSum _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | select _ _ _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | lt _ _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
      | binop _ _ _ => rw [hc] at ihc; simp [evalExpr, ihc, iht, ihe]
  | .lt a b =>
      have iha := normalizeExpr_correct a mem symMem h
      have ihb := normalizeExpr_correct b mem symMem h
      simp only [normalizeExpr]
      cases ha : normalizeExpr a symMem with
      | lit x =>
          rw [ha] at iha; simp only [evalExpr] at iha
          cases hb : normalizeExpr b symMem with
          | lit y => rw [hb] at ihb; simp only [evalExpr] at ihb ⊢; rw [← iha, ← ihb]
          | var s i => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | add _ _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | mul _ _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | max _ _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | load _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | reduceSum _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | select _ _ _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | lt _ _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
          | binop _ _ _ => rw [hb] at ihb; simp [evalExpr, iha, ihb]
      | var s i => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | add _ _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | mul _ _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | max _ _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | load _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | reduceSum _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | select _ _ _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | lt _ _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
      | binop _ _ _ => rw [ha] at iha; simp [evalExpr, iha, ihb]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := List.sizeOf_lt_of_mem (by assumption); omega)

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 3: concreteMem helpers
-- ══════════════════════════════════════════════════════════════════════════════

def concreteMem (a b : List Int) : Nat → Int := layoutMemory a b

-- layoutMemory a b addr:
--   addr < n       => a.getD addr 0
--   n ≤ addr < 2n  => b.getD (addr-n) 0
--   2n ≤ addr      => 0
-- After simp [layoutMemory] with ha : k < a.length and the four show-facts,
-- the goal reduces to:
--   a.getD k 0 + b.getD k 0 = a.getD k 0 + b.getD k 0  (rfl)

theorem vectorAddSpecExpr_correct (a b : List Int) (pid bs i n : Nat)
    (hla : a.length = n) (hlb : b.length = n) (hi : pid * bs + i < n) :
    evalExpr (vectorAddSpecExpr pid bs i n) (concreteMem a b) =
    a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
  simp only [vectorAddSpecExpr, evalExpr, concreteMem, layoutMemory]
  have ha : pid * bs + i < a.length := by omega
  have h1 : ¬ (n + pid * bs + i < a.length) := by omega
  have h2 : n + pid * bs + i < 2 * a.length := by omega
  have h3 : n + pid * bs + i - a.length = pid * bs + i := by omega
  rw [if_pos ha, if_neg h1, if_pos h2, h3]

theorem normalizeWithMem_correct (e : Expr) (a b : List Int) (n : Nat)
    (hla : a.length = n) (hlb : b.length = n) :
    evalExpr (normalizeWithMem e n) (concreteMem a b) =
    evalExpr e (concreteMem a b) := by
  unfold normalizeWithMem
  apply normalizeExpr_correct
  intro addr
  simp only [concreteMem, layoutMemory]
  by_cases h1 : addr < n <;> by_cases h2 : addr < 2 * n
  · simp only [if_pos h1, evalExpr]; simp [concreteMem, layoutMemory, ← hla, h1]
  · simp only [if_pos h1, evalExpr]; simp [concreteMem, layoutMemory, ← hla, h1]
  · simp only [if_neg h1, if_pos h2, evalExpr]
    simp [concreteMem, layoutMemory, ← hla, ← hlb, h1, h2]
  · simp only [if_neg h1, if_neg h2, evalExpr]
    have ha : ¬ addr < a.length := by omega
    have ha2 : ¬ addr < 2 * a.length := by omega
    rw [if_neg ha, if_neg ha2]


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 4: symCheck_sound (sorry)
-- ══════════════════════════════════════════════════════════════════════════════

-- vectorAddInitState faithful: maps a_base/b_base/c_base/bsize same as symVectorAddInitState
theorem initStates_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (vectorAddInitState a b pid bs gs)
      (symVectorAddInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- hmem
    intro addr
    simp only [symVectorAddInitState, parsedInitState, evalExpr, concreteMem, layoutMemory,
               vectorAddInitState]
    by_cases h1 : addr < a.length <;> by_cases h2 : addr < 2 * a.length <;>
      simp [h1, h2, evalExpr, layoutMemory]
  · -- hsc: a_base/b_base/c_base/bsize all match
    intro v val hv
    simp only [vectorAddInitState] at hv
    split at hv <;> simp_all [TritonValue.scalar, symVectorAddInitState, evalExpr]
  · -- hten: no tensors
    intro v sh vals hv
    simp only [vectorAddInitState] at hv
    split at hv <;> simp_all
  · -- hnone
    intro v hv
    simp only [vectorAddInitState] at hv
    simp only [symVectorAddInitState]
    split at hv <;> simp_all

theorem symCheck_sound (K : TritonKernel) (pid bs gs n i : Nat)
    (hcheck : symCheckVectorAdd K pid bs gs n i = true) :
    ∀ (a b : List Int), a.length = n → b.length = n → pid * bs + i < n →
      MachineState.readMem (evalKernel K (vectorAddInitState a b pid bs gs))
        (2 * n + pid * bs + i) =
      a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
  intro a b hla hlb hi
  simp only [symCheckVectorAdd] at hcheck
  have heval_eq : evalExpr
      (normalizeWithMem
        ((symEvalKernel K (symVectorAddInitState pid bs gs n)).memory
          (2 * n + pid * bs + i)) n)
      (concreteMem a b) =
      evalExpr (vectorAddSpecExpr pid bs i n) (concreteMem a b) :=
    beq_evalExpr _ _ _ hcheck
  rw [normalizeWithMem_correct _ a b n hla hlb] at heval_eq
  rw [vectorAddSpecExpr_correct a b pid bs i n hla hlb hi] at heval_eq
  have hfaithful := initStates_faithful a b pid bs gs
  have hsound := symEval_sound K
    (vectorAddInitState a b pid bs gs)
    (symVectorAddInitState pid bs gs n)
    (concreteMem a b)
    (by rwa [hla] at hfaithful)
    (2 * n + pid * bs + i)
  exact hsound.symm.trans heval_eq

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 5: Expr.beq_false_ne
-- ══════════════════════════════════════════════════════════════════════════════

mutual
  def exprBeqRefl : (e : Expr) → Expr.beq e e = true
    | .lit _ => by simp [Expr.beq]
    | .var _ _ => by simp [Expr.beq]
    | .add e1 e2 => by simp [Expr.beq, exprBeqRefl e1, exprBeqRefl e2]
    | .mul e1 e2 => by simp [Expr.beq, exprBeqRefl e1, exprBeqRefl e2]
    | .max e1 e2 => by simp [Expr.beq, exprBeqRefl e1, exprBeqRefl e2]
    | .load e => by simp [Expr.beq, exprBeqRefl e]
    | .reduceSum es => by simp [Expr.beq, exprListBeqRefl es]
    | .select c t e => by simp [Expr.beq, exprBeqRefl c, exprBeqRefl t, exprBeqRefl e]
    | .lt a b => by simp [Expr.beq, exprBeqRefl a, exprBeqRefl b]
    | .binop o a b => by
        simp only [Expr.beq, exprBeqRefl a, exprBeqRefl b, Bool.and_true, Bool.true_and]
        cases o <;> rfl
  def exprListBeqRefl : (es : List Expr) → ExprList.beq es es = true
    | [] => by simp [ExprList.beq]
    | e::es => by simp [ExprList.beq, exprBeqRefl e, exprListBeqRefl es]
end

theorem Expr.beq_false_ne (e1 e2 : Expr) (h : Expr.beq e1 e2 = false) : e1 ≠ e2 := by
  intro heq; subst heq; simp [exprBeqRefl e1] at h

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 6: initStatesTutorial_faithful (sorry)
-- ══════════════════════════════════════════════════════════════════════════════

theorem initStatesTutorial_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (parsedInitState a b pid bs gs)
      (symVectorAddTutorialInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- hmem
    intro addr
    simp only [symVectorAddTutorialInitState, parsedInitState, evalExpr, concreteMem, layoutMemory]
    by_cases h1 : addr < a.length <;> by_cases h2 : addr < 2 * a.length <;>
      simp [h1, h2, evalExpr, layoutMemory]
  · -- hsc: now symVectorAddTutorialInitState maps all 11 vars from parsedInitState
    intro v val hv
    simp only [parsedInitState] at hv
    -- after split: hv : some (scalar X) = some (scalar val) for matching vars
    -- simp_all [TritonValue.scalar] extracts val = X
    -- then simp [symVectorAddTutorialInitState, evalExpr] provides the witness
    split at hv <;> simp_all [TritonValue.scalar, symVectorAddTutorialInitState, evalExpr]
  · -- hten: no tensors in parsedInitState
    intro v sh vals hv
    simp only [parsedInitState] at hv
    split at hv <;> simp_all
  · -- hnone
    intro v hv
    simp only [parsedInitState] at hv
    simp only [symVectorAddTutorialInitState]
    split at hv <;> simp_all



-- ══════════════════════════════════════════════════════════════════════════════
-- Section 7: symCheckTutorial_sound
-- ══════════════════════════════════════════════════════════════════════════════

theorem initFaithfulWF_tutorial (a b : List Int) (pid bs gs : Nat) :
    FaithfulWF (parsedInitState a b pid bs gs)
               (symVectorAddTutorialInitState pid bs gs a.length)
               (concreteMem a b) := by
  refine ⟨⟨initStatesTutorial_faithful a b pid bs gs, ?_⟩, ?_⟩
  · rfl
  · intro v sh vals hv
    simp only [parsedInitState] at hv
    split at hv <;> simp_all

theorem parsedInitState_NoFloat (a b : List Int) (pid bs gs : Nat) :
    NoFloatState (parsedInitState a b pid bs gs) := by
  intro v tv hv
  simp only [parsedInitState] at hv
  split at hv <;> (
    first
    | (exfalso; exact Option.noConfusion hv)
    | (left; injection hv with hv; exact ⟨_, hv.symm⟩))


theorem symCheckTutorial_sound (K : TritonKernel) (pid bs gs n i : Nat)
    (hcheck : symCheckVectorAddTutorial K pid bs gs n i = true) :
    ∀ (a b : List Int), a.length = n → b.length = n → pid * bs + i < n →
      MachineState.readMem (evalKernel K (parsedInitState a b pid bs gs))
        (2 * n + pid * bs + i) =
      a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
  intro a b hla hlb hi
  simp only [symCheckVectorAddTutorial] at hcheck
  have heval_eq : evalExpr
      (normalizeWithMem
        ((symEvalKernel K (symVectorAddTutorialInitState pid bs gs n)).memory
          (2 * n + pid * bs + i)) n)
      (concreteMem a b) =
      evalExpr (vectorAddSpecExpr pid bs i n) (concreteMem a b) :=
    beq_evalExpr _ _ _ hcheck
  rw [normalizeWithMem_correct _ a b n hla hlb] at heval_eq
  rw [vectorAddSpecExpr_correct a b pid bs i n hla hlb hi] at heval_eq
  have hfaithful := initStatesTutorial_faithful a b pid bs gs
  have hsound := symEval_sound K
    (parsedInitState a b pid bs gs)
    (symVectorAddTutorialInitState pid bs gs n)
    (concreteMem a b)
    (by rwa [hla] at hfaithful)
    (2 * n + pid * bs + i)
  exact hsound.symm.trans heval_eq

#check @symCheck_sound
-- ══════════════════════════════════════════════════════════════════════════════
-- Section 8: Generic-fold soundness for the tutorial kernel (per-pid)
-- Replaces the unsound-as-stated symEval_sound path with the verified generic layer.
-- ══════════════════════════════════════════════════════════════════════════════

def tPrefix : TritonKernel := [
  { result := "c1024_i32", op := .constant 1024,          args := [] },
  { result := "pid",       op := .get_program_id 0,        args := [] },
  { result := "offset",    op := .muli,                    args := ["pid", "c1024_i32"] },
  { result := "range",     op := .make_range (some 1024),  args := [] },
  { result := "voffset",   op := .splat [1024],            args := ["offset"] },
  { result := "idx",       op := .addi,                    args := ["voffset", "range"] },
  { result := "aptr",      op := .addptr,                  args := ["x_ptr", "idx"] },
  { result := "bptr",      op := .addptr,                  args := ["y_ptr", "idx"] },
  { result := "cptr",      op := .addptr,                  args := ["output_ptr", "idx"] },
  { result := "a",         op := .load,                    args := ["aptr"] },
  { result := "b",         op := .load,                    args := ["bptr"] },
  { result := "c",         op := .addf,                    args := ["a", "b"] }
]

def tStore : TritonInstr := { result := "_", op := .store, args := ["cptr", "c"] }

theorem tutorial_prefix_hstep :
    ∀ (instr : TritonInstr), instr ∈ tPrefix →
      ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
        FaithfulWFI s ss mem →
        FaithfulWFI (evalInstr instr s) (symEvalInstr instr ss) mem := by
  intro instr hmem s ss mem hf
  simp only [tPrefix, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
  rcases hmem with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact constant_step_generic _ 1024 rfl hf
  · exact get_program_id_step_generic _ rfl hf
  · exact muli_step_generic _ "pid" "c1024_i32" rfl rfl hf
  · exact make_range_step_generic _ (some 1024) rfl hf
  · exact splat_step_generic _ 1024 "offset" rfl rfl hf
  · exact addi_step_generic _ "voffset" "range" rfl rfl hf
  · exact addptr_step_generic _ "x_ptr" "idx" rfl rfl hf
  · exact addptr_step_generic _ "y_ptr" "idx" rfl rfl hf
  · exact addptr_step_generic _ "output_ptr" "idx" rfl rfl hf
  · exact load_step_generic _ "aptr" rfl rfl hf
  · exact load_step_generic _ "bptr" rfl rfl hf
  · exact addf_step_generic _ "a" "b" rfl rfl hf

def cptrAllConcreteAt (pid n : Nat) : Bool :=
  (List.range 1024).all (fun j =>
    match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "cptr" with
    | some (SymValue.tensor _ g) => (g j).isConcrete
    | _ => false)

theorem cptr_concrete_at (pid n : Nat) (gp : Nat → Expr)
    (hconc : cptrAllConcreteAt pid n = true)
    (hb : (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "cptr"
          = some (SymValue.tensor [1024] gp))
    (i : Nat) (hi : i < 1024) : (gp i).isConcrete = true := by
  unfold cptrAllConcreteAt at hconc
  rw [List.all_eq_true] at hconc
  have := hconc i (List.mem_range.mpr hi)
  rw [hb] at this
  simpa using this

theorem store_faithful_at_postprefix_param (pid n : Nat) (a b : List Int)
    (hla : a.length = n) (hlb : b.length = n)
    (hcptr_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "cptr" with
                   | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hc_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "c" with
                | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hconc : cptrAllConcreteAt pid n = true) :
    StatesFaithful
      (evalInstr tStore (evalKernel tPrefix (parsedInitState a b pid 1024 1)))
      (symEvalInstr tStore (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)))
      (concreteMem a b) := by
  have hinit : FaithfulWFI (parsedInitState a b pid 1024 1)
      (symVectorAddTutorialInitState pid 1024 1 n) (concreteMem a b) := by
    have h0 := initFaithfulWF_tutorial a b pid 1024 1
    rw [hla] at h0
    exact ⟨h0, parsedInitState_NoFloat a b pid 1024 1⟩
  have hpre : FaithfulWFI
      (evalKernel tPrefix (parsedInitState a b pid 1024 1))
      (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n))
      (concreteMem a b) :=
    prefix_faithful_wfi tPrefix tutorial_prefix_hstep _ _ _ hinit
  obtain ⟨⟨⟨hsf, hraw⟩, hwf⟩, hnf⟩ := hpre
  obtain ⟨hp, hbs, hgs, hmem_f, hsc, hten, hnone⟩ := hsf
  obtain ⟨gp, hcptr_sym⟩ := extract_tensor
    (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)) "cptr" 1024 hcptr_fact
  obtain ⟨shp, addrs, hcptr_con⟩ := faithful_tensor_backward ⟨hp, hbs, hgs, hmem_f, hsc, hten, hnone⟩ hnf "cptr" 1024 gp hcptr_sym
  obtain ⟨g', hg'_sym, hg'_corr⟩ := hten "cptr" shp addrs hcptr_con
  rw [hcptr_sym] at hg'_sym
  injection hg'_sym with hg'_eq
  injection hg'_eq with hlen_cptr hg_cptr
  obtain ⟨gv, hc_sym⟩ := extract_tensor
    (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)) "c" 1024 hc_fact
  obtain ⟨shc, vals, hc_con⟩ := faithful_tensor_backward ⟨hp, hbs, hgs, hmem_f, hsc, hten, hnone⟩ hnf "c" 1024 gv hc_sym
  obtain ⟨gv', hgv'_sym, hgv'_corr⟩ := hten "c" shc vals hc_con
  rw [hc_sym] at hgv'_sym
  injection hgv'_sym with hgv'_eq
  injection hgv'_eq with hlen_c hg_c
  have hp_wfn : shapeProd shp = addrs.length :=
    WFn_tensor_len shp addrs (hwf "cptr" shp addrs hcptr_con)
  have hc_wfn : shapeProd shc = vals.length :=
    WFn_tensor_len shc vals (hwf "c" shc vals hc_con)
  have haddrs : addrs.length = 1024 := by rw [← hp_wfn, ← hlen_cptr]; simp [shapeProd]
  have hvals : vals.length = 1024 := by rw [← hc_wfn, ← hlen_c]; simp [shapeProd]
  subst hlen_cptr; subst hlen_c
  have hlen : addrs.length = vals.length := by rw [haddrs, hvals]
  apply store_tensor_faithful_when_memory_unchanged hp hbs hgs hmem_f hsc hten hnone
    tStore "cptr" "c" rfl rfl [1024] addrs vals hcptr_con hc_con hlen gp gv
    (by first | exact hcptr_sym | (rw [haddrs]; exact hcptr_sym))
    (by first | exact hc_sym | (rw [hvals]; exact hc_sym))
  · intro i hi
    rw [haddrs] at hi
    exact cptr_concrete_at pid n gp hconc hcptr_sym i hi
  · intro i hi
    rw [hg_cptr]; exact hg'_corr i (haddrs ▸ hi)
  · intro i hi
    rw [hg_c]; exact hgv'_corr i (by rw [haddrs] at hi; rw [hvals]; exact hi)

theorem tutorial_kernel_faithful_param (pid n : Nat) (a b : List Int)
    (hla : a.length = n) (hlb : b.length = n)
    (hcptr_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "cptr" with
                   | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hc_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "c" with
                | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hconc : cptrAllConcreteAt pid n = true) :
    StatesFaithful
      (evalKernel (tPrefix ++ [tStore]) (parsedInitState a b pid 1024 1))
      (symEvalKernel (tPrefix ++ [tStore]) (symVectorAddTutorialInitState pid 1024 1 n))
      (concreteMem a b) := by
  rw [evalKernel_append, symEvalKernel_append]
  simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
  exact store_faithful_at_postprefix_param pid n a b hla hlb hcptr_fact hc_fact hconc

theorem tutorial_mem_sound_param (pid n : Nat) (a b : List Int)
    (hla : a.length = n) (hlb : b.length = n)
    (hcptr_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "cptr" with
                   | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hc_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "c" with
                | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hconc : cptrAllConcreteAt pid n = true) (addr : Nat) :
    evalExpr ((symEvalKernel (tPrefix ++ [tStore]) (symVectorAddTutorialInitState pid 1024 1 n)).memory addr) (concreteMem a b) =
    (evalKernel (tPrefix ++ [tStore]) (parsedInitState a b pid 1024 1)).memory addr :=
  (tutorial_kernel_faithful_param pid n a b hla hlb hcptr_fact hc_fact hconc).2.2.2.1 addr


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem tutorial_correct_sound (pid n i : Nat) (a b : List Int)
    (hla : a.length = n) (hlb : b.length = n) (hi : pid * 1024 + i < n)
    (hcheck : symCheckVectorAddTutorial (tPrefix ++ [tStore]) pid 1024 1 n i = true)
    (hcptr_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "cptr" with
                   | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hc_fact : (match (symEvalKernel tPrefix (symVectorAddTutorialInitState pid 1024 1 n)).env "c" with
                | some (SymValue.tensor k _) => k == [1024] | _ => false) = true)
    (hconc : cptrAllConcreteAt pid n = true) :
    MachineState.readMem
      (evalKernel (tPrefix ++ [tStore]) (parsedInitState a b pid 1024 1))
      (2 * n + pid * 1024 + i) =
    a.getD (pid * 1024 + i) 0 + b.getD (pid * 1024 + i) 0 := by
  simp only [symCheckVectorAddTutorial] at hcheck
  have heval_eq : evalExpr
      (normalizeWithMem
        ((symEvalKernel (tPrefix ++ [tStore]) (symVectorAddTutorialInitState pid 1024 1 n)).memory
          (2 * n + pid * 1024 + i)) n)
      (concreteMem a b) =
      evalExpr (vectorAddSpecExpr pid 1024 i n) (concreteMem a b) :=
    beq_evalExpr _ _ _ hcheck
  rw [normalizeWithMem_correct _ a b n hla hlb] at heval_eq
  rw [vectorAddSpecExpr_correct a b pid 1024 i n hla hlb hi] at heval_eq
  have hmem := tutorial_mem_sound_param pid n a b hla hlb hcptr_fact hc_fact hconc (2 * n + pid * 1024 + i)
  rw [hmem] at heval_eq
  rw [MachineState.readMem]
  exact heval_eq


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem tutorial_sound_pid0 (i : Nat) (a b : List Int)
    (hla : a.length = 2048) (hlb : b.length = 2048) (hi : i < 1024)
    (hcheck : symCheckVectorAddTutorial (tPrefix ++ [tStore]) 0 1024 1 2048 i = true) :
    MachineState.readMem
      (evalKernel (tPrefix ++ [tStore]) (parsedInitState a b 0 1024 1))
      (2 * 2048 + 0 * 1024 + i) =
    a.getD (0 * 1024 + i) 0 + b.getD (0 * 1024 + i) 0 :=
  tutorial_correct_sound 0 2048 i a b hla hlb (by omega) hcheck
    (by native_decide) (by native_decide) (by native_decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem tutorial_sound_pid1 (i : Nat) (a b : List Int)
    (hla : a.length = 2048) (hlb : b.length = 2048) (hi : i < 1024)
    (hcheck : symCheckVectorAddTutorial (tPrefix ++ [tStore]) 1 1024 1 2048 i = true) :
    MachineState.readMem
      (evalKernel (tPrefix ++ [tStore]) (parsedInitState a b 1 1024 1))
      (2 * 2048 + 1 * 1024 + i) =
    a.getD (1 * 1024 + i) 0 + b.getD (1 * 1024 + i) 0 :=
  tutorial_correct_sound 1 2048 i a b hla hlb (by omega) hcheck
    (by native_decide) (by native_decide) (by native_decide)


#check @symCheckTutorial_sound

-- ══════════════════════════════════════════════════════════════════════════════
-- ★ checkTTIR: the executable verifier. Parse a .ttir, split pre ++ [store], run the DECIDABLE
-- checks that back verify_kernel_masked (prefix supported + pointer/mask concrete + value tensor
-- present). Returns true IFF the kernel is proven sound for ALL inputs. NO per-kernel proof.
-- (Value tensor need only exist — it's typically a computed, input-dependent result.)
-- bs = tensor width (block size). Backed by the theorem verify_kernel_masked.
-- ══════════════════════════════════════════════════════════════════════════════
def checkTTIR (src : String) (pid bs : Nat) : Bool :=
  match parseKernel src with
  | none => false
  | some k =>
    match k.getLast? with
    | none => false
    | some storeInstr =>
      let pre := k.dropLast
      match storeInstr.op, storeInstr.args with
      | .store, [p, val, m] =>
          let ss := symEvalKernel pre (symVectorAddTutorialInitState pid bs 1 (bs*2))
          pre.all instrSupported
            && symTensorAllConcrete ss p bs
            && symTensorAllConcrete ss m bs
            && (match ss.env val with | some (SymValue.tensor k _) => k == [bs] | _ => false)
      | _, _ => false


-- ══════════════════════════════════════════════════════════════════════════════
-- ★ checkVectorAdd: full-correctness verifier for a masked vector-add .ttir at (pid, n).
-- Faithfulness (1–4, as in checkTTIR) makes the symbolic model trustworthy; the per-lane
-- sweep (5) then certifies the OUTPUT itself:
--   in-bounds lane (pid*bs+i < n) → normalizes to  a[idx] + b[idx]   (correct value)
--   tail lane      (pid*bs+i ≥ n) → normalizes to  lit 0             (correctly NOT written)
-- General over src: any vector-add .ttir whose parsed form passes is certified by one theorem.
-- ══════════════════════════════════════════════════════════════════════════════
def checkVectorAdd (src : String) (pid bs n : Nat) : Bool :=
  match parseKernel src with
  | none => false
  | some k =>
    match k.getLast? with
    | none => false
    | some st =>
      let pre := k.dropLast
      match st.op, st.args with
      | .store, [p, val, m] =>
          let ss := symEvalKernel pre (symVectorAddTutorialInitState pid bs 1 n)
          pre.all instrSupported
            && symTensorAllConcrete ss p bs
            && symTensorAllConcrete ss m bs
            && (match ss.env val with | some (SymValue.tensor sh _) => sh == [bs] | _ => false)
            && (List.range bs).all (fun i =>
                 if pid * bs + i < n then
                   symCheckVectorAddTutorial k pid bs 1 n i
                 else
                   normalizeWithMem
                     ((symEvalKernel k (symVectorAddTutorialInitState pid bs 1 n)).memory
                       (2 * n + pid * bs + i)) n == Expr.lit 0)
      | _, _ => false


-- ══════════════════════════════════════════════════════════════════════════════
-- ★ checkVectorAdd_sound: if the checker passes at (pid, n), EVERY output lane of the
-- block matches the spec for ALL inputs — in-bounds lanes to a+b, tail lanes to the
-- untouched 0. Routed through verify_kernel_masked (sorry-free), NOT symEval_sound.
-- General over src: any parsed vector-add .ttir is certified with no new proof.
theorem dropLast_getLast?_eq {α} :
    ∀ (k : List α) (st : α), k.getLast? = some st → k = k.dropLast ++ [st]
  | [], st, h => by simp at h
  | [a], st, h => by simp [List.getLast?] at h; simp [List.dropLast, h]
  | a :: b :: t, st, h => by
      have h' : (b :: t).getLast? = some st := by
        rw [← h]; simp [List.getLast?_cons_cons]
      have ih := dropLast_getLast?_eq (b :: t) st h'
      calc a :: b :: t = a :: ((b :: t).dropLast ++ [st]) := by rw [← ih]
        _ = (a :: (b :: t).dropLast) ++ [st] := by simp
        _ = (a :: b :: t).dropLast ++ [st] := by simp [List.dropLast]

-- ══════════════════════════════════════════════════════════════════════════════
set_option maxRecDepth 4000 in
theorem checkVectorAdd_sound (src : String) (pid bs n : Nat)
    (hchk : checkVectorAdd src pid bs n = true)
    (k : TritonKernel) (hpk : parseKernel src = some k)
    (a b : List Int) (hla : a.length = n) (hlb : b.length = n)
    (i : Nat) (hi : i < bs) :
    MachineState.readMem (evalKernel k (parsedInitState a b pid bs 1)) (2 * n + pid * bs + i)
      = (if pid * bs + i < n then a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 else 0) := by
  -- ── unpack the checker ──────────────────────────────────────────────────────
  simp only [checkVectorAdd, hpk] at hchk
  cases hlast : k.getLast? with
  | none => simp only [hlast] at hchk; exact absurd hchk (by decide)
  | some st =>
    have hsplit : k = k.dropLast ++ [st] := dropLast_getLast?_eq k st hlast
    simp only [hlast] at hchk
    -- Pin st.op = .store and st.args = [p,val,m]; any other shape makes hchk : false = true.
    obtain ⟨p, val, m, hop, hargs⟩ :
        ∃ p val m, st.op = .store ∧ st.args = [p, val, m] := by
      rcases hargc : st.args with _ | ⟨p, _ | ⟨val, _ | ⟨m, tl⟩⟩⟩
      · simp only [hargc] at hchk; exact absurd hchk (by simp)
      · simp only [hargc] at hchk; exact absurd hchk (by simp)
      · simp only [hargc] at hchk; exact absurd hchk (by simp)
      · cases tl with
        | cons _ _ => simp only [hargc] at hchk; exact absurd hchk (by simp)
        | nil =>
          -- args = [p,val,m]; now op must be .store
          -- args = [p,val,m]; the checker's `match st.op` gives `false` unless op = .store
          by_cases hos : st.op = .store
          · exact ⟨p, val, m, hos, rfl⟩
          · exfalso
            -- st.op ≠ .store: the checker's `match st.op, st.args` takes the `_ => false` arm
            rw [hargc] at hchk
            split at hchk
            · exact hos (by assumption)
            · simp at hchk
    simp only [hop, hargs, Bool.and_eq_true] at hchk
    obtain ⟨⟨⟨⟨hpre_all, hpc⟩, hmc⟩, hvfact⟩, hsweep⟩ := hchk
    -- ── faithfulness bridge (SORRY-FREE) ────────────────────────────
    have hinitwf : FaithfulWFI (parsedInitState a b pid bs 1)
        (symVectorAddTutorialInitState pid bs 1 n) (concreteMem a b) := by
      have h0 := initFaithfulWF_tutorial a b pid bs 1
      rw [hla] at h0
      exact ⟨h0, parsedInitState_NoFloat a b pid bs 1⟩
    have hF : StatesFaithful
        (evalKernel (k.dropLast ++ [st]) (parsedInitState a b pid bs 1))
        (symEvalKernel (k.dropLast ++ [st]) (symVectorAddTutorialInitState pid bs 1 n))
        (concreteMem a b) :=
      verify_kernel_masked k.dropLast st p val m bs
        (parsedInitState a b pid bs 1)
        (symVectorAddTutorialInitState pid bs 1 n)
        (concreteMem a b) hop hargs hpre_all hpc hmc hvfact hinitwf
    have hmemF := hF.2.2.2.1 (2 * n + pid * bs + i)
    rw [hsplit, MachineState.readMem, ← hmemF]
    have hsweep_i := (List.all_eq_true.mp hsweep) i (List.mem_range.mpr hi)
    by_cases hb : pid * bs + i < n
    · simp only [hb, if_true] at hsweep_i ⊢
      have hnorm := beq_evalExpr _ _ (concreteMem a b)
        (by have := hsweep_i; simp only [symCheckVectorAddTutorial] at this; exact this)
      rw [normalizeWithMem_correct _ a b n hla hlb] at hnorm
      rw [vectorAddSpecExpr_correct a b pid bs i n hla hlb hb] at hnorm
      rw [hsplit] at hnorm
      exact hnorm
    · simp only [hb, if_false] at hsweep_i ⊢
      have hnorm := beq_evalExpr _ _ (concreteMem a b) hsweep_i
      rw [normalizeWithMem_correct _ a b n hla hlb] at hnorm
      simp only [evalExpr] at hnorm
      rw [hsplit] at hnorm
      exact hnorm

#print axioms checkVectorAdd_sound

end Trident
