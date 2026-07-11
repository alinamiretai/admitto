import Trident.Target.Dialect
import Trident.Target.Semantics
import Trident.Common.Memory

namespace Trident

-- ── Symbolic Expression Type ──────────────────────────────────────────────────

-- Integer binary operators that don't have dedicated Expr nodes.
-- One tagged node keeps the Expr matrix from exploding per-operation.
inductive IntBinop : Type
  | sub    -- subtraction  x - y
  | divs   -- signed integer division  x / y  (Lean Int./ truncates toward zero)
  | rems   -- signed remainder  x % y
  | mins   -- signed minimum  min x y
  | sgt    -- signed greater-than, yields 1/0
  deriving Repr, DecidableEq, BEq

inductive Expr : Type
  | lit  : Int → Expr
  | var  : String → Nat → Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | max  : Expr → Expr → Expr
  | load      : Expr → Expr
  | reduceSum : List Expr → Expr
  | select    : Expr → Expr → Expr → Expr
  | lt        : Expr → Expr → Expr
  | binop     : IntBinop → Expr → Expr → Expr
  deriving Repr

-- Manual BEq for Expr (needed since reduceSum contains List Expr)
mutual
  def Expr.beq : Expr → Expr → Bool
    | .lit a,        .lit b        => a == b
    | .var s1 i1,    .var s2 i2    => s1 == s2 && i1 == i2
    | .add a1 a2,    .add b1 b2    => Expr.beq a1 b1 && Expr.beq a2 b2
    | .mul a1 a2,    .mul b1 b2    => Expr.beq a1 b1 && Expr.beq a2 b2
    | .max a1 a2,    .max b1 b2    => Expr.beq a1 b1 && Expr.beq a2 b2
    | .load a,       .load b       => Expr.beq a b
    | .reduceSum as, .reduceSum bs => ExprList.beq as bs
    | .select c1 t1 e1, .select c2 t2 e2 =>
        Expr.beq c1 c2 && Expr.beq t1 t2 && Expr.beq e1 e2
    | .lt a1 b1,     .lt a2 b2     => Expr.beq a1 a2 && Expr.beq b1 b2
    | .binop o1 a1 b1, .binop o2 a2 b2 => (o1 == o2) && Expr.beq a1 a2 && Expr.beq b1 b2
    | _,             _             => false
  def ExprList.beq : List Expr → List Expr → Bool
    | [],    []    => true
    | a::as, b::bs => Expr.beq a b && ExprList.beq as bs
    | _,     _     => false
end

instance : BEq Expr := ⟨Expr.beq⟩
-- exprBeqEq: Expr.beq e1 e2 = true → e1 = e2 (proved by mutual recursion)
mutual
  def exprBeqEq_aux : (e1 e2 : Expr) → Expr.beq e1 e2 = true → e1 = e2
    | .lit a,        .lit b,        h => by simp [Expr.beq] at h; exact congrArg Expr.lit h
    | .var s1 i1,    .var s2 i2,    h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        obtain ⟨hs, hi⟩ := h; subst hs
        exact congrArg (Expr.var s1) (by exact_mod_cast hi)
    | .add a1 a2, .add b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a1 b1 h.1; have h2 := exprBeqEq_aux a2 b2 h.2
        subst h1; subst h2; rfl
    | .mul a1 a2, .mul b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a1 b1 h.1; have h2 := exprBeqEq_aux a2 b2 h.2
        subst h1; subst h2; rfl
    | .max a1 a2, .max b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a1 b1 h.1; have h2 := exprBeqEq_aux a2 b2 h.2
        subst h1; subst h2; rfl
    | .load a, .load b, h => by
        simp [Expr.beq] at h; exact congrArg Expr.load (exprBeqEq_aux a b h)
    | .reduceSum as, .reduceSum bs, h => by
        simp [Expr.beq] at h; exact congrArg Expr.reduceSum (exprListBeqEq_aux as bs h)
    | .select c1 t1 e1, .select c2 t2 e2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have hc := exprBeqEq_aux c1 c2 h.1.1
        have ht := exprBeqEq_aux t1 t2 h.1.2
        have he := exprBeqEq_aux e1 e2 h.2
        subst hc; subst ht; subst he; rfl
    | .lt a1 b1, .lt a2 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have ha := exprBeqEq_aux a1 a2 h.1; have hb := exprBeqEq_aux b1 b2 h.2
        subst ha; subst hb; rfl
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
    | .binop o1 a1 b1, .binop o2 a2 b2, h => by
        simp only [Expr.beq, Bool.and_eq_true] at h
        obtain ⟨⟨ho, ha⟩, hb⟩ := h
        have ha' := exprBeqEq_aux a1 a2 ha
        have hb' := exprBeqEq_aux b1 b2 hb
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
  def exprListBeqEq_aux : (as bs : List Expr) → ExprList.beq as bs = true → as = bs
    | [],    [],    _ => rfl
    | [],    _::_,  h => by simp [ExprList.beq] at h
    | _::_,  [],    h => by simp [ExprList.beq] at h
    | a::as, b::bs, h => by
        simp [ExprList.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a b h.1; have h2 := exprListBeqEq_aux as bs h.2
        subst h1; subst h2; rfl
end

mutual
  def exprBeqRefl_aux : (e : Expr) → Expr.beq e e = true
    | .lit _      => by simp [Expr.beq]
    | .var _ _    => by simp [Expr.beq]
    | .add e1 e2  => by simp [Expr.beq, exprBeqRefl_aux e1, exprBeqRefl_aux e2]
    | .mul e1 e2  => by simp [Expr.beq, exprBeqRefl_aux e1, exprBeqRefl_aux e2]
    | .max e1 e2  => by simp [Expr.beq, exprBeqRefl_aux e1, exprBeqRefl_aux e2]
    | .load e     => by simp [Expr.beq, exprBeqRefl_aux e]
    | .reduceSum es => by simp [Expr.beq, exprListBeqRefl_aux es]
    | .select c t e => by
        simp [Expr.beq, exprBeqRefl_aux c, exprBeqRefl_aux t, exprBeqRefl_aux e]
    | .lt a b => by simp [Expr.beq, exprBeqRefl_aux a, exprBeqRefl_aux b]
    | .binop o a b => by
        simp only [Expr.beq, exprBeqRefl_aux a, exprBeqRefl_aux b, Bool.and_true, Bool.true_and]
        cases o <;> rfl
  def exprListBeqRefl_aux : (es : List Expr) → ExprList.beq es es = true
    | []     => by simp [ExprList.beq]
    | e::es  => by simp [ExprList.beq, exprBeqRefl_aux e, exprListBeqRefl_aux es]
end

instance : DecidableEq Expr := fun a b =>
  if h : Expr.beq a b = true then
    isTrue (exprBeqEq_aux a b h)
  else
    isFalse (fun heq => by subst heq; exact h (exprBeqRefl_aux a))

-- ── Symbolic Values ───────────────────────────────────────────────────────────

-- ── Symbolic FLOAT Expression Type ────────────────────────────────────────────
-- Float-structure layer: arithmetic ops (fadd/fmul/etc) are represented as tagged
-- nodes and INTERPRETED by evalFExpr via real Float ops, so faithfulness holds by
-- matching the concrete op. This tracks data-flow structure (which values flow where,
-- shapes, addressing) without claiming bit-exact numeric guarantees beyond Lean's Float.
inductive FBinop : Type
  | fadd | fsub | fmul | fdiv
  deriving Repr, DecidableEq, BEq

inductive FExpr : Type
  | flit   : Float → FExpr                       -- float literal (e.g. 0.0 fills)
  | fvar   : String → Nat → FExpr                -- uninterpreted loaded float value
  | fload  : Nat → FExpr                         -- load float from mem at resolved addr index
  | fbinop : FBinop → FExpr → FExpr → FExpr      -- fadd/fsub/fmul/fdiv
  | ftrunc : FExpr → FExpr                       -- truncf (f32→f16); modeled as identity here
  | fdot   : List FExpr → FExpr                  -- dot contraction sum (tf32); sum of products
  deriving Repr

-- Evaluate a float symbolic expression against a float memory.
-- fmem provides the concrete value for each fvar/fload site.
def evalFExpr (e : FExpr) (fmem : Nat → Float) : Float :=
  match e with
  | .flit v       => v
  | .fvar _ i     => fmem i
  | .fload addr   => fmem addr
  | .fbinop op a b =>
      let x := evalFExpr a fmem; let y := evalFExpr b fmem
      match op with
      | .fadd => x + y
      | .fsub => x - y
      | .fmul => x * y
      | .fdiv => x / y
  | .ftrunc a     => evalFExpr a fmem
  | .fdot terms   => terms.foldl (fun acc e => acc + evalFExpr e fmem) 0.0

inductive SymValue : Type
  | scalar : Expr → SymValue
  | tensor : List Nat → (Nat → Expr) → SymValue
  | fscalar : FExpr → SymValue
  | ftensor : List Nat → (Nat → FExpr) → SymValue


-- ── Symbolic Machine State ────────────────────────────────────────────────────

structure SymState where
  pid        : Nat
  block_size : Nat
  grid_size  : Nat
  memory     : Nat → Expr
  env        : String → Option SymValue

def SymState.lookup (s : SymState) (v : String) : Option SymValue := s.env v

def SymState.bind (s : SymState) (v : String) (val : SymValue) : SymState :=
  { s with env := fun name => if name == v then some val else s.env name }

def SymState.writeMem (s : SymState) (addr : Nat) (val : Expr) : SymState :=
  { s with memory := fun a => if a == addr then val else s.memory a }

-- ── Evaluate Expr On Concrete Inputs ─────────────────────────────────────────

def evalExpr (e : Expr) (mem : Nat → Int) : Int :=
  match e with
  | .lit n     => n
  | .var _ i   => mem i
  | .add e1 e2 => evalExpr e1 mem + evalExpr e2 mem
  | .mul e1 e2 => evalExpr e1 mem * evalExpr e2 mem
  | .max e1 e2 => Max.max (evalExpr e1 mem) (evalExpr e2 mem)
  | .load addr     => mem (evalExpr addr mem).natAbs
  | .reduceSum es  => es.foldl (fun acc e => acc + evalExpr e mem) 0
  | .select c t e  => if evalExpr c mem != 0 then evalExpr t mem else evalExpr e mem
  | .lt a b        => if evalExpr a mem < evalExpr b mem then 1 else 0
  | .binop op a b  =>
      let x := evalExpr a mem; let y := evalExpr b mem
      match op with
      | .sub  => x - y
      | .divs => x / y
      | .rems => x % y
      | .mins => Min.min x y
      | .sgt  => if x > y then 1 else 0

-- ── Expression Normalization ──────────────────────────────────────────────────

/-- Simplify concrete arithmetic and resolve loads via memory layout -/
def normalizeExpr (e : Expr) (mem : Nat → Expr) : Expr :=
  match e with
  | .lit n     => .lit n
  | .var s i   => .var s i
  | .add e1 e2 =>
      match normalizeExpr e1 mem, normalizeExpr e2 mem with
      | .lit a, .lit b => .lit (a + b)
      | n1,     n2     => .add n1 n2
  | .mul e1 e2 =>
      match normalizeExpr e1 mem, normalizeExpr e2 mem with
      | .lit a, .lit b => .lit (a * b)
      | n1,     n2     => .mul n1 n2
  | .max e1 e2 =>
      match normalizeExpr e1 mem, normalizeExpr e2 mem with
      | .lit a, .lit b => .lit (Max.max a b)
      | n1,     n2     => .max n1 n2
  | .reduceSum es =>
      .reduceSum (es.map (fun e => normalizeExpr e mem))
  | .select c t e =>
      match normalizeExpr c mem with
      | .lit k => if k != 0 then normalizeExpr t mem else normalizeExpr e mem
      | nc     => .select nc (normalizeExpr t mem) (normalizeExpr e mem)
  | .lt a b =>
      match normalizeExpr a mem, normalizeExpr b mem with
      | .lit x, .lit y => .lit (if x < y then 1 else 0)
      | na, nb => .lt na nb
  | .binop op a b =>
      match normalizeExpr a mem, normalizeExpr b mem with
      | .lit x, .lit y =>
          match op with
          | .sub  => .lit (x - y)
          | .divs => .lit (x / y)
          | .rems => .lit (x % y)
          | .mins => .lit (Min.min x y)
          | .sgt  => .lit (if x > y then 1 else 0)
      | na, nb => .binop op na nb
  | .load addr =>
      match normalizeExpr addr mem with
      | .lit n => mem n.natAbs
      | naddr  => .load naddr

-- ── Helper: normalize with vector-add memory layout ──────────────────────────

def normalizeWithMem (e : Expr) (n : Nat) : Expr :=
  normalizeExpr e (fun addr =>
    if addr < n then Expr.var "a" addr
    else if addr < 2 * n then Expr.var "b" addr
    else Expr.lit 0)

-- ── Symbolic Operation Semantics ──────────────────────────────────────────────

def symAdd (a b : Option SymValue) : Option SymValue :=
  match a, b with
  | some (SymValue.scalar x), some (SymValue.scalar y) =>
      some (SymValue.scalar (Expr.add x y))
  | some (SymValue.scalar x), some (SymValue.tensor m ys) =>
      some (SymValue.tensor m (fun i => Expr.add x (ys i)))
  | some (SymValue.tensor m xs), some (SymValue.scalar y) =>
      some (SymValue.tensor m (fun i => Expr.add (xs i) y))
  | some (SymValue.tensor m xs), some (SymValue.tensor n ys) =>
      if m == n then some (SymValue.tensor m (fun i => Expr.add (xs i) (ys i)))
      else none
  | _, _ => none

-- Generic symbolic binary op producing an Expr.binop node, tagged by IntBinop.
-- Mirrors symAdd's scalar/tensor broadcasting structure.
def symBinop (op : IntBinop) (a b : Option SymValue) : Option SymValue :=
  match a, b with
  | some (SymValue.scalar x), some (SymValue.scalar y) =>
      some (SymValue.scalar (Expr.binop op x y))
  | some (SymValue.scalar x), some (SymValue.tensor m ys) =>
      some (SymValue.tensor m (fun i => Expr.binop op x (ys i)))
  | some (SymValue.tensor m xs), some (SymValue.scalar y) =>
      some (SymValue.tensor m (fun i => Expr.binop op (xs i) y))
  | some (SymValue.tensor m xs), some (SymValue.tensor n ys) =>
      if m == n then some (SymValue.tensor m (fun i => Expr.binop op (xs i) (ys i)))
      else none
  | _, _ => none

def symMax (a b : Option SymValue) : Option SymValue :=
  match a, b with
  | some (SymValue.scalar x), some (SymValue.scalar y) =>
      some (SymValue.scalar (Expr.max x y))
  | some (SymValue.scalar x), some (SymValue.tensor m ys) =>
      some (SymValue.tensor m (fun i => Expr.max x (ys i)))
  | some (SymValue.tensor m xs), some (SymValue.scalar y) =>
      some (SymValue.tensor m (fun i => Expr.max (xs i) y))
  | some (SymValue.tensor m xs), some (SymValue.tensor _ ys) =>
      some (SymValue.tensor m (fun i => Expr.max (xs i) (ys i)))
  | _, _ => none

-- ── 2D shape ops: expand_dims (insert size-1 axis) + broadcast (expand size-1 axes) ──
def symExpandDims (axis : Nat) (v : Option SymValue) : Option SymValue :=
  match v with
  | some (SymValue.tensor sh f) => some (SymValue.tensor (sh.take axis ++ [1] ++ sh.drop axis) f)
  | _ => none

def symBroadcast (shape : List Nat) (v : Option SymValue) : Option SymValue :=
  match v with
  | some (SymValue.tensor srcShape f) =>
      match srcShape, shape with
      | [s0, s1], [t0, t1] =>
          some (SymValue.tensor shape (fun idx =>
            let i := idx / t1
            let j := idx % t1
            let si := if s0 == 1 then 0 else i
            let sj := if s1 == 1 then 0 else j
            f (si * s1 + sj)))
      | _, _ => none
  | _ => none

def symEvalOp (op : TritonOp) (args : List String) (s : SymState)
    : Option SymValue :=
  match op with
  | .copy =>
      match args with
      | [v] => s.lookup v
      | _ => none
  | .get_program_id _ =>
      some (SymValue.scalar (Expr.lit (Int.ofNat s.pid)))
  | .constant v =>
      some (SymValue.scalar (Expr.lit v))
  | .constant_tensor val shape =>
      some (SymValue.tensor shape (fun _ => Expr.lit val))
  | .truncf => match args with
      | [v] => s.lookup v
      | _ => none
  | .make_range sizeOpt =>
      some (SymValue.tensor [sizeOpt.getD s.block_size] (fun i => Expr.lit (Int.ofNat i)))
  | .splat shape =>
      match args with
      | [v] => match s.lookup v with
        | some (SymValue.scalar e) =>
            some (SymValue.tensor shape (fun _ => e))
        | _ => none
      | _ => none
  | .addptr =>
      match args with
      | [p, o] => match s.lookup p, s.lookup o with
        | some (SymValue.scalar base), some (SymValue.scalar off) =>
            some (SymValue.scalar (Expr.add base off))
        | some (SymValue.tensor n bases), some (SymValue.tensor m offs) =>
            if n == m then some (SymValue.tensor n (fun i => Expr.add (bases i) (offs i)))
            else none
        | some (SymValue.scalar base), some (SymValue.tensor n offs) =>
            some (SymValue.tensor n (fun i => Expr.add base (offs i)))
        | _, _ => none
      | _ => none
  | .addi => match args with
      | [a, b] => symAdd (s.lookup a) (s.lookup b)
      | _ => none
  | .subi => match args with
      | [a, b] => symBinop .sub (s.lookup a) (s.lookup b)
      | _ => none
  | .divsi => match args with
      | [a, b] => symBinop .divs (s.lookup a) (s.lookup b)
      | _ => none
  | .remsi => match args with
      | [a, b] => symBinop .rems (s.lookup a) (s.lookup b)
      | _ => none
  | .minsi => match args with
      | [a, b] => symBinop .mins (s.lookup a) (s.lookup b)
      | _ => none
  | .andi => match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.scalar x), some (SymValue.scalar y) =>
            some (SymValue.scalar (Expr.select x (Expr.select y (Expr.lit 1) (Expr.lit 0)) (Expr.lit 0)))
        | some (SymValue.tensor s1 xs), some (SymValue.tensor s2 ys) =>
            if s1 == s2 then
              some (SymValue.tensor s1 (fun i => Expr.select (xs i) (Expr.select (ys i) (Expr.lit 1) (Expr.lit 0)) (Expr.lit 0)))
            else none
        | _, _ => none
      | _ => none
  | .addf => match args with
      | [a, b] => symAdd (s.lookup a) (s.lookup b)
      | _ => none
  | .cmpi_slt =>
      -- comparison producing per-element 0/1: x < y ? 1 : 0, mirroring concrete.
      -- Uses Expr.lt so the mask is a real symbolic condition (NOT hardcoded to 1),
      -- which is what lets masked load/store be verified for ALL inputs.
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.tensor na xs), some (SymValue.tensor nb ys) =>
            -- shape guard mirrors concrete: mismatched lengths no-op (none)
            if na == nb then some (SymValue.tensor na (fun i => Expr.lt (xs i) (ys i)))
            else none
        | some (SymValue.scalar x), some (SymValue.scalar y) =>
            some (SymValue.scalar (Expr.lt x y))
        | _, _ => none
      | _ => none
  | .cmpi_sgt =>
      -- x > y ? 1 : 0 via Expr.binop .sgt, mirroring concrete cmpi_sgt.
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.tensor na xs), some (SymValue.tensor nb ys) =>
            if na == nb then some (SymValue.tensor na (fun i => Expr.binop .sgt (xs i) (ys i)))
            else none
        | some (SymValue.scalar x), some (SymValue.scalar y) =>
            some (SymValue.scalar (Expr.binop .sgt x y))
        | _, _ => none
      | _ => none

  | .cmpi_sge =>
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.tensor n _), some (SymValue.tensor _ _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))
        | some (SymValue.tensor n _), some (SymValue.scalar _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))
        | some (SymValue.scalar _), some (SymValue.tensor n _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))
        | some (SymValue.scalar _), some (SymValue.scalar _) =>
            some (SymValue.scalar (Expr.lit 1))
        | _, _ => none
      | _ => none

  | .maxsi => match args with
      | [a, b] => symMax (s.lookup a) (s.lookup b)
      | _ => none
  | .muli =>
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.scalar x), some (SymValue.scalar y) =>
            some (SymValue.scalar (Expr.mul x y))
        | some (SymValue.tensor n xs), some (SymValue.tensor k ys) =>
            if n == k then some (SymValue.tensor n (fun i => Expr.mul (xs i) (ys i)))
            else none
        | _, _ => none
      | _ => none
  | .load =>
      -- mirror concrete: [ptr] unmasked, [ptr,mask] masked (0 default),
      -- [ptr,mask,other] masked with `other` fallback. Masked elements use .select.
      match args with
      | [ptr] =>
          match s.lookup ptr with
          | some (SymValue.tensor n addrs) =>
              some (SymValue.tensor n (fun i => Expr.load (addrs i)))
          | some (SymValue.scalar addr) =>
              some (SymValue.scalar (Expr.load addr))
          | _ => none
      | [ptr, mask] =>
          match s.lookup ptr, s.lookup mask with
          | some (SymValue.tensor n addrs), some (SymValue.tensor nm masks) =>
              if n == nm then
                some (SymValue.tensor n (fun i =>
                  Expr.select (masks i) (Expr.load (addrs i)) (Expr.lit 0)))
              else none
          | _, _ => none
      | [ptr, mask, other] =>
          match s.lookup ptr, s.lookup mask, s.lookup other with
          | some (SymValue.tensor n addrs), some (SymValue.tensor _ masks),
            some (SymValue.tensor _ others) =>
              some (SymValue.tensor n (fun i =>
                Expr.select (masks i) (Expr.load (addrs i)) (others i)))
          | _, _, _ => none
      | _ => none
  | .select =>
      match args with
      | [cond, a, b] => match s.lookup cond, s.lookup a, s.lookup b with
        | some (SymValue.tensor n _),
          some (SymValue.tensor _ as_),
          some (SymValue.tensor _ bs_) =>
            -- select(cond, a, b): symbolically = max(b, a) for ReLU pattern
            some (SymValue.tensor n (fun i => Expr.max (bs_ i) (as_ i)))
        | some (SymValue.tensor n _),
          some (SymValue.tensor _ as_),
          some (SymValue.scalar b) =>
            -- select(cond, tensor, scalar): e.g. select(x>=0, x, 0)
            some (SymValue.tensor n (fun i => Expr.max b (as_ i)))
        | some (SymValue.tensor n _),
          some (SymValue.scalar a),
          some (SymValue.tensor _ bs_) =>
            some (SymValue.tensor n (fun i => Expr.max (bs_ i) a))
        | _, _, _ => none
      | _ => none

  | .dot =>
      -- Matrix multiply mirroring concrete doDot: C[i,j] = sum_k(A[i,k] * B[k,j])
      -- A is [m,k1], B is [k2,n]; guard k1==k2; output [m,n]. Optional accumulator (3rd arg).
      let symDot (va vb : SymValue) (acc : Option (Nat → Expr)) : Option SymValue :=
        match va, vb with
        | SymValue.tensor [m, k1] fa, SymValue.tensor [k2, n] fb =>
            if k1 != k2 then none else
            some (SymValue.tensor [m, n] (fun idx =>
              let i := idx / n
              let j := idx % n
              let sum := Expr.reduceSum ((List.range k1).map (fun kk =>
                Expr.mul (fa (i * k1 + kk)) (fb (kk * n + j))))
              match acc with
              | some fAcc => Expr.add sum (fAcc idx)
              | none => sum))
        | _, _ => none
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some va, some vb => symDot va vb none
        | _, _ => none
      | [a, b, accVar] => match s.lookup a, s.lookup b with
        | some va, some vb =>
            match s.lookup accVar with
            | some (SymValue.tensor _ fAcc) => symDot va vb (some fAcc)
            | _ => none
        | _, _ => none
      | _ => none

  | .expand_dims axis =>
      match args with
      | [v] => symExpandDims axis (s.lookup v)
      | _ => none
  | .broadcast shape =>
      match args with
      | [v] => symBroadcast shape (s.lookup v)
      | _ => none
  | .reduce_sum _ =>
      match args with
      | [v] => match s.lookup v with
        | some (SymValue.tensor n f) =>
            let exprs := (List.range (shapeProd n)).map f
            some (SymValue.scalar (Expr.reduceSum exprs))
        | _ => none
      | _ => none

  | .store => none
  | _ => none

-- ── Symbolic Instruction + Kernel Execution ───────────────────────────────────

def symEvalInstr (instr : TritonInstr) (s : SymState) : SymState :=
  match instr.op with
  | .store =>
      -- [p,v] unmasked (write all); [p,v,m] masked: write only mask-true indices,
      -- mirroring concrete's filterMap. Structural match keeps symbolic ≡ concrete.
      match instr.args with
      | [p, v] =>
          match s.lookup p, s.lookup v with
          | some (SymValue.tensor n addrs), some (SymValue.tensor _ vals) =>
              List.foldl (fun st i =>
                let addr := (evalExpr (addrs i) (fun _ => 0)).natAbs
                st.writeMem addr (vals i)) s (List.range (shapeProd n))
          | some (SymValue.scalar addrExpr), some (SymValue.scalar valExpr) =>
              let addr := (evalExpr addrExpr (fun _ => (0 : Int))).natAbs
              s.writeMem addr valExpr
          | _, _ => s
      | [p, v, m] =>
          match s.lookup p, s.lookup v, s.lookup m with
          | some (SymValue.tensor n addrs), some (SymValue.tensor _ vals),
            some (SymValue.tensor _ masks) =>
              List.foldl (fun st i =>
                if (evalExpr (masks i) (fun _ => 0)) != 0 then
                  let addr := (evalExpr (addrs i) (fun _ => 0)).natAbs
                  st.writeMem addr (vals i)
                else st) s (List.range (shapeProd n))
          | _, _, _ => s
      | _ => s
  | _ =>
      match symEvalOp instr.op instr.args s with
      | some val => s.bind instr.result val
      | none     => s

def symEvalKernel (kernel : TritonKernel) (s : SymState) : SymState :=
  List.foldl (fun st instr => symEvalInstr instr st) s kernel


/-- Symbolic for-loop: mirror evalForLoop, binding the induction var as Expr.lit each iteration. -/
def symEvalForLoop (loop : ForLoop) (ss : SymState) : SymState :=
  (List.range loop.trip).foldl
    (fun st k => symEvalKernel loop.body (st.bind loop.ivName (SymValue.scalar (Expr.lit (Int.ofNat k)))))
    ss

-- ── Vector Add Symbolic Check ─────────────────────────────────────────────────

def symVectorAddInitState (pid bs gs n : Nat) : SymState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr =>
      if addr < n then Expr.var "a" addr
      else if addr < 2 * n then Expr.var "b" addr
      else Expr.lit 0
  , env        := fun v => match v with
      | "a_base" => some (SymValue.scalar (Expr.lit 0))
      | "b_base" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "c_base" => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "bsize"  => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | _        => none }

def vectorAddSpecExpr (pid bs i n : Nat) : Expr :=
  Expr.add (Expr.var "a" (pid * bs + i)) (Expr.var "b" (n + pid * bs + i))

def symCheckVectorAdd (kernel : TritonKernel) (pid bs gs n i : Nat) : Bool :=
  let s' := symEvalKernel kernel (symVectorAddInitState pid bs gs n)
  let raw  := s'.memory (2 * n + pid * bs + i)
  let norm := normalizeWithMem raw n
  norm == vectorAddSpecExpr pid bs i n

def symVectorAddTutorialInitState (pid bs gs n : Nat) : SymState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr =>
      if addr < n then Expr.var "a" addr
      else if addr < 2 * n then Expr.var "b" addr
      else Expr.lit 0
  , env        := fun v => match v with
      | "arg0"       => some (SymValue.scalar (Expr.lit 0))
      | "arg1"       => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "arg2"       => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "a_base"     => some (SymValue.scalar (Expr.lit 0))
      | "b_base"     => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "c_base"     => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "bsize"      => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | "x_ptr"      => some (SymValue.scalar (Expr.lit 0))
      | "y_ptr"      => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "output_ptr" => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "n_elements" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | _            => none }

def symCheckVectorAddTutorial (kernel : TritonKernel) (pid bs gs n i : Nat) : Bool :=
  let s' := symEvalKernel kernel (symVectorAddTutorialInitState pid bs gs n)
  let raw  := s'.memory (2 * n + pid * bs + i)
  let norm := normalizeWithMem raw n
  norm == vectorAddSpecExpr pid bs i n

end Trident
