-- Trident.Common.Values
-- Runtime values that exist during Triton kernel execution.
-- Shared between Source and Target languages.
--
-- CompCert equivalent: common/Values.v

namespace Trident

/--
A `TritonValue` is the data that lives in a register during execution.
Either a single scalar integer, or a tile (tensor) of integers.

We work over `Int` (arbitrary precision) rather than `Int32` for now.
This avoids bitvector overflow complications during initial proof development.
Bitvector semantics can be added as a refinement later.
-/
inductive TritonValue where
  | scalar (val : Int)
  | tensor (shape : List Nat) (vals : List Int)
  | fscalar (val : Float)
  | ftensor (shape : List Nat) (vals : List Float)
  deriving BEq, Repr

/-- Flat element count of a tensor shape (product of dimensions). -/
def shapeProd (shape : List Nat) : Nat := shape.foldl (· * ·) 1

namespace TritonValue

-- Smart constructors for common cases
def scalar0 : TritonValue := scalar 0
def tile (bs : Nat) (vals : List Int) : TritonValue := tensor [bs] vals

-- Accessors
def isScalar : TritonValue → Bool
  | scalar _ => true
  | _        => false

def isTensor : TritonValue → Bool
  | tensor _ _ => true
  | _          => false

def asScalar : TritonValue → Option Int
  | scalar v => some v
  | _        => none

def asTensor : TritonValue → Option (List Nat × List Int)
  | tensor s vs => some (s, vs)
  | _           => none

/-- Element-wise map over a TritonValue -/
def map (f : Int → Int) : TritonValue → TritonValue
  | scalar v      => scalar (f v)
  | tensor s vals => tensor s (vals.map f)
  | other         => other

/-- Element-wise zip of two TritonValues with the same shape -/
def zipWith (f : Int → Int → Int) : TritonValue → TritonValue → Option TritonValue
  | scalar x,      scalar y      => some (scalar (f x y))
  | tensor s1 xs,  tensor s2 ys  =>
      if s1 == s2
      then some (tensor s1 ((xs.zip ys).map (fun (x, y) => f x y)))
      else none
  | _,             _             => none

def isFScalar : TritonValue → Bool
  | fscalar _ => true
  | _         => false

def isFTensor : TritonValue → Bool
  | ftensor _ _ => true
  | _           => false

def asFScalar : TritonValue → Option Float
  | fscalar v => some v
  | _         => none

def asFTensor : TritonValue → Option (List Nat × List Float)
  | ftensor s vs => some (s, vs)
  | _            => none

def mapF (f : Float → Float) : TritonValue → TritonValue
  | fscalar v      => fscalar (f v)
  | ftensor s vals => ftensor s (vals.map f)
  | other          => other

def zipWithF (f : Float → Float → Float) : TritonValue → TritonValue → Option TritonValue
  | fscalar x,      fscalar y      => some (fscalar (f x y))
  | ftensor s1 xs,  ftensor s2 ys  =>
      if s1 == s2
      then some (ftensor s1 ((xs.zip ys).map (fun (x, y) => f x y)))
      else none
  | _,              _              => none

/-- Rank-1 wellformedness: tensor has single-dimension shape [n] with n = length.
    This is the supported class for elementwise/vector-add kernels (all tensors
    are [block_size]). Under WF1, concrete shape-equality and symbolic
    length-equality coincide exactly. -/

def WF1 : TritonValue → Prop
  | tensor sh vals  => sh = [vals.length]
  | ftensor sh vals => sh = [vals.length]
  | _ => True

/-- Rank-agnostic wellformedness: flat data length equals shape product.
    WF1 (rank-1, sh = [len]) is the special case. This is the invariant for 2D+ kernels. -/
def WFn : TritonValue → Prop
  | tensor sh vals  => shapeProd sh = vals.length
  | ftensor sh vals => shapeProd sh = vals.length
  | _ => True

/-- WF1 (rank-1) implies WFn (rank-agnostic): sh = [len] gives shapeProd sh = len. -/
theorem WF1_imp_WFn (t : TritonValue) (h : t.WF1) : t.WFn := by
  cases t with
  | tensor sh vals => simp only [WF1] at h; subst h; simp [WFn, shapeProd]
  | ftensor sh vals => simp only [WF1] at h; subst h; simp [WFn, shapeProd]
  | scalar => trivial
  | fscalar => trivial

/-- WFn extraction: recover shapeProd = length. -/
theorem WFn_tensor_len (sh : List Nat) (vals : List Int) (h : (tensor sh vals).WFn) :
    shapeProd sh = vals.length := h

end TritonValue
-- Key lemma: getD of zip+map with equal-length lists
theorem zipWith_add_getD (a b : List Int) (i : Nat) (h_len : a.length = b.length) :
    ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 =
    a.getD i 0 + b.getD i 0 := by
  by_cases h : i < a.length
  · have hb : i < b.length := by omega
    have hzip : i < (a.zip b).length := by simp [List.length_zip]; omega
    have hmap : i < ((a.zip b).map (fun p => p.fst + p.snd)).length := by
      rw [List.length_map]; exact hzip
    rw [show ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 =
        ((a.zip b).map (fun p => p.fst + p.snd))[i] from by
      simp [List.getD, List.getElem?_eq_getElem hmap]]
    rw [show a.getD i 0 = a[i] from by simp [List.getD, List.getElem?_eq_getElem h]]
    rw [show b.getD i 0 = b[i] from by simp [List.getD, List.getElem?_eq_getElem hb]]
    simp [List.getElem_map, List.getElem_zip]
  · have ha : a.length <= i := Nat.not_lt.mp h
    have hb : b.length <= i := by omega
    have hzip : (a.zip b).length <= i := by simp [List.length_zip]; omega
    have hmap : ((a.zip b).map (fun p => p.fst + p.snd)).length <= i := by
      rw [List.length_map]; exact hzip
    simp [List.getD, List.getElem?_eq_none hmap,
          List.getElem?_eq_none ha, List.getElem?_eq_none hb]


-- Bridge: for rank-1 wellformed tensors, concrete shape-equality and symbolic
-- length-equality are the SAME boolean. This is what makes the concrete
-- (shape-guarded) and symbolic (length-guarded) elementwise ops provably agree.
theorem wf1_shape_iff_length
    (sha shb : List Nat) (xs ys : List Int)
    (hwa : (TritonValue.tensor sha xs).WF1) (hwb : (TritonValue.tensor shb ys).WF1) :
    (sha == shb) = (xs.length == ys.length) := by
  simp only [TritonValue.WF1] at hwa hwb
  subst hwa; subst hwb
  simp

end Trident
