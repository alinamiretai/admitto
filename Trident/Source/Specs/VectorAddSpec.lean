import Trident.Source.Lang

namespace Trident

def vectorAddSpec (a b : List Int) : List Int :=
  (a.zip b).map (fun (x, y) => x + y)

@[simp]
theorem vectorAddSpec_eq_eval (a b : List Int) :
    vectorAddSpec a b = TensorExpr.vectorAdd.eval [a, b] := by
  simp [vectorAddSpec, TensorExpr.vectorAdd, TensorExpr.eval]


@[simp]
theorem vectorAddSpec_getD (a b : List Int) (i : Nat) (h_len : a.length = b.length) :
    (vectorAddSpec a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  simp only [vectorAddSpec]
  exact zipWith_add_getD a b i h_len

@[simp]
theorem vectorAddSpec_length (a b : List Int) :
    (vectorAddSpec a b).length = min a.length b.length := by
  simp [vectorAddSpec]

theorem vectorAddSpec_length_eq (a b : List Int) (h : a.length = b.length) :
    (vectorAddSpec a b).length = a.length := by
  simp [vectorAddSpec, h]

end Trident
