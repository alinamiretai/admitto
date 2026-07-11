import Trident.Common.Smallstep

namespace Trident

inductive TensorExpr where
  | input  (idx : Nat)
  | const  (val : Int) (len : Nat)
  | zip    (op : Int → Int → Int) (a b : TensorExpr)
  | map    (f : Int → Int) (a : TensorExpr)
  | reduce (f : Int → Int → Int) (init : Int) (a : TensorExpr)
  | concat (a b : TensorExpr)
  deriving Inhabited

def TensorExpr.eval (inputs : List (List Int)) : TensorExpr → List Int
  | .input i      => inputs.getD i []
  | .const v n    => List.replicate n v
  | .zip op a b   =>
      let xs := a.eval inputs
      let ys := b.eval inputs
      (xs.zip ys).map (fun (x, y) => op x y)
  | .map f a      => (a.eval inputs).map f
  | .reduce f z a => [(a.eval inputs).foldl f z]
  | .concat a b   => a.eval inputs ++ b.eval inputs

def TensorExpr.vectorAdd : TensorExpr := .zip (· + ·) (.input 0) (.input 1)
def TensorExpr.relu      : TensorExpr := .map (fun x => max 0 x) (.input 0)
def TensorExpr.vectorMul : TensorExpr := .zip (· * ·) (.input 0) (.input 1)
def TensorExpr.sumReduce : TensorExpr := .reduce (· + ·) 0 (.input 0)

def tensorExprSemantics (prog : TensorExpr) : SourceSemantics where
  State  := List (List Int)
  init   := id
  output := prog.eval
  step   := fun _ _ => False

@[simp]
theorem eval_vectorAdd (a b : List Int) :
    TensorExpr.vectorAdd.eval [a, b] =
    (a.zip b).map (fun (x, y) => x + y) := by
  simp [TensorExpr.vectorAdd, TensorExpr.eval]

@[simp]
theorem eval_relu (xs : List Int) :
    TensorExpr.relu.eval [xs] = xs.map (fun x => max 0 x) := by
  simp [TensorExpr.relu, TensorExpr.eval]

@[simp]
theorem eval_vectorAdd_getD (a b : List Int) (i : Nat) (h_len : a.length = b.length) :
    (TensorExpr.vectorAdd.eval [a, b]).getD i 0 =
    a.getD i 0 + b.getD i 0 := by
  simp only [TensorExpr.vectorAdd, TensorExpr.eval]
  exact zipWith_add_getD a b i h_len

end Trident
