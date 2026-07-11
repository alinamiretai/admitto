-- Trident.SourceLang
-- The formal SOURCE language of Trident.
--
-- In CompCert, Clight is the source language with defined semantics.
-- The compiler transforms Clight → Assembly, and CompCert proves
-- that transformation preserves Clight's meaning.
--
-- In Trident, SpecLang is the source language.
-- The Triton compiler transforms SpecLang programs → TTIR,
-- and Trident proves that transformation preserves SpecLang's meaning.
--
-- SpecLang programs are pure mathematical functions.
-- They have NO notion of GPU, tile, block, pointer, or parallelism.
-- They are the ground truth — the thing we are proving TTIR implements.

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip

namespace Trident

/-
1. SPECLANG: THE SOURCE LANGUAGE
A SpecLang program is simply a function from inputs to outputs.
We parameterize over the input/output types to keep it general.

For now we work over List Int (flat arrays of integers).
This covers: vector add, ReLU, matmul, layer norm, elementwise ops.
Floating point extensions can be added later.
-/

-- A SpecLang kernel takes:
--   inputs  : a list of input arrays (each is a List Int)
--   returns : one output array (List Int)
-- This models any elementwise or reduction kernel.
structure SpecKernel where
  -- Human-readable name (used by the CLI for --against matching)
  name   : String
  -- The mathematical function itself
  -- inputs.(0) = first input array, inputs.(1) = second, etc.
  spec   : List (List Int) → List Int
  -- The precondition: what must be true of the inputs
  -- (e.g., "both input arrays have the same length")
  pre    : List (List Int) → Prop

/-
2. SPECLANG SEMANTICS
The meaning of a SpecLang program is just function application.
This is deliberately trivial — SpecLang is pure math.
There is no interpreter, no state, no side effects.
-/
def evalSpec (kernel : SpecKernel) (inputs : List (List Int)) : List Int :=
  kernel.spec inputs

/-
3. THE COMPILATION RELATION
This is the key CompCert concept.
A TTIR kernel K is a "valid compilation" of a SpecLang spec S if
there exists a correspondence between TTIR execution and spec evaluation.

We state this as a Prop so it can appear in theorem statements.
The actual proof of this Prop is what lives in Trident/Simulation/.
-/
structure CompilationTarget where
  -- The source spec
  source    : SpecKernel
  -- How to extract the relevant output from a MachineState
  -- (which variable holds the result after kernel execution?)
  outputVar : String
  -- How to construct an initial MachineState from inputs
  -- (how do inputs get loaded into virtual memory?)
  initState : List (List Int) → Nat → Nat → Nat → (Nat → Int) → MachineState

end Trident
