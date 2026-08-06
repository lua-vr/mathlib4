/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib

/-!
# Empirical measures

In this file we define empirical measures.

## Main definitions

* `Foo`: ...

## Main statements

* `foo_bar`: ...

## Implementation notes

...

## References

* [Author, *Title*][bibkey]

## Tags

tag1, tag2
-/

public noncomputable section

open MeasureTheory
open scoped NNReal

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → α}
  {x : α} {n : ℕ} (g : α → E)

def empiricalMeasure (f : α → α) (x : α) (n : ℕ) : Measure α :=
  birkhoffAverage ℝ≥0 f Measure.dirac (n + 1) x

instance : IsProbabilityMeasure (empiricalMeasure f x n) := by
  constructor
  simp [empiricalMeasure, birkhoffAverage, birkhoffSum, ENNReal.smul_def, ENNReal.inv_mul_cancel]

example (g : α → E) : ∫ y, g y ∂ empiricalMeasure f x n = birkhoffAverage ℝ f g (n + 1) x := sorry

section Invariant

-- the sequence has a limit point in the weak-* topology

-- a limit point is an invariant measure.

end Invariant
