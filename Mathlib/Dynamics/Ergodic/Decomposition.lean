/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import Mathlib

variable {α β : Type*} [m : MeasurableSpace α] [MeasurableSpace β] {f : α → α} (hf : Measurable f)

open MeasureTheory MeasurableSpace ProbabilityTheory Kernel

def MarkovColimit (_ : α → α) := α

instance : MeasurableSpace (MarkovColimit f) := invariants (m := m) f

variable (f) in
noncomputable def markovColimit : Kernel α (MarkovColimit f) :=
  deterministic id (measurable_id'' <| invariants_le f)

lemma markovColimit_invariant :
    markovColimit f ∘ₖ deterministic _ hf = markovColimit f := by
  sorry

section IsColimit

variable (k : Kernel α β) (hk : k ∘ₖ deterministic _ hf = k)

def markovColimit_desc : Kernel (MarkovColimit f) β := by
  sorry

theorem markovColimit_fac : markovColimit_desc ∘ₖ markovColimit f = k := by
  sorry

def markovColimit_uniq (k : Kernel α β) (hk : k ∘ₖ deterministic _ hf = k) :
    Kernel (MarkovColimit f) β := by
  sorry

end IsColimit

noncomputable section Decomposition

variable (f : α → α) (μ : Measure α) (hμ : MeasurePreserving f μ μ) [IsFiniteMeasure μ]
  [StandardBorelSpace α] [Nonempty α]

def foo : Kernel Unit (MarkovColimit f × α) :=
  (markovColimit f ×ₖ Kernel.id) ∘ₖ const Unit μ

instance : IsFiniteKernel (β := MarkovColimit f × α) (foo f μ) := by
  rw [foo, markovColimit]
  infer_instance

def bar : Kernel (MarkovColimit f) α :=
  Kernel.condKernel (foo f μ) ∘ₖ Kernel.deterministic ((), ·) (by fun_prop)


end Decomposition

#check invariants

#check Measure.condKernel
