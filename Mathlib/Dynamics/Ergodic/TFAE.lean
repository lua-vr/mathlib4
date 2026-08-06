/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Integrable
public import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Equivalent definitions of ergodicity.

In this file we ...

## Main definitions

* `Foo`: ...

## Main statements

* `foo_bar`: ...

## Implementation notes

...

## References

* [Krerley Oliveira & Marcelo Viana, *Foundations of Ergodic Theory*][bibkey]

## Tags

tag1, tag2
-/

@[expose] public section

open Filter MeasureTheory Topology

variable {α : Type*} [MeasurableSpace α] {f : α → α} {μ : Measure α} [IsProbabilityMeasure μ]

/-- **Equivalent characterizations of ergodicity**
(Oliveira–Viana, *Foundations of Ergodic Theory*, Proposition 4.1.3).

Let `μ` be an invariant probability measure of a measurable map `f : α → α`.
The following are equivalent:

* (a) for every measurable set `B`, the mean sojourn time `τ(B, x)` equals `μ B`
  at `μ`-a.e. point;
* (b) for every measurable set `B`, the function `τ(B, ·)` is a.e. constant;
* (c) for every integrable `φ`, the time average `φ̃ x` equals `∫ φ ∂μ` at a.e. point;
* (d) for every integrable `φ`, the time average `φ̃` is a.e. constant;
* (e) every integrable invariant `ψ` satisfies `ψ x = ∫ ψ ∂μ` at a.e. point;
* (f) every integrable invariant `ψ` is a.e. constant;
* (g) every invariant measurable set has measure `0` or `1`;
* (h) `f` is ergodic in the sense of `PreErgodic`.

Here the mean sojourn time `τ(B, ·)` and the time average `φ̃` are written as limits of
Birkhoff averages, so no appeal to the Birkhoff ergodic theorem is needed to *state* the result. -/
theorem ergodic_tfae (hf : MeasurePreserving f μ μ) :
    List.TFAE [
      -- (a)
      ∀ B : Set α, MeasurableSet B → ∀ᵐ x ∂μ,
        Tendsto (birkhoffAverage ℝ f (B.indicator 1) · x) atTop (𝓝 (μ B).toReal),
      -- (b)
      ∀ B : Set α, MeasurableSet B → ∃ c : ℝ, ∀ᵐ x ∂μ,
        Tendsto (birkhoffAverage ℝ f (B.indicator 1) · x) atTop (𝓝 c),
      -- (c)
      ∀ φ : α → ℝ, Integrable φ μ → ∀ᵐ x ∂μ,
        Tendsto (birkhoffAverage ℝ f φ · x) atTop (𝓝 (∫ y, φ y ∂μ)),
      -- (d)
      ∀ φ : α → ℝ, Integrable φ μ → ∃ c : ℝ, ∀ᵐ x ∂μ,
        Tendsto (birkhoffAverage ℝ f φ · x) atTop (𝓝 c),
      -- (e)
      ∀ ψ : α → ℝ, Integrable ψ μ → ψ ∘ f =ᵐ[μ] ψ → ψ =ᵐ[μ] fun _ ↦ ∫ y, ψ y ∂μ,
      -- (f)
      ∀ ψ : α → ℝ, Integrable ψ μ → ψ ∘ f =ᵐ[μ] ψ → ∃ c : ℝ, ψ =ᵐ[μ] fun _ ↦ c,
      -- (g)
      ∀ A : Set α, MeasurableSet A → f ⁻¹' A =ᵐ[μ] A → μ A = 0 ∨ μ A = 1,
      -- (h)
      PreErgodic f μ] := by
  sorry
