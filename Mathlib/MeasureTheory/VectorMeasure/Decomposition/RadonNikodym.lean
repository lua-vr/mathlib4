/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Radon-Nikodym derivatives of vector measures

This file contains results about Radon-Nikodym derivatives of signed measures
that depend both on the Lebesgue decomposition of signed measures
and the theory of Radon-Nikodym derivatives of usual measures.
-/

public section

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α}

open Measure VectorMeasure

namespace SignedMeasure

theorem withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutelyContinuous_ennreal_iff, (_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ),
    totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi, rnDeriv_def, integral_sub,
      setIntegral_toReal_rnDeriv h.1 i, setIntegral_toReal_rnDeriv h.2 i]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      rw [JordanDecomposition.toSignedMeasure, _root_.sub_apply,
        toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi, measureReal_def,
        measureReal_def]
    all_goals
      refine Integrable.integrableOn ?_
      refine ⟨?_, hasFiniteIntegral_toReal_of_lintegral_ne_top ?_⟩
      · apply Measurable.aestronglyMeasurable (by fun_prop)
      · exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α)
    [SigmaFinite μ] : s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩

/-- If a signed measure `s` is absolutely continuous with respect to `μ`, then integrating `f`
against `s` is the same as integrating `s.rnDeriv μ • f` against `μ`. -/
theorem integral_rnDeriv_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : SignedMeasure α} {μ : Measure α} [s.HaveLebesgueDecomposition μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) {f : α → G} (hf : s.Integrable f) :
    ∫ x, s.rnDeriv μ x • f x ∂μ = ∫ᵛ x, f x ∂<•s := by
  rw [absolutelyContinuous_ennreal_iff, ennrealToMeasure_toENNRealVectorMeasure,
    totalVariation_absolutelyContinuous_iff] at h
  obtain ⟨hPμ, hNμ⟩ := h
  rw [VectorMeasure.Integrable, ← totalVariation_eq_variation, totalVariation] at hf
  have hP := hf.mono_measure (Measure.le_add_right le_rfl)
  have hN := hf.mono_measure (Measure.le_add_left le_rfl)
  simp_rw [rnDeriv_def, sub_smul]
  rw [integral_sub ((integrable_rnDeriv_smul_iff hPμ).mpr hP)
      ((integrable_rnDeriv_smul_iff hNμ).mpr hN), MeasureTheory.integral_rnDeriv_smul hPμ,
    MeasureTheory.integral_rnDeriv_smul hNμ]
  conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  rw [integral_sub_vectorMeasure (by simpa [VectorMeasure.Integrable])
    (by simpa [VectorMeasure.Integrable]), integral_toSignedMeasure, integral_toSignedMeasure]

end SignedMeasure

theorem withDensityᵥ_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] [SigmaFinite μ] {f : α → E}
    (hμν : μ ≪ ν) (hf : Integrable f μ) :
    ν.withDensityᵥ (fun x ↦ (μ.rnDeriv ν x).toReal • f x) = μ.withDensityᵥ f := by
  rw [withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (measurable_rnDeriv μ ν).aemeasurable
    (rnDeriv_lt_top μ ν) ((integrable_rnDeriv_smul_iff hμν).mpr hf), withDensity_rnDeriv_eq μ ν hμν]

end MeasureTheory
