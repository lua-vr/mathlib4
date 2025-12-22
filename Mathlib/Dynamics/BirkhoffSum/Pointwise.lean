/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Algebra.Order.Group.PartialSups
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Pointwise Ergodic Theorem

The Pointwise Ergodic Theorem, also known as Birkhoff's Ergodic Theorem, establishes the convergence
of time averages for dynamical systems.

Let `(α, μ)` be a probability space and `f: α → α` be a measure-preserving transformation. The
result states that, for any integrable function `φ  ∈ L¹(μ)`, the time averages
`(1/n)∑_{k=0}^{n-1} φ(f^k x)` converge almost everywhere as `n → ∞` to a limit function `φ*`.
Moreover the limit function `φ*` is essentially `f`-invariant and integrable with `∫φ* dμ = ∫φ dμ`.
If the system is ergodic, then `φ*` equals the constant `∫f dμ` almost everywhere.

The limit function `φ*` is equal to the conditional expectation of `φ` with respect to the σ-algebra
of `f`-invariant sets. This is used explicitly during this proof and also in the main statement.

## Main statements

* `ae_tendsTo_birkhoffAverage_condExp`: time average coincides with conditional expectation

-/

variable {α : Type*}

section BirkhoffMax

/-- The maximum of `birkhoffSum f g i` for `i` ranging from `0` to `n`. -/
def birkhoffMax (f : α → α) (g : α → ℝ) : ℕ →o (α → ℝ) := partialSups (birkhoffSum f g)

lemma birkhoffMax_nonneg {f : α → α} {g n} :
    0 ≤ birkhoffMax f g n := by
  apply (le_partialSups_of_le _ n.zero_le).trans'
  rfl

lemma birkhoffMax_succ {f : α → α} {g n} :
    birkhoffMax f g (n + 1) = 0 ⊔ (g + birkhoffMax f g n ∘ f) := by
  have : birkhoffSum f g ∘ Nat.succ = fun k ↦ g + birkhoffSum f g k ∘ f := by
    funext
    exact birkhoffSum_succ' ..
  erw [partialSups_succ', this, partialSups_const_add, birkhoffSum_zero']
  funext
  simp [birkhoffMax, partialSups]

example (p : Prop) (h : False ∨ p) : p := h.elim (·.elim) id

lemma birkhoffMax_succ' {f : α → α} {g n x} (hpos : 0 < birkhoffMax f g (n + 1) x) :
    birkhoffMax f g (n + 1) x = g x + birkhoffMax f g n (f x) := by
  erw [birkhoffMax_succ, lt_sup_iff] at hpos
  cases hpos with
  | inl h => absurd h; exact lt_irrefl 0
  | inr h =>
    erw [birkhoffMax_succ, Pi.sup_apply, sup_of_le_right h.le] 
    rfl

lemma birkhoffMax_comp_le_succ {f : α → α} {g n} :
    birkhoffMax f g n ≤ birkhoffMax f g (n + 1) := by
  gcongr
  exact n.le_succ

lemma birkhoffMax_le_birkhoffMax {f : α → α} {g n x} (hpos : 0 < birkhoffMax f g n x) :
    birkhoffMax f g n x ≤ g x + birkhoffMax f g n (f x) := by
  match n with
  | 0 => absurd hpos; exact lt_irrefl 0
  | n + 1 => 
    apply le_of_eq_of_le (birkhoffMax_succ' hpos)
    apply add_le_add_right
    exact birkhoffMax_comp_le_succ (f x)

lemma birkhoffMax_pos_of_mem_support {f : α → α} {g : α → ℝ} {n x}
    (hx : x ∈ (birkhoffMax f g n).support) : 0 < birkhoffMax f g n x := by
  apply lt_or_gt_of_ne at hx
  cases hx with
  | inl h =>
    absurd h; exact (birkhoffMax_nonneg x).not_gt
  | inr h => exact h

-- TODO: move elsewhere
@[measurability]
lemma birkhoffSum_measurable [MeasurableSpace α] {f : α → α} (hf : Measurable f) {g : α → ℝ}
    (hg : Measurable g) {n} : Measurable (birkhoffSum f g n) := by
  apply Finset.measurable_sum
  measurability

@[measurability]
lemma birkhoffMax_measurable [MeasurableSpace α] {f : α → α} (hf : Measurable f) {g : α → ℝ}
    (hg : Measurable g) {n} : Measurable (birkhoffMax f g n) := by
  unfold birkhoffMax
  induction n <;> measurability

section MeasurePreserving

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac) {g : α → ℝ} {n}
  (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)

include hf

@[measurability]
lemma birkhoffSum_aestronglyMeasurable (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffSum f g n) μ := by
  apply Finset.aestronglyMeasurable_fun_sum
  exact fun i _ => hg.comp_measurePreserving (hf.iterate i)

@[measurability]
lemma birkhoffMax_aestronglyMeasurable (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n <;> measurability

include hg

-- TODO: move elsewhere
lemma birkhoffSum_integrable : Integrable (birkhoffSum f g n) μ :=
  integrable_finset_sum _ fun _ _ ↦ (hf.iterate _).integrable_comp_of_integrable hg

lemma birkhoffMax_integrable : Integrable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n with
  | zero => exact integrable_zero ..
  | succ n hn => simpa using Integrable.sup hn (birkhoffSum_integrable μ hf hg)

lemma birkhoffMax_integral_le :
    ∫ x, birkhoffMax f g n x ∂μ ≤
    ∫ x in (birkhoffMax f g n).support, g x ∂μ +
    ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
  have := hf.integrable_comp_of_integrable (birkhoffMax_integrable μ hf hg (n := n))
  rw [←integral_add hg.restrict, ←setIntegral_support]
  · apply setIntegral_mono_on₀
    · exact (birkhoffMax_integrable μ hf hg).restrict
    · exact .add hg.restrict this.restrict
    · exact AEStronglyMeasurable.nullMeasurableSet_support (by measurability)
    · intro x hx
      exact birkhoffMax_le_birkhoffMax (birkhoffMax_pos_of_mem_support hx)
  · exact this.restrict

lemma setIntegral_nonneg_on_birkhoffMax_support :
    0 ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
  have hg₁ : AEStronglyMeasurable (birkhoffMax f g n) μ := by measurability
  have hg₂ : Integrable (birkhoffMax f g n) μ := birkhoffMax_integrable μ hf hg
  have hg₃ : Integrable (birkhoffMax f g n ∘ f) μ := hf.integrable_comp_of_integrable hg₂
  calc
    0 ≤ ∫ x in (birkhoffMax f g n).supportᶜ, birkhoffMax f g n (f x) ∂μ := by
      exact integral_nonneg (fun x  => birkhoffMax_nonneg (f x))
    _ = ∫ x, birkhoffMax f g n (f x) ∂μ -
        ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
      exact setIntegral_compl₀ hg₁.nullMeasurableSet_support hg₃
    _ = ∫ x, birkhoffMax f g n x ∂μ -
        ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
      rw [←integral_map hf.aemeasurable (hf.map_eq.symm ▸ hg₁), hf.map_eq]
    _ ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
      grw [birkhoffMax_integral_le μ hf hg]
      grind

end MeasurePreserving

end BirkhoffMax

section PR -- todo: separate PR

variable {ι α : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] [LinearOrder α]

theorem partialSups_exists (f : ι → α) (i : ι) :
    ∃ j ≤ i, partialSups f i = f j := by
  obtain ⟨j, hj⟩ : ∃ j ∈ Finset.Iic i, ∀ k ∈ Finset.Iic i, f k ≤ f j :=
    Finset.exists_max_image _ _ ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  simp_all only [Finset.mem_Iic, partialSups, OrderHom.coe_mk]
  use j, hj.1
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun k hk => hj.2 k (Finset.mem_Iic.1 hk)
  · exact Finset.le_sup' _ (Finset.mem_Iic.2 hj.1 )

end PR

section BirkhoffSup

def birkhoffSupSet (f : α → α) (g : α → ℝ) : Set α := {x | ∃ n : ℕ, birkhoffSum f g n x > 0}

lemma birkhoffSupSet_eq_iSup_birkhoffMax_support {f : α → α} {g : α → ℝ} :
    birkhoffSupSet f g = ⋃ n : ℕ, (birkhoffMax f g n).support := by
  ext x
  simp only [birkhoffSupSet, gt_iff_lt, Set.mem_setOf_eq, Set.mem_iUnion, Function.mem_support]
  constructor
  · refine fun ⟨n, hn⟩ => ⟨n, ?_⟩
    apply ne_of_gt
    apply hn.trans_le
    exact le_partialSups (birkhoffSum f g) _ _
  · rintro ⟨n, hn⟩
    apply lt_or_gt_of_ne at hn
    cases hn with
    | inl h => absurd h; exact not_lt_of_ge (birkhoffMax_nonneg x)
    | inr h =>
      rw [birkhoffMax, Pi.partialSups_apply] at h
      rcases partialSups_exists (birkhoffSum f g · x) n with ⟨m, _, hm₂⟩
      exact ⟨m, hm₂ ▸ h⟩

section MeasurePreserving

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac) {g : α → ℝ} {n}
  (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)

include hf hg

lemma tendsto_setIntegral_on_birkhoffMax_support_birkhoffSupSet :
    Tendsto (fun n ↦ ∫ x in (birkhoffMax f g n).support, g x ∂μ) atTop
            (𝓝 <| ∫ x in birkhoffSupSet f g, g x ∂ μ) := by
  rw [birkhoffSupSet_eq_iSup_birkhoffMax_support]
  apply tendsto_setIntegral_of_monotone₀ _ _ hg.integrableOn
  · intros
    exact AEStronglyMeasurable.nullMeasurableSet_support (by measurability)
  · intro i j hij x
    have : 0 ≤ birkhoffMax f g i x := birkhoffMax_nonneg x
    have := (birkhoffMax f g).mono hij x
    grind [Function.mem_support]

/-- The *Maximal Ergodic Theorem*

The integral of `g` over the set where the supremum of the Birkhoff sums
is positive is non-negative. -/
theorem setIntegral_nonneg_on_birkhoffSupSet :
    0 ≤ ∫ x in birkhoffSupSet f g, g x ∂μ := by
  apply ge_of_tendsto' (tendsto_setIntegral_on_birkhoffMax_support_birkhoffSupSet μ hf hg)
  intro n
  exact setIntegral_nonneg_on_birkhoffMax_support μ hf hg

end MeasurePreserving

end BirkhoffSup

