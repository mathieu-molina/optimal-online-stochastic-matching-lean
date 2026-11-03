import Matching.SupermodularChains
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The supermodular chain formula for tail probabilities. The only random
hypotheses are measurable coordinates and almost-sure supermodularity. Two
models with matching chain exceedance laws therefore have equal maximum tails.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

noncomputable def maximumExceedance (d : Ω → Finset ι → ℝ) (a : ℝ) : Set Ω :=
  {ω | ∃ A, a < d ω A}

noncomputable def chainExceedance (d : Ω → Finset ι → ℝ) (a : ℝ)
    (C : Finset (Finset ι)) : Set Ω := {ω | ∀ A ∈ C, a < d ω A}

theorem measurableSet_maximumExceedance {d : Ω → Finset ι → ℝ}
    (hd : ∀ A, Measurable (fun ω => d ω A)) (a : ℝ) :
    MeasurableSet (maximumExceedance d a) := by
  unfold maximumExceedance
  simp only [setOf_exists]
  exact MeasurableSet.iUnion (fun A => measurableSet_lt measurable_const (hd A))

theorem measurableSet_chainExceedance {d : Ω → Finset ι → ℝ}
    (hd : ∀ A, Measurable (fun ω => d ω A)) (a : ℝ) (C : Finset (Finset ι)) :
    MeasurableSet (chainExceedance d a C) := by
  unfold chainExceedance
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun A => MeasurableSet.iInter
    (fun _ => measurableSet_lt measurable_const (hd A)))

theorem integral_event_constant (μ : Measure Ω) (E : Set Ω) [DecidablePred (· ∈ E)] (hE : MeasurableSet E) (c : ℝ) :
    (∫ ω, if ω ∈ E then c else 0 ∂μ) = μ.real E * c := by
  classical
  have he : (fun ω => if ω ∈ E then c else 0) = E.indicator (fun _ => c) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [he, integral_indicator_const c hE, smul_eq_mul]

theorem integrable_event_constant (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) [DecidablePred (· ∈ E)] (hE : MeasurableSet E) (c : ℝ) :
    Integrable (fun ω => if ω ∈ E then c else 0) μ := by
  classical
  have he : (fun ω => if ω ∈ E then c else 0) = E.indicator (fun _ => c) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [he]
  exact (integrable_const c : Integrable (fun _ : Ω => c) μ).indicator hE

theorem supermodular_max_tail_chain_formula (μ : Measure Ω) [IsFiniteMeasure μ]
    {d : Ω → Finset ι → ℝ} (hd : ∀ A, Measurable (fun ω => d ω A))
    (hmod : ∀ᵐ ω ∂μ, SupermodularFinset (d ω)) (a : ℝ) :
    μ.real (maximumExceedance d a) =
      ∑ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
        (-chainWeight C) * μ.real (chainExceedance d a C) := by
  classical
  have he : (fun ω => if ω ∈ maximumExceedance d a then (1 : ℝ) else 0) =ᵐ[μ]
      fun ω => ∑ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
        if ω ∈ chainExceedance d a C then -chainWeight C else 0 := by
    filter_upwards [hmod] with ω hω
    calc
      _ = (if ∃ A, a < d ω A then (1 : ℝ) else 0) := by
        by_cases h : ∃ A, a < d ω A <;> simp [maximumExceedance, h]
      _ = _ := supermodular_max_chain_identity hω a
      _ = _ := by
        apply Finset.sum_congr rfl
        intro C hC
        by_cases h : ∀ A ∈ C, a < d ω A <;> simp [chainExceedance, h]
  have hi := integral_congr_ae he
  rw [integral_event_constant μ _ (measurableSet_maximumExceedance hd a), mul_one] at hi
  rw [integral_finset_sum _ (fun C _ => integrable_event_constant μ _
    (measurableSet_chainExceedance hd a C) (-chainWeight C))] at hi
  rw [hi]
  apply Finset.sum_congr rfl
  intro C hC
  rw [integral_event_constant μ _ (measurableSet_chainExceedance hd a C), mul_comm]

theorem chainExceedance_empty_vertex {d : Ω → Finset ι → ℝ}
    (hd : ∀ ω, d ω ∅ = 0) {a : ℝ} (ha : 0 ≤ a)
    {C : Finset (Finset ι)} (hC : ∅ ∈ C) : chainExceedance d a C = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro ω hω
  have h := hω ∅ hC
  rw [hd ω] at h
  exact (not_lt_of_ge ha) h

variable {Ω' : Type*} [MeasurableSpace Ω']

theorem maximum_tail_eq_of_chain_laws (μ : Measure Ω) (ν : Measure Ω')
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {d : Ω → Finset ι → ℝ} {e : Ω' → Finset ι → ℝ}
    (hd : ∀ A, Measurable (fun ω => d ω A))
    (he : ∀ A, Measurable (fun ω => e ω A))
    (hdmod : ∀ᵐ ω ∂μ, SupermodularFinset (d ω))
    (hemod : ∀ᵐ ω ∂ν, SupermodularFinset (e ω)) (a : ℝ)
    (hchain : ∀ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
      μ.real (chainExceedance d a C) = ν.real (chainExceedance e a C)) :
    μ.real (maximumExceedance d a) = ν.real (maximumExceedance e a) := by
  rw [supermodular_max_tail_chain_formula μ hd hdmod,
    supermodular_max_tail_chain_formula ν he hemod]
  apply Finset.sum_congr rfl
  intro C hC
  rw [hchain C hC]

end StochasticMatching
