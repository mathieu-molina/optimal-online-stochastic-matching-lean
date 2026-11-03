import Matching.CompletionReconstruction

/-! The complete one-segment disintegration formula for the original demand
sample: a terminal-survival term plus the marked first-completion terms.
Adaptive history integration and the posterior flow are not assumed here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching.ServiceCurveFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

theorem segment_measure_decomposition :
    (independentExponentials (ι := ι)) =
      independentExponentials.restrict p.terminalSurvival +
        Measure.sum (fun j => independentExponentials.restrict
          (variableWinner p.service p.deadline j)) := by
  have hcover : (p.terminalSurvival ∪ ⋃ j, variableWinner p.service p.deadline j :
      Set (ι → ℝ)) =ᵐ[independentExponentials] (univ : Set (ι → ℝ)) := by
    filter_upwards [p.no_completion_or_unique_ae] with z hz
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      rcases hz with hs | ⟨j, hj, _⟩
      · exact Or.inl hs
      · exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
  have hdis : Disjoint p.terminalSurvival (⋃ j, variableWinner p.service p.deadline j) := by
    apply Set.disjoint_left.mpr
    intro z hs hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    exact p.winner_subset_completion j hj hs
  have h := Measure.restrict_congr_set (μ := independentExponentials) hcover
  rw [Measure.restrict_univ, Measure.restrict_union hdis
    (MeasurableSet.iUnion p.measurable_winner),
    Measure.restrict_iUnion p.winner_disjoint p.measurable_winner] at h
  exact h.symm

theorem segment_lintegral_decomposition (f : (ι → ℝ) → ℝ≥0∞) :
    (∫⁻ z, f z ∂independentExponentials) =
      (∫⁻ z in p.terminalSurvival, f z ∂independentExponentials) +
        ∑ j, ∫⁻ z in variableWinner p.service p.deadline j, f z ∂independentExponentials := by
  have h := congrArg (fun μ : Measure (ι → ℝ) => ∫⁻ z, f z ∂μ) p.segment_measure_decomposition
  dsimp only at h
  rw [lintegral_add_measure, lintegral_sum_measure, tsum_fintype] at h
  exact h

theorem terminal_original_sample_lintegral (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in p.terminalSurvival, f z ∂independentExponentials) =
      ENNReal.ofReal (Real.exp (-(∑ i, p.service i p.deadline))) *
        ∫⁻ y, f (fun i => y i + p.service i p.deadline) ∂independentExponentials := by
  have hnonneg : ∀ i, 0 ≤ p.service i p.deadline := by
    intro i
    rw [← p.service_zero i]
    exact p.service_monotone i ⟨le_refl _, p.deadline_pos.le⟩
      ⟨p.deadline_pos.le, le_refl _⟩ p.deadline_pos.le
  have hm : Measurable (fun y : ι → ℝ => fun i => y i + p.service i p.deadline) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i).add_const _
  have h := lintegral_vector_residual hnonneg
    (fun y => f (fun i => y i + p.service i p.deadline)) (hf.comp hm)
  simp only [sub_add_cancel] at h
  change (∫⁻ z in p.terminalSurvival, f z ∂independentExponentials) =
    independentExponentials p.terminalSurvival *
      ∫⁻ y, f (fun i => y i + p.service i p.deadline) ∂independentExponentials at h
  rw [p.terminal_survival_probability] at h
  exact h

/-- Full one-step law, retaining the original demand coordinates. -/
theorem one_step_original_sample_lintegral (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂independentExponentials) =
      ENNReal.ofReal (Real.exp (-(∑ i, p.service i p.deadline))) *
        (∫⁻ y, f (fun i => y i + p.service i p.deadline) ∂independentExponentials) +
      ∑ j, ∫⁻ t in Icc 0 p.deadline,
        ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t))) *
          (∫⁻ y, f (p.reconstructMarked j (t, y)) ∂independentExponentials) := by
  rw [p.segment_lintegral_decomposition f, p.terminal_original_sample_lintegral f hf]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact p.original_sample_branch_lintegral j f hf

end StochasticMatching.ServiceCurveFamily
