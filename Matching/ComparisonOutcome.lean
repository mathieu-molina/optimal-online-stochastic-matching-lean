import Matching.FirstStepReward
import Matching.PosteriorComparison
import Matching.MeasurableBranching
import Matching.AdaptiveBudget

/-! A concrete one-step random comparison payoff, its integrability and its
expected drift under the original exponential demand sample.
-/

open MeasureTheory Set
open scoped BigOperators

namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

noncomputable def comparisonOutcome (elapsed : ℝ) (initial : ι → ℝ) (z : ι → ℝ) : ℝ :=
  branchSelect (variableWinner p.service p.deadline)
    (fun j z => p.comparisonJump elapsed initial j (cappedHit (p.service j) p.deadline (z j)))
    (fun _ => p.comparisonPotential elapsed initial p.deadline) z

theorem measurable_comparisonOutcome (elapsed : ℝ) (initial : ι → ℝ) :
    Measurable (p.comparisonOutcome elapsed initial) :=
  measurable_branchSelect p.winner_disjoint p.measurable_winner
    (fun j => (p.continuous_comparisonJump elapsed initial j).measurable.comp (p.measurable_clock j))
    measurable_const

theorem comparisonOutcome_winner (elapsed : ℝ) (initial : ι → ℝ) {z : ι → ℝ} {j : ι}
    (hz : z ∈ variableWinner p.service p.deadline j) :
    p.comparisonOutcome elapsed initial z =
      p.comparisonJump elapsed initial j (cappedHit (p.service j) p.deadline (z j)) :=
  branchSelect_of_mem p.winner_disjoint _ _ hz

theorem comparisonOutcome_terminal (elapsed : ℝ) (initial : ι → ℝ) {z : ι → ℝ}
    (hz : z ∈ p.terminalSurvival) :
    p.comparisonOutcome elapsed initial z = p.comparisonPotential elapsed initial p.deadline := by
  apply branchSelect_of_not_mem
  intro j hj
  exact p.winner_subset_completion j hj hz

theorem comparisonPotential_bounds (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i)
    {t : ℝ} (ht : t ∈ Icc 0 p.deadline) :
    0 ≤ p.comparisonPotential elapsed initial t ∧
      p.comparisonPotential elapsed initial t ≤ Fintype.card ι := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact Comparison.continuation_nonneg (by linarith [ht.2])
      (add_nonneg (hx i) (p.service_nonneg ht i))
  · calc
      _ ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (Comparison.continuation_lt_one _ _).le)
      _ = _ := by simp

theorem comparisonJump_bounds (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i)
    (j : ι) {t : ℝ} (ht : t ∈ Icc 0 p.deadline) :
    0 ≤ p.comparisonJump elapsed initial j t ∧
      p.comparisonJump elapsed initial j t ≤ Fintype.card ι := by
  have hn : 0 ≤ ∑ i : {i : ι // i ≠ j},
      Comparison.continuation (elapsed + t) (initial i.1 + p.service i.1 t) := by
    apply Finset.sum_nonneg
    intro i _
    exact Comparison.continuation_nonneg (by linarith [ht.2])
      (add_nonneg (hx i.1) (p.service_nonneg ht i.1))
  have hu : (∑ i : {i : ι // i ≠ j},
      Comparison.continuation (elapsed + t) (initial i.1 + p.service i.1 t)) ≤
      (Fintype.card {i : ι // i ≠ j} : ℝ) := by
    calc
      _ ≤ ∑ _i : {i : ι // i ≠ j}, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (Comparison.continuation_lt_one _ _).le)
      _ = _ := by simp
  have hc : (Fintype.card {i : ι // i ≠ j} : ℝ) + 1 = Fintype.card ι := by
    exact_mod_cast survivor_card j
  unfold comparisonJump
  constructor <;> linarith

theorem comparisonOutcome_bounds (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i) (z : ι → ℝ) :
    0 ≤ p.comparisonOutcome elapsed initial z ∧
      p.comparisonOutcome elapsed initial z ≤ Fintype.card ι := by
  classical
  by_cases hw : ∃ j, z ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hw
    rw [p.comparisonOutcome_winner elapsed initial hj]
    exact p.comparisonJump_bounds elapsed initial hT hx j
      (cappedHit_bounds (p.service_continuous j) p.deadline_pos.le)
  · unfold comparisonOutcome
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    exact p.comparisonPotential_bounds elapsed initial hT hx ⟨p.deadline_pos.le, le_refl _⟩

theorem integrable_comparisonOutcome (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i) :
    Integrable (p.comparisonOutcome elapsed initial) independentExponentials := by
  apply (integrable_const (Fintype.card ι : ℝ)).mono'
    (p.measurable_comparisonOutcome elapsed initial).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (p.comparisonOutcome_bounds elapsed initial hT hx z).1]
  exact (p.comparisonOutcome_bounds elapsed initial hT hx z).2

theorem comparisonOutcome_expected_drift (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i) :
    (∫ z, p.comparisonOutcome elapsed initial z ∂independentExponentials) -
      p.comparisonPotential elapsed initial 0 =
    ∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u i => p.service i u) t *
      ∑ i, -(initial i + p.service i t + 1 - p.rate i t) *
        Comparison.sensitivity (elapsed + t) (initial i + p.service i t) := by
  have hi := p.integrable_comparisonOutcome elapsed initial hT hx
  rw [p.segment_measure_decomposition, integrable_add_measure] at hi
  have he : (∫ z, p.comparisonOutcome elapsed initial z ∂independentExponentials) =
      (∫ _ in p.terminalSurvival, p.comparisonPotential elapsed initial p.deadline
        ∂(independentExponentials (ι := ι))) +
      ∑ j, ∫ z in variableWinner p.service p.deadline j,
        p.comparisonJump elapsed initial j (cappedHit (p.service j) p.deadline (z j))
          ∂independentExponentials := by
    conv_lhs => rw [p.segment_measure_decomposition]
    rw [integral_add_measure hi.1 hi.2, integral_sum_measure hi.2, tsum_fintype]
    congr 1
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_survivalBox
        (fun i => p.service i p.deadline))] with z hz
      exact p.comparisonOutcome_terminal elapsed initial hz
    · apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (p.measurable_winner j)] with z hz
      exact p.comparisonOutcome_winner elapsed initial hz
  rw [he]
  exact p.comparison_actual_first_step elapsed initial

theorem comparisonOutcome_expected_lower_bound (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i)
    (hgap : ∀ t ∈ Icc 0 p.deadline, ∀ i,
      0 ≤ initial i + p.service i t + 1 - p.rate i t) :
    p.comparisonPotential elapsed initial 0 -
      (∫ t in (0 : ℝ)..p.deadline,
        survivalCurve (fun u i => p.service i u) t * Comparison.lossKernel (elapsed + t) *
          ∑ i, (initial i + p.service i t + 1 - p.rate i t)) ≤
      ∫ z, p.comparisonOutcome elapsed initial z ∂independentExponentials := by
  have h := p.comparison_first_step_lower_bound elapsed initial hT hx hgap
  have hd := p.comparisonOutcome_expected_drift elapsed initial hT hx
  rw [← p.comparison_first_step_identity elapsed initial] at hd
  linarith

end StochasticMatching.ServiceCurveFamily
