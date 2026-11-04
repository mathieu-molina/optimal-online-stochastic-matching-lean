import Matching.CoordinateComparison
import Matching.ComparisonOutcome

/-! The actual one-step comparison reward for a tagged job. A completion of
another job retains the tagged potential, while its own completion pays one.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

noncomputable def coordinateOutcome (elapsed : ℝ) (initial : ι → ℝ) (i : ι) (z : ι → ℝ) : ℝ :=
  branchSelect (variableWinner p.service p.deadline)
    (fun j z => p.coordinateJump elapsed initial i j (cappedHit (p.service j) p.deadline (z j)))
    (fun _ => p.coordinatePotential elapsed initial i p.deadline) z

theorem measurable_coordinateOutcome (elapsed : ℝ) (initial : ι → ℝ) (i : ι) :
    Measurable (p.coordinateOutcome elapsed initial i) :=
  measurable_branchSelect p.winner_disjoint p.measurable_winner
    (fun j => (p.continuous_coordinateJump elapsed initial i j).measurable.comp (p.measurable_clock j))
    measurable_const

theorem coordinateOutcome_winner (elapsed : ℝ) (initial : ι → ℝ) (i : ι) {z : ι → ℝ} {j : ι}
    (hz : z ∈ variableWinner p.service p.deadline j) :
    p.coordinateOutcome elapsed initial i z =
      p.coordinateJump elapsed initial i j (cappedHit (p.service j) p.deadline (z j)) :=
  branchSelect_of_mem p.winner_disjoint _ _ hz

theorem coordinateOutcome_terminal (elapsed : ℝ) (initial : ι → ℝ) (i : ι) {z : ι → ℝ}
    (hz : z ∈ p.terminalSurvival) :
    p.coordinateOutcome elapsed initial i z = p.coordinatePotential elapsed initial i p.deadline := by
  apply branchSelect_of_not_mem
  intro j hj
  exact p.winner_subset_completion j hj hz

theorem coordinatePotential_bounds (elapsed : ℝ) (initial : ι → ℝ) (i : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i)
    {t : ℝ} (ht : t ∈ Icc 0 p.deadline) :
    0 ≤ p.coordinatePotential elapsed initial i t ∧
      p.coordinatePotential elapsed initial i t ≤ 1 :=
  ⟨Comparison.continuation_nonneg (by linarith [ht.2])
    (add_nonneg hx (p.service_nonneg ht i)), (Comparison.continuation_lt_one _ _).le⟩

theorem coordinateJump_bounds (elapsed : ℝ) (initial : ι → ℝ) (i j : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i)
    {t : ℝ} (ht : t ∈ Icc 0 p.deadline) :
    0 ≤ p.coordinateJump elapsed initial i j t ∧ p.coordinateJump elapsed initial i j t ≤ 1 := by
  unfold coordinateJump
  split_ifs
  · exact ⟨zero_le_one, le_refl _⟩
  · exact p.coordinatePotential_bounds elapsed initial i hT hx ht

theorem coordinateOutcome_bounds (elapsed : ℝ) (initial : ι → ℝ) (i : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i) (z : ι → ℝ) :
    0 ≤ p.coordinateOutcome elapsed initial i z ∧ p.coordinateOutcome elapsed initial i z ≤ 1 := by
  classical
  by_cases hw : ∃ j, z ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hw
    rw [p.coordinateOutcome_winner elapsed initial i hj]
    exact p.coordinateJump_bounds elapsed initial i j hT hx
      (cappedHit_bounds (p.service_continuous j) p.deadline_pos.le)
  · unfold coordinateOutcome
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    exact p.coordinatePotential_bounds elapsed initial i hT hx ⟨p.deadline_pos.le, le_refl _⟩

theorem integrable_coordinateOutcome (elapsed : ℝ) (initial : ι → ℝ) (i : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i) :
    Integrable (p.coordinateOutcome elapsed initial i) independentExponentials := by
  apply (integrable_const (1 : ℝ)).mono'
    (p.measurable_coordinateOutcome elapsed initial i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (p.coordinateOutcome_bounds elapsed initial i hT hx z).1]
  exact (p.coordinateOutcome_bounds elapsed initial i hT hx z).2

theorem coordinateOutcome_expected_payoff (elapsed : ℝ) (initial : ι → ℝ) (i : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i) :
    (∫ z, p.coordinateOutcome elapsed initial i z ∂independentExponentials) =
      (∫ _ in p.terminalSurvival, p.coordinatePotential elapsed initial i p.deadline
        ∂(independentExponentials (ι := ι))) +
      ∑ j, ∫ z in variableWinner p.service p.deadline j,
        p.coordinateJump elapsed initial i j (cappedHit (p.service j) p.deadline (z j))
          ∂independentExponentials := by
  have hi := p.integrable_coordinateOutcome elapsed initial i hT hx
  rw [p.segment_measure_decomposition, integrable_add_measure] at hi
  conv_lhs => rw [p.segment_measure_decomposition]
  rw [integral_add_measure hi.1 hi.2, integral_sum_measure hi.2, tsum_fintype]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_survivalBox
      (fun j => p.service j p.deadline))] with z hz
    exact p.coordinateOutcome_terminal elapsed initial i hz
  · apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (p.measurable_winner j)] with z hz
    exact p.coordinateOutcome_winner elapsed initial i hz

theorem coordinateOutcome_expected_lower_bound (elapsed : ℝ) (initial : ι → ℝ) (i : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i)
    (hgap : ∀ t ∈ Icc 0 p.deadline, 0 ≤ initial i + p.service i t + 1 - p.rate i t) :
    p.coordinatePotential elapsed initial i 0 -
      (∫ t in (0 : ℝ)..p.deadline,
        survivalCurve (fun u j => p.service j u) t * Comparison.lossKernel (elapsed + t) *
          (initial i + p.service i t + 1 - p.rate i t)) ≤
      ∫ z, p.coordinateOutcome elapsed initial i z ∂independentExponentials := by
  rw [p.coordinateOutcome_expected_payoff elapsed initial i hT hx]
  exact p.coordinate_first_step_lower_bound elapsed initial i hT hx hgap

end StochasticMatching.ServiceCurveFamily
