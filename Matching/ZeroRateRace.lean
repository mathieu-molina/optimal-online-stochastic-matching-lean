import Matching.RacePartition

/-! Constant-rate races allowing idle jobs. Division by zero is never used to
declare a winner: the winning coordinate is explicitly required to have a
positive rate. A zero-rate job cannot complete.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def servingWinner (r : ι → ℝ) (j : ι) : Set (ι → ℝ) :=
  {z | 0 < r j ∧ ∀ i, i ≠ j → r i * (z j / r j) < z i}

theorem zero_rate_never_wins {r : ι → ℝ} {j : ι} (hj : r j = 0) :
    servingWinner r j = ∅ := by simp [servingWinner, hj]

theorem measurableSet_servingWinner (r : ι → ℝ) (j : ι) :
    MeasurableSet (servingWinner r j) := by
  by_cases hj : 0 < r j
  · have hs : servingWinner r j = ⋂ i : {i : ι // i ≠ j},
        {z : ι → ℝ | r i.1 * (z j / r j) < z i.1} := by
      ext z
      simp [servingWinner, hj]
    rw [hs]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_lt _ (measurable_pi_apply i.1)
    fun_prop
  · simp [servingWinner, hj]

theorem servingWinner_disjoint (r : ι → ℝ) :
    Pairwise (fun i j => Disjoint (servingWinner r i) (servingWinner r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hji : z i / r i < z j / r j :=
    (lt_div_iff₀ hj.1).mpr (by simpa [mul_comm] using hi.2 j (Ne.symm hij))
  have hij' : z j / r j < z i / r i :=
    (lt_div_iff₀ hi.1).mpr (by simpa [mul_comm] using hj.2 i hij)
  exact lt_asymm hji hij'

theorem constantCandidateEvent_ae_servingWinner {r : ι → ℝ} (j : ι) (hj : 0 < r j) :
    constantCandidateEvent r j =ᵐ[independentExponentials] servingWinner r j := by
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  apply propext
  change (∀ i : {i : ι // i ≠ j}, r i.1 * max (z j / r j) 0 < z i.1) ↔
    0 < r j ∧ ∀ i, i ≠ j → r i * (z j / r j) < z i
  rw [max_eq_left (div_pos (hz j) hj).le]
  constructor
  · intro h
    exact ⟨hj, fun i hi => h ⟨i, hi⟩⟩
  · intro h i
    exact h.2 i.1 i.2

theorem nonnegative_first_completion_marked_law {r : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i) (j : ι) (hj : 0 < r j) :
    Measure.map (raceObservation r j)
      (independentExponentials.restrict (servingWinner r j)) =
      (volume.withDensity (markedTimeDensity r j)).prod
        (independentExponentials (ι := {i : ι // i ≠ j})) := by
  have hae : constantMarkedObservation r j =ᵐ[independentExponentials] raceObservation r j := by
    filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
    simp [constantMarkedObservation, residualObservation, candidateHistory,
      constantService, raceObservation, max_eq_left (div_pos (hz j) hj).le]
  have hm : Measure.map (constantMarkedObservation r j)
      (independentExponentials.restrict (servingWinner r j)) =
      Measure.map (raceObservation r j)
        (independentExponentials.restrict (servingWinner r j)) :=
    Measure.map_congr (ae_restrict_of_ae hae)
  rw [← hm, ← Measure.restrict_congr_set (constantCandidateEvent_ae_servingWinner j hj)]
  exact constant_rate_marked_law hr j hj

theorem servingWinner_probability {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (j : ι) :
    independentExponentials (servingWinner r j) = ENNReal.ofReal (r j / ∑ i, r i) := by
  by_cases hj : 0 < r j
  · have hR := total_rate_pos hr j hj
    letI := isProbabilityMeasureExponential hR
    have h := congrArg (fun μ : Measure (ℝ × ({i : ι // i ≠ j} → ℝ)) => μ univ)
      (nonnegative_first_completion_marked_law hr j hj)
    dsimp only at h
    rw [Measure.map_apply (measurable_raceObservation r j) MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      markedTimeMeasure_eq_scaled hr j hj, ← univ_prod_univ, Measure.prod_prod] at h
    simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using h
  · have hz : r j = 0 := le_antisymm (not_lt.mp hj) (hr j)
    simp [zero_rate_never_wins hz, hz]

theorem servingWinner_mass_sum {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hR : 0 < ∑ i, r i) : ∑ j, independentExponentials (servingWinner r j) = 1 := by
  simp_rw [servingWinner_probability hr]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hr i) hR.le),
    ← Finset.sum_div, div_self hR.ne', ENNReal.ofReal_one]

theorem nonnegative_first_completion_unique_ae {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hR : 0 < ∑ i, r i) :
    ∀ᵐ z ∂independentExponentials, ∃! j, z ∈ servingWinner r j := by
  have hunion : independentExponentials (⋃ j, servingWinner r j) = 1 := by
    rw [measure_iUnion (servingWinner_disjoint r) (measurableSet_servingWinner r),
      tsum_fintype, servingWinner_mass_sum hr hR]
  have hfull : ∀ᵐ z ∂independentExponentials, z ∈ ⋃ j, servingWinner r j := by
    rw [ae_iff]
    change independentExponentials (⋃ j, servingWinner r j)ᶜ = 0
    rw [measure_compl (MeasurableSet.iUnion (measurableSet_servingWinner r))
      (measure_ne_top _ _), measure_univ, hunion, tsub_self]
  filter_upwards [hfull] with z hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  refine ⟨j, hj, ?_⟩
  intro i hi
  by_contra hij
  exact Set.disjoint_left.mp (servingWinner_disjoint r hij) hi hj

end StochasticMatching
