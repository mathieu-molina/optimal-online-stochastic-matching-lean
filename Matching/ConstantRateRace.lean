import Matching.MarkedResidual
import Matching.ExponentialScaling
import Matching.SurvivalCurve
import Matching.InitialState

/-! The marked first-completion law for nonnegative constant rates.
For a fixed candidate with positive rate, the time measure has density
`r j * exp (-(sum r) * t)` on the nonnegative half-line, and the other residual
demands form an independent vector of unit exponentials.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def constantService (r : ι → ℝ) (t : ℝ) (i : ι) : ℝ := r i * max t 0

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_constantService (r : ι → ℝ) : Measurable (constantService r) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul (measurable_id.max measurable_const)

omit [Fintype ι] [DecidableEq ι] in
theorem constantService_nonneg {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (t : ℝ) (i : ι) :
    0 ≤ constantService r t i := mul_nonneg (hr i) (le_max_right _ _)

noncomputable def markedTimeDensity (r : ι → ℝ) (j : ι) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if 0 ≤ t then r j * Real.exp (-(∑ i, r i) * t) else 0)

theorem measurable_markedTimeDensity (r : ι → ℝ) (j : ι) :
    Measurable (markedTimeDensity r j) := by
  unfold markedTimeDensity
  apply Measurable.ennreal_ofReal
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (by fun_prop) measurable_const

theorem constant_candidate_density {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (j : ι) :
    (expMeasure (r j)).withDensity
      (fun t => independentExponentials
        (survivalBox (fun i : {i : ι // i ≠ j} => constantService r t i.1))) =
      volume.withDensity (markedTimeDensity r j) := by
  classical
  let a : ℝ → {i : ι // i ≠ j} → ℝ := fun t i => constantService r t i.1
  have ha : Measurable a := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).comp (measurable_constantService r)
  have ha0 : ∀ t i, 0 ≤ a t i := fun t i => constantService_nonneg hr t i.1
  have hpdf : Measurable (exponentialPDF (r j)) :=
    (measurable_exponentialPDFReal (r j)).ennreal_ofReal
  change (expMeasure (r j)).withDensity (fun t => independentExponentials (survivalBox (a t))) = _
  rw [expMeasure_eq_withDensity, ← withDensity_mul volume hpdf
    (measurable_survival_weight ha ha0)]
  congr 1
  funext t
  change exponentialPDF (r j) t * independentExponentials (survivalBox (a t)) = _
  rw [exponentialPDF_eq, survivalBox_measure_exp_sum (ha0 t)]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, ← ENNReal.ofReal_mul (mul_nonneg (hr j) (Real.exp_pos _).le)]
    unfold markedTimeDensity
    rw [if_pos ht]
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    have hsum := Fintype.sum_subtype_add_sum_subtype
      (fun i : ι => i = j) r
    have hs : r j + ∑ i : {i : ι // i ≠ j}, r i.1 = ∑ i, r i := by
      simpa using hsum
    simp only [a, constantService, max_eq_left ht, ← Finset.sum_mul]
    rw [← hs]
    ring
  · simp [ht, markedTimeDensity]

def constantCandidateEvent (r : ι → ℝ) (j : ι) : Set (ι → ℝ) :=
  candidateHistory j (fun z => z / r j) ⁻¹'
    historySurvival (fun t (i : {i : ι // i ≠ j}) => constantService r t i.1)

noncomputable def constantMarkedObservation (r : ι → ℝ) (j : ι) :
    (ι → ℝ) → ℝ × ({i : ι // i ≠ j} → ℝ) :=
  residualObservation (fun t (i : {i : ι // i ≠ j}) => constantService r t i.1) ∘
    candidateHistory j (fun z => z / r j)

theorem constant_rate_marked_law {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (j : ι) (hj : 0 < r j) :
    Measure.map (constantMarkedObservation r j)
      (independentExponentials.restrict (constantCandidateEvent r j)) =
      (volume.withDensity (markedTimeDensity r j)).prod
        (independentExponentials (ι := {i : ι // i ≠ j})) := by
  have ha : Measurable (fun t (i : {i : ι // i ≠ j}) => constantService r t i.1) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).comp (measurable_constantService r)
  have ht : Measurable (fun z : ℝ => z / r j) := measurable_id.div_const (r j)
  have h := candidate_completion_factorization j ht ha
    (fun t i => constantService_nonneg hr t i.1)
  rw [scaled_unitExponential hj, constant_candidate_density hr j] at h
  exact h

def strictWinner (r : ι → ℝ) (j : ι) : Set (ι → ℝ) :=
  {z | ∀ i, i ≠ j → z j / r j < z i / r i}

noncomputable def raceObservation (r : ι → ℝ) (j : ι) (z : ι → ℝ) :
    ℝ × ({i : ι // i ≠ j} → ℝ) :=
  (z j / r j, fun i => z i.1 - r i.1 * (z j / r j))

theorem measurable_raceObservation (r : ι → ℝ) (j : ι) :
    Measurable (raceObservation r j) := by
  unfold raceObservation
  have ht : Measurable (fun z : ι → ℝ => z j / r j) := by fun_prop
  apply Measurable.prodMk ht
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.1).sub
    (measurable_const.mul ht)

theorem measurableSet_strictWinner (r : ι → ℝ) (j : ι) :
    MeasurableSet (strictWinner r j) := by
  have hs : strictWinner r j =
      ⋂ i : {i : ι // i ≠ j}, {z : ι → ℝ | z j / r j < z i.1 / r i.1} := by
    ext z
    simp [strictWinner]
  rw [hs]
  apply MeasurableSet.iInter
  intro i
  have hj : Measurable (fun z : ι → ℝ => z j / r j) := by fun_prop
  have hi : Measurable (fun z : ι → ℝ => z i.1 / r i.1) := by fun_prop
  exact measurableSet_lt hj hi

theorem constantCandidateEvent_ae_strictWinner {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (j : ι) :
    constantCandidateEvent r j =ᵐ[independentExponentials] strictWinner r j := by
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  apply propext
  change (∀ i : {i : ι // i ≠ j}, r i.1 * max (z j / r j) 0 < z i.1) ↔
    ∀ i, i ≠ j → z j / r j < z i / r i
  rw [max_eq_left (div_pos (hz j) (hr j)).le]
  constructor
  · intro h i hi
    exact (lt_div_iff₀ (hr i)).mpr (by simpa [mul_comm] using h ⟨i, hi⟩)
  · intro h i
    simpa [mul_comm] using (lt_div_iff₀ (hr i.1)).mp (h i.1 i.2)

theorem constantMarkedObservation_ae {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (j : ι) :
    constantMarkedObservation r j =ᵐ[independentExponentials] raceObservation r j := by
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  simp [constantMarkedObservation, residualObservation, candidateHistory,
    constantService, raceObservation, max_eq_left (div_pos (hz j) (hr j)).le]

/-- The actual strictly earliest job, its time, and all other residual demands. -/
theorem first_completion_marked_law {r : ι → ℝ} (hr : ∀ i, 0 < r i) (j : ι) :
    Measure.map (raceObservation r j)
      (independentExponentials.restrict (strictWinner r j)) =
      (volume.withDensity (markedTimeDensity r j)).prod
        (independentExponentials (ι := {i : ι // i ≠ j})) := by
  have hm : Measure.map (constantMarkedObservation r j)
      (independentExponentials.restrict (strictWinner r j)) =
      Measure.map (raceObservation r j)
        (independentExponentials.restrict (strictWinner r j)) :=
    Measure.map_congr (ae_restrict_of_ae (constantMarkedObservation_ae hr j))
  rw [← hm, ← Measure.restrict_congr_set (constantCandidateEvent_ae_strictWinner hr j)]
  exact constant_rate_marked_law (fun i => (hr i).le) j (hr j)

theorem total_rate_pos {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (j : ι) (hj : 0 < r j) :
    0 < ∑ i, r i := by
  exact lt_of_lt_of_le hj (Finset.single_le_sum (fun i _ => hr i) (Finset.mem_univ j))

theorem markedTimeDensity_eq_scaled {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (j : ι) (hj : 0 < r j) :
    markedTimeDensity r j =
      ENNReal.ofReal (r j / ∑ i, r i) • exponentialPDF (∑ i, r i) := by
  have hR := total_rate_pos hr j hj
  funext t
  simp only [markedTimeDensity, Pi.smul_apply, smul_eq_mul, exponentialPDF_eq]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, ← ENNReal.ofReal_mul (div_nonneg (hr j) hR.le)]
    congr 1
    field_simp
    <;> ring
  · simp [ht]

theorem markedTimeMeasure_eq_scaled {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (j : ι) (hj : 0 < r j) :
    volume.withDensity (markedTimeDensity r j) =
      ENNReal.ofReal (r j / ∑ i, r i) • expMeasure (∑ i, r i) := by
  have hpdf : Measurable (exponentialPDF (∑ i, r i)) :=
    (measurable_exponentialPDFReal _).ennreal_ofReal
  rw [markedTimeDensity_eq_scaled hr j hj, withDensity_smul
    _ hpdf, expMeasure_eq_withDensity]

theorem strictWinner_probability {r : ι → ℝ} (hr : ∀ i, 0 < r i) (j : ι) :
    independentExponentials (strictWinner r j) = ENNReal.ofReal (r j / ∑ i, r i) := by
  have hR := total_rate_pos (fun i => (hr i).le) j (hr j)
  letI := isProbabilityMeasureExponential hR
  have h := congrArg (fun μ : Measure (ℝ × ({i : ι // i ≠ j} → ℝ)) => μ univ)
    (first_completion_marked_law hr j)
  dsimp only at h
  rw [Measure.map_apply (measurable_raceObservation r j) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    markedTimeMeasure_eq_scaled (fun i => (hr i).le) j (hr j),
    ← univ_prod_univ, Measure.prod_prod] at h
  simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using h

/-- Expected marked rewards, with the surviving demand vector integrated out. -/
theorem first_completion_reward_lintegral {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (j : ι) (f : ℝ × ({i : ι // i ≠ j} → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in strictWinner r j, f (raceObservation r j z) ∂independentExponentials) =
      ∫⁻ t, markedTimeDensity r j t *
        (∫⁻ y, f (t, y) ∂independentExponentials) ∂volume := by
  rw [← lintegral_map hf (measurable_raceObservation r j),
    first_completion_marked_law hr j, lintegral_prod _ hf.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_markedTimeDensity r j) hf.lintegral_prod_right']
  rfl

end StochasticMatching
