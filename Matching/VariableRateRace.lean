import Matching.HittingDensity
import Matching.MarkedResidual
import Matching.SurvivalCurve

/-! Marked first-completion law before a deadline for continuous nonnegative
time-varying rates. Flat service intervals and idle jobs are permitted. The
rates/service curves are fixed for a given segment; constructing the adaptive
posterior flow and integrating over its histories remain separate tasks.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

def clampTime (T t : ℝ) : ℝ := max 0 (min t T)

theorem clampTime_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTime T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem clampTime_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : clampTime T t = t := by
  simp [clampTime, min_eq_left ht.2, max_eq_right ht.1]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def boundedService (a : ι → ℝ → ℝ) (T t : ℝ) (i : ι) : ℝ := a i (clampTime T t)

theorem measurable_boundedService {a : ι → ℝ → ℝ} (ha : ∀ i, Continuous (a i)) (T : ℝ) :
    Measurable (boundedService a T) := by
  apply measurable_pi_lambda
  intro i
  exact (ha i).measurable.comp
    (measurable_const.max (measurable_id.min measurable_const))

theorem boundedService_nonneg {a : ι → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hm : ∀ i, MonotoneOn (a i) (Icc 0 T)) (ha0 : ∀ i, a i 0 = 0) (t : ℝ) (i : ι) :
    0 ≤ boundedService a T t i := by
  change 0 ≤ a i (clampTime T t)
  rw [← ha0 i]
  exact hm i ⟨le_refl _, hT⟩ (clampTime_mem hT t) (clampTime_mem hT t).1

noncomputable def variableMarkedTimeMeasure (a r : ι → ℝ → ℝ) (T : ℝ) (j : ι) : Measure ℝ :=
  (volume.restrict (Icc 0 T)).withDensity
    (fun t => ENNReal.ofReal (r j t * Real.exp (-(∑ i, a i t))))

theorem variable_candidate_time_density {a r : ι → ℝ → ℝ}
    (ha : ∀ i, Continuous (a i)) (hr : ∀ i, Continuous (r i))
    {T : ℝ} (hT : 0 < T) (hm : ∀ i, MonotoneOn (a i) (Icc 0 T))
    (ha0 : ∀ i, a i 0 = 0) (hr0 : ∀ i t, t ∈ Icc 0 T → 0 ≤ r i t)
    (hd : ∀ i t, t ∈ Icc 0 T → HasDerivAt (a i) (r i t) t) (j : ι) :
    ((Measure.map (cappedHit (a j) T) unitExponential).withDensity
      (fun t => independentExponentials
        (survivalBox (fun i : {i : ι // i ≠ j} => boundedService a T t i.1)))).restrict (Iio T) =
      variableMarkedTimeMeasure a r T j := by
  classical
  let b : ℝ → {i : ι // i ≠ j} → ℝ := fun t i => boundedService a T t i.1
  have hb : Measurable b := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).comp (measurable_boundedService ha T)
  have hb0 : ∀ t i, 0 ≤ b t i := fun t i => boundedService_nonneg hT.le hm ha0 t i.1
  have hpdf : Measurable (fun t => ENNReal.ofReal (r j t * Real.exp (-a j t))) := by
    have haj := ha j
    have hrj := hr j
    fun_prop
  rw [restrict_withDensity measurableSet_Iio]
  change (completionTimeLaw (a j) T).withDensity
    (fun t => independentExponentials (survivalBox (b t))) = _
  rw [completionTimeLaw_eq_density (ha j) (hr j) hT (hm j) (ha0 j) (hr0 j) (hd j),
    serviceDensityMeasure, ← withDensity_mul (volume.restrict (Icc 0 T)) hpdf
      (measurable_survival_weight hb hb0)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ENNReal.ofReal (r j t * Real.exp (-a j t)) *
      independentExponentials (survivalBox (b t)) = _
  rw [survivalBox_measure_exp_sum (hb0 t),
    ← ENNReal.ofReal_mul (mul_nonneg (hr0 j t ht) (Real.exp_pos _).le)]
  change ENNReal.ofReal (r j t * Real.exp (-a j t) * Real.exp (-(∑ i, b t i))) =
    ENNReal.ofReal (r j t * Real.exp (-(∑ i, a i t)))
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  have hs : a j t + ∑ i : {i : ι // i ≠ j}, a i.1 t = ∑ i, a i t := by
    simpa using Fintype.sum_subtype_add_sum_subtype (fun i : ι => i = j) (fun i => a i t)
  simp only [b, boundedService, clampTime_eq ht]
  rw [← hs]
  ring

def variableWinner (a : ι → ℝ → ℝ) (T : ℝ) (j : ι) : Set (ι → ℝ) :=
  {z | cappedHit (a j) T (z j) < T ∧
    ∀ i, i ≠ j → cappedHit (a j) T (z j) < cappedHit (a i) T (z i)}

noncomputable def variableObservation (a : ι → ℝ → ℝ) (T : ℝ) (j : ι) (z : ι → ℝ) :
    ℝ × ({i : ι // i ≠ j} → ℝ) :=
  (cappedHit (a j) T (z j), fun i => z i.1 - a i.1 (cappedHit (a j) T (z j)))

/-- The time and all surviving residual demands of a specified first job.
The density includes the sum of all jobs' cumulative service, even if some
rates vanish on nontrivial intervals. -/
theorem variable_first_completion_marked_law {a r : ι → ℝ → ℝ}
    (ha : ∀ i, Continuous (a i)) (hr : ∀ i, Continuous (r i))
    {T : ℝ} (hT : 0 < T) (hm : ∀ i, MonotoneOn (a i) (Icc 0 T))
    (ha0 : ∀ i, a i 0 = 0) (hr0 : ∀ i t, t ∈ Icc 0 T → 0 ≤ r i t)
    (hd : ∀ i t, t ∈ Icc 0 T → HasDerivAt (a i) (r i t) t) (j : ι) :
    Measure.map (variableObservation a T j)
      (independentExponentials.restrict (variableWinner a T j)) =
      (variableMarkedTimeMeasure a r T j).prod
        (independentExponentials (ι := {i : ι // i ≠ j})) := by
  let τ := cappedHit (a j) T
  let b : ℝ → {i : ι // i ≠ j} → ℝ := fun t i => boundedService a T t i.1
  have hτ : Measurable τ := measurable_cappedHit (ha j) hT.le (hm j)
  have hb : Measurable b := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).comp (measurable_boundedService ha T)
  have hb0 : ∀ t i, 0 ≤ b t i := fun t i => boundedService_nonneg hT.le hm ha0 t i.1
  have hobs : Measurable (residualObservation b ∘ candidateHistory j τ) :=
    (measurable_residualObservation hb).comp (measurable_candidateHistory j hτ)
  have hcut := congrArg
    (fun μ : Measure (ℝ × ({i : ι // i ≠ j} → ℝ)) => μ.restrict (Iio T ×ˢ univ))
    (candidate_completion_factorization j hτ hb hb0)
  dsimp only at hcut
  rw [Measure.restrict_map hobs (measurableSet_Iio.prod MeasurableSet.univ),
    Measure.restrict_restrict (hobs (measurableSet_Iio.prod MeasurableSet.univ)),
    ← Measure.restrict_prod_eq_prod_univ,
    variable_candidate_time_density ha hr hT hm ha0 hr0 hd j] at hcut
  have hfun : residualObservation b ∘ candidateHistory j τ = variableObservation a T j := by
    funext z
    simp [residualObservation, candidateHistory, variableObservation, b, boundedService, τ,
      clampTime_eq (cappedHit_bounds (z := z j) (ha j) hT.le)]
  have hset : (residualObservation b ∘ candidateHistory j τ) ⁻¹' (Iio T ×ˢ univ) ∩
        candidateHistory j τ ⁻¹' historySurvival b = variableWinner a T j := by
    ext z
    have hz0 := (cappedHit_bounds (z := z j) (ha j) hT.le).1
    have hzt := clampTime_eq (cappedHit_bounds (z := z j) (ha j) hT.le)
    change ((τ (z j) < T ∧ True) ∧ ∀ i : {i : ι // i ≠ j},
      a i.1 (clampTime T (τ (z j))) < z i.1) ↔
      τ (z j) < T ∧ ∀ i, i ≠ j → τ (z j) < cappedHit (a i) T (z i)
    change clampTime T (τ (z j)) = τ (z j) at hzt
    rw [hzt]
    constructor
    · rintro ⟨⟨hzT, _⟩, hz⟩
      refine ⟨hzT, ?_⟩
      intro i hi
      exact lt_of_not_ge (fun hle => (not_le.mpr (hz ⟨i, hi⟩))
        ((cappedHit_le_iff (ha i) hT.le (hm i) hz0 hzT).mp hle))
    · rintro ⟨hzT, hz⟩
      refine ⟨⟨hzT, trivial⟩, ?_⟩
      intro i
      exact lt_of_not_ge (fun hle => (not_le.mpr (hz i.1 i.2))
        ((cappedHit_le_iff (ha i.1) hT.le (hm i.1) hz0 hzT).mpr hle))
  rw [hset, hfun] at hcut
  exact hcut

end StochasticMatching
