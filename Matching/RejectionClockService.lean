import Matching.ServiceExecution
import Matching.OneStepLaw
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Add an independent rejection clock so that job completions and rejected
arrivals together have a constant total event rate. This is the one-step
uniformization construction used for the online matching coupling.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def withRejectionClock (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, (∑ i, p.rate i t) ≤ Λ) : ServiceCurveFamily (Option ι) where
  deadline := p.deadline
  deadline_pos := p.deadline_pos
  service j t := j.elim (Λ * t - ∑ i, p.service i t) (fun i => p.service i t)
  rate j t := j.elim (Λ - ∑ i, p.rate i t) (fun i => p.rate i t)
  service_continuous j := by
    cases j with
    | none => exact (continuous_const.mul continuous_id).sub (continuous_finset_sum _ (fun i _ => p.service_continuous i))
    | some i => exact p.service_continuous i
  rate_continuous j := by
    cases j with
    | none => exact continuous_const.sub (continuous_finset_sum _ (fun i _ => p.rate_continuous i))
    | some i => exact p.rate_continuous i
  service_monotone j := by
    cases j with
    | none =>
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 p.deadline)
          (((continuous_const.mul continuous_id).sub (continuous_finset_sum _ (fun i _ => p.service_continuous i))).continuousOn)
        · intro t ht
          have hd := ((hasDerivAt_id t).const_mul Λ).sub
            (HasDerivAt.sum (u := Finset.univ) (fun i _ => p.service_deriv i t (interior_subset ht)))
          simpa only [mul_one] using hd.hasDerivWithinAt
        · intro t ht
          exact sub_nonneg.mpr (hΛ t (interior_subset ht))
    | some i => exact p.service_monotone i
  service_zero j := by cases j <;> simp [p.service_zero]
  rate_nonneg j t ht := by
    cases j with
    | none => exact sub_nonneg.mpr (hΛ t ht)
    | some i => exact p.rate_nonneg i t ht
  service_deriv j t ht := by
    cases j with
    | none =>
        have hd := ((hasDerivAt_id t).const_mul Λ).sub
          (HasDerivAt.sum (u := Finset.univ) (fun i _ => p.service_deriv i t ht))
        simpa only [mul_one] using hd
    | some i => exact p.service_deriv i t ht

theorem withRejectionClock_total_service (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, (∑ i, p.rate i t) ≤ Λ) (t : ℝ) :
    (∑ j, (p.withRejectionClock Λ hΛ).service j t) = Λ * t := by
  rw [Fintype.sum_option]
  change (Λ * t - ∑ i, p.service i t) + (∑ i, p.service i t) = _
  ring

theorem withRejectionClock_total_rate (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, (∑ i, p.rate i t) ≤ Λ) (t : ℝ) :
    (∑ j, (p.withRejectionClock Λ hΛ).rate j t) = Λ := by
  rw [Fintype.sum_option]
  change (Λ - ∑ i, p.rate i t) + (∑ i, p.rate i t) = _
  ring

theorem withRejectionClock_survival (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, (∑ i, p.rate i t) ≤ Λ) {t : ℝ}
    (ht : t ∈ Icc 0 p.deadline) :
    (independentExponentials (ι := Option ι)).real
      (survivalBox (fun j => (p.withRejectionClock Λ hΛ).service j t)) = Real.exp (-Λ * t) := by
  rw [survivalBox_real (fun j => (p.withRejectionClock Λ hΛ).service_nonneg ht j),
    withRejectionClock_total_service]
  congr 1
  ring

theorem withRejectionClock_marked_density (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, (∑ i, p.rate i t) ≤ Λ) (j : Option ι) :
    variableMarkedTimeMeasure (p.withRejectionClock Λ hΛ).service
      (p.withRejectionClock Λ hΛ).rate p.deadline j =
      (volume.restrict (Icc 0 p.deadline)).withDensity
        (fun t => ENNReal.ofReal ((p.withRejectionClock Λ hΛ).rate j t * Real.exp (-Λ * t))) := by
  unfold variableMarkedTimeMeasure
  simp only [withRejectionClock_total_service, neg_mul]

theorem withRejectionClock_first_event_law (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, (∑ i, p.rate i t) ≤ Λ) (j : Option ι) :
    Measure.map (variableObservation (p.withRejectionClock Λ hΛ).service p.deadline j)
      (independentExponentials.restrict
        (variableWinner (p.withRejectionClock Λ hΛ).service p.deadline j)) =
      ((volume.restrict (Icc 0 p.deadline)).withDensity
        (fun t => ENNReal.ofReal ((p.withRejectionClock Λ hΛ).rate j t * Real.exp (-Λ * t)))).prod
        (independentExponentials (ι := {i : Option ι // i ≠ j})) := by
  let q := p.withRejectionClock Λ hΛ
  have h := variable_first_completion_marked_law q.service_continuous q.rate_continuous q.deadline_pos
    q.service_monotone q.service_zero q.rate_nonneg q.service_deriv j
  have hd : variableMarkedTimeMeasure q.service q.rate q.deadline j =
      (volume.restrict (Icc 0 p.deadline)).withDensity
        (fun t => ENNReal.ofReal (q.rate j t * Real.exp (-Λ * t))) :=
    p.withRejectionClock_marked_density Λ hΛ j
  rw [hd] at h
  exact h

end StochasticMatching.ServiceCurveFamily
