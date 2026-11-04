import Matching.PosteriorGap
import Matching.ServiceExecution
import Matching.ComparisonPotential
import Matching.FirstStepIdentity

/-! Differentiate the comparison potential along actual service curves and
identify its marked-completion jumps. No stochastic generator is assumed.
-/

open MeasureTheory Set
open scoped BigOperators

namespace StochasticMatching

namespace Comparison

theorem hasDerivAt_comp {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun u => continuation (a u) (b u))
      (timeDerivative (a t) (b t) * a' + workDerivative (a t) (b t) * b') t := by
  have he := (((hasDerivAt_const t (1 : ℝ)).sub ha).exp.sub_const 1)
  have hi := ((hb.add_const 1).mul he).neg.exp
  convert (hasDerivAt_const t (1 : ℝ)).sub hi using 1
  dsimp [continuation, timeDerivative, workDerivative, sensitivity]
  ring

end Comparison

namespace ServiceCurveFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

noncomputable def comparisonPotential (elapsed : ℝ) (initial : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Comparison.continuation (elapsed + t) (initial i + p.service i t)

noncomputable def comparisonDerivative (elapsed : ℝ) (initial : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (Comparison.timeDerivative (elapsed + t) (initial i + p.service i t) +
    Comparison.workDerivative (elapsed + t) (initial i + p.service i t) * p.rate i t)

noncomputable def comparisonJump (elapsed : ℝ) (initial : ι → ℝ) (j : ι) (t : ℝ) : ℝ :=
  1 + ∑ i : {i : ι // i ≠ j}, Comparison.continuation (elapsed + t) (initial i.1 + p.service i.1 t)

theorem continuous_comparisonPotential (elapsed : ℝ) (initial : ι → ℝ) :
    Continuous (p.comparisonPotential elapsed initial) := by
  unfold comparisonPotential Comparison.continuation
  apply continuous_finset_sum
  intro i _
  have hs := p.service_continuous i
  fun_prop

theorem continuous_comparisonDerivative (elapsed : ℝ) (initial : ι → ℝ) :
    Continuous (p.comparisonDerivative elapsed initial) := by
  unfold comparisonDerivative Comparison.timeDerivative Comparison.workDerivative Comparison.sensitivity
  apply continuous_finset_sum
  intro i _
  have hs := p.service_continuous i
  have hr := p.rate_continuous i
  fun_prop

theorem continuous_comparisonJump (elapsed : ℝ) (initial : ι → ℝ) (j : ι) :
    Continuous (p.comparisonJump elapsed initial j) := by
  unfold comparisonJump Comparison.continuation
  apply continuous_const.add
  apply continuous_finset_sum
  intro i _
  have hs := p.service_continuous i.1
  fun_prop

theorem hasDerivAt_comparisonPotential (elapsed : ℝ) (initial : ι → ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 p.deadline) :
    HasDerivAt (p.comparisonPotential elapsed initial) (p.comparisonDerivative elapsed initial t) t := by
  unfold comparisonPotential comparisonDerivative
  apply HasDerivAt.sum
  intro i _
  have h := Comparison.hasDerivAt_comp ((hasDerivAt_id t).const_add elapsed)
    ((p.service_deriv i t ht).const_add (initial i))
  simpa only [mul_one] using h

theorem comparisonJump_sub (elapsed : ℝ) (initial : ι → ℝ) (j : ι) (t : ℝ) :
    p.comparisonJump elapsed initial j t - p.comparisonPotential elapsed initial t =
      1 - Comparison.continuation (elapsed + t) (initial j + p.service j t) := by
  let f := fun i => Comparison.continuation (elapsed + t) (initial i + p.service i t)
  have hs : (∑ i : {i : ι // i ≠ j}, f i.1) = ∑ i ∈ Finset.univ.erase j, f i :=
    (Finset.sum_subtype (Finset.univ.erase j) (by simp) f).symm
  have h := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ j)
  change 1 + (∑ i : {i : ι // i ≠ j}, f i.1) - ∑ i, f i = 1 - f j
  rw [hs]
  linarith

theorem comparison_drift (elapsed : ℝ) (initial : ι → ℝ) (t : ℝ) :
    p.comparisonDerivative elapsed initial t +
      ∑ j, p.rate j t * (p.comparisonJump elapsed initial j t - p.comparisonPotential elapsed initial t) =
      ∑ j, -(initial j + p.service j t + 1 - p.rate j t) *
        Comparison.sensitivity (elapsed + t) (initial j + p.service j t) := by
  simp_rw [p.comparisonJump_sub]
  unfold comparisonDerivative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := Comparison.generator_factor (elapsed + t) (initial j + p.service j t) (p.rate j t)
  convert h using 1 <;> ring

theorem comparison_first_step_identity (elapsed : ℝ) (initial : ι → ℝ) :
    survivalCurve (fun t i => p.service i t) p.deadline * p.comparisonPotential elapsed initial p.deadline +
      (∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u i => p.service i u) t *
        ∑ j, p.rate j t * p.comparisonJump elapsed initial j t) -
      p.comparisonPotential elapsed initial 0 =
      ∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u i => p.service i u) t *
        ∑ j, -(initial j + p.service j t + 1 - p.rate j t) *
          Comparison.sensitivity (elapsed + t) (initial j + p.service j t) := by
  have hs := p.service_continuous
  have h := first_step_identity_finite p.deadline
    (survivalCurve (fun t i => p.service i t)) (p.comparisonPotential elapsed initial)
    (p.comparisonDerivative elapsed initial) p.rate (p.comparisonJump elapsed initial)
    (by unfold survivalCurve; fun_prop) (p.continuous_comparisonPotential elapsed initial)
    (p.continuous_comparisonDerivative elapsed initial) p.rate_continuous
    (p.continuous_comparisonJump elapsed initial) (survivalCurve_initial p.service_zero)
    (fun t ht => hasDerivAt_survivalCurve (fun i => p.service_deriv i t
      (by simpa only [uIcc_of_le p.deadline_pos.le] using ht)))
    (fun t ht => p.hasDerivAt_comparisonPotential elapsed initial
      (by simpa only [uIcc_of_le p.deadline_pos.le] using ht))
  simpa only [p.comparison_drift] using h

end ServiceCurveFamily
end StochasticMatching
