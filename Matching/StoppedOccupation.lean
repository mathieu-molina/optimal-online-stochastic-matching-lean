import Matching.LossBudget
import Mathlib.MeasureTheory.Integral.Prod

/-! A weighted occupation identity for a bounded measurable stopping clock.
It is a direct Fubini calculation, with the joint integrability proved from the
integrable weight and the continuous time kernel on a compact interval.
-/

open MeasureTheory Set
namespace StochasticMatching

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_weighted_stopped_interval {D : ℝ} (hD : 0 ≤ D)
    (τ : Ω → ℝ) (hτ : Measurable τ) (hτbounds : ∀ ω, τ ω ∈ Icc 0 D)
    (f : Ω → ℝ) (hf : Integrable f μ) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ ω, f ω * (∫ t in (0 : ℝ)..τ ω, g t) ∂μ) =
      ∫ t in (0 : ℝ)..D, g t * (∫ ω in {ω | t < τ ω}, f ω ∂μ) := by
  let ν : Measure ℝ := volume.restrict (Icc 0 D)
  let F : ℝ → Ω → ℝ := fun t ω => if t < τ ω then g t * f ω else 0
  have hs : MeasurableSet {x : ℝ × Ω | x.1 < τ x.2} :=
    measurableSet_lt measurable_fst (hτ.comp measurable_snd)
  have hgi : Integrable g ν := hg.continuousOn.integrableOn_Icc
  have hFi : Integrable (Function.uncurry F) (ν.prod μ) :=
    (hgi.mul_prod hf).indicator hs
  have hleft : ∀ t, (∫ ω, F t ω ∂μ) = g t * (∫ ω in {ω | t < τ ω}, f ω ∂μ) := by
    intro t
    have he : F t = fun ω => g t * ({ω | t < τ ω}.indicator f ω) := by
      funext ω
      by_cases ht : t < τ ω <;> simp [F, ht]
    rw [he, integral_const_mul, integral_indicator (measurableSet_lt measurable_const hτ)]
  have hright : ∀ ω, (∫ t, F t ω ∂ν) = f ω * (∫ t in (0 : ℝ)..τ ω, g t) := by
    intro ω
    have hset : Iio (τ ω) ∩ Icc 0 D = Ico 0 (τ ω) := by
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨ht, ht0, _⟩
        exact ⟨ht0, ht⟩
      · rintro ⟨ht0, ht⟩
        exact ⟨ht, ht0, ht.le.trans (hτbounds ω).2⟩
    change (∫ t, (Iio (τ ω)).indicator (fun t => g t * f ω) t
      ∂volume.restrict (Icc 0 D)) = _
    rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      hset, integral_mul_const, ← integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hτbounds ω).1]
    ring
  have hswap := integral_integral_swap hFi
  change (∫ t, ∫ ω, F t ω ∂μ ∂ν) = ∫ ω, ∫ t, F t ω ∂ν ∂μ at hswap
  simp_rw [hleft, hright] at hswap
  rw [intervalIntegral.integral_of_le hD, ← integral_Icc_eq_integral_Ioc]
  exact hswap.symm

namespace Comparison

theorem integral_lossKernel_shift (elapsed T : ℝ) :
    (∫ t in (0 : ℝ)..T, lossKernel (elapsed + t)) =
      continuation elapsed 0 - continuation (elapsed + T) 0 := by
  have hd : ∀ t ∈ uIcc 0 T,
      HasDerivAt (fun u => -continuation (elapsed + u) 0) (lossKernel (elapsed + t)) t := by
    intro t _
    have h := ((hasDerivAt_time (elapsed + t) 0).comp t
      ((hasDerivAt_id t).const_add elapsed)).neg
    simpa only [Function.comp_def, mul_one, lossKernel] using h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_lossKernel.comp (continuous_const.add continuous_id)).intervalIntegrable 0 T)
  simpa only [add_zero, neg_sub_neg] using hi

end Comparison
end StochasticMatching
