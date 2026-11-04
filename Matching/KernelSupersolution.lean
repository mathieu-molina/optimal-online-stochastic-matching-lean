import Matching.FiniteKernelIteration
import Matching.EmpiricalTailBound
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Bounded supersolutions control every finite kernel iterate and the
supremum of the expected rewards of those iterates. -/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace StochasticMatching
variable {H : Type*} [MeasurableSpace H]

theorem iterateKernel_integral_le (K : Kernel H H) [IsMarkovKernel K]
    (V : H → ℝ) (hV : Measurable V) (C : ℝ) (hbound : ∀ h, |V h| ≤ C)
    (hstep : ∀ h, (∫ h', V h' ∂K h) ≤ V h) (n : ℕ) (h : H) :
    (∫ h', V h' ∂iterateKernel K n h) ≤ V h := by
  have hi (n : ℕ) (h : H) : Integrable V (iterateKernel K n h) :=
    integrable_of_abs_bounded _ hV C hbound
  induction n with
  | zero =>
      change (∫ h', V h' ∂Measure.dirac h) ≤ V h
      rw [integral_dirac' V h hV.stronglyMeasurable]
  | succ n ih =>
      rw [iterateKernel_succ, Kernel.integral_comp (hi (n + 1) h)]
      apply le_trans _ ih
      exact integral_mono (hi (n + 1) h |>.integral_comp) (hi n h) hstep

noncomputable def kernelExpectedReward (K : Kernel H H) (R : H → ℝ) (h : H) : ℝ :=
  ⨆ n : ℕ, ∫ h', R h' ∂iterateKernel K n h

theorem kernelExpectedReward_le (K : Kernel H H) [IsMarkovKernel K]
    (V R : H → ℝ) (hV : Measurable V) (hR : Measurable R)
    (C D : ℝ) (hVbound : ∀ h, |V h| ≤ C) (hRbound : ∀ h, |R h| ≤ D)
    (hRV : ∀ h, R h ≤ V h)
    (hstep : ∀ h, (∫ h', V h' ∂K h) ≤ V h) (h : H) :
    kernelExpectedReward K R h ≤ V h := by
  apply ciSup_le
  intro n
  exact (integral_mono
    (integrable_of_abs_bounded _ hR D hRbound)
    (integrable_of_abs_bounded _ hV C hVbound) hRV).trans
      (iterateKernel_integral_le K V hV C hVbound hstep n h)

end StochasticMatching
