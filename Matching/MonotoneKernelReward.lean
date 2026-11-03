import Matching.KernelSupersolution
import Matching.MarkovTransitionSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

/-! For bounded increasing rewards, the supremum of the finite expected
rewards is the expectation of the actual limiting reward on the trajectory. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace StochasticMatching
variable {H : Type*} [MeasurableSpace H]

theorem markovTrajectory_reward_monotone (K : Kernel H H) [IsMarkovKernel K]
    (R : H → ℝ) (hR : Measurable R) (hstep : ∀ h, ∀ᵐ h' ∂K h, R h ≤ R h') (h : H) :
    ∀ᵐ z ∂markovTrajectory K h, Monotone (fun n => R (z n)) := by
  have hS : MeasurableSet {p : H × H | R p.1 ≤ R p.2} :=
    measurableSet_le (hR.comp measurable_fst) (hR.comp measurable_snd)
  filter_upwards [markovTrajectory_all_steps_support K _ hS hstep h] with z hz
  exact monotone_nat_of_le_succ hz

theorem kernelExpectedReward_eq_trajectory (K : Kernel H H) [IsMarkovKernel K]
    (R : H → ℝ) (hR : Measurable R) (C : ℝ) (hbound : ∀ h, |R h| ≤ C)
    (hstep : ∀ h, ∀ᵐ h' ∂K h, R h ≤ R h') (h : H) :
    kernelExpectedReward K R h =
      ∫ z, (⨆ n : ℕ, R (z n)) ∂markovTrajectory K h := by
  let μ := markovTrajectory K h
  have hm (n : ℕ) : Measurable (fun z : ℕ → H => R (z n)) := hR.comp (measurable_pi_apply n)
  have hi (n : ℕ) : Integrable (fun z : ℕ → H => R (z n)) μ :=
    integrable_of_abs_bounded _ (hm n) C (fun z => hbound (z n))
  have hb (z : ℕ → H) : BddAbove (range (fun n : ℕ => R (z n))) :=
    ⟨C, fun _ ⟨n, hn⟩ => hn ▸ (le_abs_self _).trans (hbound (z n))⟩
  have hmono := markovTrajectory_reward_monotone K R hR hstep h
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => C)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound (z n)))
    (hmono.mono (fun z hz => tendsto_atTop_ciSup hz (hb z)))
  have he (n : ℕ) : (∫ z, R (z n) ∂μ) = ∫ x, R x ∂iterateKernel K n h := by
    rw [← markovTrajectory_coordinate_law K h n,
      integral_map_of_stronglyMeasurable (measurable_pi_apply n) hR.stronglyMeasurable]
  have hEmono : Monotone (fun n => ∫ z, R (z n) ∂μ) := by
    intro n k hnk
    exact integral_mono_ae (hi n) (hi k) (hmono.mono (fun z hz => hz hnk))
  have hEb : BddAbove (range (fun n : ℕ => ∫ z, R (z n) ∂μ)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hle := integral_mono (hi n) (integrable_const C)
      (fun z : ℕ → H => (le_abs_self _).trans (hbound (z n)))
    simpa using hle
  have hlim := tendsto_nhds_unique (tendsto_atTop_ciSup hEmono hEb) ht
  simpa only [he, kernelExpectedReward] using hlim

end StochasticMatching
