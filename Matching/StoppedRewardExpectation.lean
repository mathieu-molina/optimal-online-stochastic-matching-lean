import Matching.MonotoneKernelReward
import Matching.StoppedOutput

/-! The expected reward at an almost-sure finite absorbing time is bounded
by the supremum of finite-step expected rewards. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace StochasticMatching
variable {H : Type*} [MeasurableSpace H]

theorem expected_stopped_reward_le (K : Kernel H H) [IsMarkovKernel K]
    (S : Set H) (hS : MeasurableSet S) (habs : ∀ h ∈ S, K h = Measure.dirac h)
    (R : H → ℝ) (hR : Measurable R) (C : ℝ) (hb : ∀ h, |R h| ≤ C) (h : H)
    (hterm : ∀ᵐ z ∂markovTrajectory K h, ∃ n, z n ∈ S) :
    (∫ z, stoppedOutput S R z ∂markovTrajectory K h) ≤ kernelExpectedReward K R h := by
  let rel : Set (H × H) := {p | p.1 ∈ S → p.2 ∈ S ∧ R p.2 = R p.1}
  have hm : MeasurableSet rel := ((hS.preimage measurable_fst).mem.imp
    ((hS.preimage measurable_snd).mem.and
      (measurableSet_eq_fun (hR.comp measurable_snd) (hR.comp measurable_fst)).mem)).setOf
  have hs : ∀ a, ∀ᵐ b ∂K a, (a, b) ∈ rel := by
    intro a
    by_cases ha : a ∈ S
    · rw [habs a ha]
      apply (ae_dirac_iff (hm.preimage (measurable_const.prodMk measurable_id))).mpr
      exact fun _ => ⟨ha, rfl⟩
    · exact Eventually.of_forall (fun _ hx => False.elim (ha hx))
  have hl : ∀ᵐ z ∂markovTrajectory K h,
      Tendsto (fun n => R (z n)) atTop (𝓝 (stoppedOutput S R z)) := by
    filter_upwards [hterm, markovTrajectory_all_steps_support K rel hm hs h] with z hz hzstep
    let m := firstEntryTime S z
    have hmS : z m ∈ S := firstEntryTime_spec S z hz
    have hp (n : ℕ) (hn : m ≤ n) : z n ∈ S ∧ R (z n) = R (z m) := by
      induction n, hn using Nat.le_induction with
      | base => exact ⟨hmS, rfl⟩
      | succ n hn ih =>
          have hh := hzstep n ih.1
          exact ⟨hh.1, hh.2.trans ih.2⟩
    have he : (fun n => R (z n)) =ᶠ[atTop] (fun _ => stoppedOutput S R z) :=
      eventually_atTop.mpr ⟨m, fun n hn => (hp n hn).2⟩
    exact tendsto_const_nhds.congr' he.symm
  have hlim := tendsto_integral_of_dominated_convergence (μ := markovTrajectory K h) (fun _ => C)
    (fun n => (hR.comp (measurable_pi_apply n)).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb (z n))) hl
  have he (n : ℕ) : (∫ z, R (z n) ∂markovTrajectory K h) = ∫ x, R x ∂iterateKernel K n h := by
    rw [← markovTrajectory_coordinate_law K h n,
      integral_map_of_stronglyMeasurable (measurable_pi_apply n) hR.stronglyMeasurable]
  change Tendsto (fun n => ∫ z, R (z n) ∂markovTrajectory K h) atTop
    (𝓝 (∫ z, stoppedOutput S R z ∂markovTrajectory K h)) at hlim
  simp only [he] at hlim
  have hbound : BddAbove (range (fun n : ℕ => ∫ x, R x ∂iterateKernel K n h)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hle := integral_mono (μ := iterateKernel K n h) (integrable_of_abs_bounded _ hR C hb) (integrable_const C)
      (fun x : H => (le_abs_self _).trans (hb x))
    simpa using hle
  exact le_of_tendsto hlim (Eventually.of_forall (fun n => le_ciSup hbound n))

end StochasticMatching
