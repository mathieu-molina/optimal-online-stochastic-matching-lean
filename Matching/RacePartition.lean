import Matching.ConstantRateRace

/-! The constant-rate marked branches exhaust the probability space up to a
null set. In particular, a first completion exists and is almost surely unique.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem strictWinner_disjoint (r : ι → ℝ) :
    Pairwise (fun i j => Disjoint (strictWinner r i) (strictWinner r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact lt_asymm (hi j (Ne.symm hij)) (hj i hij)

theorem winner_residual_pos {r z : ι → ℝ} (hr : ∀ i, 0 < r i)
    {j : ι} (hj : z ∈ strictWinner r j) (i : {i : ι // i ≠ j}) :
    0 < (raceObservation r j z).2 i := by
  have h := (lt_div_iff₀ (hr i.1)).mp (hj i.1 i.2)
  change 0 < z i.1 - r i.1 * (z j / r j)
  nlinarith

theorem winner_completes_exactly {r z : ι → ℝ} {j : ι} (hj : 0 < r j) :
    r j * (raceObservation r j z).1 = z j := by
  change r j * (z j / r j) = z j
  field_simp

theorem strictWinner_mass_sum [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    ∑ j, independentExponentials (strictWinner r j) = 1 := by
  have hR := total_rate_pos (fun i => (hr i).le) (Classical.arbitrary ι)
    (hr (Classical.arbitrary ι))
  simp_rw [strictWinner_probability hr]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hr i).le hR.le),
    ← Finset.sum_div, div_self hR.ne', ENNReal.ofReal_one]

theorem strictWinner_union_probability [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) : independentExponentials (⋃ j, strictWinner r j) = 1 := by
  rw [measure_iUnion (strictWinner_disjoint r) (measurableSet_strictWinner r),
    tsum_fintype, strictWinner_mass_sum hr]

theorem first_completion_unique_ae [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) :
    ∀ᵐ z ∂independentExponentials, ∃! j, z ∈ strictWinner r j := by
  have hfull : ∀ᵐ z ∂independentExponentials, z ∈ ⋃ j, strictWinner r j := by
    rw [ae_iff]
    change independentExponentials (⋃ j, strictWinner r j)ᶜ = 0
    rw [measure_compl (MeasurableSet.iUnion (measurableSet_strictWinner r))
      (measure_ne_top _ _), measure_univ, strictWinner_union_probability hr, tsub_self]
  filter_upwards [hfull] with z hz
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  refine ⟨j, hj, ?_⟩
  intro i hi
  by_contra hij
  exact lt_asymm (hi j (Ne.symm hij)) (hj i hij)

end StochasticMatching
