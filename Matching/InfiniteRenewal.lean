import Matching.RenewalNonexplosion
import Mathlib.Probability.ProductMeasure

/-! A genuine infinite exponential renewal process. Its partial sums have
the finite laws already proved, hence almost surely exceed every deadline.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching

noncomputable def infiniteExponentials : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => unitExponential)

instance infiniteExponentials_probability : IsProbabilityMeasure infiniteExponentials := by
  unfold infiniteExponentials
  infer_instance

theorem infiniteExponentials_restriction (S : Finset ℕ) :
    Measure.map S.restrict infiniteExponentials = independentExponentials (ι := ↥S) :=
  Measure.infinitePi_map_restrict _

theorem infiniteExponentials_sum_law (S : Finset ℕ) :
    Measure.map (fun z : ℕ → ℝ => ∑ i ∈ S, z i) infiniteExponentials = exponentialSumLaw S.card := by
  have hs : Measurable (fun z : ↥S → ℝ => ∑ i, z i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hr : Measurable (S.restrict : (ℕ → ℝ) → (↥S → ℝ)) := by fun_prop
  have h := independentExponentials_subset_sum_law (Finset.univ : Finset ↥S)
  rw [← infiniteExponentials_restriction S, Measure.map_map hs hr] at h
  simpa only [Function.comp_def, Finset.restrict, Finset.sum_coe_sort, Finset.card_univ, Fintype.card_coe] using h

theorem infiniteExponentials_unbounded :
    ∀ᵐ z ∂infiniteExponentials, ∀ T : ℝ, ∃ n, T < ∑ i ∈ Finset.range n, z i := by
  apply exponential_renewal_unbounded infiniteExponentials (fun i z => z i) measurable_pi_apply
  intro n
  simpa only [Finset.card_range] using infiniteExponentials_sum_law (Finset.range n)

theorem infiniteExponentials_coordinate_pos (i : ℕ) :
    ∀ᵐ z ∂infiniteExponentials, 0 < z i := by
  have h := infiniteExponentials_sum_law ({i} : Finset ℕ)
  have hsum : exponentialSumLaw 1 = unitExponential := by
    have hc := independentExponentials_subset_sum_law (Finset.univ : Finset Unit)
    simpa only [Finset.univ_unique, Finset.sum_singleton, Finset.card_singleton,
      independentExponentials_coordinate_law] using hc.symm
  simp only [Finset.sum_singleton, Finset.card_singleton, hsum] at h
  have hp := unitExponential_ae_pos
  rw [← h] at hp
  have hm : Measurable (fun z : ℕ → ℝ => z i) := measurable_pi_apply i
  exact (ae_map_iff hm.aemeasurable measurableSet_Ioi).mp hp

theorem infiniteExponentials_all_pos : ∀ᵐ z ∂infiniteExponentials, ∀ i, 0 < z i :=
  ae_all_iff.mpr infiniteExponentials_coordinate_pos

theorem infiniteExponentials_finite_arrivals (T : ℝ) :
    ∀ᵐ z ∂infiniteExponentials, Set.Finite {n : ℕ | (∑ i ∈ Finset.range n, z i) ≤ T} := by
  filter_upwards [infiniteExponentials_unbounded, infiniteExponentials_all_pos] with z hz hpos
  obtain ⟨k, hk⟩ := hz T
  apply (Set.finite_Iio k).subset
  intro n hn
  change n < k
  by_contra hnk
  have hs : (∑ i ∈ Finset.range k, z i) ≤ ∑ i ∈ Finset.range n, z i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_of_not_gt hnk))
      (fun i _ _ => (hpos i).le)
  exact (not_le.mpr hk) (hs.trans hn)

end StochasticMatching
