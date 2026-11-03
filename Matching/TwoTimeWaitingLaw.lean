import Matching.TwoTimePoissonLaw

/-! Two nested waiting-time inequalities have the same joint probability as
the corresponding two Poisson count inequalities. This is the two-time form
of the canonical process identity needed for arbitrary chains.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {n : ℕ}

noncomputable def prefixDemand (z : Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), z i

theorem finite_count_prefix_lt_iff {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (hm : m ≤ n) :
    finiteRenewalCount z t < m ↔ t < prefixDemand z m := by
  by_cases hm0 : m = 0
  · subst m
    simp [prefixDemand, not_lt.mpr ht]
  · let j : Fin n := ⟨m - 1, by omega⟩
    have he : Finset.univ.filter (fun i : Fin n => i.val < m) = Finset.Iic j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      change i.val < m ↔ i.val ≤ m - 1
      omega
    have hc : finiteRenewalCount z t < m ↔ finiteRenewalCount z t ≤ j.val := by
      dsimp only [j]
      omega
    rw [hc, finiteRenewalCount_le_iff hz t j]
    simp only [prefixDemand, he, arrivalTime]

theorem exponential_poisson_two_time_waiting_law (m n : ℕ) (hmn : m ≤ n) (a b : ℝ≥0) :
    (independentExponentials (ι := Fin n)).real
      {z | (a : ℝ) < prefixDemand z m ∧ (a : ℝ) + b < ∑ i, z i} =
    ((poissonMeasure a).prod (poissonMeasure b)).real
      {p : ℕ × ℕ | p.1 < m ∧ p.1 + p.2 < n} := by
  have he : ({z : Fin n → ℝ | (a : ℝ) < prefixDemand z m ∧ (a : ℝ) + b < ∑ i, z i} : Set (Fin n → ℝ)) =ᵐ[independentExponentials]
      {z | finiteRenewalCount z a < m ∧ finiteRenewalCount z ((a : ℝ) + b) < n} := by
    filter_upwards [independentExponentials_ae_pos (ι := Fin n)] with z hz
    apply propext
    exact and_congr (finite_count_prefix_lt_iff (fun i => (hz i).le) a.coe_nonneg m hmn).symm
      (finiteRenewalCount_lt_iff_total (fun i => (hz i).le) ((a : ℝ) + b)
        (add_nonneg a.coe_nonneg b.coe_nonneg)).symm
  rw [measureReal_congr he]
  exact exponential_poisson_two_time_count_law m n a b

end StochasticMatching
