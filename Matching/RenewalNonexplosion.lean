import Matching.FiniteRenewalPoisson

/-! Exponential renewal times cannot accumulate in a bounded interval.
The theorem applies to any sample space whose finite partial sums have the
proved exponential-sum distributions; it does not assume nonexplosion.
-/
open MeasureTheory Set ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching

theorem exponentialSumLaw_small_tail (n : ℕ) (a : ℝ≥0) :
    exponentialSumLaw n (Iic (a : ℝ)) = poissonMeasure a (Ici n) := by
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have ht := exponentialSumLaw_tail_eq_poissonLowerTail n a.coe_nonneg
  rw [poissonLowerTail_eq_probability] at ht
  have he := measureReal_compl (μ := exponentialSumLaw n) (s := Ioi (a : ℝ)) measurableSet_Ioi
  have hp := measureReal_compl (μ := poissonMeasure a) (s := {k : ℕ | k < n})
    (measurableSet_lt measurable_id measurable_const)
  have hc : ({k : ℕ | k < n} : Set ℕ)ᶜ = Ici n := by ext k; simp
  rw [compl_Ioi, measureReal_univ_eq_one] at he
  rw [hc, measureReal_univ_eq_one] at hp
  rw [he, ht, hp]

theorem poisson_tail_iInf_zero (a : ℝ≥0) :
    (⨅ n : ℕ, poissonMeasure a (Ici n)) = 0 := by
  have ha : Antitone (fun n : ℕ => (Ici n : Set ℕ)) :=
    fun _ _ h => Ici_subset_Ici.mpr h
  have he : (⋂ n : ℕ, (Ici n : Set ℕ)) = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro k hk
    have h := mem_iInter.mp hk (k + 1)
    change k + 1 ≤ k at h
    omega
  rw [← ha.measure_iInter (fun _ => measurableSet_Ici.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩, he, measure_empty]

theorem exponential_renewal_exceeds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (fun ω => ∑ i ∈ Finset.range n, X i ω) μ = exponentialSumLaw n)
    (a : ℝ≥0) : ∀ᵐ ω ∂μ, ∃ n, (a : ℝ) < ∑ i ∈ Finset.range n, X i ω := by
  let E : Set Ω := {ω | ∀ n, (∑ i ∈ Finset.range n, X i ω) ≤ (a : ℝ)}
  have hbound : ∀ n, μ E ≤ poissonMeasure a (Ici n) := by
    intro n
    have hs : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
      Finset.measurable_sum _ (fun i _ => hm i)
    calc μ E ≤ μ {ω | (∑ i ∈ Finset.range n, X i ω) ≤ (a : ℝ)} :=
        measure_mono (fun ω hω => hω n)
      _ = exponentialSumLaw n (Iic (a : ℝ)) := by
        rw [← hlaw n, Measure.map_apply hs measurableSet_Iic]
        rfl
      _ = poissonMeasure a (Ici n) := exponentialSumLaw_small_tail n a
  have hz : μ E = 0 := le_antisymm
    ((le_iInf hbound).trans_eq (poisson_tail_iInf_zero a)) (zero_le _)
  apply ae_iff.mpr
  simpa only [not_exists, not_lt] using hz

theorem exponential_renewal_unbounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (fun ω => ∑ i ∈ Finset.range n, X i ω) μ = exponentialSumLaw n) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ, ∃ n, T < ∑ i ∈ Finset.range n, X i ω := by
  have h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ n, (k : ℝ) < ∑ i ∈ Finset.range n, X i ω :=
    fun k => exponential_renewal_exceeds μ X hm hlaw (k : ℝ≥0)
  filter_upwards [ae_all_iff.mpr h] with ω hω T
  obtain ⟨k, hk⟩ := exists_nat_ge T
  obtain ⟨n, hn⟩ := hω k
  exact ⟨n, hk.trans_lt hn⟩

end StochasticMatching
