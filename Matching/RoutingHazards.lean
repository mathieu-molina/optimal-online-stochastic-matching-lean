import Matching.AssignmentSelector

/-! The type/job event-rate matrix for an online routing decision. Its row
sums are the original arrival intensities; its job-column sums are the
scheduling rates, with the remaining column representing rejections.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def arrivalRoutingRate (N : σ → Finset ι) (capacity : σ → ℝ)
    (x : ι → ℝ) (s : σ) (j : Option ι) : ℝ :=
  capacity s * selectedAssignment N capacity x s j

theorem arrivalRoutingRate_nonneg (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (j : Option ι) : 0 ≤ arrivalRoutingRate N capacity x s j :=
  mul_nonneg (hc s) (selectedAssignment_nonneg N capacity hc hx s j)

theorem arrivalRoutingRate_type_sum (N : σ → Finset ι) (capacity : σ → ℝ)
    (x : ι → ℝ) (s : σ) : (∑ j, arrivalRoutingRate N capacity x s j) = capacity s := by
  simp only [arrivalRoutingRate, ← Finset.mul_sum, selectedAssignment_sum, mul_one]

theorem arrivalRoutingRate_job_sum (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) (i : ι) :
    (∑ s, arrivalRoutingRate N capacity x s (some i)) = x i :=
  selectedAssignment_recovers_rates N capacity hc hx i

theorem arrivalRoutingRate_reject_sum (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) :
    (∑ s, arrivalRoutingRate N capacity x s none) = (∑ s, capacity s) - ∑ i, x i := by
  have h : (∑ j : Option ι, ∑ s, arrivalRoutingRate N capacity x s j) = ∑ s, capacity s := by
    rw [Finset.sum_comm]
    simp only [arrivalRoutingRate_type_sum]
  rw [Fintype.sum_option] at h
  simp only [arrivalRoutingRate_job_sum N capacity hc hx] at h
  linarith

theorem supplyRegion_total_rate_le (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) :
    (∑ i, x i) ≤ ∑ s, capacity s := by
  have h := Finset.sum_nonneg (fun s (_ : s ∈ (Finset.univ : Finset σ)) =>
    arrivalRoutingRate_nonneg N capacity hc hx s none)
  rw [arrivalRoutingRate_reject_sum N capacity hc hx] at h
  linarith

theorem arrivalRoutingRate_supported (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : i ∉ N s) : arrivalRoutingRate N capacity x s (some i) = 0 := by
  simp only [arrivalRoutingRate, selectedAssignment_supported N capacity hc hx s i hi, mul_zero]

theorem arrivalRoutingRate_zero_job (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (i : ι) (hi : x i = 0) (s : σ) : arrivalRoutingRate N capacity x s (some i) = 0 := by
  have hs := Finset.single_le_sum
    (fun t (_ : t ∈ (Finset.univ : Finset σ)) => arrivalRoutingRate_nonneg N capacity hc hx t (some i))
    (Finset.mem_univ s)
  rw [arrivalRoutingRate_job_sum N capacity hc hx, hi] at hs
  exact le_antisymm hs (arrivalRoutingRate_nonneg N capacity hc hx s (some i))

theorem continuous_arrivalRoutingRate (N : σ → Finset ι) (capacity : σ → ℝ)
    (s : σ) (j : Option ι) : Continuous (fun x => arrivalRoutingRate N capacity x s j) :=
  continuous_const.mul ((continuous_apply j).comp (continuous_selectedAssignment N capacity s))

end StochasticMatching
