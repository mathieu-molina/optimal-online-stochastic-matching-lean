import Matching.ContinuousSupplyFlow
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Measurable assignment probabilities recovered from feasible scheduling
rates. `none` represents rejecting an arrival, and `some i` assigns it to job i.
The finite probability law recovers every target rate, including zero supplies.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def selectedAssignment (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ)
    (s : σ) : Option ι → ℝ
  | none => 1 - ∑ i, flowAssignmentProbability capacity (selectedSupplyFlow N capacity x) s i
  | some i => flowAssignmentProbability capacity (selectedSupplyFlow N capacity x) s i

theorem selectedAssignment_nonneg (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (j : Option ι) : 0 ≤ selectedAssignment N capacity x s j := by
  have hf := (selectedSupplyFlow_correct N capacity hcapacity hx).1
  cases j with
  | none => exact sub_nonneg.mpr (flowAssignmentProbability_sum_le_one hf s)
  | some i => exact flowAssignmentProbability_nonneg hf s i

theorem selectedAssignment_sum (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ) (s : σ) :
    (∑ j, selectedAssignment N capacity x s j) = 1 := by
  rw [Fintype.sum_option]
  simp only [selectedAssignment]
  ring

theorem selectedAssignment_supported (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : i ∉ N s) : selectedAssignment N capacity x s (some i) = 0 :=
  flowAssignmentProbability_supported (selectedSupplyFlow_correct N capacity hcapacity hx).1 s i hi

theorem selectedAssignment_recovers_rates (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) (i : ι) :
    (∑ s, capacity s * selectedAssignment N capacity x s (some i)) = x i := by
  obtain ⟨hf, he⟩ := selectedSupplyFlow_correct N capacity hcapacity hx
  change (∑ s, capacity s * flowAssignmentProbability capacity (selectedSupplyFlow N capacity x) s i) = x i
  rw [assignment_probabilities_recover_rates hf, he]

theorem continuous_selectedAssignment (N : σ → Finset ι) (capacity : σ → ℝ) (s : σ) :
    Continuous (fun x => selectedAssignment N capacity x s) := by
  have hc : ∀ i, Continuous (fun x => flowAssignmentProbability capacity (selectedSupplyFlow N capacity x) s i) := by
    intro i
    exact (((continuous_apply i).comp ((continuous_apply s).comp
      (continuous_selectedSupplyFlow_rates N capacity))).div_const (capacity s))
  apply continuous_pi
  intro j
  cases j with
  | none => exact continuous_const.sub (continuous_finset_sum _ (fun i _ => hc i))
  | some i => exact hc i

noncomputable def selectedAssignmentPMF (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (s : σ) : PMF (Option ι) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (selectedAssignment N capacity x s j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => selectedAssignment_nonneg N capacity hcapacity hx s j),
      selectedAssignment_sum, ENNReal.ofReal_one])

theorem selectedAssignmentPMF_mass (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (s : σ) (j : Option ι) :
    (selectedAssignmentPMF N capacity hcapacity x hx s j).toReal = selectedAssignment N capacity x s j := by
  exact ENNReal.toReal_ofReal (selectedAssignment_nonneg N capacity hcapacity hx s j)

theorem selectedAssignmentPMF_recovers_rates (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (i : ι) :
    (∑ s, capacity s * (selectedAssignmentPMF N capacity hcapacity x hx s (some i)).toReal) = x i := by
  simp only [selectedAssignmentPMF_mass]
  exact selectedAssignment_recovers_rates N capacity hcapacity hx i

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_assignment_of_rates (N : σ → Finset ι) (capacity : σ → ℝ)
    {r : Ω → (ι → ℝ)} (hr : Measurable r) :
    Measurable (fun ω s => selectedAssignment N capacity (r ω) s) := by
  apply measurable_pi_lambda
  intro s
  exact ((continuous_selectedAssignment N capacity s).measurable).comp hr

theorem assignment_of_rates_valid (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (r : Ω → (ι → ℝ))
    (hr : ∀ ω, r ω ∈ supplyRegion N capacity) (ω : Ω) :
    (∀ s j, 0 ≤ selectedAssignment N capacity (r ω) s j) ∧
    (∀ s, (∑ j, selectedAssignment N capacity (r ω) s j) = 1) ∧
    (∀ s i, i ∉ N s → selectedAssignment N capacity (r ω) s (some i) = 0) ∧
    ∀ i, (∑ s, capacity s * selectedAssignment N capacity (r ω) s (some i)) = r ω i :=
  ⟨selectedAssignment_nonneg N capacity hcapacity (hr ω), selectedAssignment_sum N capacity (r ω),
    selectedAssignment_supported N capacity hcapacity (hr ω), selectedAssignment_recovers_rates N capacity hcapacity (hr ω)⟩

end StochasticMatching
