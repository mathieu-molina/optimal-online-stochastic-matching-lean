import Matching.PoissonAddition
import Mathlib.MeasureTheory.Constructions.Pi

/-! The independent finite type-count model and Poisson laws for arbitrary
subsets of arrival types. These supply the increment laws needed along chains.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ]

noncomputable def independentPoissons (a : σ → ℝ≥0) : Measure (σ → ℕ) :=
  Measure.pi (fun s => poissonMeasure (a s))

instance independentPoissons_probability (a : σ → ℝ≥0) : IsProbabilityMeasure (independentPoissons a) := by
  unfold independentPoissons
  infer_instance

theorem independentPoissons_coordinate_law (a : σ → ℝ≥0) (s : σ) :
    Measure.map (fun n : σ → ℕ => n s) (independentPoissons a) = poissonMeasure (a s) := by
  classical
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_pi_apply s) hS]
  have he : (fun n : σ → ℕ => n s) ⁻¹' S = Set.univ.pi (fun t => if t = s then S else Set.univ) := by
    ext n
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hn t
      by_cases ht : t = s <;> simp [ht, hn]
    · intro hn
      simpa using hn s
  rw [he, independentPoissons, Measure.pi_pi]
  simp only [apply_ite, measure_univ, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem independentPoissons_coordinates_independent (a : σ → ℝ≥0) :
    iIndepFun (fun s (n : σ → ℕ) => n s) (independentPoissons a) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun s => (measurable_pi_apply s).aemeasurable)).mpr
  simp only [independentPoissons_coordinate_law]
  exact Measure.map_id

theorem independentPoissons_subset_sum_law (a : σ → ℝ≥0) (S : Finset σ) :
    Measure.map (fun n : σ → ℕ => ∑ s ∈ S, n s) (independentPoissons a) = poissonMeasure (∑ s ∈ S, a s) :=
  poisson_finset_sum_law (independentPoissons a) S (fun s n => n s) a measurable_pi_apply
    (independentPoissons_coordinates_independent a) (independentPoissons_coordinate_law a)

theorem independentPoissons_disjoint_subset_sums (a : σ → ℝ≥0) (S T : Finset σ) (hST : Disjoint S T) :
    IndepFun (fun n : σ → ℕ => ∑ s ∈ S, n s) (fun n : σ → ℕ => ∑ s ∈ T, n s) (independentPoissons a) := by
  classical
  have h := (independentPoissons_coordinates_independent a).indepFun_finset S T hST measurable_pi_apply
  have hS : Measurable (fun n : S → ℕ => ∑ s, n s) := Finset.measurable_sum _ (fun s _ => measurable_pi_apply s)
  have hT : Measurable (fun n : T → ℕ => ∑ s, n s) := Finset.measurable_sum _ (fun s _ => measurable_pi_apply s)
  have h' := h.comp hS hT
  simpa only [Function.comp_def, Finset.sum_coe_sort] using h'

end StochasticMatching
