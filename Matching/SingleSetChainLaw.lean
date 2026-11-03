import Matching.ExponentialPoissonTail
import Matching.NestedPoissonCounts
import Matching.OfflineDualityReduction

/-! The one-set case of the Poisson/exponential deficiency identity, for an
arbitrary job subset and arbitrary overlapping arrival neighborhoods.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ]

theorem independentPoissons_subset_sum_with_threshold_law (intensity : σ → ℝ≥0)
    (S : Finset σ) (a : ℝ≥0) :
    Measure.map (fun p : (σ → ℕ) × ℕ => (∑ s ∈ S, p.1 s) + p.2)
      ((independentPoissons intensity).prod (poissonMeasure a)) =
        poissonMeasure ((∑ s ∈ S, intensity s) + a) := by
  have hm : Measurable (fun n : σ → ℕ => ∑ s ∈ S, n s) :=
    Finset.measurable_sum S (fun s _ => measurable_pi_apply s)
  have hp := Measure.map_prod_map (independentPoissons intensity) (poissonMeasure a) hm measurable_id
  rw [independentPoissons_subset_sum_law, Measure.map_id] at hp
  have he : (fun p : (σ → ℕ) × ℕ => (∑ s ∈ S, p.1 s) + p.2) =
      (fun p : ℕ × ℕ => p.1 + p.2) ∘ Prod.map (fun n : σ → ℕ => ∑ s ∈ S, n s) id := rfl
  rw [he, ← Measure.map_map (measurable_fst.add measurable_snd) (hm.prodMap measurable_id),
    ← hp, poisson_addition_law]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

theorem poisson_exponential_single_set_law (N : σ → Finset ι) (intensity : σ → ℝ≥0)
    (A : Finset ι) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | (a : ℝ) < supplyDeficiency N (fun s => (intensity s : ℝ)) z A} =
    ((independentPoissons intensity).prod (poissonMeasure a)).real
      {p : (σ → ℕ) × ℕ | (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A} := by
  let b : ℝ≥0 := ∑ s ∈ touchingTypes N A, intensity s
  have hb : (b : ℝ) = supplyCoverage N (fun s => (intensity s : ℝ)) A := by
    rw [supplyCoverage_eq_touching_sum]
    simp only [b, NNReal.coe_sum]
  have he : {z : ι → ℝ | (a : ℝ) < supplyDeficiency N (fun s => (intensity s : ℝ)) z A} =
      {z | ((b + a : ℝ≥0) : ℝ) < ∑ i ∈ A, z i} := by
    ext z
    simp only [mem_setOf_eq, supplyDeficiency, NNReal.coe_add, hb]
    constructor <;> intro h <;> linarith
  have hp := congrArg (fun μ : Measure ℕ => μ.real {k : ℕ | k < A.card})
    (independentPoissons_subset_sum_with_threshold_law intensity (touchingTypes N A) a)
  dsimp only at hp
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at hp
  change ((independentPoissons intensity).prod (poissonMeasure a)).real
    {p : (σ → ℕ) × ℕ | (∑ s ∈ touchingTypes N A, p.1 s) + p.2 < A.card} =
      (poissonMeasure (b + a)).real {k : ℕ | k < A.card} at hp
  have hr : {p : (σ → ℕ) × ℕ | (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A} =
      {p : (σ → ℕ) × ℕ | (∑ s ∈ touchingTypes N A, p.1 s) + p.2 < A.card} := by
    ext p
    simp only [mem_setOf_eq, supplyDeficiency, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← arrivalCoverageCount_cast, lt_sub_iff_add_lt, ← Nat.cast_add, Nat.cast_lt,
      arrivalCoverageCount_eq_touching_sum, add_comm]
  rw [he, hr, hp]
  exact exponential_subset_sum_poisson_tail A (b + a)

theorem poisson_exponential_singleton_chain_law (N : σ → Finset ι) (intensity : σ → ℝ≥0)
    (A : Finset ι) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      (chainExceedance (supplyDeficiency N (fun s => (intensity s : ℝ))) a {A}) =
    ((independentPoissons intensity).prod (poissonMeasure a)).real
      {p : (σ → ℕ) × ℕ | ∀ B ∈ ({A} : Finset (Finset ι)),
        (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) B} := by
  simpa only [chainExceedance, Finset.mem_singleton, forall_eq] using
    poisson_exponential_single_set_law N intensity A a

end StochasticMatching
