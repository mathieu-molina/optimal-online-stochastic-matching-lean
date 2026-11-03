import Matching.FiniteRenewalJoint

/-! Equality of the two-time count events for the actual exponential renewal
path and independent Poisson increments. This is a joint law, not a deduction
from separate one-time marginals.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {n : ℕ}

theorem finiteRenewalCount_mono_time (z : Fin n → ℝ) : Monotone (finiteRenewalCount z) := by
  intro t u htu
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans htu⟩

theorem finite_count_two_time_sum (m : ℕ) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    (independentExponentials (ι := Fin n)).real
      {z | finiteRenewalCount z t < m ∧ finiteRenewalCount z u < n} =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j.val < m)),
        poissonWeight t j.val * poissonLowerTail (u - t) (n - j.val) := by
  let S := Finset.univ.filter (fun j : Fin n => j.val < m)
  let E : Fin n → Set (Fin n → ℝ) := fun j =>
    {z | finiteRenewalCount z t = j.val ∧ finiteRenewalCount z u < n}
  have he : {z : Fin n → ℝ | finiteRenewalCount z t < m ∧ finiteRenewalCount z u < n} = ⋃ j ∈ S, E j := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hz
      let j : Fin n := ⟨finiteRenewalCount z t, (finiteRenewalCount_mono_time z htu).trans_lt hz.2⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.1⟩, rfl, hz.2⟩
    · rintro ⟨j, hj, hzt, hzu⟩
      exact ⟨hzt.symm ▸ (Finset.mem_filter.mp hj).2, hzu⟩
  have hd : Set.PairwiseDisjoint (S : Set (Fin n)) E := by
    intro i _ j _ hij
    change Disjoint (E i) (E j)
    rw [Set.disjoint_left]
    intro z hi hj
    exact hij (Fin.ext (hi.1.symm.trans hj.1))
  have hm : ∀ j ∈ S, MeasurableSet (E j) := by
    intro j _
    exact ((measurableSet_singleton j.val).preimage (measurable_finiteRenewalCount t)).inter
      (measurableSet_lt (measurable_finiteRenewalCount u) measurable_const)
  rw [he, measureReal_biUnion_finset hd hm]
  apply Finset.sum_congr rfl
  intro j _
  exact finite_count_two_time_atom_tail j ht htu

theorem poisson_two_increment_sum (m n : ℕ) (a b : ℝ≥0) :
    ((poissonMeasure a).prod (poissonMeasure b)).real
      {p : ℕ × ℕ | p.1 < m ∧ p.1 + p.2 < n} =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j.val < m)),
        poissonWeight a j.val * poissonLowerTail b (n - j.val) := by
  let S := Finset.univ.filter (fun j : Fin n => j.val < m)
  let E : Fin n → Set (ℕ × ℕ) := fun j => {j.val} ×ˢ {q : ℕ | q < n - j.val}
  have he : {p : ℕ × ℕ | p.1 < m ∧ p.1 + p.2 < n} = ⋃ j ∈ S, E j := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hp
      let j : Fin n := ⟨p.1, by omega⟩
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩, ?_⟩
      change p.1 = j.val ∧ p.2 < n - j.val
      exact ⟨rfl, by dsimp [j]; omega⟩
    · rintro ⟨j, hj, hp⟩
      have h1 : p.1 = j.val := hp.1
      have h2 : p.2 < n - j.val := hp.2
      have h3 : j.val < m := (Finset.mem_filter.mp hj).2
      have h4 := j.isLt
      omega
  have hd : Set.PairwiseDisjoint (S : Set (Fin n)) E := by
    intro i _ j _ hij
    change Disjoint (E i) (E j)
    rw [Set.disjoint_left]
    intro p hi hj
    exact hij (Fin.ext (hi.1.symm.trans hj.1))
  have hm : ∀ j ∈ S, MeasurableSet (E j) := fun j _ =>
    (measurableSet_singleton j.val).prod (Set.to_countable _).measurableSet
  rw [he, measureReal_biUnion_finset hd hm]
  apply Finset.sum_congr rfl
  intro j _
  change ((poissonMeasure a).prod (poissonMeasure b)).real
    ({j.val} ×ˢ {q : ℕ | q < n - j.val}) = _
  rw [measureReal_prod_prod, poissonMeasure_real_singleton, ← poissonLowerTail_eq_probability]

theorem exponential_poisson_two_time_count_law (m n : ℕ) (a b : ℝ≥0) :
    (independentExponentials (ι := Fin n)).real
      {z | finiteRenewalCount z a < m ∧ finiteRenewalCount z ((a : ℝ) + b) < n} =
    ((poissonMeasure a).prod (poissonMeasure b)).real
      {p : ℕ × ℕ | p.1 < m ∧ p.1 + p.2 < n} := by
  rw [finite_count_two_time_sum m a.coe_nonneg (le_add_of_nonneg_right b.coe_nonneg),
    poisson_two_increment_sum, add_sub_cancel_left]

end StochasticMatching
