import Matching.IndependentPoissons
import Matching.FiniteChainRecurrence

/-! Independent Poisson increments satisfy the same finite chain recurrence
as the nested exponential waiting sums.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

theorem independentPoissons_head_tail_law {n : ℕ} (a : Fin (n+1) → ℝ≥0) :
    Measure.map (fun x : Fin (n+1) → ℕ => (x 0, fun k : Fin n => x k.succ))
      (independentPoissons a) =
      (poissonMeasure (a 0)).prod (independentPoissons (fun k : Fin n => a k.succ)) := by
  have h := (measurePreserving_piFinSuccAbove (fun k => poissonMeasure (a k)) 0).map_eq
  simpa only [MeasurableEquiv.piFinSuccAbove, Fin.succAbove_zero,
    independentPoissons] using h

theorem poisson_chain_recursion {n : ℕ} (a : Fin (n+1) → ℝ≥0) (m : Fin (n+1) → ℕ) :
    (independentPoissons a).real {x | ∀ k, cumulativeFin x k < m k} =
      ∑ j : Fin (m 0), poissonWeight (a 0) j.val *
        (independentPoissons (fun k : Fin n => a k.succ)).real
          {x | ∀ k, cumulativeFin x k < m k.succ - j.val} := by
  let μ := independentPoissons (fun k : Fin n => a k.succ)
  let S : Set (ℕ × (Fin n → ℕ)) :=
    {p | p.1 < m 0 ∧ ∀ k, p.1 + cumulativeFin p.2 k < m k.succ}
  have hlaw := congrArg (fun ν : Measure (ℕ × (Fin n → ℕ)) => ν.real S)
    (independentPoissons_head_tail_law a)
  dsimp only at hlaw
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at hlaw
  have he : (fun x : Fin (n+1) → ℕ => (x 0, fun k : Fin n => x k.succ)) ⁻¹' S =
      {x | ∀ k, cumulativeFin x k < m k} := by
    ext x
    simp only [mem_preimage, S, mem_setOf_eq, Fin.forall_fin_succ,
      cumulativeFin_zero, cumulativeFin_succ]
  rw [he] at hlaw
  rw [hlaw]
  let E : Fin (m 0) → Set (ℕ × (Fin n → ℕ)) := fun j =>
    {j.val} ×ˢ {x | ∀ k, cumulativeFin x k < m k.succ - j.val}
  have hS : S = ⋃ j ∈ (Finset.univ : Finset (Fin (m 0))), E j := by
    ext p
    simp only [S, mem_setOf_eq, mem_iUnion, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨hp, hq⟩
      refine ⟨⟨p.1, hp⟩, rfl, ?_⟩
      intro k
      have h := hq k
      try dsimp only at *
      omega
    · rintro ⟨j, hp, hq⟩
      have hp' : p.1 = j.val := hp
      refine ⟨hp'.symm ▸ j.isLt, ?_⟩
      intro k
      have h := hq k
      try dsimp only at *
      omega
  have hd : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin (m 0))) : Set (Fin (m 0))) E := by
    intro j _ k _ hjk
    change Disjoint (E j) (E k)
    rw [Set.disjoint_left]
    intro p hj hk
    exact hjk (Fin.ext (hj.1.symm.trans hk.1))
  have hE : ∀ j ∈ (Finset.univ : Finset (Fin (m 0))), MeasurableSet (E j) :=
    fun j _ => (Set.to_countable _).measurableSet
  rw [hS, measureReal_biUnion_finset hd hE]
  apply Finset.sum_congr rfl
  intro j _
  change ((poissonMeasure (a 0)).prod μ).real
    ({j.val} ×ˢ {x | ∀ k, cumulativeFin x k < m k.succ - j.val}) = _
  rw [measureReal_prod_prod, poissonMeasure_real_singleton]

theorem poisson_chain_value {n : ℕ} (a : Fin n → ℝ≥0) (m : Fin n → ℕ) :
    (independentPoissons a).real {x | ∀ k, cumulativeFin x k < m k} = poissonChainValue a m := by
  induction n with
  | zero =>
      have he : {x : Fin 0 → ℕ | ∀ k, cumulativeFin x k < m k} = Set.univ := by ext x; simp
      rw [he, measureReal_univ_eq_one, poissonChainValue_zero]
  | succ n ih =>
      rw [poisson_chain_recursion, poissonChainValue_succ]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]

end StochasticMatching
