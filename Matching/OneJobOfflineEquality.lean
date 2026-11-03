import Matching.SingleSetChainLaw

/-! The chain duality and expected offline equality are unconditional for
instances with at most one offline job and any finite set of arrival types.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Subsingleton ι]
  [Fintype σ] [DecidableEq σ]

theorem nonempty_finset_eq_univ_subsingleton {A : Finset ι} (hA : A.Nonempty) : A = Finset.univ := by
  obtain ⟨i, hi⟩ := hA
  apply Finset.eq_univ_of_forall
  intro j
  simpa only [Subsingleton.elim j i] using hi

theorem poisson_exponential_chain_law_one_job (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    PoissonExponentialChainLaw N intensity := by
  intro a C hC
  by_cases hzero : ∅ ∈ C
  · have hl := chainExceedance_empty_vertex
      (fun z => supplyDeficiency_empty N (fun s => (intensity s : ℝ)) z) a.coe_nonneg hzero
    rw [hl]
    have hr : {p : (σ → ℕ) × ℕ | ∀ A ∈ C,
        (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      have h := hp ∅ hzero
      rw [supplyDeficiency_empty] at h
      exact (not_lt_of_ge (Nat.cast_nonneg p.2)) h
    rw [hr]
    simp
  · have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hC).1
    have hc : C = {Finset.univ} := by
      apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      refine ⟨hne, ?_⟩
      intro A hA
      apply nonempty_finset_eq_univ_subsingleton
      exact Finset.nonempty_iff_ne_empty.mpr (fun h => hzero (h ▸ hA))
    rw [hc]
    exact poisson_exponential_singleton_chain_law N intensity Finset.univ a

theorem expected_offline_equality_one_job (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    (∫ z, offlineValue (supplyRegion N (fun s => (intensity s : ℝ))) z ∂independentExponentials) =
      ∫ counts, arrivalOfflineValue N counts ∂independentPoissons intensity :=
  expected_offline_equality_of_chain_law N intensity (poisson_exponential_chain_law_one_job N intensity)

end StochasticMatching
