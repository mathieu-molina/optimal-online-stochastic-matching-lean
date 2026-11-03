import Matching.NestedWaitingCountLaw
import Mathlib.Algebra.BigOperators.Option

/-! An independent Poisson threshold can be treated as one additional arrival
type present in every set of a chain.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ]

theorem independentPoissons_augment_law (a : σ → ℝ≥0) (t : ℝ≥0) :
    Measure.map (fun p : (σ → ℕ) × ℕ => fun s : Option σ => s.elim p.2 p.1)
      ((independentPoissons a).prod (poissonMeasure t)) =
      independentPoissons (fun s : Option σ => s.elim t a) := by
  have h := Measure.pi_map_piOptionEquivProd (fun s : Option σ => poissonMeasure (s.elim t a))
  have hf : (fun p : (σ → ℕ) × ℕ => fun s : Option σ => s.elim p.2 p.1) =
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option σ => ℕ)).symm := by
    funext p s
    cases s <;> rfl
  rw [hf]
  simpa only [independentPoissons, Option.elim_none, Option.elim_some] using h

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

theorem nested_subset_waiting_threshold_law (A : Fin n → Finset ι) (hA : Monotone A)
    (F : Fin n → Finset σ) (hF : Monotone F) (a : σ → ℝ≥0) (t : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | ∀ k, (t : ℝ) + ∑ s ∈ F k, (a s : ℝ) < ∑ i ∈ A k, z i} =
      ((independentPoissons a).prod (poissonMeasure t)).real
        {p | ∀ k, p.2 + (∑ s ∈ F k, p.1 s) < (A k).card} := by
  have he := nested_subset_waiting_count_law A hA (fun k => (F k).insertNone)
    (Finset.insertNone.monotone.comp hF) (fun s : Option σ => s.elim t a)
  simp only [Finset.sum_insertNone, Option.elim_none, Option.elim_some, NNReal.coe_add, NNReal.coe_sum] at he
  have hp := congrArg (fun μ : Measure (Option σ → ℕ) => μ.real
    {x | ∀ k, (∑ s ∈ (F k).insertNone, x s) < (A k).card}) (independentPoissons_augment_law a t)
  dsimp only at hp
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at hp
  simp only [Set.preimage_setOf_eq, Finset.sum_insertNone, Option.elim_none, Option.elim_some] at hp
  exact he.trans hp.symm

end StochasticMatching
