import Matching.HistoryServiceAssembly
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Measurable transitions on a finite dependent tree of policy states. -/
open MeasureTheory Set
namespace StochasticMatching

theorem measurableEmbedding_sigma_injection {A : Type*} {B : A → Type*}
    [∀ a, MeasurableSpace (B a)] (a : A) : MeasurableEmbedding (Sigma.mk a : B a → Sigma B) := by
  classical
  refine ⟨fun _ _ h => by simpa using h, measurable_sigma_injection a, ?_⟩
  intro S hS
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro b
  change MeasurableSet ((Sigma.mk b) ⁻¹' (Sigma.mk a '' S))
  by_cases h : b = a
  · subst b
    have hi : Function.Injective (Sigma.mk a : B a → Sigma B) := fun _ _ h => by simpa using h
    rw [hi.preimage_image]
    exact hS
  · have he : (Sigma.mk b) ⁻¹' (Sigma.mk a '' S) = ∅ := by
      ext x
      simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false]
      rintro ⟨y, _, hy⟩
      exact h (congrArg Sigma.fst hy).symm
    rw [he]
    exact MeasurableSet.empty

theorem measurable_sigma_prod_elim {A : Type*} {B : A → Type*} {E C : Type*}
    [Countable A] [∀ a, MeasurableSpace (B a)] [MeasurableSpace E] [MeasurableSpace C]
    (f : (a : A) → B a × E → C) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun x : Sigma B × E => f x.1.1 (x.1.2, x.2)) := by
  intro S hS
  have he : (fun x : Sigma B × E => f x.1.1 (x.1.2, x.2)) ⁻¹' S =
      ⋃ a, (Prod.map (Sigma.mk a) id) '' ((f a) ⁻¹' S) := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨x.1.1, ⟨(x.1.2, x.2), hx, rfl⟩⟩
    · intro hx
      obtain ⟨a, y, hy, he⟩ := mem_iUnion.mp hx
      subst x
      exact hy
  rw [he]
  exact MeasurableSet.iUnion (fun a =>
    ((measurableEmbedding_sigma_injection a).prodMap MeasurableEmbedding.id).measurableSet_image' (hf a hS))

theorem measurable_prod_sum_elim {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (f : A × B → D) (g : A × C → D)
    (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun x : A × (B ⊕ C) => Sum.elim (fun b => f (x.1, b)) (fun c => g (x.1, c)) x.2) := by
  convert (hf.sumElim hg).comp (MeasurableEquiv.prodSumDistrib A B C).measurable using 1
  funext x
  rcases x with ⟨a, b | c⟩ <;> rfl

theorem measurable_sum_prod_elim {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (f : A × C → D) (g : B × C → D)
    (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun x : (A ⊕ B) × C => Sum.elim (fun a => f (a, x.2)) (fun b => g (b, x.2)) x.1) := by
  convert (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib A B C).measurable using 1
  funext x
  rcases x with ⟨a | b, c⟩ <;> rfl

end StochasticMatching
