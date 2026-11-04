import Matching.PoissonOnlineController
import Matching.MeasurableCursorBranches

open MeasureTheory Set
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem measurableSet_ControllerStepValid (N : σ → Finset ι)
    (T : H → ℝ) (hT : Measurable T) (A : H → Finset ι) (hA : Measurable A) (h : H) :
    MeasurableSet {y | ControllerStepValid N T A h y} := by
  have hterminal : Measurable (fun x : ControllerState H ι => x = .inl (A h)) := by
    have hm := (measurable_of_countable (fun B : Finset ι => B = A h)).sumElim
      (measurable_const : Measurable (fun _ : H => False))
    convert hm using 1
    funext x
    cases x <;> simp
  have hmark : Measurable (fun p : ℝ × (σ × Option ι) => ∀ i, p.2.2 = some i → i ∈ N p.2.1 ∩ A h) :=
    (measurable_of_countable (fun p : σ × Option ι => ∀ i, p.2 = some i → i ∈ N p.1 ∩ A h)).comp measurable_snd
  have hafter : Measurable (fun p : ℝ × (σ × Option ι) => unmatchedAfterMark (A h) p.2.2) :=
    (measurable_of_countable (unmatchedAfterMark (A h))).comp (measurable_snd.comp measurable_snd)
  have heq := measurable_of_countable (fun p : Finset ι × Finset ι => p.1 = p.2)
  have hupdate : Measurable (fun y : (ℝ × (σ × Option ι)) × ControllerState H ι =>
      match y.2 with
      | .inl B => B = unmatchedAfterMark (A h) y.1.2.2
      | .inr h' => A h' = unmatchedAfterMark (A h) y.1.2.2 ∧ T h' = T h - y.1.1) := by
    have hf : Measurable (fun y : (ℝ × (σ × Option ι)) × Finset ι =>
        y.2 = unmatchedAfterMark (A h) y.1.2.2) :=
      heq.comp (measurable_snd.prodMk (hafter.comp measurable_fst))
    have hg : Measurable (fun y : (ℝ × (σ × Option ι)) × H =>
        A y.2 = unmatchedAfterMark (A h) y.1.2.2 ∧ T y.2 = T h - y.1.1) :=
      (heq.comp ((hA.comp measurable_snd).prodMk (hafter.comp measurable_fst))).and
        (measurableSet_eq_fun (hT.comp measurable_snd)
          (measurable_const.sub (measurable_fst.comp measurable_fst))).mem
    convert measurable_prod_sum_elim _ _ hf hg using 1
    funext y
    rcases y with ⟨p, B | h'⟩ <;> rfl
  have hm : Measurable (ControllerStepValid N T A h) := by
    have hf : Measurable (fun y : Unit × ControllerState H ι => y.2 = .inl (A h)) :=
      hterminal.comp measurable_snd
    have hg := (hmark.comp measurable_fst).and hupdate
    convert measurable_sum_prod_elim _ _ hf hg using 1
    funext y
    rcases y with ⟨u | p, x⟩ <;> rfl
  exact hm.setOf

end StochasticMatching
