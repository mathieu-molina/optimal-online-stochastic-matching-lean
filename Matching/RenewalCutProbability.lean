import Matching.ExponentialPoissonTail

/-! The probability of exactly n renewals by a deterministic time: the nth
arrival has occurred but the next exponential waiting time has not ended.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

theorem exponentialSumLaw_add_reverse (n : ℕ) :
    Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
      ((exponentialSumLaw n).prod unitExponential) = exponentialSumLaw (n + 1) := by
  have h := congrArg (Measure.map (fun p : ℝ × ℝ => p.1 + p.2))
    (Measure.prod_swap (μ := exponentialSumLaw n) (ν := unitExponential))
  rw [Measure.map_map (measurable_fst.add measurable_snd) measurable_swap] at h
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, add_comm, exponentialSumLaw] using h

def renewalCut (t : ℝ) : Set (ℝ × ℝ) := {p | p.1 ≤ t ∧ t < p.1 + p.2}

theorem measurableSet_renewalCut (t : ℝ) : MeasurableSet (renewalCut t) :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))

theorem renewal_cut_probability (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((exponentialSumLaw n).prod unitExponential).real (renewalCut t) = poissonWeight t n := by
  let μ := (exponentialSumLaw n).prod unitExponential
  let A : Set (ℝ × ℝ) := {p | t < p.1 + p.2}
  let B : Set (ℝ × ℝ) := {p | t < p.1}
  have hB : MeasurableSet B := measurableSet_lt measurable_const measurable_fst
  have hpos : ∀ᵐ p ∂μ, 0 < p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
    exact Filter.Eventually.of_forall (fun _ => unitExponential_ae_pos)
  have hi : (A ∩ B : Set (ℝ × ℝ)) =ᵐ[μ] B := by
    filter_upwards [hpos] with p hp
    apply propext
    change ((t < p.1 + p.2 ∧ t < p.1) ↔ t < p.1)
    constructor
    · exact And.right
    · intro h
      exact ⟨by linarith, h⟩
  have hAprob : μ.real A = poissonLowerTail t (n + 1) := by
    have h := congrArg (fun ν : Measure ℝ => ν.real (Ioi t)) (exponentialSumLaw_add_reverse n)
    dsimp only at h
    rw [map_measureReal_apply (measurable_fst.add measurable_snd) measurableSet_Ioi,
      exponentialSumLaw_tail_eq_poissonLowerTail (n + 1) ht] at h
    exact h
  have hBprob : μ.real B = poissonLowerTail t n := by
    have he : B = Ioi t ×ˢ (Set.univ : Set ℝ) := by ext p; simp [B]
    rw [he, measureReal_prod_prod, measureReal_univ_eq_one, mul_one,
      exponentialSumLaw_tail_eq_poissonLowerTail n ht]
  have he : A \ B = renewalCut t := by
    ext p
    simp only [A, B, renewalCut, mem_diff, mem_setOf_eq, not_lt]
    exact and_comm
  have h := measureReal_diff_add_inter (μ := μ) (s := A) hB
  rw [he, measureReal_congr hi, hAprob, hBprob] at h
  simp only [poissonLowerTail, Finset.sum_range_succ] at h
  linarith

end StochasticMatching
