import Matching.TraceLength

/-! A measurable bounded payoff read directly from the recorded completion log. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {J : Type*} [MeasurableSpace J]

noncomputable def completionEntryReward : (Unit ⊕ (J × ℝ × ℝ)) → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

noncomputable def completionLogReward (n : ℕ) (L : CompletionLog J) : ℝ :=
  ∑ k ∈ Finset.range n, completionEntryReward (L k)

theorem measurable_completionEntryReward : Measurable (completionEntryReward (J := J)) :=
  measurable_const.sumElim measurable_const

theorem completionEntryReward_bounds (e : (Unit ⊕ (J × ℝ × ℝ))) :
    0 ≤ completionEntryReward e ∧ completionEntryReward e ≤ 1 := by
  cases e <;> norm_num [completionEntryReward]

theorem measurable_completionLogReward (n : ℕ) :
    Measurable (completionLogReward (J := J) n) := by
  apply Finset.measurable_sum
  intro k _
  exact measurable_completionEntryReward.comp (measurable_pi_apply k)

theorem completionLogReward_bounds (n : ℕ) (L : CompletionLog J) :
    0 ≤ completionLogReward n L ∧ completionLogReward n L ≤ n := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => (completionEntryReward_bounds (L k)).1)
  · calc
      completionLogReward n L ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => (completionEntryReward_bounds (L k)).2)
      _ = n := by simp

theorem integrable_completionLogReward (n : ℕ) (μ : Measure (CompletionLog J))
    [IsFiniteMeasure μ] : Integrable (completionLogReward n) μ := by
  apply (integrable_const (n : ℝ)).mono' (measurable_completionLogReward n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun L => by
    rw [Real.norm_of_nonneg (completionLogReward_bounds n L).1]
    exact (completionLogReward_bounds n L).2)

theorem completionLogReward_of_length {n m : ℕ} (L : CompletionLog J)
    (hL : LogLength m L) (hm : m ≤ n) : completionLogReward n L = m := by
  have he : ∀ k, completionEntryReward (L k) = if k < m then (1 : ℝ) else 0 := by
    intro k
    have hk := hL k
    cases h : L k with
    | inl u =>
      cases u
      have hmk : m ≤ k := hk.mp h
      simp [completionEntryReward, not_lt.mpr hmk]
    | inr e =>
      have hkm : k < m := lt_of_not_ge (fun hmk => by simpa [h] using hk.mpr hmk)
      simp [completionEntryReward, hkm]
  simp only [completionLogReward, he]
  rw [← Finset.sum_subset (Finset.range_mono hm)]
  · rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
    simp
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [not_lt.mpr hk]

namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem completionLogReward_eq_count (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) :
    completionLogReward (Fintype.card ι) (s.completionLog label x) = s.completionCount x :=
  completionLogReward_of_length _ (s.completionLog_length label x) (s.completionCount_le x)

end PosteriorStage
end StochasticMatching
