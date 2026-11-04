import Matching.StageExpectation
import Matching.ExpectedExecution

/-! An exact global decomposition for the concrete adaptive completion count.
The accumulated defect is recursively assembled from actual marked-history
laws. No local conditional identity or Dynkin formula is assumed here.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
universe u v

noncomputable def totalDefect : (n : ℕ) → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    (s : PosteriorStage H ι) → (H → ℝ) → Measure H → ℝ
  | 0, _, _, _, _, _, _, _, _ => 0
  | n + 1, _, _, _, _, _, s, elapsed, ν =>
      (∫ h, s.defect elapsed h ∂ν) +
        ∑ j, totalDefect n (s.next j) (fun h => elapsed h.1 + h.2)
          (s.service.markedHistoryMeasure ν j)

variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem countPlan_one_plus_integral (n : ℕ) (s : PosteriorStage H ι)
    (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, (1 + (AdaptivePlan.run (E := ℕ) (countPlan n s 0) x : ℝ))
      ∂ν.prod independentExponentials) =
    (∫ _ : H, (1 : ℝ) ∂ν) +
      ∫ x, (AdaptivePlan.run (E := ℕ) (countPlan n s 0) x : ℝ) ∂ν.prod independentExponentials := by
  rw [integral_add (integrable_const 1) (integrable_countPlan n s 0 _)]
  congr 1
  simpa only [measureReal_univ_eq_one, one_smul] using
    (integral_fun_fst (μ := ν) (ν := independentExponentials (ι := ι)) (fun _ : H => (1 : ℝ)))

theorem countPlan_expected_eq_potential_sub_defect (n : ℕ) (s : PosteriorStage H ι)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (hn : Fintype.card ι ≤ n) :
    (∫ x, (AdaptivePlan.run (E := ℕ) (countPlan n s 0) x : ℝ) ∂ν.prod independentExponentials) =
      (∫ h, s.potential R.elapsed h ∂ν) - totalDefect n s R.elapsed ν := by
  induction n generalizing H ι with
  | zero =>
    letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
    simp [countPlan, AdaptivePlan.run, potential, totalDefect]
  | succ n ih =>
    have hlocal := s.potential_defect_recursion R ν hν
    have hchild : ∀ j,
        (∫ x, (1 + (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) 0) x : ℝ))
          ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials) =
        (∫ h, 1 + (s.next j).potential (R.next j).elapsed h
          ∂s.service.markedHistoryMeasure ν j) -
        totalDefect n (s.next j) (R.next j).elapsed (s.service.markedHistoryMeasure ν j) := by
      intro j
      letI := s.service.finite_markedHistoryMeasure ν j
      have hmem := R.next_concentrated ν hν j
      have hn' : Fintype.card {i : ι // i ≠ j} ≤ n := by
        have hc := survivor_card j
        omega
      rw [countPlan_one_plus_integral,
        ih (s.next j) (R.next j) (s.service.markedHistoryMeasure ν j) hmem hn',
        integral_add (integrable_const 1)
          ((s.next j).integrable_potential (R.next j) (s.service.markedHistoryMeasure ν j) hmem)]
      ring
    rw [countPlan_expected_completions]
    simp_rw [hchild]
    rw [Finset.sum_sub_distrib]
    change _ = (∫ h, s.potential R.elapsed h ∂ν) -
      ((∫ h, s.defect R.elapsed h ∂ν) +
        ∑ j, totalDefect n (s.next j) (R.next j).elapsed (s.service.markedHistoryMeasure ν j))
    linarith

theorem totalDefect_nonneg (n : ℕ) (s : PosteriorStage H ι)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) : 0 ≤ totalDefect n s R.elapsed ν := by
  induction n generalizing H ι with
  | zero => exact le_refl 0
  | succ n ih =>
    change 0 ≤ (∫ h, s.defect R.elapsed h ∂ν) +
      ∑ j, totalDefect n (s.next j) (R.next j).elapsed (s.service.markedHistoryMeasure ν j)
    apply add_nonneg
    · apply integral_nonneg_of_ae
      filter_upwards [hν] with h hh
      exact (s.defect_bounds R hh).1
    · apply Finset.sum_nonneg
      intro j _
      letI := s.service.finite_markedHistoryMeasure ν j
      exact ih (s.next j) (R.next j) (s.service.markedHistoryMeasure ν j)
        (R.next_concentrated ν hν j)

theorem completionCount_expected_eq_potential_sub_defect (s : PosteriorStage H ι)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ x, (s.completionCount x : ℝ) ∂ν.prod independentExponentials) =
      (∫ h, s.potential R.elapsed h ∂ν) - totalDefect (Fintype.card ι) s R.elapsed ν :=
  countPlan_expected_eq_potential_sub_defect (Fintype.card ι) s R ν hν (le_refl _)

theorem completionCount_expected_le_potential (s : PosteriorStage H ι)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ x, (s.completionCount x : ℝ) ∂ν.prod independentExponentials) ≤
      ∫ h, s.potential R.elapsed h ∂ν := by
  rw [completionCount_expected_eq_potential_sub_defect s R ν hν]
  exact sub_le_self _ (totalDefect_nonneg (Fintype.card ι) s R ν hν)

end StochasticMatching.PosteriorStage
