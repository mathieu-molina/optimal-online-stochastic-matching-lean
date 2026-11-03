import Matching.PathBounds
import Matching.ExpectedExecution

/-! The recursive completion count counts precisely the original coordinates
whose integrated service reaches their incoming demand by the deadline.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

noncomputable def completedServiceReward (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) : ℝ :=
  ∑ i, if cumulativePath n s label x (s.deadline x.1) (label i) = x.2 i then 1 else 0

theorem cumulativePath_terminal_survivor (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) {j : ι} (hw : x ∈ s.service.winner j) (i : {i : ι // i ≠ j}) :
    cumulativePath (n + 1) s label x (s.deadline x.1) (label i.1) =
      (s.service.curves x.1).service i.1 (s.service.clock j x) +
      cumulativePath n (s.next j) (fun i => label i.1) (s.service.observation j x)
        ((s.next j).deadline (s.service.observation j x).1) (label i.1) := by
  rw [cumulativePath_restart n s label hP0 hPc hPcompact hPdown hmem x hw
    (t := s.deadline x.1) hw.1.le]
  simp only [Pi.add_apply, labelLift_at_label label hinj]
  have hd := s.next_deadline_on_winner hw
  change (s.next j).deadline (s.service.observation j x).1 = _ at hd
  rw [hd]

theorem completedServiceReward_eq_count (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) (hx : GoodExecution n s x) :
    completedServiceReward n s label x =
      (AdaptivePlan.run (E := ℕ) (countPlan n s 0) x : ℝ) := by
  classical
  induction n generalizing H ι with
  | zero =>
    have hz : ∀ i, (0 : ℝ) ≠ x.2 i := fun i => ne_of_lt (hx i)
    simp [completedServiceReward, cumulativePath, ratePath, hz, countPlan, AdaptivePlan.run]
  | succ n ih =>
    rcases hx with ⟨hp, hterm | ⟨j, hj, hchild⟩⟩
    · rw [AdaptivePlan.run_of_terminal (countPlan (n + 1) s 0) hterm]
      simp only [countPlan, Nat.cast_zero]
      change completedServiceReward (n + 1) s label x = 0
      unfold completedServiceReward
      apply Finset.sum_eq_zero
      intro i _
      have hs := cumulativePath_first_segment n s label x (s.deadline_pos x.1).le
        (le_of_eq (s.stopClock_terminal x hterm).symm)
      rw [hs, labelLift_at_label label hinj]
      exact if_neg (ne_of_lt (hterm i))
    · let f : ι → ℝ := fun i =>
        if cumulativePath (n + 1) s label x (s.deadline x.1) (label i) = x.2 i then 1 else 0
      have heq (i : {i : ι // i ≠ j}) :
          (cumulativePath (n + 1) s label x (s.deadline x.1) (label i.1) = x.2 i.1) ↔
          (cumulativePath n (s.next j) (fun i => label i.1) (s.service.observation j x)
            ((s.next j).deadline (s.service.observation j x).1) (label i.1) =
              (s.service.observation j x).2 i) := by
        rw [cumulativePath_terminal_survivor n s label hinj hP0 hPc hPcompact hPdown hmem x hj i]
        change _ + _ = x.2 i.1 ↔ _ =
          x.2 i.1 - (s.service.curves x.1).service i.1 (s.service.clock j x)
        constructor <;> intro h <;> linarith
      have hsub : (∑ i : {i : ι // i ≠ j}, f i.1) =
          completedServiceReward n (s.next j) (fun i => label i.1) (s.service.observation j x) := by
        unfold completedServiceReward
        apply Finset.sum_congr rfl
        intro i _
        simp only [f, heq i]
      have hwin : f j = 1 := by
        dsimp only [f]
        rw [cumulativePath_at_completed_winner n s label hinj hP0 hPc hPcompact hPdown hmem
          x hj (hp j) (t := s.deadline x.1) hj.1.le]
        exact if_pos rfl
      have hs : (∑ i : {i : ι // i ≠ j}, f i.1) = ∑ i ∈ Finset.univ.erase j, f i :=
        (Finset.sum_subtype (Finset.univ.erase j) (by simp) f).symm
      have hsum := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ j)
      rw [← hs, hsub, hwin] at hsum
      change _ = completedServiceReward (n + 1) s label x at hsum
      rw [← hsum]
      rw [ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective)
        (s.next_feasibleAllocation label hPdown hmem j) (s.service.observation j x) hchild]
      rw [AdaptivePlan.run_of_winner (countPlan (n + 1) s 0) hj]
      change _ = (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) 1)
        (s.service.observation j x) : ℝ)
      rw [countPlan_offset n (s.next j) 1, Nat.cast_add, Nat.cast_one]
      ring

theorem completedServiceReward_eq_completionCount_ae (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) :
    completedServiceReward (Fintype.card ι) s label =ᵐ[ν.prod independentExponentials]
      fun x => (s.completionCount x : ℝ) := by
  filter_upwards [goodExecution_ae (Fintype.card ι) s ν] with x hx
  exact completedServiceReward_eq_count (Fintype.card ι) s label hinj
    hP0 hPc hPcompact hPdown hmem x hx

end StochasticMatching.PosteriorStage
