import Matching.RateIntegral

/-! Exact concatenation of the integrated service path across an actual
completion. The restarted path has no rate or service at the removed label.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem ratePath_outside (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) {t : ℝ} (ht : ¬ (0 ≤ t ∧ t < s.deadline x.1)) :
    ratePath n s label (t, x) = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact if_neg ht

theorem ratePath_restart (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) {j : ι} (hw : x ∈ s.service.winner j)
    {t : ℝ} (ht : s.service.clock j x ≤ t) :
    ratePath (n + 1) s label (t, x) =
      ratePath n (s.next j) (fun i => label i.1)
        (t - s.service.clock j x, s.service.observation j x) := by
  classical
  have hc : 0 ≤ s.service.clock j x := by
    rw [← s.service.stopClock_winner hw]
    exact (s.service.stopClock_bounds x).1
  by_cases hD : t < s.deadline x.1
  · change (if 0 ≤ t ∧ t < s.deadline x.1 then
      branchSelect s.queryWinner _ _ (t, x) else 0) = _
    rw [if_pos ⟨hc.trans ht, hD⟩]
    have hq : (t, x) ∈ s.queryWinner j := hw
    rw [branchSelect_of_mem s.queryWinner_disjoint _ _ hq]
    exact if_neg (not_lt.mpr ht)
  · rw [ratePath_outside (n + 1) s label x (fun h => hD h.2)]
    symm
    apply ratePath_outside
    intro h
    have hd := s.next_deadline_on_winner hw
    change (s.next j).deadline (s.service.observation j x).1 = _ at hd
    rw [hd] at h
    exact hD (by linarith [h.2])

theorem cumulativePath_restart (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) {j : ι} (hw : x ∈ s.service.winner j)
    {t : ℝ} (ht : s.service.clock j x ≤ t) :
    cumulativePath (n + 1) s label x t =
      labelLift label (fun i => (s.service.curves x.1).service i (s.service.clock j x)) +
      cumulativePath n (s.next j) (fun i => label i.1) (s.service.observation j x)
        (t - s.service.clock j x) := by
  let c := s.service.clock j x
  have hc : 0 ≤ c := by
    dsimp only [c]
    rw [← s.service.stopClock_winner hw]
    exact (s.service.stopClock_bounds x).1
  have hfirst := cumulativePath_first_segment n s label x hc
    (le_of_eq (s.service.stopClock_winner hw).symm)
  have hi := ratePath_intervalIntegrable (n + 1) s label hP0 hPc hPcompact hPdown hmem x
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c t)
  change cumulativePath (n + 1) s label x c +
    (∫ u in c..t, ratePath (n + 1) s label (u, x)) =
    cumulativePath (n + 1) s label x t at hsplit
  rw [← hsplit, hfirst]
  congr 1
  calc
    _ = ∫ u in c..t, ratePath n (s.next j) (fun i => label i.1)
        (u - c, s.service.observation j x) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hcu : c ≤ u := by
        have hct : c ≤ t := ht
        rw [uIcc_of_le hct] at hu
        exact hu.1
      exact ratePath_restart n s label x hw hcu
    _ = _ := by
      simpa only [sub_self, cumulativePath, c] using
        (intervalIntegral.integral_comp_sub_right
          (fun u => ratePath n (s.next j) (fun i => label i.1) (u, s.service.observation j x))
          (a := c) (b := t) c)

theorem cumulativePath_zero_off_labels (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) (t : ℝ) (a : J) (ha : ∀ i, label i ≠ a) :
    cumulativePath n s label x t a = 0 := by
  have hi := ratePath_intervalIntegrable n s label hP0 hPc hPcompact hPdown hmem x 0 t
  have hp := (ContinuousLinearMap.proj a : (J → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.proj_apply] at hp
  change (∫ u in (0 : ℝ)..t, ratePath n s label (u, x)) a = 0
  rw [← hp]
  have hz : (fun u : ℝ => ratePath n s label (u, x) a) = fun _ => 0 := by
    funext u
    exact ratePath_zero_off_labels n s label (u, x) a ha
  rw [hz]
  simp

theorem cumulativePath_at_completed_winner (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) {j : ι} (hw : x ∈ s.service.winner j) (hz : 0 < x.2 j)
    {t : ℝ} (ht : s.service.clock j x ≤ t) :
    cumulativePath (n + 1) s label x t (label j) = x.2 j := by
  rw [cumulativePath_restart n s label hP0 hPc hPcompact hPdown hmem x hw ht]
  simp only [Pi.add_apply, labelLift_at_label label hinj]
  rw [cumulativePath_zero_off_labels n (s.next j) (fun i => label i.1)
    hP0 hPc hPcompact hPdown (s.next_feasibleAllocation label hPdown hmem j)
    (s.service.observation j x) (t - s.service.clock j x) (label j)
    (fun i h => i.2 (hinj h)), add_zero]
  exact (s.service.curves x.1).winner_service_eq hz hw

end StochasticMatching.PosteriorStage
