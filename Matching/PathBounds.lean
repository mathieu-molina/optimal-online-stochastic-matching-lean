import Matching.PathRestart
import Matching.GoodExecution

/-! On every valid recursive execution, integrated service is nonnegative
and never exceeds the incoming residual demand, at every time in the horizon.
These are pathwise statements; validity has already been proved almost surely.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem stopClock_terminal (s : PosteriorStage H ι) (x : H × (ι → ℝ))
    (hx : x ∈ s.service.terminalEvent) : s.service.stopClock x = s.deadline x.1 := by
  rw [s.service.stopClock_eq]
  exact (s.service.curves x.1).stopClock_terminal (mem_univ_pi.mpr hx)

theorem service_le_demand_before_stop (s : PosteriorStage H ι) (x : H × (ι → ℝ))
    (hz : ∀ i, 0 < x.2 i)
    (hx : x ∈ s.service.terminalEvent ∨ ∃ j, x ∈ s.service.winner j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s.service.stopClock x) (i : ι) :
    (s.service.curves x.1).service i t ≤ x.2 i := by
  have htD : t ≤ (s.service.curves x.1).deadline :=
    ht.trans (s.service.stopClock_bounds x).2
  have hm := (s.service.curves x.1).service_monotone i ⟨ht0, htD⟩
    (s.service.stopClock_bounds x) ht
  apply hm.trans
  rcases hx with hterm | ⟨j, hj⟩
  · rw [s.stopClock_terminal x hterm]
    exact (hterm i).le
  · rw [s.service.stopClock_winner hj]
    by_cases hij : i = j
    · subst i
      exact ((s.service.curves x.1).winner_service_eq (hz j) hj).le
    · exact ((s.service.curves x.1).winner_other_service_lt hj hij).le

theorem cumulativePath_bounds (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) (hx : GoodExecution n s x)
    {t : ℝ} (ht0 : 0 ≤ t) (htD : t ≤ s.deadline x.1) (i : ι) :
    0 ≤ cumulativePath n s label x t (label i) ∧
      cumulativePath n s label x t (label i) ≤ x.2 i := by
  induction n generalizing H ι t with
  | zero =>
    have hz : 0 ≤ x.2 i := (hx i).le
    simpa only [cumulativePath, ratePath, intervalIntegral.integral_zero, Pi.zero_apply] using
      And.intro (le_refl (0 : ℝ)) hz
  | succ n ih =>
    have hp := hx.1
    by_cases hstop : t ≤ s.service.stopClock x
    · rw [cumulativePath_first_segment n s label x ht0 hstop,
        labelLift_at_label label hinj]
      refine ⟨(s.service.curves x.1).service_nonneg ⟨ht0, htD⟩ i, ?_⟩
      apply s.service_le_demand_before_stop x hp _ ht0 hstop i
      rcases hx.2 with hterm | ⟨j, hj, _⟩
      · exact Or.inl hterm
      · exact Or.inr ⟨j, hj⟩
    · have hafter : s.service.stopClock x ≤ t := le_of_lt (lt_of_not_ge hstop)
      rcases hx.2 with hterm | ⟨j, hj, hnext⟩
      · exact False.elim (hstop (by simpa only [s.stopClock_terminal x hterm] using htD))
      · rw [s.service.stopClock_winner hj] at hafter
        by_cases hij : i = j
        · subst i
          rw [cumulativePath_at_completed_winner n s label hinj hP0 hPc hPcompact hPdown hmem
            x hj (hp j) hafter]
          exact ⟨(hp j).le, le_refl _⟩
        · let a : {i : ι // i ≠ j} := ⟨i, hij⟩
          have hiLabel : Function.Injective (fun i : {i : ι // i ≠ j} => label i.1) :=
            hinj.comp Subtype.val_injective
          have htime : t - s.service.clock j x ≤
              (s.next j).deadline (s.service.observation j x).1 := by
            change t - s.service.clock j x ≤ (s.next j).deadline (x.1, s.service.clock j x)
            rw [s.next_deadline_on_winner hj]
            exact sub_le_sub_right htD _
          have hchild := ih (s.next j) (fun i => label i.1) hiLabel
            (s.next_feasibleAllocation label hPdown hmem j) (s.service.observation j x) hnext
            (sub_nonneg.mpr hafter) htime a
          rw [cumulativePath_restart n s label hP0 hPc hPcompact hPdown hmem x hj hafter]
          simp only [Pi.add_apply, labelLift_at_label label hinj]
          have hc : s.service.clock j x ∈ Icc 0 (s.service.curves x.1).deadline := by
            rw [← s.service.stopClock_winner hj]
            exact s.service.stopClock_bounds x
          have hs := (s.service.curves x.1).service_nonneg hc i
          change 0 ≤ cumulativePath n (s.next j) (fun i => label i.1)
            (s.service.observation j x) (t - s.service.clock j x) (label i) ∧
            cumulativePath n (s.next j) (fun i => label i.1)
              (s.service.observation j x) (t - s.service.clock j x) (label i) ≤
                x.2 i - (s.service.curves x.1).service i (s.service.clock j x) at hchild
          constructor <;> linarith [hchild.1, hchild.2]

theorem cumulativePath_bounds_ae (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ t ∈ Icc 0 (s.deadline x.1), ∀ i,
      0 ≤ cumulativePath n s label x t (label i) ∧
        cumulativePath n s label x t (label i) ≤ x.2 i := by
  filter_upwards [goodExecution_ae n s ν] with x hx
  intro t ht i
  exact cumulativePath_bounds n s label hinj hP0 hPc hPcompact hPdown hmem x hx ht.1 ht.2 i

end StochasticMatching.PosteriorStage
