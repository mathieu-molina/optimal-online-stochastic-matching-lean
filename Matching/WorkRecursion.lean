import Matching.HistorySegmentWork
import Matching.PathCount
import Matching.PathRegularity

/-! The terminal work of the concrete integrated rate path splits into actual
first-segment work and the work performed by its selected restart branch.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

noncomputable def terminalWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) : ℝ :=
  ∑ i, cumulativePath n s label x (s.deadline x.1) (label i)

noncomputable def futureWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) : ℝ :=
  branchSelect s.service.winner
    (fun j x => terminalWork n (s.next j) (fun i => label i.1) (s.service.observation j x))
    (fun _ => 0) x

theorem measurable_terminalService (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (fun x : H × (ι → ℝ) => cumulativePath n s label x (s.deadline x.1)) := by
  have hg : Measurable (fun x : H × (ι → ℝ) => (s.deadline x.1, x)) :=
    (s.measurable_deadline.comp measurable_fst).prodMk measurable_id
  have hc := (measurable_cumulativePath n s label).comp hg
  exact hc

theorem measurable_terminalWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (terminalWork n s label) := by
  unfold terminalWork
  apply Finset.measurable_sum
  intro i _
  have hc := (measurable_pi_apply (label i)).comp (measurable_terminalService n s label)
  exact hc

theorem measurable_futureWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (futureWork n s label) :=
  measurable_branchSelect s.service.winner_disjoint s.service.measurable_winner
    (fun j => (measurable_terminalWork n (s.next j) (fun i => label i.1)).comp
      (s.service.measurable_observation j)) measurable_const

theorem terminalWork_step (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (x : H × (ι → ℝ)) (hx : GoodExecution (n + 1) s x) :
    terminalWork (n + 1) s label x = (∑ i, s.stoppedWork i x) + futureWork n s label x := by
  classical
  rcases hx.2 with hterm | ⟨j, hj, _⟩
  · have hf : futureWork n s label x = 0 := by
      apply branchSelect_of_not_mem
      intro j hj
      exact Set.disjoint_left.mp (s.service.winner_disjoint_terminal j) hterm hj
    rw [hf, add_zero]
    unfold terminalWork stoppedWork
    rw [s.stopClock_terminal x hterm,
      cumulativePath_first_segment n s label x (s.deadline_pos x.1).le
        (le_of_eq (s.stopClock_terminal x hterm).symm)]
    simp only [labelLift_at_label label hinj]
  · have hf : futureWork n s label x =
        terminalWork n (s.next j) (fun i => label i.1) (s.service.observation j x) :=
      branchSelect_of_mem s.service.winner_disjoint _ _ hj
    rw [hf]
    unfold terminalWork
    rw [cumulativePath_restart n s label hP0 hPc hPcompact hPdown hmem x hj
      (t := s.deadline x.1) hj.1.le]
    simp only [Pi.add_apply, labelLift_at_label label hinj]
    rw [Finset.sum_add_distrib]
    have hd := s.next_deadline_on_winner hj
    change (s.next j).deadline (s.service.observation j x).1 = _ at hd
    rw [← hd]
    congr 1
    · unfold stoppedWork
      rw [s.service.stopClock_winner hj]
    · let f : ι → ℝ := fun i => cumulativePath n (s.next j) (fun i => label i.1)
        (s.service.observation j x) ((s.next j).deadline (s.service.observation j x).1) (label i)
      have hz : f j = 0 := cumulativePath_zero_off_labels n (s.next j) (fun i => label i.1)
        hP0 hPc hPcompact hPdown (s.next_feasibleAllocation label hPdown hmem j)
        (s.service.observation j x) _ (label j) (fun i h => i.2 (hinj h))
      have hs : (∑ i : {i : ι // i ≠ j}, f i.1) = ∑ i ∈ Finset.univ.erase j, f i :=
        (Finset.sum_subtype (Finset.univ.erase j) (by simp) f).symm
      have hsum := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ j)
      rw [← hs, hz, add_zero] at hsum
      exact hsum.symm

theorem integrable_terminalWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] :
    Integrable (terminalWork n s label) (ν.prod independentExponentials) := by
  unfold terminalWork
  apply integrable_finset_sum
  intro i _
  have hi : Integrable (fun x : H × (ι → ℝ) => x.2 i) (ν.prod independentExponentials) := by
    simpa only [Pi.zero_apply, zero_add] using
      integrable_history_demand ν (fun _ => (0 : ι → ℝ)) i (integrable_const 0)
  have hm := (measurable_pi_apply (label i)).comp (measurable_terminalService n s label)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [goodExecution_ae n s ν] with x hx
  have hb := cumulativePath_bounds n s label hinj hP0 hPc hPcompact hPdown hmem x hx
    (t := s.deadline x.1) (s.deadline_pos x.1).le (le_refl _) i
  change ‖cumulativePath n s label x (s.deadline x.1) (label i)‖ ≤ x.2 i
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

theorem integrable_futureWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] :
    Integrable (futureWork n s label) (ν.prod independentExponentials) := by
  have hs : Integrable (fun x => ∑ i, s.stoppedWork i x) (ν.prod independentExponentials) :=
    integrable_finset_sum _ (fun i _ => s.integrable_stoppedWork i _)
  apply ((integrable_terminalWork (n + 1) s label hinj hP0 hPc hPcompact hPdown hmem ν).sub hs).congr
  filter_upwards [goodExecution_ae (n + 1) s ν] with x hx
  have he := terminalWork_step n s label hinj hP0 hPc hPcompact hPdown hmem x hx
  change terminalWork (n + 1) s label x - (∑ i, s.stoppedWork i x) = futureWork n s label x
  linarith

end StochasticMatching.PosteriorStage
