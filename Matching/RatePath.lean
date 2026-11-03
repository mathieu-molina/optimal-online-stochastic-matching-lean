import Matching.LabelFeasibility
import Matching.MeasurableBranching

/-! A jointly measurable rate path on the original demand sample, with fixed
original job labels. It follows the actual first-completion branches and
restarts at the remaining relative time. Feasibility holds at every query.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {J : Type w} [Fintype J] [DecidableEq J]

variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

def queryWinner (s : PosteriorStage H ι) (j : ι) : Set (ℝ × (H × (ι → ℝ))) :=
  {q | q.2 ∈ s.service.winner j}

theorem queryWinner_disjoint (s : PosteriorStage H ι) :
    Pairwise (fun i j => Disjoint (s.queryWinner i) (s.queryWinner j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro q hi hj
  exact Set.disjoint_left.mp (s.service.winner_disjoint hij) hi hj

theorem measurable_queryWinner (s : PosteriorStage H ι) (j : ι) : MeasurableSet (s.queryWinner j) :=
  (s.service.measurable_winner j).preimage measurable_snd

noncomputable def currentRate (s : PosteriorStage H ι) (label : ι → J)
    (q : ℝ × (H × (ι → ℝ))) : J → ℝ :=
  labelLift label (fun i => (s.service.curves q.2.1).rate i q.1)

theorem measurable_currentRate (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.currentRate label) := by
  apply (labelLift label).continuous.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact (s.service.measurable_rate i).comp
    ((measurable_fst.comp measurable_snd).prodMk measurable_fst)

noncomputable def ratePath : (n : ℕ) → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    PosteriorStage H ι → (ι → J) → ℝ × (H × (ι → ℝ)) → (J → ℝ)
  | 0, _, _, _, _, _, _, _, _ => 0
  | n + 1, _, _, _, _, _, s, label, q =>
      if 0 ≤ q.1 ∧ q.1 < s.deadline q.2.1 then
        branchSelect s.queryWinner
          (fun j q => if q.1 < s.service.clock j q.2 then s.currentRate label q else
            ratePath n (s.next j) (fun i => label i.1)
              (q.1 - s.service.clock j q.2, s.service.observation j q.2))
          (s.currentRate label) q
      else 0

theorem measurable_ratePath (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (ratePath n s label) := by
  induction n generalizing H ι with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.ite
      ((measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst (s.measurable_deadline.comp (measurable_fst.comp measurable_snd))))
    · apply measurable_branchSelect s.queryWinner_disjoint s.measurable_queryWinner
      · intro j
        apply Measurable.ite
          (measurableSet_lt measurable_fst ((s.service.measurable_clock j).comp measurable_snd))
          (s.measurable_currentRate label)
        apply (ih (s.next j) (fun i => label i.1)).comp
        exact (measurable_fst.sub ((s.service.measurable_clock j).comp measurable_snd)).prodMk
          ((s.service.measurable_observation j).comp measurable_snd)
      · exact s.measurable_currentRate label
    · exact measurable_const

theorem ratePath_feasible (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P) (hPclosed : IsClosed P)
    (hPdown : NonnegDownwardClosed P) (hmem : s.data.FeasibleAllocation label P)
    (q : ℝ × (H × (ι → ℝ))) : ratePath n s label q ∈ P := by
  induction n generalizing H ι with
  | zero => exact hP0
  | succ n ih =>
    classical
    change (if 0 ≤ q.1 ∧ q.1 < s.deadline q.2.1 then
      branchSelect s.queryWinner _ _ q else 0) ∈ P
    split_ifs with htime
    · by_cases hw : ∃ j, q ∈ s.queryWinner j
      · obtain ⟨j, hj⟩ := hw
        rw [branchSelect_of_mem s.queryWinner_disjoint _ _ hj]
        change (if q.1 < s.service.clock j q.2 then s.currentRate label q else
          ratePath n (s.next j) (fun i => label i.1)
            (q.1 - s.service.clock j q.2, s.service.observation j q.2)) ∈ P
        split_ifs
        · exact s.lifted_rate_mem label hPc hPclosed hmem q.2.1 q.1
        · exact ih (s.next j) (fun i => label i.1)
            (s.next_feasibleAllocation label hPdown hmem j) _
      · rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
        exact s.lifted_rate_mem label hPc hPclosed hmem q.2.1 q.1
    · exact hP0

theorem ratePath_zero_off_labels (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (q : ℝ × (H × (ι → ℝ))) (a : J) (ha : ∀ i, label i ≠ a) :
    ratePath n s label q a = 0 := by
  induction n generalizing H ι with
  | zero => rfl
  | succ n ih =>
    classical
    change (if 0 ≤ q.1 ∧ q.1 < s.deadline q.2.1 then
      branchSelect (E := J → ℝ) s.queryWinner _ _ q else 0) a = 0
    split_ifs with htime
    · by_cases hw : ∃ j, q ∈ s.queryWinner j
      · obtain ⟨j, hj⟩ := hw
        rw [branchSelect_of_mem s.queryWinner_disjoint _ _ hj]
        change (if q.1 < s.service.clock j q.2 then s.currentRate label q else
          ratePath n (s.next j) (fun i => label i.1)
            (q.1 - s.service.clock j q.2, s.service.observation j q.2)) a = 0
        split_ifs
        · exact labelLift_off_labels label _ ha
        · exact ih (s.next j) (fun i => label i.1) _ (fun i => ha i.1)
      · rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
        exact labelLift_off_labels label _ ha
    · rfl

theorem restarted_rate_zero_at_winner (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (j : ι)
    (q : ℝ × ((H × ℝ) × ({i : ι // i ≠ j} → ℝ))) :
    ratePath n (s.next j) (fun i => label i.1) q (label j) = 0 := by
  apply ratePath_zero_off_labels
  intro i hi
  exact i.2 (hinj hi)

end StochasticMatching.PosteriorStage
