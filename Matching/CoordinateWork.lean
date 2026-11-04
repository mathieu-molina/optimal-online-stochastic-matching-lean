import Matching.WorkRecursion

/-! Expected terminal service of one tagged active job, with exact restart
recursion. The tagged job's own first completion contributes its probability;
every other first completion passes its service calculation to the child.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

noncomputable def coordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) (i : ι)
    (x : H × (ι → ℝ)) : ℝ := cumulativePath n s label x (s.deadline x.1) (label i)

noncomputable def childCoordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) (i j : ι)
    (x : (H × ℝ) × ({k : ι // k ≠ j} → ℝ)) : ℝ :=
  if hij : i ≠ j then coordinateWork n (s.next j) (fun k => label k.1) ⟨i, hij⟩ x else 0

noncomputable def nextCoordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) (i j : ι)
    (x : (H × ℝ) × ({k : ι // k ≠ j} → ℝ)) : ℝ :=
  if hij : i ≠ j then coordinateWork n (s.next j) (fun k => label k.1) ⟨i, hij⟩ x else 1

noncomputable def futureCoordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) (i : ι)
    (x : H × (ι → ℝ)) : ℝ :=
  branchSelect s.service.winner
    (fun j x => childCoordinateWork n s label i j (s.service.observation j x)) (fun _ => 0) x

theorem measurable_coordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) (i : ι) :
    Measurable (coordinateWork n s label i) := by
  have h := (measurable_pi_apply (label i)).comp (measurable_terminalService n s label)
  exact h

theorem measurable_childCoordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) (i j : ι) :
    Measurable (childCoordinateWork n s label i j) := by
  unfold childCoordinateWork
  split_ifs
  · exact measurable_coordinateWork n (s.next j) _ _
  · exact measurable_const

theorem integrable_coordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    Integrable (coordinateWork n s label i) (ν.prod independentExponentials) := by
  have hi : Integrable (fun x : H × (ι → ℝ) => x.2 i) (ν.prod independentExponentials) := by
    simpa only [Pi.zero_apply, zero_add] using
      integrable_history_demand ν (fun _ => (0 : ι → ℝ)) i (integrable_const 0)
  apply hi.mono' (measurable_coordinateWork n s label i).aestronglyMeasurable
  filter_upwards [goodExecution_ae n s ν] with x hx
  have hb := cumulativePath_bounds n s label hinj hP0 hPc hPcompact hPdown hmem x hx
    (t := s.deadline x.1) (s.deadline_pos x.1).le (le_refl _) i
  change ‖cumulativePath n s label x (s.deadline x.1) (label i)‖ ≤ x.2 i
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

theorem coordinateWork_step (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (i : ι)
    (x : H × (ι → ℝ)) (hx : GoodExecution (n + 1) s x) :
    coordinateWork (n + 1) s label i x = s.stoppedWork i x + futureCoordinateWork n s label i x := by
  rcases hx.2 with hterm | ⟨j, hj, _⟩
  · have hf : futureCoordinateWork n s label i x = 0 := by
      apply branchSelect_of_not_mem
      intro j hj
      exact Set.disjoint_left.mp (s.service.winner_disjoint_terminal j) hterm hj
    rw [hf, add_zero]
    unfold coordinateWork stoppedWork
    rw [s.stopClock_terminal x hterm,
      cumulativePath_first_segment n s label x (s.deadline_pos x.1).le
        (le_of_eq (s.stopClock_terminal x hterm).symm), labelLift_at_label label hinj]
  · have hf : futureCoordinateWork n s label i x =
        childCoordinateWork n s label i j (s.service.observation j x) :=
      branchSelect_of_mem s.service.winner_disjoint _ _ hj
    rw [hf]
    unfold coordinateWork stoppedWork
    rw [cumulativePath_restart n s label hP0 hPc hPcompact hPdown hmem x hj
      (t := s.deadline x.1) hj.1.le, Pi.add_apply, labelLift_at_label label hinj,
      s.service.stopClock_winner hj]
    congr 1
    have hd := s.next_deadline_on_winner hj
    change (s.next j).deadline (s.service.observation j x).1 = _ at hd
    rw [← hd]
    unfold childCoordinateWork
    split_ifs with hij
    · rfl
    · have he : i = j := not_ne_iff.mp hij
      subst i
      exact cumulativePath_zero_off_labels n (s.next j) (fun k => label k.1)
        hP0 hPc hPcompact hPdown (s.next_feasibleAllocation label hPdown hmem j)
        (s.service.observation j x) _ (label j) (fun k h => k.2 (hinj h))

theorem integrable_futureCoordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    Integrable (futureCoordinateWork n s label i) (ν.prod independentExponentials) := by
  apply ((integrable_coordinateWork (n + 1) s label hinj hP0 hPc hPcompact hPdown hmem ν i).sub
    (s.integrable_stoppedWork i _)).congr
  filter_upwards [goodExecution_ae (n + 1) s ν] with x hx
  have he := coordinateWork_step n s label hinj hP0 hPc hPcompact hPdown hmem i x hx
  change coordinateWork (n + 1) s label i x - s.stoppedWork i x = futureCoordinateWork n s label i x
  linarith

theorem futureCoordinateWork_winner_integral (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (ν : Measure H) (i j : ι) :
    (∫ x in s.service.winner j, futureCoordinateWork n s label i x ∂ν.prod independentExponentials) =
      ∫ x, childCoordinateWork n s label i j x
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  calc
    _ = ∫ x in s.service.winner j,
        childCoordinateWork n s label i j (s.service.observation j x)
          ∂ν.prod independentExponentials := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
      exact branchSelect_of_mem s.service.winner_disjoint _ _ hx
    _ = ∫ x, childCoordinateWork n s label i j x
        ∂Measure.map (s.service.observation j)
          ((ν.prod independentExponentials).restrict (s.service.winner j)) :=
      (integral_map_of_stronglyMeasurable (s.service.measurable_observation j)
        (measurable_childCoordinateWork n s label i j).stronglyMeasurable).symm
    _ = _ := by rw [s.service.first_completion_factorization]

theorem integral_futureCoordinateWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    (∫ x, futureCoordinateWork n s label i x ∂ν.prod independentExponentials) =
      ∑ j, ∫ x, childCoordinateWork n s label i j x
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  have hi := integrable_futureCoordinateWork n s label hinj hP0 hPc hPcompact hPdown hmem ν i
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure] at hi
  have ht : (∫ x in s.service.terminalEvent, futureCoordinateWork n s label i x
      ∂ν.prod independentExponentials) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem s.service.measurable_terminalEvent] with x hx
    apply branchSelect_of_not_mem
    intro j hj
    exact Set.disjoint_left.mp (s.service.winner_disjoint_terminal j) hx hj
  conv_lhs => rw [s.service.segment_measure_decomposition ν]
  rw [integral_add_measure hi.1 hi.2, ht, zero_add, integral_sum_measure hi.2, tsum_fintype]
  exact Finset.sum_congr rfl (fun j _ => futureCoordinateWork_winner_integral n s label ν i j)

theorem expected_coordinateWork_step (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    (∫ x, coordinateWork (n + 1) s label i x ∂ν.prod independentExponentials) =
      ∑ j, ∫ x, nextCoordinateWork n s label i j x
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  have he : coordinateWork (n + 1) s label i =ᵐ[ν.prod independentExponentials]
      fun x => s.stoppedWork i x + futureCoordinateWork n s label i x := by
    filter_upwards [goodExecution_ae (n + 1) s ν] with x hx
    exact coordinateWork_step n s label hinj hP0 hPc hPcompact hPdown hmem i x hx
  rw [integral_congr_ae he,
    integral_add (s.integrable_stoppedWork i _)
      (integrable_futureCoordinateWork n s label hinj hP0 hPc hPcompact hPdown hmem ν i),
    s.stoppedWork_expected_marked ν i,
    integral_futureCoordinateWork n s label hinj hP0 hPc hPcompact hPdown hmem ν i]
  let M : ℝ := ∫ _ : (H × ℝ) × ({j : ι // j ≠ i} → ℝ), (1 : ℝ)
    ∂(s.service.markedHistoryMeasure ν i).prod independentExponentials
  have hterm : ∀ j, (∫ x, nextCoordinateWork n s label i j x
      ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials) =
      (∫ x, childCoordinateWork n s label i j x
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials) +
        if j = i then M else 0 := by
    intro j
    by_cases hij : i ≠ j
    · simp only [nextCoordinateWork, childCoordinateWork, dif_pos hij, if_neg (Ne.symm hij), add_zero]
    · have he : i = j := not_ne_iff.mp hij
      subst j
      simp only [nextCoordinateWork, childCoordinateWork, ne_eq, not_true_eq_false,
        dite_false, if_pos rfl, integral_zero, zero_add]
      rfl
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end StochasticMatching.PosteriorStage
