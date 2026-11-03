import Matching.WorkRecursion

/-! Expected integrated work equals the expected completion count for every
finite depth of the actual posterior-policy execution.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem futureWork_winner_integral (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (ν : Measure H) (j : ι) :
    (∫ x in s.service.winner j, futureWork n s label x ∂ν.prod independentExponentials) =
      ∫ x, terminalWork n (s.next j) (fun i => label i.1) x
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  calc
    _ = ∫ x in s.service.winner j,
        terminalWork n (s.next j) (fun i => label i.1) (s.service.observation j x)
          ∂ν.prod independentExponentials := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
      exact branchSelect_of_mem s.service.winner_disjoint _ _ hx
    _ = ∫ x, terminalWork n (s.next j) (fun i => label i.1) x
        ∂Measure.map (s.service.observation j)
          ((ν.prod independentExponentials).restrict (s.service.winner j)) :=
      (integral_map_of_stronglyMeasurable (s.service.measurable_observation j)
        (measurable_terminalWork n (s.next j) (fun i => label i.1)).stronglyMeasurable).symm
    _ = _ := by rw [s.service.first_completion_factorization]

theorem integral_futureWork (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, futureWork n s label x ∂ν.prod independentExponentials) =
      ∑ j, ∫ x, terminalWork n (s.next j) (fun i => label i.1) x
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  have hi := integrable_futureWork n s label hinj hP0 hPc hPcompact hPdown hmem ν
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure] at hi
  have ht : (∫ x in s.service.terminalEvent, futureWork n s label x
      ∂ν.prod independentExponentials) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem s.service.measurable_terminalEvent] with x hx
    apply branchSelect_of_not_mem
    intro j hj
    exact Set.disjoint_left.mp (s.service.winner_disjoint_terminal j) hx hj
  conv_lhs => rw [s.service.segment_measure_decomposition ν]
  rw [integral_add_measure hi.1 hi.2, ht, zero_add, integral_sum_measure hi.2, tsum_fintype]
  exact Finset.sum_congr rfl (fun j _ => futureWork_winner_integral n s label ν j)

theorem terminalWork_expected_step (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, terminalWork (n + 1) s label x ∂ν.prod independentExponentials) =
      ∑ j, ∫ x, (1 + terminalWork n (s.next j) (fun i => label i.1) x)
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  have hs : Integrable (fun x => ∑ i, s.stoppedWork i x) (ν.prod independentExponentials) :=
    integrable_finset_sum _ (fun i _ => s.integrable_stoppedWork i _)
  have he : terminalWork (n + 1) s label =ᵐ[ν.prod independentExponentials]
      fun x => (∑ i, s.stoppedWork i x) + futureWork n s label x := by
    filter_upwards [goodExecution_ae (n + 1) s ν] with x hx
    exact terminalWork_step n s label hinj hP0 hPc hPcompact hPdown hmem x hx
  rw [integral_congr_ae he,
    integral_add hs (integrable_futureWork n s label hinj hP0 hPc hPcompact hPdown hmem ν),
    integral_finset_sum _ (fun i _ => s.integrable_stoppedWork i _),
    integral_futureWork n s label hinj hP0 hPc hPcompact hPdown hmem ν,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  letI := s.service.finite_markedHistoryMeasure ν j
  rw [s.stoppedWork_expected_marked ν j,
    integral_add (integrable_const 1)
      (integrable_terminalWork n (s.next j) (fun i => label i.1)
        (hinj.comp Subtype.val_injective) hP0 hPc hPcompact hPdown
        (s.next_feasibleAllocation label hPdown hmem j) (s.service.markedHistoryMeasure ν j))]

theorem expected_terminalWork_eq_count (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, terminalWork n s label x ∂ν.prod independentExponentials) =
      ∫ x, (AdaptivePlan.run (E := ℕ) (countPlan n s 0) x : ℝ) ∂ν.prod independentExponentials := by
  induction n generalizing H ι with
  | zero => simp [terminalWork, cumulativePath, ratePath, countPlan, AdaptivePlan.run]
  | succ n ih =>
    rw [terminalWork_expected_step n s label hinj hP0 hPc hPcompact hPdown hmem ν,
      countPlan_expected_completions]
    apply Finset.sum_congr rfl
    intro j _
    letI := s.service.finite_markedHistoryMeasure ν j
    have hn := s.next_feasibleAllocation label hPdown hmem j
    rw [integral_add (integrable_const 1)
        (integrable_terminalWork n (s.next j) (fun i => label i.1)
          (hinj.comp Subtype.val_injective) hP0 hPc hPcompact hPdown hn
          (s.service.markedHistoryMeasure ν j)),
      integral_add (integrable_const 1) (integrable_countPlan n (s.next j) 0 _),
      ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective) hn
        (s.service.markedHistoryMeasure ν j)]

end StochasticMatching.PosteriorStage
