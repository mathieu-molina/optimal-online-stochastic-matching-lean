import Matching.CursorDecisionStep
import Matching.RoutedMemoryMeasurable
import Matching.MarkedRoutingTrajectory

/-! The actual marked routing process maintains a valid partial matching
record, disjoint from currently available jobs, with the correct payoff. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

def CursorMemoryValid (N : σ → Finset J) (n : ℕ) (label : ι → J)
    (x : RoutingCursor n H ι × RoutedMemory σ J) : Prop :=
  RoutedMemoryValid N x.2 ∧ RoutedMemoryAvoids (cursorAvailable n label x.1) x.2 ∧
    routedMemoryAccepted x.2 = cursorDepth n x.1

theorem measurableSet_cursorMemoryValid (N : σ → Finset J) (n : ℕ) (label : ι → J) :
    MeasurableSet {x : RoutingCursor n H ι × RoutedMemory σ J | CursorMemoryValid N n label x} := by
  letI : MeasurableSpace (Finset J) := ⊤
  have hA : Measurable (fun x : RoutingCursor n H ι × RoutedMemory σ J =>
      cursorAvailable n label x.1) := (measurable_cursorAvailable (H := H) n label).comp measurable_fst
  have hm (k : ℕ) : Measurable (fun x : RoutingCursor n H ι × RoutedMemory σ J => x.2.2 k) :=
    (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
  have hav : MeasurableSet {x : RoutingCursor n H ι × RoutedMemory σ J |
      RoutedMemoryAvoids (cursorAvailable n label x.1) x.2} := by
    simp only [RoutedMemoryAvoids, setOf_forall]
    apply MeasurableSet.iInter
    intro k
    have hj : MeasurableSet {x : RoutingCursor n H ι × RoutedMemory σ J | ∀ j,
        routedEventJob (x.2.2 k) = some j → j ∉ cursorAvailable n label x.1} := by
      simp only [setOf_forall]
      apply MeasurableSet.iInter
      intro j
      exact (((measurable_routedEventJob.comp (hm k)) (measurableSet_singleton (some j))).mem.imp
        (hA ((Set.to_countable {A : Finset J | j ∉ A}).measurableSet)).mem).setOf
    exact ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).mem.imp hj.mem).setOf
  exact (measurable_snd (measurableSet_routedMemoryValid N)).inter (hav.inter
    (measurableSet_eq_fun_of_countable (measurable_routedMemoryAccepted.comp measurable_snd)
      ((measurable_cursorDepth n).comp measurable_fst)))

def StoppedCursorMemoryValid (N : σ → Finset J) (n : ℕ) (label : ι → J) :
    Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) → Prop :=
  Sum.elim (fun _ => True) (CursorMemoryValid N n label)

theorem measurableSet_stoppedCursorMemoryValid (N : σ → Finset J) (n : ℕ) (label : ι → J) :
    MeasurableSet {x : Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) |
      StoppedCursorMemoryValid N n label x} := by
  apply measurableSet_sum_iff.mpr
  exact ⟨MeasurableSet.univ, measurableSet_cursorMemoryValid N n label⟩

namespace PosteriorStage

theorem markedCursorUpdate_preserves (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (N : σ → Finset J)
    (x : RoutingCursor n H ι × RoutedMemory σ J) (hx : CursorMemoryValid N n label x)
    (e : RoutedEvent σ J)
    (he : e ∈ admissibleArrival N (cursorAvailable n label x.1)ᶜ ((s.cursorService n label).curves x.1).deadline) :
    StoppedCursorMemoryValid N n label (loggedEventUpdate (s.typedCursorUpdate n label) id (x, e)) := by
  cases e with
  | inl u => cases u; trivial
  | inr e =>
    rcases e with ⟨t, a, j⟩
    have he' : t ∈ Ioo 0 ((s.cursorService n label).curves x.1).deadline ∧
        ∀ b, j = some b → b ∈ N a ∧ b ∈ cursorAvailable n label x.1 := by
      simpa [admissibleArrival] using he
    have hU : s.typedCursorUpdate n label (x.1, .inr (t, (a, j))) =
        s.cursorUpdate n label (x.1, .inr (t, j)) :=
      guardedEventUpdate_of_valid (fun y => ((s.cursorService n label).curves y).deadline)
        (s.cursorUpdate n label) x.1 t j he'.1.1.le he'.1.2
    cases j with
    | none =>
      obtain ⟨y, hy, hd, hA⟩ := s.cursorUpdate_rejected n label x.1 t
      have hv := hx.1.append N x.2 (cursorAvailable n label x.1) (cursorAvailable n label y) hx.2.1
        t a none (by simp) (by rw [hA]) (by simp)
      unfold loggedEventUpdate
      rw [hU, hy]
      change CursorMemoryValid N n label (y, appendEvent (x.2, .inr (t, (a, none))))
      refine ⟨hv.1, hv.2, ?_⟩
      rw [routedMemoryAccepted_append, hd]
      simpa [routedEventAccepted, routedEventJob] using hx.2.2
    | some b =>
      obtain ⟨y, hy, hd, hA⟩ := s.cursorUpdate_accepted n label hinj x.1 t b (he'.2 b rfl).2
      have hv := hx.1.append N x.2 (cursorAvailable n label x.1) (cursorAvailable n label y) hx.2.1
        t a (some b) he'.2 (hA.trans (Finset.erase_subset _ _))
        (fun j hj => by cases Option.some.inj hj; exact fun hj => (Finset.mem_erase.mp (hA hj)).1 rfl)
      unfold loggedEventUpdate
      rw [hU, hy]
      change CursorMemoryValid N n label (y, appendEvent (x.2, .inr (t, (a, some b))))
      refine ⟨hv.1, hv.2, ?_⟩
      rw [routedMemoryAccepted_append, hd, hx.2.2]
      rfl

theorem markedTrajectory_valid (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c)) (h : H) :
    ∀ᵐ z ∂s.markedTrajectory n label N c hc hmem (initialRoutingCursor n h, emptyRoutedMemory),
      ∀ k, StoppedCursorMemoryValid N n label (z k) := by
  let p := (s.cursorService n label).comap (Prod.fst : RoutingCursor n H ι × RoutedMemory σ J → _) measurable_fst
  let hp := fun (x : RoutingCursor n H ι × RoutedMemory σ J) t ht =>
    s.cursorService_supply_feasible n label N c hc hmem x.1 t ht
  let U := loggedEventUpdate (s.typedCursorUpdate (σ := σ) n label) id
  have hU := measurable_loggedEventUpdate _ (s.measurable_typedCursorUpdate (σ := σ) n label) id measurable_id
  letI := historyRoutingKernel_markov N c hc p hp
  letI := routingTransition_markov N c hc p hp U hU
  apply markovTrajectory_invariant (absorbingKernel (routingTransition N c hc p hp U))
    _ (measurableSet_stoppedCursorMemoryValid N n label)
  · intro a ha
    cases a with
    | inl u =>
      exact (ae_dirac_iff (measurableSet_stoppedCursorMemoryValid N n label)).mpr trivial
    | inr x =>
      change ∀ᵐ y ∂eventUpdateKernel (historyRoutingKernel N c p) U x,
        StoppedCursorMemoryValid N n label y
      rw [eventUpdateKernel_apply _ U hU]
      apply (ae_map_iff (hU.comp measurable_prodMk_left).aemeasurable
        (measurableSet_stoppedCursorMemoryValid N n label)).mpr
      have he := routingNextArrival_admissible N c hc ((s.cursorService n label).curves x.1)
        (s.cursorService_supply_feasible n label N c hc hmem x.1)
        (cursorAvailable n label x.1)ᶜ
        (fun j hj t _ => s.cursorService_frozen_outside n label x.1 j (by simpa using hj) t)
      filter_upwards [he] with e he
      exact s.markedCursorUpdate_preserves n label hinj N x ha e he
  · change CursorMemoryValid N n label (initialRoutingCursor n h, emptyRoutedMemory)
    exact ⟨routedMemoryValid_empty N, routedMemoryAvoids_empty _, by rw [routedMemoryAccepted_empty, cursorDepth_initial]⟩

end PosteriorStage
end StochasticMatching
