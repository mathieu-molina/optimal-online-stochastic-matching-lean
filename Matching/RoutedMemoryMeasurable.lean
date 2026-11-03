import Matching.RoutedMemory
import Matching.CursorCombinatorics

/-! Measurable validity predicates for the observed routing records. -/
open MeasureTheory Set
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def RoutedEventSupported (N : σ → Finset ι) : RoutedEvent σ ι → Prop :=
  Sum.elim (fun _ => True) (fun e => ∀ j, e.2.2 = some j → j ∈ N e.2.1)

theorem routedEventSupported_iff (N : σ → Finset ι) (e : RoutedEvent σ ι) :
    RoutedEventSupported N e ↔ ∀ t s j, e = .inr (t, (s, some j)) → j ∈ N s := by
  cases e with
  | inl u => simp [RoutedEventSupported]
  | inr e =>
    constructor
    · intro h t s j he
      have he' := Sum.inr.inj he
      cases he'
      exact h j rfl
    · intro h j hj
      apply h e.1 e.2.1 j
      cases e with
      | mk t q => cases q with
        | mk s a => simp only at hj; subst a; rfl

theorem measurableSet_routedEventSupported (N : σ → Finset ι) :
    MeasurableSet {e | RoutedEventSupported N e} := by
  have hP : MeasurableSet {q : σ × Option ι | ∀ j, q.2 = some j → j ∈ N q.1} :=
    (Set.to_countable _).measurableSet
  have he : {e | RoutedEventSupported N e} =
      Sum.inl '' (Set.univ : Set Unit) ∪
        Sum.inr '' {e : ℝ × (σ × Option ι) | e.2 ∈ {q | ∀ j, q.2 = some j → j ∈ N q.1}} := by
    ext e
    cases e <;> simp [RoutedEventSupported]
  rw [he]
  exact MeasurableSet.univ.inl_image.union (measurable_snd hP).inr_image

theorem measurableSet_routedMemoryValid (N : σ → Finset ι) :
    MeasurableSet {m : RoutedMemory σ ι | RoutedMemoryValid N m} := by
  have hm (k : ℕ) : Measurable (fun m : RoutedMemory σ ι => m.2 k) :=
    (measurable_pi_apply k).comp measurable_snd
  have hg : MeasurableSet {m : RoutedMemory σ ι | ∀ k, k < m.1 → ∃ e, m.2 k = .inr e} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro k
    have he : {m : RoutedMemory σ ι | ∃ e, m.2 k = .inr e} =
        (fun m : RoutedMemory σ ι => m.2 k) ⁻¹' Set.range Sum.inr := by ext m; simp [eq_comm]
    have hE : MeasurableSet {m : RoutedMemory σ ι | ∃ e, m.2 k = .inr e} := by
      rw [he]; exact hm k measurableSet_range_inr
    exact ((measurableSet_lt measurable_const measurable_fst).mem.imp hE.mem).setOf
  have hs : MeasurableSet {m : RoutedMemory σ ι | ∀ k, k < m.1 → RoutedEventSupported N (m.2 k)} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k =>
      ((measurableSet_lt measurable_const measurable_fst).mem.imp
        ((hm k) (measurableSet_routedEventSupported N)).mem).setOf)
  have hu : MeasurableSet {m : RoutedMemory σ ι | ∀ k l, k < m.1 → l < m.1 → ∀ j,
      routedEventJob (m.2 k) = some j → routedEventJob (m.2 l) = some j → k = l} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro l
    have hj : MeasurableSet {m : RoutedMemory σ ι | ∀ j,
        routedEventJob (m.2 k) = some j → routedEventJob (m.2 l) = some j → k = l} := by
      simp only [setOf_forall]
      apply MeasurableSet.iInter
      intro j
      have hkl : MeasurableSet {m : RoutedMemory σ ι | k = l} := by
        by_cases h : k = l <;> simp [h]
      exact (((measurable_routedEventJob.comp (hm k)) (measurableSet_singleton (some j))).mem.imp
        (((measurable_routedEventJob.comp (hm l)) (measurableSet_singleton (some j))).mem.imp
          hkl.mem)).setOf
    exact ((measurableSet_lt measurable_const measurable_fst).mem.imp
      ((measurableSet_lt measurable_const measurable_fst).mem.imp hj.mem)).setOf
  have he : {m : RoutedMemory σ ι | RoutedMemoryValid N m} =
      {m | ∀ k, k < m.1 → ∃ e, m.2 k = .inr e} ∩
      {m | ∀ k, k < m.1 → RoutedEventSupported N (m.2 k)} ∩
      {m | ∀ k l, k < m.1 → l < m.1 → ∀ j,
        routedEventJob (m.2 k) = some j → routedEventJob (m.2 l) = some j → k = l} := by
    ext m
    simp only [mem_setOf_eq, mem_inter_iff, routedEventSupported_iff]
    exact ⟨fun h => ⟨⟨h.genuine, h.supported⟩, h.unique⟩,
      fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  rw [he]
  exact (hg.inter hs).inter hu

end StochasticMatching
