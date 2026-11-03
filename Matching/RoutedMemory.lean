import Matching.ArrivalMemoryCounts

/-! Retain the actual routing decision along with every typed arrival. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

abbrev RoutedEvent (σ ι : Type*) := Unit ⊕ (ℝ × (σ × Option ι))
abbrev RoutedMemory (σ ι : Type*) := EventMemory (RoutedEvent σ ι)

def emptyRoutedMemory : RoutedMemory σ ι := (0, fun _ => .inl ())

def routedEventJob : RoutedEvent σ ι → Option ι := Sum.elim (fun _ => none) (fun e => e.2.2)

def routedEventAccepted (e : RoutedEvent σ ι) : ℕ := if (routedEventJob e).isSome then 1 else 0

def routedMemoryAccepted (m : RoutedMemory σ ι) : ℕ :=
  ∑ k ∈ Finset.range m.1, routedEventAccepted (m.2 k)

def routedMemoryInput (m : RoutedMemory σ ι) : ArrivalMemory σ :=
  (m.1, fun k => arrivalTypeProjection (m.2 k))

theorem measurable_routedEventJob : Measurable (routedEventJob (σ := σ) (ι := ι)) :=
  measurable_const.sumElim (measurable_snd.comp measurable_snd)

theorem measurable_routedEventAccepted : Measurable (routedEventAccepted (σ := σ) (ι := ι)) :=
  (measurable_of_countable (fun a : Option ι => if a.isSome then (1 : ℕ) else 0)).comp measurable_routedEventJob

theorem measurable_routedMemoryAccepted : Measurable (routedMemoryAccepted (σ := σ) (ι := ι)) := by
  have hm : Measurable (fun x : RoutedMemory σ ι × ℕ => ∑ k ∈ Finset.range x.2, routedEventAccepted (x.1.2 k)) :=
    measurable_from_prod_countable (fun n => Finset.measurable_sum (Finset.range n) (fun k _ =>
      measurable_routedEventAccepted.comp ((measurable_pi_apply k).comp measurable_snd)))
  exact hm.comp (measurable_id.prodMk measurable_fst)

theorem measurable_routedMemoryInput : Measurable (routedMemoryInput (σ := σ) (ι := ι)) :=
  measurable_fst.prodMk (measurable_pi_lambda _ (fun k =>
    measurable_arrivalTypeProjection.comp ((measurable_pi_apply k).comp measurable_snd)))

theorem routedMemoryInput_append (m : RoutedMemory σ ι) (e : RoutedEvent σ ι) :
    routedMemoryInput (appendEvent (m, e)) = appendEvent (routedMemoryInput m, arrivalTypeProjection e) := by
  apply Prod.ext
  · rfl
  funext k
  by_cases hk : k = m.1
  · subst k
    simp [routedMemoryInput, appendEvent]
  · simp [routedMemoryInput, appendEvent, Function.update_of_ne hk, hk]

theorem routedMemoryAccepted_empty : routedMemoryAccepted (emptyRoutedMemory (σ := σ) (ι := ι)) = 0 := by
  simp [routedMemoryAccepted, emptyRoutedMemory]

theorem routedMemoryAccepted_append (m : RoutedMemory σ ι) (e : RoutedEvent σ ι) :
    routedMemoryAccepted (appendEvent (m, e)) = routedMemoryAccepted m + routedEventAccepted e := by
  change (∑ k ∈ Finset.range (m.1 + 1), routedEventAccepted ((appendEvent (m, e)).2 k)) = _
  rw [Finset.sum_range_succ, appendEvent_at_last]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [appendEvent_preserves_prefix m e k (Finset.mem_range.mp hk)]

structure RoutedMemoryValid (N : σ → Finset ι) (m : RoutedMemory σ ι) : Prop where
  genuine : ∀ k, k < m.1 → ∃ e, m.2 k = .inr e
  supported : ∀ k, k < m.1 → ∀ t s j, m.2 k = .inr (t, (s, some j)) → j ∈ N s
  unique : ∀ k l, k < m.1 → l < m.1 → ∀ j,
    routedEventJob (m.2 k) = some j → routedEventJob (m.2 l) = some j → k = l

def RoutedMemoryAvoids (A : Finset ι) (m : RoutedMemory σ ι) : Prop :=
  ∀ k, k < m.1 → ∀ j, routedEventJob (m.2 k) = some j → j ∉ A

theorem routedMemoryValid_empty (N : σ → Finset ι) : RoutedMemoryValid N (emptyRoutedMemory (σ := σ) (ι := ι)) := by
  constructor
  · intro k hk; exact False.elim (Nat.not_lt_zero k hk)
  · intro k hk; exact False.elim (Nat.not_lt_zero k hk)
  · intro k l hk; exact False.elim (Nat.not_lt_zero k hk)

theorem routedMemoryAvoids_empty (A : Finset ι) : RoutedMemoryAvoids A (emptyRoutedMemory (σ := σ) (ι := ι)) := by
  intro k hk
  simp [emptyRoutedMemory] at hk

theorem RoutedMemoryValid.append (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) (A B : Finset ι) (hav : RoutedMemoryAvoids A m)
    (t : ℝ) (s : σ) (a : Option ι) (hs : ∀ j, a = some j → j ∈ N s ∧ j ∈ A)
    (hB : B ⊆ A) (hremove : ∀ j, a = some j → j ∉ B) :
    RoutedMemoryValid N (appendEvent (m, .inr (t, (s, a)))) ∧
      RoutedMemoryAvoids B (appendEvent (m, .inr (t, (s, a)))) := by
  let e : RoutedEvent σ ι := .inr (t, (s, a))
  have hold (k : ℕ) (hk : k < m.1) : (appendEvent (m, e)).2 k = m.2 k :=
    appendEvent_preserves_prefix m e k hk
  have hlast : (appendEvent (m, e)).2 m.1 = e := appendEvent_at_last m e
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro k hk
    change k < m.1 + 1 at hk
    by_cases he : k = m.1
    · subst k; exact ⟨_, hlast⟩
    · rw [hold k (by omega)]
      exact h.genuine k (by omega)
  · intro k hk u q j he
    change k < m.1 + 1 at hk
    by_cases hkm : k = m.1
    · subst k
      rw [hlast] at he
      have ht := Sum.inr.inj he
      have hq : s = q := congrArg (fun x : ℝ × (σ × Option ι) => x.2.1) ht
      have ha : a = some j := congrArg (fun x : ℝ × (σ × Option ι) => x.2.2) ht
      exact hq ▸ (hs j ha).1
    · rw [hold k (by omega)] at he
      exact h.supported k (by omega) u q j he
  · intro k l hk hl j he hf
    change k < m.1 + 1 at hk
    change l < m.1 + 1 at hl
    by_cases hkm : k = m.1
    · subst k
      by_cases hlm : l = m.1
      · exact hlm.symm
      · rw [hlast] at he
        rw [hold l (by omega)] at hf
        exact False.elim (hav l (by omega) j hf (hs j he).2)
    · rw [hold k (by omega)] at he
      by_cases hlm : l = m.1
      · subst l
        rw [hlast] at hf
        exact False.elim (hav k (by omega) j he (hs j hf).2)
      · rw [hold l (by omega)] at hf
        exact h.unique k l (by omega) (by omega) j he hf
  · intro k hk j he
    change k < m.1 + 1 at hk
    by_cases hkm : k = m.1
    · subst k
      rw [hlast] at he
      exact hremove j he
    · rw [hold k (by omega)] at he
      exact fun hj => hav k (by omega) j he (hB hj)

end StochasticMatching
