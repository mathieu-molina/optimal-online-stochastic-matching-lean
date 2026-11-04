import Matching.LastArrivalLog

/-! A measurable observation of the last live state before absorption.
The reader is total; its live-state specification holds on terminating
paths that start live. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace E]

theorem measurableSet_unitTerminal : MeasurableSet {a : Unit ⊕ A | a = .inl ()} := by
  have he : {a : Unit ⊕ A | a = .inl ()} = Set.range (Sum.inl : Unit → Unit ⊕ A) := by
    ext a
    cases a with
    | inl u => cases u; simp
    | inr x => simp
  rw [he]
  exact measurableSet_range_inl

noncomputable def lastLiveObservation (O : A → E) (d : E) (z : ℕ → Unit ⊕ A) : E :=
  Sum.elim (fun _ => d) O (z (firstEntryTime {a | a = .inl ()} z - 1))

theorem measurable_lastLiveObservation (O : A → E) (hO : Measurable O) (d : E) :
    Measurable (lastLiveObservation O d) := by
  have hm : Measurable (fun x : (ℕ → Unit ⊕ A) × ℕ => x.1 x.2) :=
    measurable_from_prod_countable (fun n => measurable_pi_apply n)
  exact (measurable_const.sumElim hO).comp
    (hm.comp (measurable_id.prodMk ((measurable_of_countable (fun n : ℕ => n - 1)).comp
      (measurable_firstEntryTime _ measurableSet_unitTerminal))))

theorem lastLiveObservation_map (f : A → B) (O : B → E) (d : E) (z : ℕ → Unit ⊕ A) :
    lastLiveObservation O d (fun k => Sum.map id f (z k)) =
      lastLiveObservation (O ∘ f) d z := by
  have he := firstEntryTime_eq_of_membership {a : Unit ⊕ A | a = .inl ()}
    {a : Unit ⊕ B | a = .inl ()} z (fun k => Sum.map id f (z k))
    (fun k => by cases hk : z k <;> simp [hk])
  unfold lastLiveObservation
  rw [← he]
  dsimp only
  cases z (firstEntryTime {a | a = .inl ()} z - 1) <;> rfl

theorem lastLiveObservation_comp {F : Type*} (g : E → F) (O : A → E) (d : E)
    (z : ℕ → Unit ⊕ A) :
    g (lastLiveObservation O d z) = lastLiveObservation (g ∘ O) (g d) z := by
  unfold lastLiveObservation
  cases z (firstEntryTime {a | a = .inl ()} z - 1) <;> rfl

theorem lastLiveObservation_spec (O : A → E) (d : E) (z : ℕ → Unit ⊕ A)
    (hzero : z 0 ≠ .inl ()) (hterm : ∃ k, z k = .inl ()) :
    ∃ x, z (firstEntryTime {a | a = .inl ()} z - 1) = .inr x ∧
      lastLiveObservation O d z = O x := by
  let m := firstEntryTime {a : Unit ⊕ A | a = .inl ()} z
  have hm : z m = .inl () := firstEntryTime_spec {a : Unit ⊕ A | a = .inl ()} z hterm
  have hmpos : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    exact hzero (hm0 ▸ hm)
  cases he : z (m - 1) with
  | inl u =>
    cases u
    have hle : m ≤ m - 1 := firstEntryTime_le _ z he
    omega
  | inr x => exact ⟨x, rfl, by unfold lastLiveObservation; rw [he]; rfl⟩

theorem markovTrajectory_initial_mem (K : Kernel A A) [IsMarkovKernel K] (a : A)
    (S : Set A) (hS : MeasurableSet S) (ha : a ∈ S) :
    ∀ᵐ z ∂markovTrajectory K a, z 0 ∈ S := by
  have h : ∀ᵐ y ∂iterateKernel K 0 a, y ∈ S := (ae_dirac_iff hS).mpr ha
  rw [← markovTrajectory_coordinate_law K a 0] at h
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
    (show MeasurableSet {x | x ∈ S} from hS)).mp h

end StochasticMatching
