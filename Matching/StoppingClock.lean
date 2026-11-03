import Matching.ComparisonOutcome

/-! The actual end of a first service segment. Before the deadline, survival
is exactly being before this clock, almost surely on the original sample.
-/

open MeasureTheory Set
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

noncomputable def stopClock (z : ι → ℝ) : ℝ :=
  branchSelect (variableWinner p.service p.deadline)
    (fun j z => cappedHit (p.service j) p.deadline (z j)) (fun _ => p.deadline) z

theorem measurable_stopClock : Measurable p.stopClock :=
  measurable_branchSelect p.winner_disjoint p.measurable_winner p.measurable_clock measurable_const

theorem stopClock_winner {z : ι → ℝ} {j : ι}
    (hz : z ∈ variableWinner p.service p.deadline j) :
    p.stopClock z = cappedHit (p.service j) p.deadline (z j) :=
  branchSelect_of_mem p.winner_disjoint _ _ hz

theorem stopClock_terminal {z : ι → ℝ} (hz : z ∈ p.terminalSurvival) :
    p.stopClock z = p.deadline := by
  apply branchSelect_of_not_mem
  intro j hj
  exact p.winner_subset_completion j hj hz

theorem stopClock_bounds (z : ι → ℝ) : p.stopClock z ∈ Icc 0 p.deadline := by
  classical
  by_cases hw : ∃ j, z ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hw
    rw [p.stopClock_winner hj]
    exact cappedHit_bounds (p.service_continuous j) p.deadline_pos.le
  · unfold stopClock
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    exact ⟨p.deadline_pos.le, le_refl _⟩

theorem service_lt_iff_before_clock (z : ι → ℝ) (i : ι) {t : ℝ}
    (ht : t ∈ Ico 0 p.deadline) :
    p.service i t < z i ↔ t < cappedHit (p.service i) p.deadline (z i) := by
  have h := cappedHit_le_iff (z := z i) (p.service_continuous i) p.deadline_pos.le
    (p.service_monotone i) ht.1 ht.2
  constructor
  · intro hs
    exact lt_of_not_ge (fun hc => (not_le.mpr hs) (h.mp hc))
  · intro hc
    exact lt_of_not_ge (fun hs => (not_le.mpr hc) (h.mpr hs))

theorem survival_iff_before_stopClock {z : ι → ℝ}
    (hz : z ∈ p.terminalSurvival ∨ ∃ j, z ∈ variableWinner p.service p.deadline j)
    {t : ℝ} (ht : t ∈ Ico 0 p.deadline) :
    z ∈ survivalBox (fun i => p.service i t) ↔ t < p.stopClock z := by
  rcases hz with hz | ⟨j, hj⟩
  · rw [p.stopClock_terminal hz]
    apply iff_of_true _ ht.2
    apply mem_univ_pi.mpr
    intro i
    exact lt_of_le_of_lt (p.service_monotone i ⟨ht.1, ht.2.le⟩
      ⟨p.deadline_pos.le, le_refl _⟩ ht.2.le) (mem_univ_pi.mp hz i)
  · rw [p.stopClock_winner hj]
    constructor
    · intro hs
      exact (p.service_lt_iff_before_clock z j ht).mp (mem_univ_pi.mp hs j)
    · intro hc
      apply mem_univ_pi.mpr
      intro i
      apply (p.service_lt_iff_before_clock z i ht).mpr
      by_cases hij : i = j
      · simpa only [hij] using hc
      · exact hc.trans (hj.2 i hij)

theorem survival_iff_before_stopClock_ae :
    ∀ᵐ z ∂(independentExponentials (ι := ι)), ∀ t ∈ Ico 0 p.deadline,
      z ∈ survivalBox (fun i => p.service i t) ↔ t < p.stopClock z := by
  filter_upwards [p.no_completion_or_unique_ae] with z hz
  intro t ht
  apply p.survival_iff_before_stopClock _ ht
  rcases hz with hz | ⟨j, hj, _⟩
  · exact Or.inl hz
  · exact Or.inr ⟨j, hj⟩

end StochasticMatching.ServiceCurveFamily
