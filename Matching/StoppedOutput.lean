import Matching.MarkovTransitionSupport
import Matching.MeasureApproximation

/-! Read the output at the first absorbing state of an infinite trajectory.
Finite-time event probabilities approximate this actual stopped output.
-/
open MeasureTheory Set ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal Topology
namespace StochasticMatching
variable {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]

def firstEntryPredicate (S : Set A) (z : ℕ → A) (n : ℕ) : Prop :=
  (∃ m, z m ∈ S) → z n ∈ S

theorem firstEntry_exists (S : Set A) (z : ℕ → A) : ∃ n, firstEntryPredicate S z n := by
  by_cases h : ∃ n, z n ∈ S
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, fun _ => hn⟩
  · exact ⟨0, fun hm => False.elim (h hm)⟩

noncomputable def firstEntryTime (S : Set A) (z : ℕ → A) : ℕ := by
  classical
  exact Nat.find (firstEntry_exists S z)

theorem measurable_firstEntryTime (S : Set A) (hS : MeasurableSet S) : Measurable (firstEntryTime S) := by
  classical
  apply measurable_find
  intro n
  have hm : ∀ k, MeasurableSet {z : ℕ → A | z k ∈ S} := fun k => hS.preimage (measurable_pi_apply k)
  have he : {z : ℕ → A | firstEntryPredicate S z n} =
      (⋃ m, {z | z m ∈ S})ᶜ ∪ {z | z n ∈ S} := by
    ext z
    simp only [firstEntryPredicate, mem_setOf_eq, mem_union, mem_compl_iff, mem_iUnion]
    exact imp_iff_not_or
  rw [he]
  exact (MeasurableSet.iUnion hm).compl.union (hm n)

theorem firstEntryTime_spec (S : Set A) (z : ℕ → A) (h : ∃ n, z n ∈ S) :
    z (firstEntryTime S z) ∈ S := by
  classical
  exact Nat.find_spec (firstEntry_exists S z) h

theorem firstEntryTime_le (S : Set A) (z : ℕ → A) {n : ℕ} (h : z n ∈ S) : firstEntryTime S z ≤ n := by
  classical
  exact Nat.find_min' (firstEntry_exists S z) (fun _ => h)

noncomputable def stoppedOutput (S : Set A) (O : A → E) (z : ℕ → A) : E := O (z (firstEntryTime S z))

theorem measurable_stoppedOutput (S : Set A) (hS : MeasurableSet S) (O : A → E) (hO : Measurable O) :
    Measurable (stoppedOutput S O) := by
  have hm : Measurable (fun x : (ℕ → A) × ℕ => x.1 x.2) :=
    measurable_from_prod_countable (fun n => measurable_pi_apply n)
  exact hO.comp (hm.comp (measurable_id.prodMk (measurable_firstEntryTime S hS)))

def terminalMembershipStep (S : Set A) (O : A → E) (B : Set E) : Set (A × A) :=
  {x | x.1 ∈ S → x.2 ∈ S ∧ (O x.1 ∈ B ↔ O x.2 ∈ B)}

theorem measurable_terminalMembershipStep (S : Set A) (hS : MeasurableSet S)
    (O : A → E) (hO : Measurable O) (B : Set E) (hB : MeasurableSet B) :
    MeasurableSet (terminalMembershipStep S O B) := by
  exact ((hS.preimage measurable_fst).mem.imp ((hS.preimage measurable_snd).mem.and
    ((hB.preimage (hO.comp measurable_fst)).mem.iff (hB.preimage (hO.comp measurable_snd)).mem))).setOf

theorem terminalMembership_persists (S : Set A) (O : A → E) (B : Set E) (z : ℕ → A)
    (hz : ∀ n, (z n, z (n + 1)) ∈ terminalMembershipStep S O B)
    (i j : ℕ) (hij : i ≤ j) (hi : z i ∈ S) : z j ∈ S ∧ (O (z i) ∈ B ↔ O (z j) ∈ B) := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨hi, Iff.rfl⟩
  | succ j hij ih =>
    have hj := hz j ih.1
    exact ⟨hj.1, ih.2.trans hj.2⟩

theorem stoppedOutput_agrees_at_terminal_ae (K : Kernel A A) [IsMarkovKernel K]
    (S : Set A) (hS : MeasurableSet S) (habs : ∀ a ∈ S, K a = Measure.dirac a)
    (O : A → E) (hO : Measurable O) (B : Set E) (hB : MeasurableSet B) (a : A) (n : ℕ) :
    ∀ᵐ z ∂markovTrajectory K a, z n ∈ S → (stoppedOutput S O z ∈ B ↔ O (z n) ∈ B) := by
  have hR := measurable_terminalMembershipStep S hS O hO B hB
  have hstep : ∀ a, ∀ᵐ b ∂K a, (a, b) ∈ terminalMembershipStep S O B := by
    intro a
    by_cases ha : a ∈ S
    · rw [habs a ha]
      apply (ae_dirac_iff (hR.preimage (measurable_const.prodMk measurable_id))).mpr
      exact fun _ => ⟨ha, Iff.rfl⟩
    · exact Eventually.of_forall (fun b hab => False.elim (ha hab))
  filter_upwards [markovTrajectory_all_steps_support K _ hR hstep a] with z hz
  intro hn
  exact (terminalMembership_persists S O B z hz (firstEntryTime S z) n (firstEntryTime_le S z hn)
    (firstEntryTime_spec S z ⟨n, hn⟩)).2

theorem stoppedOutput_step_approximation (K : Kernel A A) [IsMarkovKernel K]
    (S : Set A) (hS : MeasurableSet S) (habs : ∀ a ∈ S, K a = Measure.dirac a)
    (O : A → E) (hO : Measurable O) (B : Set E) (hB : MeasurableSet B) (a : A) (n : ℕ) :
    Measure.map (stoppedOutput S O) (markovTrajectory K a) B ≤
      Measure.map O (iterateKernel K n a) B + iterateKernel K n a Sᶜ ∧
    Measure.map O (iterateKernel K n a) B ≤
      Measure.map (stoppedOutput S O) (markovTrajectory K a) B + iterateKernel K n a Sᶜ := by
  have hf := measurable_stoppedOutput S hS O hO
  have hg : Measurable (fun z : ℕ → A => O (z n)) := hO.comp (measurable_pi_apply n)
  let bad : Set (ℕ → A) := {z | z n ∉ S}
  have he : ∀ᵐ z ∂markovTrajectory K a, z ∉ bad →
      (stoppedOutput S O z ∈ B ↔ O (z n) ∈ B) := by
    filter_upwards [stoppedOutput_agrees_at_terminal_ae K S hS habs O hO B hB a n] with z hz
    exact fun hn => hz (not_not.mp hn)
  have hmass : markovTrajectory K a bad = iterateKernel K n a Sᶜ := by
    rw [← markovTrajectory_coordinate_law K a n, Measure.map_apply (measurable_pi_apply n) hS.compl]
    rfl
  have hmap : Measure.map (fun z : ℕ → A => O (z n)) (markovTrajectory K a) =
      Measure.map O (iterateKernel K n a) := by
    rw [← markovTrajectory_coordinate_law K a n, Measure.map_map hO (measurable_pi_apply n)]
    rfl
  have h1 := map_measure_le_of_agree _ _ _ hf hg bad B hB he
  have h2 := map_measure_le_of_agree _ _ _ hg hf bad B hB (he.mono (fun z hz hn => (hz hn).symm))
  rw [hmass, hmap] at h1 h2
  exact ⟨h1, h2⟩

theorem stoppedOutput_law_of_geometric_approximation (K : Kernel A A) [IsMarkovKernel K]
    (S : Set A) (hS : MeasurableSet S) (habs : ∀ a ∈ S, K a = Measure.dirac a)
    (O : A → E) (hO : Measurable O) (a : A) (ν : Measure E) (q : ℝ≥0∞) (hq : q < 1)
    (hbound : ∀ n, iterateKernel K n a Sᶜ ≤ q ^ n)
    (happrox : ∀ n B, MeasurableSet B →
      ν B ≤ Measure.map O (iterateKernel K n a) B + q ^ n ∧
      Measure.map O (iterateKernel K n a) B ≤ ν B + q ^ n) :
    Measure.map (stoppedOutput S O) (markovTrajectory K a) = ν := by
  ext B hB
  have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hnear := fun n => stoppedOutput_step_approximation K S hS habs O hO B hB a n
  apply le_antisymm
  · have hlim : Tendsto (fun n : ℕ => ν B + q ^ n + q ^ n) atTop (𝓝 (ν B)) := by
      simpa using (tendsto_const_nhds.add hpow).add hpow
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun n => (hnear n).1.trans
      (add_le_add ((happrox n B hB).2) (hbound n)))
  · have hlim : Tendsto (fun n : ℕ =>
        Measure.map (stoppedOutput S O) (markovTrajectory K a) B + q ^ n + q ^ n) atTop
        (𝓝 (Measure.map (stoppedOutput S O) (markovTrajectory K a) B)) := by
      simpa using (tendsto_const_nhds.add hpow).add hpow
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun n => (happrox n B hB).1.trans
      (add_le_add ((hnear n).2.trans (add_le_add_left (hbound n) _)) le_rfl))

end StochasticMatching
