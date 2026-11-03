import Matching.TrajectoryProjection

/-! Almost-sure support properties of every adjacent transition in a full
Markov trajectory, proved from its finite joint laws.
-/
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A : Type*} [MeasurableSpace A]

theorem appendHistory_at_old (n : ℕ) (h : ↥(Finset.Iic n) → A) (a : A)
    (i : ℕ) (hi : i ≤ n) :
    appendHistory n h a ⟨i, Finset.mem_Iic.mpr (hi.trans (Nat.le_succ n))⟩ = h ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp [appendHistory, IicProdIoc, hi]

theorem appendHistory_at_last (n : ℕ) (h : ↥(Finset.Iic n) → A) (a : A) :
    appendHistory n h a ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = a := by
  simp [appendHistory, IicProdIoc, MeasurableEquiv.piSingleton]

theorem markovTrajectory_step_support (K : Kernel A A) [IsMarkovKernel K]
    (R : Set (A × A)) (hR : MeasurableSet R)
    (hK : ∀ a, ∀ᵐ b ∂K a, (a, b) ∈ R) (a : A) (n : ℕ) :
    ∀ᵐ z ∂markovTrajectory K a, (z n, z (n + 1)) ∈ R := by
  let i : ↥(Finset.Iic (n + 1)) := ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩
  let j : ↥(Finset.Iic (n + 1)) := ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
  let Q : Set (↥(Finset.Iic (n + 1)) → A) := {h | (h i, h j) ∈ R}
  have hQ : MeasurableSet Q := hR.preimage ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hnext : ∀ h : ↥(Finset.Iic n) → A,
      ∀ᵐ g ∂Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) n (n + 1) h, g ∈ Q := by
    intro h
    rw [partialTraj_next_apply]
    apply (ae_map_iff (measurable_appendHistory n h).aemeasurable hQ).mpr
    filter_upwards [hK (lastCoordinate n h)] with b hb
    change (appendHistory n h b i, appendHistory n h b j) ∈ R
    rw [appendHistory_at_old n h b n le_rfl, appendHistory_at_last]
    exact hb
  have hfinite : ∀ᵐ g ∂Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 (n + 1)
      (fun _ => a), g ∈ Q := by
    rw [Kernel.partialTraj_succ_eq_comp (κ := markovHistoryKernel K) (X := fun _ => A) (Nat.zero_le n)]
    apply Kernel.ae_comp_of_ae_ae hQ
    exact Filter.Eventually.of_forall hnext
  have hm : Measurable (frestrictLe (π := fun _ => A) (n + 1)) := measurable_frestrictLe (n + 1)
  have hmap : Measure.map (frestrictLe (π := fun _ => A) (n + 1)) (markovTrajectory K a) =
      Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 (n + 1) (fun _ => a) := by
    exact Kernel.traj_map_frestrictLe_apply (X := fun _ => A) (κ := markovHistoryKernel K) 0 (n + 1) (fun _ => a)
  rw [← hmap] at hfinite
  exact (ae_map_iff hm.aemeasurable hQ).mp hfinite

theorem markovTrajectory_all_steps_support (K : Kernel A A) [IsMarkovKernel K]
    (R : Set (A × A)) (hR : MeasurableSet R)
    (hK : ∀ a, ∀ᵐ b ∂K a, (a, b) ∈ R) (a : A) :
    ∀ᵐ z ∂markovTrajectory K a, ∀ n, (z n, z (n + 1)) ∈ R :=
  ae_all_iff.mpr (fun n => markovTrajectory_step_support K R hR hK a n)

end StochasticMatching
