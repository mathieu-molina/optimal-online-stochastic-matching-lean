import Matching.FiniteKernelIteration
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! An actual probability law on infinite state trajectories, with finite
marginals identified with the independently defined kernel iterates.
-/
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A : Type*} [MeasurableSpace A]

def lastCoordinate (n : ℕ) (h : ↥(Finset.Iic n) → A) : A := h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

theorem measurable_lastCoordinate (n : ℕ) : Measurable (lastCoordinate (A := A) n) :=
  measurable_pi_apply _

noncomputable def markovHistoryKernel (K : Kernel A A) (n : ℕ) :
    Kernel (↥(Finset.Iic n) → A) A := K.comap (lastCoordinate n) (measurable_lastCoordinate n)

instance markovHistoryKernel_markov (K : Kernel A A) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel K n) := by unfold markovHistoryKernel; infer_instance

noncomputable def markovTrajectory (K : Kernel A A) [IsMarkovKernel K] (a : A) : Measure (ℕ → A) :=
  Kernel.traj (X := fun _ => A) (markovHistoryKernel K) 0 (fun _ => a)

instance markovTrajectory_probability (K : Kernel A A) [IsMarkovKernel K] (a : A) :
    IsProbabilityMeasure (markovTrajectory K a) := by unfold markovTrajectory; infer_instance

theorem partialTraj_next_last (κ : (n : ℕ) → Kernel (↥(Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => A) κ n (n + 1)).map (lastCoordinate (n + 1)) = κ n := by
  have hm : Measurable (IicProdIoc (X := fun _ => A) n (n + 1)) := measurable_IicProdIoc
  rw [Kernel.partialTraj_succ_self, ← Kernel.map_comp_right _ hm
    (measurable_lastCoordinate (n + 1))]
  have he : lastCoordinate (A := A) (n + 1) ∘ IicProdIoc (X := fun _ => A) n (n + 1) =
      (MeasurableEquiv.piSingleton (X := fun _ => A) n).symm ∘ Prod.snd := by
    funext x
    simp [lastCoordinate, IicProdIoc, MeasurableEquiv.piSingleton]
  rw [he, Kernel.map_comp_right _ measurable_snd (MeasurableEquiv.piSingleton (X := fun _ => A) n).symm.measurable,
    ← Kernel.snd_eq, Kernel.snd_prod, ← Kernel.map_comp_right _ (MeasurableEquiv.piSingleton (X := fun _ => A) n).measurable
      (MeasurableEquiv.piSingleton (X := fun _ => A) n).symm.measurable]
  have hi : (MeasurableEquiv.piSingleton (X := fun _ => A) n).symm ∘ MeasurableEquiv.piSingleton (X := fun _ => A) n = id := by
    funext x
    exact (MeasurableEquiv.piSingleton (X := fun _ => A) n).symm_apply_apply x
  rw [hi, Kernel.map_id]

theorem partialTraj_markov_last (K : Kernel A A) [IsMarkovKernel K]
    (n : ℕ) (h : ↥(Finset.Iic 0) → A) :
    Measure.map (lastCoordinate n) (Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 n h) =
      iterateKernel K n (lastCoordinate 0 h) := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac (measurable_lastCoordinate 0)]
      rfl
  | succ n ih =>
      rw [← Kernel.map_apply _ (measurable_lastCoordinate (n + 1)),
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.map_comp, partialTraj_next_last]
      change ((K.comap (lastCoordinate n) (measurable_lastCoordinate n)) ∘ₖ
        Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 n) h = _
      rw [← Kernel.comp_map _ K (measurable_lastCoordinate n), Kernel.comp_apply,
        Kernel.map_apply _ (measurable_lastCoordinate n), ih]
      rfl

theorem markovTrajectory_coordinate_law (K : Kernel A A) [IsMarkovKernel K] (a : A) (n : ℕ) :
    Measure.map (fun z : ℕ → A => z n) (markovTrajectory K a) = iterateKernel K n a := by
  have hm : Measurable (frestrictLe (π := fun _ => A) n) := measurable_frestrictLe n
  have he : (fun z : ℕ → A => z n) = lastCoordinate n ∘ frestrictLe n := rfl
  rw [he, ← Measure.map_map (measurable_lastCoordinate n) hm]
  unfold markovTrajectory
  rw [Kernel.traj_map_frestrictLe_apply, partialTraj_markov_last]
  rfl

theorem markovTrajectory_invariant (K : Kernel A A) [IsMarkovKernel K]
    (S : Set A) (hS : MeasurableSet S)
    (hstep : ∀ a ∈ S, ∀ᵐ b ∂K a, b ∈ S) (a : A) (ha : a ∈ S) :
    ∀ᵐ z ∂markovTrajectory K a, ∀ n, z n ∈ S := by
  apply ae_all_iff.mpr
  intro n
  have h := iterateKernel_invariant K S hS hstep n a ha
  rw [← markovTrajectory_coordinate_law K a n] at h
  have hm : Measurable (fun z : ℕ → A => z n) := measurable_pi_apply n
  exact (ae_map_iff hm.aemeasurable hS).mp h

end StochasticMatching
