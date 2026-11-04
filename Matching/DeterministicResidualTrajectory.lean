import Matching.DeterministicResidualIteration
import Matching.TrajectoryProjection

/-! Upgrade a deterministic fresh-residual construction to equality of
complete observed trajectory laws, retaining the entire finite history in
the induction invariant. -/
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B R : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace R]

theorem markovTrajectory_congr (K L : Kernel A A) [IsMarkovKernel K] [IsMarkovKernel L]
    (h : K = L) (a : A) : markovTrajectory K a = markovTrajectory L a := by
  subst L
  rfl

theorem map_product_of_fiber_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A × R → B × R) (hF : Measurable F)
    (K : Kernel A B) [IsMarkovKernel K]
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (K a).prod ρ) :
    Measure.map F (μ.prod ρ) = (μ.bind K).prod ρ := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hfF : Measurable (fun x : A × R => f (F x)) := hf.comp hF
  rw [lintegral_map hf hF, lintegral_prod _ hfF.aemeasurable,
    lintegral_prod _ hf.aemeasurable,
    Measure.lintegral_bind K.aemeasurable hf.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro a
  have hFa : Measurable (fun r : R => F (a, r)) := hF.comp measurable_prodMk_left
  rw [← lintegral_map hf hFa, hlaw a,
    lintegral_prod _ hf.aemeasurable]

theorem measurable_appendHistory_pair (n : ℕ) :
    Measurable (fun x : (↥(Finset.Iic n) → A) × A => appendHistory n x.1 x.2) :=
  measurable_IicProdIoc.comp (measurable_fst.prodMk
    ((MeasurableEquiv.piSingleton (X := fun _ => A) n).measurable.comp measurable_snd))

def residualHistory (F : A × R → A × R) (n : ℕ) (a : A) (r : R) :
    (↥(Finset.Iic n) → A) × R :=
  ((fun i => (F^[i.1] (a, r)).1), (F^[n] (a, r)).2)

theorem measurable_residualHistory (F : A × R → A × R) (hF : Measurable F)
    (n : ℕ) (a : A) : Measurable (residualHistory F n a) :=
  (measurable_pi_lambda _ (fun i : ↥(Finset.Iic n) =>
    ((hF.iterate i.1).comp measurable_prodMk_left).fst)).prodMk
    ((hF.iterate n).comp measurable_prodMk_left).snd

def residualHistoryStep (F : A × R → A × R) (n : ℕ)
    (x : (↥(Finset.Iic n) → A) × R) : (↥(Finset.Iic (n + 1)) → A) × R :=
  let q := F (lastCoordinate n x.1, x.2)
  (appendHistory n x.1 q.1, q.2)

theorem measurable_residualHistoryStep (F : A × R → A × R) (hF : Measurable F) (n : ℕ) :
    Measurable (residualHistoryStep F n) := by
  have hq := hF.comp (((measurable_lastCoordinate n).comp measurable_fst).prodMk measurable_snd)
  exact ((measurable_appendHistory_pair n).comp (measurable_fst.prodMk hq.fst)).prodMk hq.snd

theorem residualHistory_succ (F : A × R → A × R) (n : ℕ) (a : A) :
    residualHistory F (n + 1) a = residualHistoryStep F n ∘ residualHistory F n a := by
  funext r
  apply Prod.ext
  · funext i
    by_cases hi : i.1 ≤ n
    · simp [residualHistory, residualHistoryStep, appendHistory, IicProdIoc, hi]
    · have he : i.1 = n + 1 := by have h := Finset.mem_Iic.mp i.2; omega
      simp [residualHistory, residualHistoryStep, appendHistory, IicProdIoc, hi, he,
        lastCoordinate, MeasurableEquiv.piSingleton, Function.iterate_succ_apply']
  · simp [residualHistory, residualHistoryStep, lastCoordinate, Function.iterate_succ_apply']

theorem residualHistoryStep_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (F : A × R → A × R) (hF : Measurable F) (K : Kernel A A) [IsMarkovKernel K]
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (K a).prod ρ)
    (n : ℕ) (h : ↥(Finset.Iic n) → A) :
    Measure.map (fun r => residualHistoryStep F n (h, r)) ρ =
      (Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) n (n + 1) h).prod ρ := by
  have hm := Measure.map_prod_map (K (lastCoordinate n h)) ρ
    (measurable_appendHistory n h) measurable_id
  have hFa : Measurable (fun r : R => F (lastCoordinate n h, r)) := hF.comp measurable_prodMk_left
  rw [Measure.map_id, ← hlaw (lastCoordinate n h),
    Measure.map_map ((measurable_appendHistory n h).prodMap measurable_id)
      hFa] at hm
  rw [partialTraj_next_apply]
  exact hm.symm

theorem residualHistory_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (F : A × R → A × R) (hF : Measurable F) (K : Kernel A A) [IsMarkovKernel K]
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (K a).prod ρ)
    (n : ℕ) (a : A) :
    Measure.map (residualHistory F n a) ρ =
      (Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 n (fun _ => a)).prod ρ := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.dirac_prod]
      congr 1
      funext r
      apply Prod.ext
      · funext i
        have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
        simp [residualHistory, hi]
      · rfl
  | succ n ih =>
      rw [residualHistory_succ,
        ← Measure.map_map (measurable_residualHistoryStep F hF n) (measurable_residualHistory F hF n a), ih,
        map_product_of_fiber_law ρ _ _ (measurable_residualHistoryStep F hF n) _
          (residualHistoryStep_law ρ F hF K hlaw n),
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.comp_apply]

def residualObservedPath (F : A × R → A × R) (a : A) (r : R) (n : ℕ) : A :=
  (F^[n] (a, r)).1

theorem measurable_residualObservedPath (F : A × R → A × R) (hF : Measurable F) (a : A) :
    Measurable (residualObservedPath F a) :=
  measurable_pi_lambda _ (fun n => ((hF.iterate n).comp measurable_prodMk_left).fst)

theorem deterministicResidual_trajectory_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (F : A × R → A × R) (hF : Measurable F) (K : Kernel A A) [IsMarkovKernel K]
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (K a).prod ρ) (a : A) :
    Measure.map (residualObservedPath F a) ρ = markovTrajectory K a := by
  letI : ∀ n, IsProbabilityMeasure
      (Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 n (fun _ => a)) :=
    fun _ => by infer_instance
  letI : ∀ I, IsFiniteMeasure (inducedFamily (X := fun _ => A)
    (fun n => Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 n (fun _ => a)) I) :=
    fun _ => by infer_instance
  have ht := Kernel.isProjectiveLimit_trajFun (X := fun _ => A) (markovHistoryKernel K) 0 (fun _ => a)
  apply (ht.unique _).symm
  apply (isProjectiveLimit_nat_iff (Kernel.isProjectiveMeasureFamily_partialTraj (X := fun _ => A)
    (markovHistoryKernel K) (fun _ => a)) _).mpr
  intro n
  rw [inducedFamily_Iic]
  change Measure.map (frestrictLe n) (Measure.map (residualObservedPath F a) ρ) = _
  rw [Measure.map_map (measurable_frestrictLe n) (measurable_residualObservedPath F hF a)]
  have h := congrArg (Measure.map (Prod.fst : (↥(Finset.Iic n) → A) × R → _))
    (residualHistory_law ρ F hF K hlaw n a)
  rw [Measure.map_map measurable_fst (measurable_residualHistory F hF n a),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

end StochasticMatching
