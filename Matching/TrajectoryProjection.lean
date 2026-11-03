import Matching.MarkovTrajectory

/-! A one-step projection identity determines the law of the entire
infinite trajectory, not only its individual time marginals.
-/
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def historyProjection (f : A → B) (n : ℕ) (h : ↥(Finset.Iic n) → A) : ↥(Finset.Iic n) → B :=
  fun i => f (h i)

theorem measurable_historyProjection (f : A → B) (hf : Measurable f) (n : ℕ) :
    Measurable (historyProjection f n) := measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))

def appendHistory (n : ℕ) (h : ↥(Finset.Iic n) → A) (a : A) : ↥(Finset.Iic (n + 1)) → A :=
  IicProdIoc (X := fun _ => A) n (n + 1) (h, MeasurableEquiv.piSingleton (X := fun _ => A) n a)

theorem measurable_appendHistory (n : ℕ) (h : ↥(Finset.Iic n) → A) :
    Measurable (appendHistory n h) := by
  exact measurable_IicProdIoc.comp (measurable_const.prodMk (MeasurableEquiv.piSingleton (X := fun _ => A) n).measurable)

theorem historyProjection_append (f : A → B) (n : ℕ) (h : ↥(Finset.Iic n) → A) (a : A) :
    historyProjection f (n + 1) (appendHistory n h a) = appendHistory n (historyProjection f n h) (f a) := by
  funext i
  by_cases hi : i.val ≤ n
  · simp [historyProjection, appendHistory, IicProdIoc, hi]
  · simp [historyProjection, appendHistory, IicProdIoc, hi, MeasurableEquiv.piSingleton]

theorem partialTraj_next_apply (κ : (n : ℕ) → Kernel (↥(Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) (h : ↥(Finset.Iic n) → A) :
    Kernel.partialTraj (X := fun _ => A) κ n (n + 1) h = Measure.map (appendHistory n h) (κ n h) := by
  have hm : Measurable (IicProdIoc (X := fun _ => A) n (n + 1)) := measurable_IicProdIoc
  have hp : Measurable (Prod.mk h : (↥(Finset.Ioc n (n + 1)) → A) →
      (↥(Finset.Iic n) → A) × (↥(Finset.Ioc n (n + 1)) → A)) := measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hm hp,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ => A) n).measurable,
    Measure.map_map (hm.comp hp) (MeasurableEquiv.piSingleton (X := fun _ => A) n).measurable]
  rfl

theorem partialTraj_markov_step_projection (K : Kernel A A) [IsMarkovKernel K]
    (L : Kernel B B) [IsMarkovKernel L] (f : A → B) (hf : Measurable f)
    (hstep : ∀ a, Measure.map f (K a) = L (f a)) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) n (n + 1)).map (historyProjection f (n + 1)) =
      (Kernel.partialTraj (X := fun _ => B) (markovHistoryKernel L) n (n + 1)).comap
        (historyProjection f n) (measurable_historyProjection f hf n) := by
  ext h : 1
  rw [Kernel.map_apply _ (measurable_historyProjection f hf (n + 1)), Kernel.comap_apply,
    partialTraj_next_apply, partialTraj_next_apply,
    Measure.map_map (measurable_historyProjection f hf (n + 1)) (measurable_appendHistory n h)]
  change Measure.map _ (K (lastCoordinate n h)) =
    Measure.map (appendHistory n (historyProjection f n h)) (L (f (lastCoordinate n h)))
  rw [← hstep, Measure.map_map (measurable_appendHistory n (historyProjection f n h)) hf]
  congr 1
  funext a
  exact historyProjection_append f n h a

theorem partialTraj_markov_projection (K : Kernel A A) [IsMarkovKernel K]
    (L : Kernel B B) [IsMarkovKernel L] (f : A → B) (hf : Measurable f)
    (hstep : ∀ a, Measure.map f (K a) = L (f a)) (n : ℕ) (h : ↥(Finset.Iic 0) → A) :
    Measure.map (historyProjection f n)
        (Kernel.partialTraj (X := fun _ => A) (markovHistoryKernel K) 0 n h) =
      Kernel.partialTraj (X := fun _ => B) (markovHistoryKernel L) 0 n (historyProjection f 0 h) := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.partialTraj_self, Kernel.id_apply, Kernel.id_apply,
        Measure.map_dirac (measurable_historyProjection f hf 0)]
  | succ n ih =>
      rw [← Kernel.map_apply _ (measurable_historyProjection f hf (n + 1)),
        Kernel.partialTraj_succ_eq_comp (κ := markovHistoryKernel K) (X := fun _ => A) (Nat.zero_le n), Kernel.map_comp,
        partialTraj_markov_step_projection K L f hf hstep n,
        ← Kernel.comp_map _ _ (measurable_historyProjection f hf n), Kernel.comp_apply,
        Kernel.map_apply _ (measurable_historyProjection f hf n), ih,
        Kernel.partialTraj_succ_eq_comp (κ := markovHistoryKernel L) (X := fun _ => B) (Nat.zero_le n), Kernel.comp_apply]

theorem markovTrajectory_projection (K : Kernel A A) [IsMarkovKernel K]
    (L : Kernel B B) [IsMarkovKernel L] (f : A → B) (hf : Measurable f)
    (hstep : ∀ a, Measure.map f (K a) = L (f a)) (a : A) :
    Measure.map (fun z : ℕ → A => fun n => f (z n)) (markovTrajectory K a) =
      markovTrajectory L (f a) := by
  let F : (ℕ → A) → (ℕ → B) := fun z n => f (z n)
  have hF : Measurable F := measurable_pi_lambda _ (fun n => hf.comp (measurable_pi_apply n))
  letI : ∀ n, IsProbabilityMeasure (Kernel.partialTraj (X := fun _ => B)
      (markovHistoryKernel L) 0 n (fun _ => f a)) := fun _ => by infer_instance
  letI : ∀ I, IsFiniteMeasure (inducedFamily (X := fun _ => B) (fun n => Kernel.partialTraj (X := fun _ => B)
      (markovHistoryKernel L) 0 n (fun _ => f a)) I) := fun _ => by infer_instance
  have ht := Kernel.isProjectiveLimit_trajFun (X := fun _ => B) (markovHistoryKernel L) 0 (fun _ => f a)
  apply (ht.unique _).symm
  apply (isProjectiveLimit_nat_iff (Kernel.isProjectiveMeasureFamily_partialTraj (X := fun _ => B)
    (markovHistoryKernel L) (fun _ => f a)) _).mpr
  intro n
  rw [inducedFamily_Iic]
  change Measure.map (frestrictLe n) (Measure.map F (markovTrajectory K a)) = _
  rw [Measure.map_map (measurable_frestrictLe n) hF]
  have he : frestrictLe n ∘ F = historyProjection f n ∘ frestrictLe n := rfl
  rw [he, ← Measure.map_map (measurable_historyProjection f hf n) (measurable_frestrictLe n)]
  unfold markovTrajectory
  rw [Kernel.traj_map_frestrictLe_apply, partialTraj_markov_projection K L f hf hstep n]
  rfl

end StochasticMatching
