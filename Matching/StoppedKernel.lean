import Matching.TrajectoryProjection

/-! Absorbing termination, event-driven state updates, and projection of
complete stopped trajectories.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]

noncomputable def eventUpdateKernel (K : Kernel A E) [IsSFiniteKernel K]
    (U : A × E → C) : Kernel A C := (Kernel.id ×ₖ K).map U

theorem eventUpdateKernel_apply (K : Kernel A E) [IsSFiniteKernel K]
    (U : A × E → C) (hU : Measurable U) (a : A) :
    eventUpdateKernel K U a = Measure.map (fun e => U (a, e)) (K a) := by
  unfold eventUpdateKernel
  rw [Kernel.map_apply _ hU, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hU measurable_prodMk_left]
  rfl

theorem eventUpdateKernel_markov (K : Kernel A E) [IsMarkovKernel K]
    (U : A × E → C) (hU : Measurable U) : IsMarkovKernel (eventUpdateKernel K U) :=
  Kernel.IsMarkovKernel.map _ hU

theorem eventUpdateKernel_projection (K : Kernel A E) [IsSFiniteKernel K]
    (L : Kernel B F) [IsSFiniteKernel L]
    (U : A × E → C) (hU : Measurable U) (V : B × F → D) (hV : Measurable V)
    (f : A → B) (g : E → F) (hg : Measurable g) (q : C → D) (hq : Measurable q)
    (hK : ∀ a, Measure.map g (K a) = L (f a))
    (hUV : ∀ a e, q (U (a, e)) = V (f a, g e)) (a : A) :
    Measure.map q (eventUpdateKernel K U a) = eventUpdateKernel L V (f a) := by
  have hu : Measurable (fun e => U (a, e)) := hU.comp measurable_prodMk_left
  have hv : Measurable (fun e => V (f a, e)) := hV.comp measurable_prodMk_left
  rw [eventUpdateKernel_apply K U hU, Measure.map_map hq hu,
    eventUpdateKernel_apply L V hV, ← hK a, Measure.map_map hv hg]
  congr 1
  funext e
  exact hUV a e

noncomputable def absorbingKernel (K : Kernel A (Unit ⊕ A)) : Kernel (Unit ⊕ A) (Unit ⊕ A) where
  toFun := Sum.elim (fun _ => Measure.dirac (Sum.inl ())) K
  measurable' := measurable_const.sumElim K.measurable

instance absorbingKernel_markov (K : Kernel A (Unit ⊕ A)) [IsMarkovKernel K] :
    IsMarkovKernel (absorbingKernel K) := by
  constructor
  intro x
  cases x with
  | inl u => change IsProbabilityMeasure (Measure.dirac (Sum.inl () : Unit ⊕ A)); infer_instance
  | inr a => change IsProbabilityMeasure (K a); infer_instance

theorem absorbingKernel_projection (K : Kernel A (Unit ⊕ A)) (L : Kernel B (Unit ⊕ B))
    (f : A → B) (hf : Measurable f)
    (hK : ∀ a, Measure.map (Sum.map id f) (K a) = L (f a)) (x : Unit ⊕ A) :
    Measure.map (Sum.map id f) (absorbingKernel K x) = absorbingKernel L (Sum.map id f x) := by
  cases x with
  | inl u =>
      change Measure.map (Sum.map id f) (Measure.dirac (Sum.inl ())) = Measure.dirac (Sum.inl ())
      rw [Measure.map_dirac (measurable_id.sumMap hf)]
      rfl
  | inr a => exact hK a

theorem absorbingTrajectory_projection (K : Kernel A (Unit ⊕ A)) [IsMarkovKernel K]
    (L : Kernel B (Unit ⊕ B)) [IsMarkovKernel L] (f : A → B) (hf : Measurable f)
    (hK : ∀ a, Measure.map (Sum.map id f) (K a) = L (f a)) (x : Unit ⊕ A) :
    Measure.map (fun z : ℕ → Unit ⊕ A => fun n => Sum.map id f (z n))
        (markovTrajectory (absorbingKernel K) x) =
      markovTrajectory (absorbingKernel L) (Sum.map id f x) :=
  markovTrajectory_projection _ _ (Sum.map id f) (measurable_id.sumMap hf)
    (absorbingKernel_projection K L f hf hK) x

theorem absorbingKernel_terminal (K : Kernel A (Unit ⊕ A)) :
    absorbingKernel K (Sum.inl ()) = Measure.dirac (Sum.inl ()) := rfl

theorem absorbingTrajectory_terminal (K : Kernel A (Unit ⊕ A)) [IsMarkovKernel K] :
    ∀ᵐ z ∂markovTrajectory (absorbingKernel K) (Sum.inl ()), ∀ n, z n = Sum.inl () := by
  have hS : MeasurableSet ({Sum.inl ()} : Set (Unit ⊕ A)) := by
    have he : ({Sum.inl ()} : Set (Unit ⊕ A)) = Set.range Sum.inl := by
      ext x
      cases x <;> simp
    rw [he]
    exact measurableSet_range_inl
  apply markovTrajectory_invariant _ {Sum.inl ()} hS
  · intro x hx
    have hx' : x = Sum.inl () := hx
    rw [hx', absorbingKernel_terminal]
    exact (ae_dirac_iff hS).mpr rfl
  · rfl

end StochasticMatching
