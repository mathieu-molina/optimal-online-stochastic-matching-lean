import Matching.HardMarkedPotential
import Matching.KernelSupersolution

/-! General arrival-by-arrival randomized online controllers. A state may
store arbitrary observed history and internal randomness. The joint kernel
chooses the mark and next state; its type/time marginal must be the fresh
Poisson next-arrival law. Thus future input cannot be used by the decision.
Terminal states retain the unmatched set. -/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSpace (Option ι)] [MeasurableSpace (Finset ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ]

abbrev ControllerState (H ι : Type*) := Finset ι ⊕ H
abbrev ControllerEvent (σ ι : Type*) := Unit ⊕ (ℝ × (σ × Option ι))

def ControllerStepValid (N : σ → Finset ι) (T : H → ℝ) (A : H → Finset ι)
    (h : H) (y : ControllerEvent σ ι × ControllerState H ι) : Prop :=
  match y.1 with
  | .inl _ => y.2 = .inl (A h)
  | .inr p =>
      (∀ i, p.2.2 = some i → i ∈ N p.2.1 ∩ A h) ∧
      match y.2 with
      | .inl B => B = unmatchedAfterMark (A h) p.2.2
      | .inr h' => A h' = unmatchedAfterMark (A h) p.2.2 ∧ T h' = T h - p.1

structure PoissonOnlineController (N : σ → Finset ι) (intensity : σ → ℝ≥0) where
  horizon : H → ℝ
  horizon_pos : ∀ h, 0 < horizon h
  horizon_measurable : Measurable horizon
  available : H → Finset ι
  available_measurable : Measurable available
  next : Kernel H (ControllerEvent σ ι × ControllerState H ι)
  probability : ∀ h, IsProbabilityMeasure (next h)
  input_law : ∀ h, Measure.map (fun y => arrivalTypeProjection y.1) (next h) =
    poissonNextArrival (fun s => (intensity s : ℝ)) (horizon h)
  valid : ∀ h, ∀ᵐ y ∂next h, ControllerStepValid N horizon available h y

namespace PoissonOnlineController
variable {N : σ → Finset ι} {intensity : σ → ℝ≥0}

noncomputable def step (P : PoissonOnlineController (H := H) N intensity) :
    Kernel (ControllerState H ι) (ControllerState H ι) where
  toFun := Sum.elim (fun A => Measure.dirac (.inl A)) (fun h => Measure.map Prod.snd (P.next h))
  measurable' := (Measure.measurable_dirac.comp measurable_inl).sumElim
    ((Measure.measurable_map _ measurable_snd).comp P.next.measurable)

instance step_markov (P : PoissonOnlineController (H := H) N intensity) : IsMarkovKernel P.step := by
  constructor
  intro x
  cases x with
  | inl A => change IsProbabilityMeasure (Measure.dirac (.inl A : ControllerState H ι)); infer_instance
  | inr h =>
      letI := P.probability h
      exact isProbabilityMeasure_map measurable_snd.aemeasurable

def remaining (P : PoissonOnlineController (H := H) N intensity) : ControllerState H ι → Finset ι :=
  Sum.elim id P.available

theorem remaining_measurable (P : PoissonOnlineController (H := H) N intensity) :
    Measurable P.remaining := measurable_id.sumElim P.available_measurable

noncomputable def reward (P : PoissonOnlineController (H := H) N intensity) (x : ControllerState H ι) : ℝ :=
  (Fintype.card ι : ℝ) - (P.remaining x).card

noncomputable def expectedReward (P : PoissonOnlineController (H := H) N intensity) (h : H) : ℝ :=
  kernelExpectedReward P.step P.reward (.inr h)

end PoissonOnlineController
end StochasticMatching
