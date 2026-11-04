import Matching.HistoryService
import Matching.PoissonInputKernel

/-! Measurable assembly of the finite tree of posterior service stages. -/
open MeasureTheory Set
namespace StochasticMatching

theorem measurable_sigma_injection {A : Type*} {B : A → Type*}
    [∀ a, MeasurableSpace (B a)] (a : A) : Measurable (Sigma.mk a : B a → Sigma B) := by
  intro E hE
  exact (MeasurableSpace.measurableSet_iInf.mp hE) a

theorem measurable_sigma_elim {A : Type*} {B : A → Type*} {C : Type*}
    [∀ a, MeasurableSpace (B a)] [MeasurableSpace C] (f : (a : A) → B a → C)
    (hf : ∀ a, Measurable (f a)) : Measurable (fun x : Sigma B => f x.1 x.2) := by
  intro E hE
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro a
  exact hf a hE

namespace HistoryServiceFamily
variable {H B ι : Type*} [MeasurableSpace H] [MeasurableSpace B]

def comap (p : HistoryServiceFamily H ι) (f : B → H) (hf : Measurable f) : HistoryServiceFamily B ι where
  curves b := p.curves (f b)
  deadline_measurable := p.deadline_measurable.comp hf
  service_at_measurable i t := (p.service_at_measurable i t).comp hf
  rate_at_measurable i t := (p.rate_at_measurable i t).comp hf

def sum (p : HistoryServiceFamily H ι) (q : HistoryServiceFamily B ι) :
    HistoryServiceFamily (H ⊕ B) ι where
  curves := Sum.elim p.curves q.curves
  deadline_measurable := p.deadline_measurable.sumElim q.deadline_measurable
  service_at_measurable i t := (p.service_at_measurable i t).sumElim (q.service_at_measurable i t)
  rate_at_measurable i t := (p.rate_at_measurable i t).sumElim (q.rate_at_measurable i t)

def sigma {A : Type*} {C : A → Type*} [∀ a, MeasurableSpace (C a)]
    (p : (a : A) → HistoryServiceFamily (C a) ι) : HistoryServiceFamily (Sigma C) ι where
  curves x := (p x.1).curves x.2
  deadline_measurable := measurable_sigma_elim _ (fun a => (p a).deadline_measurable)
  service_at_measurable i t := measurable_sigma_elim _ (fun a => (p a).service_at_measurable i t)
  rate_at_measurable i t := measurable_sigma_elim _ (fun a => (p a).rate_at_measurable i t)

def idle (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h) : HistoryServiceFamily H ι where
  curves h := idleServiceCurve ι (D h) (hpos h)
  deadline_measurable := hD
  service_at_measurable _ _ := measurable_const
  rate_at_measurable _ _ := measurable_const
end HistoryServiceFamily
end StochasticMatching
