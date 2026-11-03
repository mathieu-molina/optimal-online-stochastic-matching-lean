import Matching.VectorResidual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! No-completion probabilities and their total hazard along service curves. -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace StochasticMatching

variable {ι : Type*} [Fintype ι]

theorem survivalBox_measure_exp_sum {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    independentExponentials (survivalBox h) = ENNReal.ofReal (Real.exp (-(∑ i, h i))) := by
  rw [survivalBox_measure hh,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos (-h i)).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]

theorem survivalBox_real {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    independentExponentials.real (survivalBox h) = Real.exp (-(∑ i, h i)) := by
  rw [measureReal_def, survivalBox_measure_exp_sum hh,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

def survivedUntil (h : ℝ → ι → ℝ) (T : ℝ) : Set (ι → ℝ) :=
  {z | ∀ u ∈ Icc 0 T, ∀ i, h u i < z i}

omit [Fintype ι] in
theorem survivedUntil_eq_survivalBox {h : ℝ → ι → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmono : ∀ i, MonotoneOn (fun u => h u i) (Icc 0 T)) :
    survivedUntil h T = survivalBox (h T) := by
  ext z
  simp only [survivedUntil, mem_setOf_eq, survivalBox, mem_univ_pi, mem_Ioi]
  constructor
  · intro hz
    exact hz T ⟨hT, le_refl _⟩
  · intro hz u hu i
    exact lt_of_le_of_lt (hmono i hu ⟨hT, le_refl _⟩ hu.2) (hz i)

theorem survivedUntil_probability {h : ℝ → ι → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmono : ∀ i, MonotoneOn (fun u => h u i) (Icc 0 T))
    (hnonneg : ∀ i, 0 ≤ h T i) :
    independentExponentials.real (survivedUntil h T) = Real.exp (-(∑ i, h T i)) := by
  rw [survivedUntil_eq_survivalBox hT hmono]
  exact survivalBox_real hnonneg

noncomputable def survivalCurve (h : ℝ → ι → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(∑ i, h t i))

theorem survivalCurve_pos (h : ℝ → ι → ℝ) (t : ℝ) : 0 < survivalCurve h t :=
  Real.exp_pos _

theorem survivalCurve_initial {h : ℝ → ι → ℝ} (hzero : ∀ i, h 0 i = 0) :
    survivalCurve h 0 = 1 := by simp [survivalCurve, hzero]

theorem hasDerivAt_survivalCurve {h : ℝ → ι → ℝ} {r : ι → ℝ} {t : ℝ}
    (hd : ∀ i, HasDerivAt (fun u => h u i) (r i) t) :
    HasDerivAt (survivalCurve h) (-(∑ i, r i) * survivalCurve h t) t := by
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  convert hs.neg.exp using 1
  dsimp [survivalCurve]
  ring

theorem survivalCurve_derivative_nonpos {h : ℝ → ι → ℝ} {r : ι → ℝ} {t : ℝ}
    (hd : ∀ i, HasDerivAt (fun u => h u i) (r i) t) (hr : ∀ i, 0 ≤ r i) :
    deriv (survivalCurve h) t ≤ 0 := by
  rw [(hasDerivAt_survivalCurve hd).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => hr i))) (survivalCurve_pos h t).le

end StochasticMatching
