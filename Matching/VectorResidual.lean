import Matching.ExponentialResidual
import Mathlib.MeasureTheory.Constructions.Pi

/-! Finite-product memorylessness under fixed coordinatewise survival thresholds. -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι]

noncomputable def independentExponentials : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => unitExponential)

instance independentExponentials_probability :
    IsProbabilityMeasure (independentExponentials (ι := ι)) := by
  unfold independentExponentials
  infer_instance

def survivalBox (h : ι → ℝ) : Set (ι → ℝ) := univ.pi (fun i => Ioi (h i))

noncomputable def vectorResidualLaw (h : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.map (fun z i => z i - h i) (independentExponentials.restrict (survivalBox h))

omit [Fintype ι] in
theorem measurable_subtract_threshold (h : ι → ℝ) :
    Measurable (fun z : ι → ℝ => fun i => z i - h i) := by
  apply measurable_pi_lambda
  intro i
  exact (show Measurable (fun z : ι → ℝ => z i) from measurable_pi_apply i).sub_const (h i)

theorem measurableSet_survivalBox (h : ι → ℝ) : MeasurableSet (survivalBox h) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)

theorem vectorResidualLaw_eq_pi (h : ι → ℝ) :
    vectorResidualLaw h = Measure.pi (fun i => residualLaw (h i)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hset : (fun z : ι → ℝ => fun i => z i - h i) ⁻¹' univ.pi s ∩ survivalBox h =
      univ.pi (fun i => (fun x : ℝ => x - h i) ⁻¹' s i ∩ Ioi (h i)) := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_univ_pi, survivalBox]
    constructor
    · intro hz i
      exact ⟨hz.1 i, hz.2 i⟩
    · intro hz
      exact ⟨fun i => (hz i).1, fun i => (hz i).2⟩
  rw [vectorResidualLaw, Measure.map_apply (measurable_subtract_threshold h)
    (MeasurableSet.univ_pi hs),
    Measure.restrict_apply ((measurable_subtract_threshold h) (MeasurableSet.univ_pi hs)),
    hset, independentExponentials, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  have hm : Measurable (fun x : ℝ => x - h i) := measurable_id.sub_const (h i)
  rw [residualLaw, Measure.map_apply hm (hs i), Measure.restrict_apply (hm (hs i))]

theorem pi_scaled_exponentials (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • unitExponential) =
      (∏ i, c i) • (independentExponentials (ι := ι)) := by
  letI : ∀ i, IsFiniteMeasure (c i • unitExponential) := fun i =>
    ⟨by simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      using (lt_top_iff_ne_top.mpr (hc i))⟩
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, smul_eq_mul, independentExponentials,
    Measure.pi_pi, Finset.prod_mul_distrib]

theorem vectorResidualLaw_eq_smul {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    vectorResidualLaw h = (∏ i, ENNReal.ofReal (Real.exp (-h i))) •
      (independentExponentials (ι := ι)) := by
  rw [vectorResidualLaw_eq_pi]
  simp_rw [residualLaw_eq_smul (hh _)]
  exact pi_scaled_exponentials _ (fun _ => ENNReal.ofReal_ne_top)

theorem survivalBox_measure {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    independentExponentials (survivalBox h) =
      ∏ i, ENNReal.ofReal (Real.exp (-h i)) := by
  rw [independentExponentials, survivalBox, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact unitExponential_Ioi (hh i)

theorem survivalBox_measure_ne_zero {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    independentExponentials (survivalBox h) ≠ 0 := by
  rw [survivalBox_measure hh]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simp [Real.exp_pos])

theorem normalized_vectorResidualLaw {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    (independentExponentials (survivalBox h))⁻¹ • vectorResidualLaw h =
      (independentExponentials (ι := ι)) := by
  rw [vectorResidualLaw_eq_smul hh, ← survivalBox_measure hh, smul_smul,
    ENNReal.inv_mul_cancel (survivalBox_measure_ne_zero hh) (measure_ne_top _ _), one_smul]

end StochasticMatching
