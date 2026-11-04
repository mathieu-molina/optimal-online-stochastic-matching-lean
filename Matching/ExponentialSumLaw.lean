import Matching.ExponentialMean
import Matching.PoissonAddition
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual distributions of finite sums of independent unit exponentials.
The recursive distribution is connected to arbitrary independent variables
and to every subset of the product demand model.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching

noncomputable def exponentialSumLaw : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
      (unitExponential.prod (exponentialSumLaw n))

instance exponentialSumLaw_probability (n : ℕ) : IsProbabilityMeasure (exponentialSumLaw n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac (0 : ℝ)); infer_instance
  | succ n ih =>
    letI := ih
    exact isProbabilityMeasure_map (measurable_fst.add measurable_snd).aemeasurable

theorem exponentialSumLaw_ae_nonneg (n : ℕ) : ∀ᵐ x ∂exponentialSumLaw n, 0 ≤ x := by
  induction n with
  | zero => simp [exponentialSumLaw]
  | succ n ih =>
    rw [exponentialSumLaw, ae_map_iff (measurable_fst.add measurable_snd).aemeasurable measurableSet_Ici]
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const (measurable_fst.add measurable_snd))).mpr
    filter_upwards [unitExponential_ae_pos] with x hx
    exact ih.mono (fun y hy => add_nonneg hx.le hy)

theorem exponential_finset_sum_law {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, Measure.map (X i) μ = unitExponential) :
    Measure.map (fun ω => ∑ i ∈ S, X i ω) μ = exponentialSumLaw S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [exponentialSumLaw]
  | @insert i S hi ih =>
    rw [Finset.card_insert_of_not_mem hi, exponentialSumLaw]
    have hm := Finset.measurable_sum S (fun j _ => hX j)
    have hInd := (hind.indepFun_finset_sum_of_not_mem hX hi).symm
    have he : (∑ j ∈ S, X j) = fun ω => ∑ j ∈ S, X j ω := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hInd
    have hp := (indepFun_iff_map_prod_eq_prod_map_map (hX i).aemeasurable hm.aemeasurable).mp hInd
    rw [hlaw i, ih] at hp
    rw [← hp, Measure.map_map (measurable_fst.add measurable_snd) ((hX i).prodMk hm)]
    congr 1
    funext ω
    simp [hi]

theorem independentExponentials_coordinates_independent {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (z : ι → ℝ) => z i) independentExponentials := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp only [independentExponentials_coordinate_law]
  exact Measure.map_id

theorem independentExponentials_subset_sum_law {ι : Type*} [Fintype ι] (S : Finset ι) :
    Measure.map (fun z : ι → ℝ => ∑ i ∈ S, z i) independentExponentials = exponentialSumLaw S.card :=
  exponential_finset_sum_law independentExponentials S (fun i z => z i) measurable_pi_apply
    independentExponentials_coordinates_independent independentExponentials_coordinate_law

theorem exponentialSumLaw_tail_recursion (n : ℕ) (a : ℝ) :
    (exponentialSumLaw (n + 1)).real (Ioi a) =
      ∫ x, (exponentialSumLaw n).real (Ioi (a - x)) ∂unitExponential := by
  classical
  let E : Set (ℝ × ℝ) := {p | a < p.1 + p.2}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_fst.add measurable_snd)
  have hi := integrable_event_constant (unitExponential.prod (exponentialSumLaw n)) E hE 1
  have he := integral_event_constant (unitExponential.prod (exponentialSumLaw n)) E hE 1
  rw [mul_one] at he
  rw [exponentialSumLaw, map_measureReal_apply (measurable_fst.add measurable_snd) measurableSet_Ioi]
  change (unitExponential.prod (exponentialSumLaw n)).real E = _
  rw [← he, integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have h := integral_event_constant (exponentialSumLaw n) (Ioi (a - x)) measurableSet_Ioi 1
  rw [mul_one] at h
  convert h using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  have hiff : (x, y) ∈ E ↔ y ∈ Ioi (a - x) := by
    change a < x + y ↔ a - x < y
    constructor <;> intro h <;> linarith
  simp only [hiff]

end StochasticMatching
