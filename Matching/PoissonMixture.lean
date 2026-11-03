import Matching.PoissonWeights
import Mathlib.MeasureTheory.Integral.Layercake

/-! Bounded random-count mixtures of Poisson lower tails. Integration over
the intensity parameter recovers the expected count. A nonnegative random
variable with these mixture tails therefore has the same expectation.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_nat_expansion (D : Ω → ℕ) (M : ℕ) (hD : ∀ ω, D ω ≤ M)
    (φ : ℕ → ℝ) (ω : Ω) :
    φ (D ω) = ∑ n ∈ Finset.range (M + 1), if D ω = n then φ n else 0 := by
  classical
  simp [Finset.sum_ite_eq', Nat.lt_succ_of_le (hD ω)]

theorem integrable_bounded_nat_function (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℕ) (hDm : Measurable D) (M : ℕ) (hD : ∀ ω, D ω ≤ M) (φ : ℕ → ℝ) :
    Integrable (fun ω => φ (D ω)) μ := by
  classical
  have he : (fun ω => φ (D ω)) = fun ω =>
      ∑ n ∈ Finset.range (M + 1), if D ω = n then φ n else 0 :=
    funext (bounded_nat_expansion D M hD φ)
  rw [he]
  apply integrable_finset_sum
  intro n _
  exact integrable_event_constant μ {ω | D ω = n} ((measurableSet_singleton n).preimage hDm) (φ n)

theorem integral_bounded_nat_function (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℕ) (hDm : Measurable D) (M : ℕ) (hD : ∀ ω, D ω ≤ M) (φ : ℕ → ℝ) :
    (∫ ω, φ (D ω) ∂μ) =
      ∑ n ∈ Finset.range (M + 1), μ.real {ω | D ω = n} * φ n := by
  classical
  have he : (fun ω => φ (D ω)) = fun ω =>
      ∑ n ∈ Finset.range (M + 1), if D ω = n then φ n else 0 :=
    funext (bounded_nat_expansion D M hD φ)
  have hi : ∀ n ∈ Finset.range (M + 1), Integrable (fun ω => if D ω = n then φ n else 0) μ := by
    intro n _
    exact integrable_event_constant μ {ω | D ω = n} ((measurableSet_singleton n).preimage hDm) (φ n)
  rw [he, integral_finset_sum _ hi]
  apply Finset.sum_congr rfl
  intro n _
  exact integral_event_constant μ {ω | D ω = n} ((measurableSet_singleton n).preimage hDm) (φ n)

theorem integrable_poisson_mixture_intensity (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℕ) (hDm : Measurable D) (M : ℕ) (hD : ∀ ω, D ω ≤ M) :
    IntegrableOn (fun a : ℝ => ∫ ω, poissonLowerTail a (D ω) ∂μ) (Ioi 0) := by
  simp_rw [integral_bounded_nat_function μ D hDm M hD]
  exact integrable_finset_sum _ (fun n _ => (integrable_poissonLowerTail_intensity n).const_mul _)

theorem integral_poisson_mixture_intensity (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℕ) (hDm : Measurable D) (M : ℕ) (hD : ∀ ω, D ω ≤ M) :
    (∫ a : ℝ in Ioi 0, ∫ ω, poissonLowerTail a (D ω) ∂μ) = ∫ ω, (D ω : ℝ) ∂μ := by
  simp_rw [integral_bounded_nat_function μ D hDm M hD]
  rw [integral_finset_sum _ (fun n _ => (integrable_poissonLowerTail_intensity n).const_mul _)]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul, integral_poissonLowerTail_intensity]

variable {Ω' : Type*} [MeasurableSpace Ω']

theorem expected_value_eq_count_of_poisson_mixture_tails
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure Ω')
    (D : Ω → ℕ) (hDm : Measurable D) (M : ℕ) (hD : ∀ ω, D ω ≤ M)
    (X : Ω' → ℝ) (hXi : Integrable X ν) (hX0 : 0 ≤ᵐ[ν] X)
    (htail : ∀ a : ℝ, 0 < a → ν.real {ω | a < X ω} = ∫ ω, poissonLowerTail a (D ω) ∂μ) :
    (∫ ω, X ω ∂ν) = ∫ ω, (D ω : ℝ) ∂μ := by
  rw [hXi.integral_eq_integral_meas_lt hX0]
  calc
    _ = ∫ a : ℝ in Ioi 0, ∫ ω, poissonLowerTail a (D ω) ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact htail a ha
    _ = _ := integral_poisson_mixture_intensity μ D hDm M hD

end StochasticMatching
