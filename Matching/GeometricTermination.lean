import Matching.StoppedKernel
import Mathlib.Analysis.SpecificLimits.Basic

/-! A uniform chance of termination gives an explicit geometric bound on
the number of transitions and almost-sure finite termination.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory ENNReal Topology
namespace StochasticMatching
variable {A : Type*} [MeasurableSpace A]

theorem iterateKernel_geometric_bound (K : Kernel A A) [IsMarkovKernel K]
    (S : Set A) (hS : MeasurableSet S) (q : ℝ≥0∞)
    (hK : ∀ a, K a S ≤ S.indicator (fun _ => q) a) (n : ℕ) (a : A) :
    iterateKernel K n a S ≤ q ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact (measure_mono (subset_univ _)).trans_eq measure_univ
  | succ n ih =>
      calc iterateKernel K (n + 1) a S = ∫⁻ b, K b S ∂iterateKernel K n a :=
          Kernel.comp_apply' _ _ _ hS
        _ ≤ ∫⁻ b, S.indicator (fun _ => q) b ∂iterateKernel K n a := lintegral_mono hK
        _ = q * iterateKernel K n a S := by rw [lintegral_indicator hS]; simp
        _ ≤ q * q ^ n := mul_le_mul_left' ih q
        _ = q ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem markovTrajectory_finite_exit (K : Kernel A A) [IsMarkovKernel K]
    (S : Set A) (hS : MeasurableSet S) (q : ℝ≥0∞) (hq : q < 1)
    (hK : ∀ a, K a S ≤ S.indicator (fun _ => q) a) (a : A) :
    ∀ᵐ z ∂markovTrajectory K a, ∃ n, z n ∉ S := by
  let E : Set (ℕ → A) := {z | ∀ n, z n ∈ S}
  have hb : ∀ n, markovTrajectory K a E ≤ q ^ n := by
    intro n
    have hm : Measurable (fun z : ℕ → A => z n) := measurable_pi_apply n
    calc markovTrajectory K a E ≤ markovTrajectory K a {z | z n ∈ S} :=
        measure_mono (fun z hz => hz n)
      _ = iterateKernel K n a S := by
        rw [← markovTrajectory_coordinate_law K a n, Measure.map_apply hm hS]
        rfl
      _ ≤ q ^ n := iterateKernel_geometric_bound K S hS q hK n a
  have hz : markovTrajectory K a E = 0 := le_antisymm
    (ge_of_tendsto (x := (atTop : Filter ℕ)) (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Eventually.of_forall hb)) (zero_le _)
  apply ae_iff.mpr
  simpa only [not_exists, not_not] using hz

theorem absorbingKernel_geometric_bound (K : Kernel A (Unit ⊕ A)) [IsMarkovKernel K]
    (q : ℝ≥0∞) (hK : ∀ a, K a (Set.range Sum.inr) ≤ q) (n : ℕ) (x : Unit ⊕ A) :
    iterateKernel (absorbingKernel K) n x (Set.range Sum.inr) ≤ q ^ n := by
  apply iterateKernel_geometric_bound _ _ measurableSet_range_inr q _ n x
  intro y
  cases y with
  | inl u =>
      change Measure.dirac (Sum.inl () : Unit ⊕ A) (Set.range Sum.inr) ≤ _
      simp [Measure.dirac_apply' _ measurableSet_range_inr]
  | inr a => simpa using hK a

theorem absorbingTrajectory_finite_termination (K : Kernel A (Unit ⊕ A)) [IsMarkovKernel K]
    (q : ℝ≥0∞) (hq : q < 1) (hK : ∀ a, K a (Set.range Sum.inr) ≤ q) (x : Unit ⊕ A) :
    ∀ᵐ z ∂markovTrajectory (absorbingKernel K) x, ∃ n, z n = Sum.inl () := by
  have hb : ∀ y, absorbingKernel K y (Set.range Sum.inr) ≤
      (Set.range Sum.inr).indicator (fun _ => q) y := by
    intro y
    cases y with
    | inl u =>
        change Measure.dirac (Sum.inl () : Unit ⊕ A) (Set.range Sum.inr) ≤ _
        simp [Measure.dirac_apply' _ measurableSet_range_inr]
    | inr a => simpa using hK a
  filter_upwards [markovTrajectory_finite_exit _ _ measurableSet_range_inr q hq hb x] with z hz
  obtain ⟨n, hn⟩ := hz
  refine ⟨n, ?_⟩
  cases he : z n with
  | inl u => cases u; rfl
  | inr a => exact False.elim (hn ⟨a, he.symm⟩)

end StochasticMatching
