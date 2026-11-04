import Matching.InfiniteRenewal
import Matching.RecycledResidualSlots

/-! Split an infinite renewal stream into its first exponential waiting
amount and the independent entire future stream. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching

def prependWaiting (x : ℝ × (ℕ → ℝ)) (n : ℕ) : ℝ :=
  match n with
  | 0 => x.1
  | k + 1 => x.2 k

theorem measurable_prependWaiting : Measurable prependWaiting := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

theorem infiniteExponentials_prepend_law :
    Measure.map prependWaiting (unitExponential.prod infiniteExponentials) = infiniteExponentials := by
  apply Measure.eq_infinitePi
  intro S E hE
  let T := S.preimage Nat.succ Nat.succ_injective.injOn
  have hT : ∀ n, n ∈ T ↔ n + 1 ∈ S := by intro n; simp [T]
  have himage : T.image Nat.succ = S.erase 0 := by
    ext n
    cases n with
    | zero => simp [T]
    | succ n => simp [T]
  have hbox : prependWaiting ⁻¹' Set.pi (↑S) E =
      (if 0 ∈ S then E 0 else Set.univ) ×ˢ Set.pi (↑T) (fun n => E (n + 1)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod]
    constructor
    · intro hx
      constructor
      · split_ifs with h0
        · exact hx 0 h0
        · trivial
      · intro n hn
        exact hx (n + 1) ((hT n).mp hn)
    · rintro ⟨hx0, hxT⟩ n hn
      cases n with
      | zero => simpa only [if_pos hn] using hx0
      | succ n => exact hxT n ((hT n).mpr hn)
  have hTmeas : ∀ n ∈ T, MeasurableSet (E (n + 1)) := fun n hn => hE _ ((hT n).mp hn)
  have h0meas : MeasurableSet (if 0 ∈ S then E 0 else Set.univ) := by
    split_ifs with h0
    · exact hE 0 h0
    · exact MeasurableSet.univ
  rw [Measure.map_apply measurable_prependWaiting (MeasurableSet.pi S.countable_toSet hE),
    hbox, Measure.prod_prod, infiniteExponentials, Measure.infinitePi_pi (μ := fun _ : ℕ => unitExponential) (s := T) hTmeas]
  have hp : (∏ n ∈ T, unitExponential (E (n + 1))) =
      ∏ n ∈ S.erase 0, unitExponential (E n) := by
    rw [← himage, Finset.prod_image]
    exact fun _ _ _ _ h => Nat.succ_injective h
  rw [hp]
  by_cases h0 : 0 ∈ S
  · rw [if_pos h0]
    exact Finset.mul_prod_erase S (fun n => unitExponential (E n)) h0
  · rw [if_neg h0, measure_univ, one_mul, Finset.erase_eq_of_not_mem h0]

def splitWaiting (z : ℕ → ℝ) : ℝ × (ℕ → ℝ) := (z 0, fun n => z (n + 1))

theorem measurable_splitWaiting : Measurable splitWaiting :=
  (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ (fun n => measurable_pi_apply (n + 1)))

theorem splitWaiting_prepend (x : ℝ × (ℕ → ℝ)) : splitWaiting (prependWaiting x) = x := rfl

theorem prependWaiting_split (z : ℕ → ℝ) : prependWaiting (splitWaiting z) = z := by
  funext n
  cases n <;> rfl

theorem infiniteExponentials_split_law :
    Measure.map splitWaiting infiniteExponentials = unitExponential.prod infiniteExponentials := by
  conv_lhs => rw [← infiniteExponentials_prepend_law]
  rw [Measure.map_map measurable_splitWaiting measurable_prependWaiting]
  change Measure.map (fun x => splitWaiting (prependWaiting x)) _ = _
  simp only [splitWaiting_prepend]
  exact Measure.map_id

end StochasticMatching
