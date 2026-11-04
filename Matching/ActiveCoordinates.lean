import Matching.CompletionState

/-!
Surviving jobs retain their original labels. Extending rates by zero on
completed jobs preserves feasibility in any nonnegative downward-closed region.
-/

namespace StochasticMatching

variable {ι : Type*} [DecidableEq ι]

def Active (D : Finset ι) := {i : ι // i ∉ D}

def maskCompleted (D : Finset ι) (v : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ D then 0 else v i

def liftActive (D : Finset ι) (v : Active D → ℝ) (i : ι) : ℝ :=
  if hi : i ∉ D then v ⟨i, hi⟩ else 0

def restrictActive (D : Finset ι) (v : ι → ℝ) (i : Active D) : ℝ := v i.val

theorem liftActive_of_active (D : Finset ι) (v : Active D → ℝ)
    (i : Active D) : liftActive D v i.val = v i := by
  simp [liftActive, i.property]

theorem liftActive_of_completed (D : Finset ι) (v : Active D → ℝ)
    {i : ι} (hi : i ∈ D) : liftActive D v i = 0 := by
  simp [liftActive, hi]

theorem restrict_liftActive (D : Finset ι) (v : Active D → ℝ) :
    restrictActive D (liftActive D v) = v := by
  funext i
  exact liftActive_of_active D v i

theorem lift_restrictActive (D : Finset ι) (v : ι → ℝ) :
    liftActive D (restrictActive D v) = maskCompleted D v := by
  funext i
  by_cases hi : i ∈ D <;> simp [liftActive, restrictActive, maskCompleted, hi]

theorem liftActive_injective (D : Finset ι) : Function.Injective (liftActive D) := by
  intro v w h
  have := congrArg (restrictActive D) h
  simpa only [restrict_liftActive] using this

theorem maskCompleted_nonneg (D : Finset ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ maskCompleted D v i := by
  intro i
  by_cases hi : i ∈ D <;> simp [maskCompleted, hi, hv i]

theorem maskCompleted_le (D : Finset ι) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) : ∀ i, maskCompleted D v i ≤ v i := by
  intro i
  by_cases hi : i ∈ D <;> simp [maskCompleted, hi, hv i]

theorem maskCompleted_idempotent (D : Finset ι) (v : ι → ℝ) :
    maskCompleted D (maskCompleted D v) = maskCompleted D v := by
  funext i
  by_cases hi : i ∈ D <;> simp [maskCompleted, hi]

theorem maskCompleted_of_subset {D E : Finset ι} (hDE : D ⊆ E) (v : ι → ℝ) :
    maskCompleted E (maskCompleted D v) = maskCompleted E v := by
  funext i
  by_cases hi : i ∈ E
  · simp [maskCompleted, hi]
  · have hiD : i ∉ D := fun h => hi (hDE h)
    simp [maskCompleted, hi, hiD]

/-- Coordinates of a later active set are included in the earlier active set
without renumbering any job. -/
def activeInclusion {D E : Finset ι} (hDE : D ⊆ E) (i : Active E) : Active D :=
  ⟨i.val, fun hi => i.property (hDE hi)⟩

omit [DecidableEq ι] in
theorem activeInclusion_label {D E : Finset ι} (hDE : D ⊆ E) (i : Active E) :
    (activeInclusion hDE i).val = i.val := rfl

omit [DecidableEq ι] in
theorem activeInclusion_injective {D E : Finset ι} (hDE : D ⊆ E) :
    Function.Injective (activeInclusion hDE) := by
  intro i j hij
  exact Subtype.ext (congrArg (fun x : Active D => x.val) hij)

theorem liftActive_restrict_survivors {D E : Finset ι} (hDE : D ⊆ E)
    (v : Active D → ℝ) :
    liftActive E (fun i => v (activeInclusion hDE i)) =
      maskCompleted E (liftActive D v) := by
  funext i
  by_cases hi : i ∈ E
  · simp [liftActive, maskCompleted, hi]
  · have hiD : i ∉ D := fun h => hi (hDE h)
    simp [liftActive, maskCompleted, hi, hiD, activeInclusion]

def NonnegDownwardClosed (P : Set (ι → ℝ)) : Prop :=
  ∀ {v w : ι → ℝ}, v ∈ P → (∀ i, 0 ≤ w i) → (∀ i, w i ≤ v i) → w ∈ P

theorem maskCompleted_mem {P : Set (ι → ℝ)} (hP : NonnegDownwardClosed P)
    (D : Finset ι) {v : ι → ℝ} (hvP : v ∈ P) (hv : ∀ i, 0 ≤ v i) :
    maskCompleted D v ∈ P :=
  hP hvP (maskCompleted_nonneg D v hv) (maskCompleted_le D v hv)

theorem liftActive_nonneg (D : Finset ι) (v : Active D → ℝ)
    (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ liftActive D v i := by
  intro i
  by_cases hi : i ∉ D <;> simp [liftActive, hi, hv]

theorem survivor_rates_feasible {P : Set (ι → ℝ)} (hP : NonnegDownwardClosed P)
    {D E : Finset ι} (hDE : D ⊆ E) (v : Active D → ℝ)
    (hvP : liftActive D v ∈ P) (hv : ∀ i, 0 ≤ v i) :
    liftActive E (fun i => v (activeInclusion hDE i)) ∈ P := by
  rw [liftActive_restrict_survivors hDE v]
  exact maskCompleted_mem hP E hvP (liftActive_nonneg D v hv)

end StochasticMatching
