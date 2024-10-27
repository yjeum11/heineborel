import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

variable (n : Type*) [Fintype n] (S : Set (n → ℝ))
#check IsCompact S

open Bornology

/- Compact → Closed and Bounded -/

/- ------------------------------------------------------------------------- -/

/- Closed and Bounded → Compact -/

/-
crux of the proof -
n-cell is compact.
[-a, a]^n is compact
-/

variable (ι : Type*) [Fintype ι]

-- Show that every bounded set is a subset of some box
theorem bounded_subset_box (A : Set (ι → ℝ)) (hA : IsBounded A) : ∃ r, A ⊆ BoxIntegral.Box.Icc r := by
  rw [Metric.isBounded_iff_subset_closedBall 0] at hA
  rcases hA with ⟨r, hA⟩
  have rpos : r ≥ 0 := by sorry
  use r
  have : Metric.closedBall 0 r ⊆ nBox r n := by
    intro x hx
    simp only [nBox, Real.norm_eq_abs, Set.mem_setOf_eq]
    simp only [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq] at hx
    simp only [Real.norm_eq_abs, Real.sqrt_le_left rpos] at hx
    by_contra!
    rcases this with ⟨i, hi⟩

    sorry
  sorry
  -- trans
  -- apply hA
  -- apply this

/-
Show that box is compact.
AFSOC box is not compact i.e. has an open cover with no finite subcover. Call it C

Let T₀ = [-a, a]ⁿ

Bisect each of the sides to get 2ⁿ boxes.
Since C has no finite subcover there must be one sub-box which can't be covered
  by a finite subcover. Call that T₁.

Repeat the process to get an infinite sequence T0, T1, ...
-- Note that the side length of T_k is (2a)/(2^k)
-- might need to make this in terms of diameter
-- also note that ∀ k, T_k can't be finitely covered

Define a sequence (x_k) such that x_k is in T_k

Define a sequence (S_k) such that S_k = ⋂ 0..k, T_k


The sequence converges to some L because it's Cauchy?
-- using the side length/diameter property

L is in T_k for all k because T_k is closed?

Let L ∈ U for some open set U ∈ C since C covers T0

There must be some ball B that contains L and is a subset of C

There must be some T_k that is a subset of B, so it is covered finitely for the
contradiction
-/

def nBox_div (n : ℕ) (a : ℝ) (k : ℕ) =

-- Is this the right way to say "every box"?
theorem isCompact_of_box (A : Set (EucR n)) (boxA : A = nBox r n)
  : IsCompact A := by
  apply isCompact_of_finite_subcover
  intro I C hC AsC
  by_contra!


-- Show that a closed subset of a compact set is compact
theorem isCompact_of_ss_compact_isClosed (A : Set (EucR n)) (clsdA : IsClosed A) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (AssK : A ⊆ K)
  : IsCompact A := sorry

-- Final theorem
theorem isCompact_of_closed_and_bounded {n : ℕ} (A : Set (EucR n)) (bndA : IsBounded A) (clsdA : IsClosed A) : IsCompact A := sorry
