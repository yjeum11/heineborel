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


