import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

-- closed inverval is bounded

open Set

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := sorry
