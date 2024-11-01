import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

-- closed interval is compact

open Set

theorem close_of_elem_interval (a b : ℝ) (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
  : dist x y ≤ dist a b := by
  simp only [mem_Icc] at *
  simp only [le_abs, abs_le, neg_sub, tsub_le_iff_right, dist]
  right
  constructor <;> linarith

def HasFiniteSubcover {X : Type u} [TopologicalSpace X] (s : Set X) :=
  ∀ (ι : Type u) (U : ι → Set X), (∀ (i : ι), IsOpen (U i)) → s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i

#check HasFiniteSubcover

def NoFiniteSubcover {X : Type u} [TopologicalSpace X] (s : Set X) := 
  ∃ (ι : Type u) (U : ι → Set X), (∀ (i : ι), IsOpen (U i)) ∧ s ⊆ ⋃ i, U i ∧ ∀ (t : Finset ι), ¬s ⊆ ⋃ i ∈ t, U i

set_option pp.explicit true in
#check NoFiniteSubcover
#print NoFiniteSubcover

-- if all subsets of a partition have a finite subcover, their union has a finite subcover

variable {α : Type*} [Fintype α]
variable {a b : ℝ} (aleb : a ≤ b) (abnc : NoFiniteSubcover (Icc a b))

theorem has_finite_subcover_of_partition (P : α → (Set ℝ))
  : (∀ i, HasFiniteSubcover (P i)) → HasFiniteSubcover (⋃ i, P i) := by
  intro h idx C hC hC'
  dsimp [HasFiniteSubcover] at h
  have covered : ∀ i : α, P i ⊆ ⋃ j, C j := by
    intro i
    simp only [iUnion_subset_iff] at hC'
    apply hC'
  have subcovered : ∀ i : α, ∃ t : Finset idx, P i ⊆ ⋃ j ∈ t, C j := by
    intro i
    apply h i idx C hC
    exact covered i
  have choose_finite_subcover : ∃ (t : α → Finset idx), ∀ (i : α), P i ⊆ ⋃ k ∈ t i, C k := by
    choose f hf using subcovered
    use f, hf
  rcases choose_finite_subcover with ⟨t, ht⟩
  let T := ⋃ i ∈ Fintype.elems, Finset.toSet (t i)
  have T_finite : Set.Finite T := by
    exact toFinite T
  have : (∀ i : α, P i ⊆ ⋃ k ∈ T_finite.toFinset, C k) := by
    intro a
    specialize ht a
    dsimp [T]
    intro x hx
    apply mem_of_subset_of_mem ht at hx
    simp
    use a
    constructor
    apply Fintype.complete
    simp at hx
    apply hx
  use Set.Finite.toFinset T_finite
  simp only [iUnion_subset_iff]
  apply this

theorem no_finite_subcover_of_partition (P : α → (Set ℝ))
  : ¬ HasFiniteSubcover (⋃ i, P i) → (∃ i, ¬ HasFiniteSubcover (P i)) := by
  contrapose!
  apply has_finite_subcover_of_partition

theorem isCompact_of_has_finite_subcover (s : Set ℝ) (h : HasFiniteSubcover s) : IsCompact s := by
  apply isCompact_of_finite_subcover
  rw [HasFiniteSubcover] at h
  apply h


-- T 0 = [a, b]
-- T n = nth split of [a, b] such that no finite subcover exists

theorem lemm1 (a b : ℝ) (h : NoFiniteSubcover (Icc a b)) : ∃ c d, NoFiniteSubcover (Icc c d) ∧ Icc c d ⊆ Icc a b ∧ 2 * Metric.diam (Icc c d) ≤ Metric.diam (Icc a b) := sorry

noncomputable def Ts : ℕ → (r : ℝ) × (s : ℝ) ×' NoFiniteSubcover (Icc r s)
  | 0 => ⟨a, b, abnc⟩
  | n + 1 => by
              have prev := lemm1 (Ts n).1 (Ts n).2.1 (Ts n).2.2
              have pf : ∃ c d : ℝ, NoFiniteSubcover (Icc c d) := by 
                rcases prev with ⟨c, d, h⟩
                use c, d
                apply h.1
              let r := Classical.choose pf
              let h := Classical.choose_spec pf
              let s := Classical.choose h
              let g := Classical.choose_spec h
              exact ⟨r, s, g⟩

noncomputable def T (n : ℕ) : Set ℝ := let S := Ts abnc n; Icc S.1 S.2.1

theorem T_ss_T (aleb : a ≤ b) (n : ℕ) : T abnc (n + 1) ⊆ T abnc n := by sorry


theorem diam_T (n : ℕ) : Metric.diam (T abnc n) = (1/2)^n * Metric.diam (T abnc 0) := sorry

theorem bad_sequence : ∃ (x : ℕ → ℝ), ∀ i, x i ∈ T abnc i := sorry

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := by
  apply isCompact_of_has_finite_subcover
  by_contra! h1

  have un : Icc a b = Icc a ((a + b)/2) ∪ Icc ((a + b) / 2) b := by
    have h1 : a ≤ ((a + b) / 2) := by linarith
    have h2 : ((a + b) / 2) ≤ b := by linarith
    simp [Icc_union_Icc_eq_Icc h1 h2]

  sorry
