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

def HasFiniteSubcover {X : Type u} [TopologicalSpace X] (s : Set X) := ∀ {ι : Type u} (U : ι → Set X), (∀ (i : ι), IsOpen (U i)) → s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i

-- if all subsets of a partition have a finite subcover, their union has a finite subcover

variable {α : Type*} [Fintype α]

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
    apply h i C hC
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

variable {a b : ℝ} {aleb : a ≤ b} (abnc : ¬ HasFiniteSubcover (Icc a b))

def Icc_csplit (a b : ℝ) (left : Bool) : Set ℝ := 
  if left then Icc a ((a + b) / 2)
          else Icc ((a + b) / 2) b

theorem Icc_eq_union_csplit : Icc a b = ⋃ i, Icc_csplit a b i := by
  simp [Icc_csplit]
  ext x
  constructor
  . intro h
    simp only [mem_iUnion, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte, mem_Icc]
    simp only [mem_Icc] at h
    by_cases h1 : (a + b) / 2 ≤ x
    . left
      exact ⟨h1, h.2⟩
    . right
      constructor
      exact h.1
      linarith
  . simp only [mem_iUnion, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte, mem_Icc]
    intro h
    rcases h with h | h
    . have : a ≤ x := by linarith
      exact ⟨this, h.2⟩
    . have : x ≤ b := by linarith
      exact ⟨h.1, this⟩

-- for an interval with no finitesubcover, there exists a bool st it has no finitesubcover
theorem exists_subinterval_bool (ha : ¬ HasFiniteSubcover (Icc a b)) 
  : ∃ v, ¬ HasFiniteSubcover (Icc_csplit a b v) := by
  rw [Icc_eq_union_csplit] at ha
  apply no_finite_subcover_of_partition
  apply ha

theorem icc_sup (a b : ℝ) (h : a ≤ b): sSup (Icc a b) = b := csSup_Icc h
theorem icc_inf (a b : ℝ) (h : a ≤ b): sInf (Icc a b) = a := csInf_Icc h

-- T 0 = [a, b]
-- T n = nth split of [a, b] such that no finite subcover exists

noncomputable def V (h : ¬ HasFiniteSubcover (Icc a b)) : Bool :=
  Classical.choose (exists_subinterval_bool h)

noncomputable def T (h : ¬ HasFiniteSubcover (Icc a b)) : ℕ → Set ℝ
  | 0 => Icc a b
  | n + 1 => Icc_csplit (sSup (T h n)) (sInf (T h n)) (V h)

theorem no_finite_subcover_in_set (n : ℕ) : ¬ HasFiniteSubcover (T abnc n) := by
  induction' n with n ih
  . simp [T]; assumption
  simp [T]
  -- split_ifs
  sorry

theorem diam_T : ∀ n, Metric.diam (T abnc n) = (1/2)^n * Metric.diam (T abnc 0) := sorry

theorem bad_sequence : ∃ (x : ℕ → ℝ), ∀ i, x i ∈ T abnc i := sorry

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := by
  apply isCompact_of_has_finite_subcover
  by_contra! h1

  have un : Icc a b = Icc a ((a + b)/2) ∪ Icc ((a + b) / 2) b := by
    have h1 : a ≤ ((a + b) / 2) := by linarith
    have h2 : ((a + b) / 2) ≤ b := by linarith
    simp [Icc_union_Icc_eq_Icc h1 h2]

  sorry 
