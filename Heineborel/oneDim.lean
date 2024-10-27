import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

-- closed interval is compact

open Set

def HasFiniteSubcover {X : Type u} [TopologicalSpace X] (s : Set X) := ∀ {ι : Type u} (U : ι → Set X), (∀ (i : ι), IsOpen (U i)) → s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i

#check HasFiniteSubcover
#check IsCompact

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

-- define a split of an interval. T 0 = [a, b] and T n+1 [a

def Icc_csplit (a b : ℝ) (left : Bool) : Set ℝ := 
  if left then Icc a ((a + b) / 2)
          else Icc ((a + b) / 2) b

theorem Icc_eq_union_csplit (a b : ℝ) {hab : a ≤ b} : Icc a b = ⋃ i, Icc_csplit a b i := by
  simp [Icc_csplit]
  ext x
  constructor
  . intro h
    simp
    simp at h
    by_cases h1 : (a + b) / 2 ≤ x
    . left
      exact ⟨h1, h.2⟩
    . right
      constructor
      exact h.1
      linarith
  . simp
    intro h
    rcases h with h | h
    . have : a ≤ x := by linarith
      exact ⟨this, h.2⟩
    . have : x ≤ b := by linarith
      exact ⟨h.1, this⟩

-- for an interval with no finitesubcover, there exists a bool st it has no finitesubcover
theorem exists_subinterval (a b : ℝ) {aleb : a ≤ b} (ha : ¬ HasFiniteSubcover (Icc a b)) : ∃ v, ¬ HasFiniteSubcover (Icc_csplit a b v) := by
  rw [Icc_eq_union_csplit a b] at ha
  apply no_finite_subcover_of_partition
  apply ha
  apply aleb

-- choice makes it so that we can find a function from the levels of the interval to the one interval.

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := by
  apply isCompact_of_has_finite_subcover
  by_contra!

  have un : Icc a b = Icc a ((a + b)/2) ∪ Icc ((a + b) / 2) b := by
    have h1 : a ≤ ((a + b) / 2) := by linarith
    have h2 : ((a + b) / 2) ≤ b := by linarith
    simp [Icc_union_Icc_eq_Icc h1 h2]

  rcases this with ⟨C, hC, hC', h⟩
  specialize h 

  
  sorry
  

