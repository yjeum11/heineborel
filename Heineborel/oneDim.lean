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

def NoFiniteSubcover {X : Type u} [TopologicalSpace X] (s : Set X) := ¬ HasFiniteSubcover s

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
  : NoFiniteSubcover (⋃ i, P i) → (∃ i, NoFiniteSubcover (P i)) := by
  simp [NoFiniteSubcover]
  contrapose!
  apply has_finite_subcover_of_partition

theorem isCompact_of_has_finite_subcover (s : Set ℝ) (h : HasFiniteSubcover s) : IsCompact s := by
  apply isCompact_of_finite_subcover
  rw [HasFiniteSubcover] at h
  apply h

-- T 0 = [a, b]
-- T n = nth split of [a, b] such that no finite subcover exists

theorem lemm1 (a b : ℝ) (aleb : a ≤ b) (h : NoFiniteSubcover (Icc a b))
  : ∃ c d, NoFiniteSubcover (Icc c d) ∧
    c ≤ d ∧
    Icc c d ⊆ Icc a b ∧
    2 * Metric.diam (Icc c d) ≤ Metric.diam (Icc a b) := by

    let avg := (a + b) / 2
    let csplit (i : Fin 2) : Set ℝ := if i == 0 then Icc a avg else Icc avg b

    have a_le_avg : a ≤ avg := by dsimp [avg]; linarith
    have avg_le_b : avg ≤ b := by dsimp [avg]; linarith

    have union_csplit : ⋃ i, csplit i = Icc a b := by
      ext x
      constructor
      . intro ⟨s, h1, h2⟩
        simp only [mem_range, mem_Icc] at *
        rcases h1 with ⟨i, hi⟩
        simp only [Fin.isValue, beq_iff_eq, csplit] at hi
        split_ifs at *
        . rw [←hi] at h2
          simp only [mem_Icc] at h2
          rcases h2 with ⟨h2, h22⟩
          constructor
          exact h2
          trans avg <;> assumption
        . rw [←hi] at h2
          simp only [mem_Icc] at h2
          rcases h2 with ⟨h2, h22⟩
          constructor
          trans avg <;> assumption
          exact h22
      . intro h
        simp only [mem_Icc] at h
        by_cases h1: x ≤ avg
        . use csplit 0
          constructor
          simp only [Fin.isValue, mem_range, exists_apply_eq_apply]
          dsimp [csplit]
          simp only [mem_Icc]
          aesop
        . use csplit 1
          constructor
          simp only [Fin.isValue, mem_range, exists_apply_eq_apply]
          dsimp [csplit]
          simp only [mem_Icc]
          simp only [not_le] at h1
          apply le_of_lt at h1
          aesop

    rw [←union_csplit] at h
    apply no_finite_subcover_of_partition at h
    rcases h with ⟨i, h⟩
    simp [csplit] at h
    split_ifs at * with hi
    . use a, avg
      constructor
      . exact h
      constructor
      . linarith
      constructor
      . refine Icc_subset_Icc ?h.right.left.h₁ ?h.right.left.h₂ <;> linarith
      simp [Real.diam_Icc aleb, Real.diam_Icc a_le_avg, avg]
      linarith
    . use avg, b
      constructor
      . exact h
      constructor
      . linarith
      constructor
      . apply Icc_subset_Icc <;> linarith
      simp [Real.diam_Icc aleb, Real.diam_Icc avg_le_b, avg]
      linarith

structure ncIcc where
  low : ℝ
  high : ℝ
  nempty : low ≤ high
  nfs : NoFiniteSubcover (Icc low high)

set_option pp.proofs true
noncomputable def Ts : ℕ → ncIcc
  | 0 => ⟨a, b, aleb, abnc⟩
  | n + 1 => by
              have prev := lemm1 (Ts n).low (Ts n).high (Ts n).nempty (Ts n).nfs
              let r := Classical.choose prev
              let h := Classical.choose_spec prev
              let s := Classical.choose h
              let g := Classical.choose_spec h
              exact ⟨r, s, g.2.1, g.1⟩

noncomputable def T (n : ℕ) : Set ℝ := let S := Ts aleb abnc n; Icc S.low S.high

theorem bad_sequence : ∃ (x : ℕ → ℝ), ∀ i, x i ∈ T aleb abnc i := by
  have : ∀ i, ∃ x, x ∈ T aleb abnc i := by
    intro i
    dsimp [T]
    have := (Ts aleb abnc i).nempty
    refine nonempty_def.mp ?_
    simpa
  choose f hf using this
  use f

theorem nested : ∀ i, T aleb abnc (i+1) ⊆ T aleb abnc i := by
  intro i
  simp [T] at *
  simp [Ts]
  apply (Classical.choose_spec (Ts.proof_9 aleb abnc i (Ts.proof_8 aleb abnc i))).2.2.1

theorem nested_closed (s : ℕ → ℝ × ℝ) (hs : ∀ n, (s n).1 ≤ (s n).2) : ∃ L, L ∈ ⋂ i, Icc ((s i).1) ((s i).2) := by sorry

theorem bad_limit : ∃ x, x ∈ ⋂ i, T aleb abnc i := by
  simp [T]
  let s (i : ℕ) : ℝ × ℝ := ⟨(Ts aleb abnc i).low, (Ts aleb abnc i).high⟩
  have hs : ∀ i, (Ts aleb abnc i).low ≤ (Ts aleb abnc i).high := by
    intro i
    apply (Ts aleb abnc i).nempty
  have := nested_closed s hs
  simp at this
  exact this

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := by
  apply isCompact_of_has_finite_subcover
  by_contra! abnc
  have : T aleb abnc 0 = Icc a b := by simp [T, Ts]
  rw [←this] at abnc
  choose x hx using bad_limit aleb abnc

  simp [HasFiniteSubcover] at abnc
  rcases abnc with ⟨idx, C, Copen, Ccover, Cnosub⟩
  simp [Metric.isOpen_iff] at Copen

  have x_mem_zero : x ∈ T aleb abnc 0 := by
    simp only [mem_iInter] at hx
    apply hx 0

  have bad_cover : ∃ i, x ∈ C i := by
    exact mem_iUnion.mp (Ccover x_mem_zero)

  rcases bad_cover with ⟨u, hu⟩

  have bad_ball : ∃ δ > 0, Metric.ball x δ ⊆ C u := by 
    exact Copen u x hu


  sorry
