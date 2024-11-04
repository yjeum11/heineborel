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

def HasFiniteSubcover {X ι : Type u} [TopologicalSpace X] (s : Set X) (C : ι → Set X) := ∀ i, IsOpen (C i) → s ⊆ ⋃ i, C i →  ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, C i

#check HasFiniteSubcover

def NoFiniteSubcover {X ι : Type u} [TopologicalSpace X] (s : Set X) (C : ι → Set X):= ¬ HasFiniteSubcover s C

-- if all subsets of a partition have a finite subcover, their union has a finite subcover

variable {α : Type*} [Fintype α]
variable {ι : Type} -- [fini : Fintype ι]
variable {a b : ℝ} (aleb : a ≤ b)

theorem has_finite_subcover_of_partition (P : α → (Set ℝ)) (C : ι → Set ℝ)
  : (∀ i, HasFiniteSubcover (P i) C) → HasFiniteSubcover (⋃ i, P i) C := by
  intro h j openC ssC
  -- intro h idx C hC hC'
  dsimp [HasFiniteSubcover] at h
  have covered : ∀ i : α, P i ⊆ ⋃ j, C j := by
    intro i
    simp only [iUnion_subset_iff] at ssC
    apply ssC
  have subcovered : ∀ i : α, ∃ t : Finset ι, P i ⊆ ⋃ j ∈ t, C j := by
    intro i
    apply h i j openC 
    exact covered i
  have choose_finite_subcover : ∃ (t : α → Finset ι), ∀ (i : α), P i ⊆ ⋃ k ∈ t i, C k := by
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

theorem no_finite_subcover_of_partition (P : α → (Set ℝ)) (C : ι → Set ℝ)
  : NoFiniteSubcover (⋃ i, P i) C → (∃ i, NoFiniteSubcover (P i) C) := by
  simp [NoFiniteSubcover]
  contrapose!
  apply has_finite_subcover_of_partition

theorem isCompact_of_has_finite_subcover (s : Set ℝ)  
  (h : ∀ (ι : Type) (C : ι → Set ℝ), HasFiniteSubcover s C) : IsCompact s := by
  dsimp [HasFiniteSubcover] at h
  apply isCompact_of_finite_subcover
  intro idx U hU ssU
  specialize h idx U
  by_cases nem : Nonempty idx
  . let a := nem.some
    apply h
    apply hU a
    apply ssU
  . simp at nem
    simp at *
    apply ssU

theorem lemm1 (a b : ℝ) (aleb : a ≤ b) (C : ι → Set ℝ) (h : NoFiniteSubcover (Icc a b) C)
  : ∃ c d, NoFiniteSubcover (Icc c d) C ∧
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
  C : ι → Set ℝ
  nfs : NoFiniteSubcover (Icc low high) C

set_option pp.proofs true
noncomputable def Ts (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : ℕ → @ncIcc ι
  | 0 => ⟨a, b, aleb, C, abnc⟩
  | n + 1 => by
              have prev := lemm1 (Ts C abnc n).low (Ts C abnc n).high (Ts C abnc n).nempty (Ts C abnc n).C (Ts C abnc n).nfs
              let r := Classical.choose prev
              let h := Classical.choose_spec prev
              let s := Classical.choose h
              let g := Classical.choose_spec h
              exact ⟨r, s, g.2.1, (Ts C abnc n).C, g.1⟩

noncomputable def T  (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) (n : ℕ) : Set ℝ := let S := Ts aleb C abnc n; Icc S.low S.high

theorem bad_sequence (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : ∃ (x : ℕ → ℝ), ∀ i, x i ∈ T aleb C abnc i := by
  have : ∀ i, ∃ x, x ∈ T aleb C abnc i := by
    intro i
    dsimp [T]
    have := (Ts aleb C abnc i).nempty
    refine nonempty_def.mp ?_
    simpa
  choose f hf using this
  use f

theorem nested : ∀ i, T aleb C abnc (i+1) ⊆ T aleb C abnc i := by
  intro i
  simp [T] at *
  simp [Ts]
  apply (Classical.choose_spec (Ts.proof_9 aleb C abnc i (Ts.proof_8 aleb C abnc i))).2.2.1

theorem nested_closed (s : ℕ → ℝ × ℝ) (hs : ∀ n, (s n).1 ≤ (s n).2) (hnest : ∀ n, (Icc (s (n+1)).1 (s (n+1)).2) ⊆ (Icc (s n).1 (s n).2))
  : ∃ L, L ∈ ⋂ i, Icc ((s i).1) ((s i).2) := by 
  have hs' : ∀ n, (s (n+1)).1 ≤ (s (n+1)).2 := by
    intro n
    apply hs (n+1)

  have hnest' : ∀ n, (s n).1 ≤ (s (n+1)).1 ∧ (s (n+1)).2 ≤ (s n).2 := by
    intro n
    specialize hnest n
    specialize hs' n
    simp [Icc_subset_Icc_iff hs'] at hnest
    apply hnest

  have hnest_left (n : ℕ) (N : ℕ) (h : n ≤ N) : (s n).1 ≤ (s N).1 := by
    induction' N, h using Nat.le_induction with N _ ih
    . simp
    trans (s N).1
    apply ih
    apply (hnest' N).1
      
  have hnest_right (n : ℕ) (N : ℕ) (h : n ≤ N) : (s N).2 ≤ (s n).2 := by
    induction' N, h using Nat.le_induction with N _ ih
    . simp
    trans (s N).2
    apply (hnest' N).2
    apply ih
  
  have : ∀ n, iSup (fun x ↦ (s x).1) ≤ (s n).2 := by
    intro n
    apply ciSup_le
    intro k
    by_cases c : k ≤ n
    . trans (s n).1
      apply hnest_left k n c
      apply hs n
    . have : n ≤ k := by exact Nat.le_of_not_ge c
      trans (s k).2
      apply hs k
      apply hnest_right n k this
  
  use iSup (fun x ↦ (s x).1)
  simp
  intro n
  constructor
  . apply le_ciSup_of_le
    simp [BddAbove, upperBounds, Nonempty]
    use (s 0).2
    simp
    intro a
    trans (s a).2
    apply hs a
    have : 0 ≤ a := by exact Nat.zero_le a
    apply hnest_right 0 a this
    use le_refl (s n).1
  . apply this

-- theorem has_finite_subcover_of_ss_one (s U : Set ℝ) (hU : IsOpen U) (hs : s ⊆ U)
--   : HasFiniteSubcover s := by
--   simp [HasFiniteSubcover]
--   intro idx C Copen Css


theorem bad_limit (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : ∃ x, x ∈ ⋂ i, T aleb C abnc i := by
  simp [T]
  let s (i : ℕ) : ℝ × ℝ := ⟨(Ts aleb C abnc i).low, (Ts aleb C abnc i).high⟩
  have hs : ∀ i, (Ts aleb C abnc i).low ≤ (Ts aleb C abnc i).high := by
    intro i
    apply (Ts aleb C abnc i).nempty
  have := nested_closed s hs (nested aleb)
  simp at this
  exact this

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := by
  apply isCompact_of_has_finite_subcover
  by_contra! ad

  rcases ad with ⟨idx, C, hC⟩

  choose x hx using bad_limit aleb C hC
  simp [HasFiniteSubcover] at hC
  rcases hC with ⟨Copen, Ccover, Cnfs⟩
  simp [Metric.isOpen_iff] at Copen

  simp [mem_iInter] at hx

  have bad_cover : ∃ i, x ∈ C i := by
    exact mem_iUnion.mp (Ccover (hx 0))

  rcases bad_cover with ⟨u, hu⟩

  have bad_ball : ∃ δ > 0, Metric.ball x δ ⊆ C u := by 
    exact Copen u x hu

  rcases bad_ball with ⟨δ, δpos, hδ⟩

  have bad_T' : ∃ n, T aleb ad n ⊆ Metric.ball x δ := sorry
  rcases bad_T' with ⟨n, hn⟩

  have bad_T : T aleb ad n ⊆ C u := by exact fun ⦃a_1⦄ a ↦ hδ (hn a)

  have no : ∀ (x : Finset idx), ¬ T aleb ad n ⊆ ⋃ i ∈ x, C i := by sorry

  have T_sub : HasFiniteSubcover (T aleb ad n) := by sorry
    

  -- takes infinite sets to cover T aleb ad n
  have T_no_sub : ¬ HasFiniteSubcover (T aleb ad n) := by
    apply (Ts aleb ad n).nfs

  contradiction
