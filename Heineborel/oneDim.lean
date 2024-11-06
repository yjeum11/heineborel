import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

-- closed interval is compact

open Set Metric Real

theorem close_of_elem_interval (a b : ℝ) (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
  : dist x y ≤ dist a b := by
  simp only [mem_Icc] at *
  simp only [le_abs, abs_le, neg_sub, tsub_le_iff_right, dist]
  right
  constructor <;> linarith

def IsOpenCover {X ι : Type u} [TopologicalSpace X] (s : Set X) (C : ι → Set X) : Prop := (∀ i, IsOpen (C i)) ∧ s ⊆ ⋃ i, C i

def HasFiniteSubcover {X ι : Type u} [TopologicalSpace X] (s : Set X) (C : ι → Set X) := ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, C i

def NoFiniteSubcover {X ι : Type u} [TopologicalSpace X] (s : Set X) (C : ι → Set X):= ¬ HasFiniteSubcover s C

-- if all subsets of a partition have a finite subcover, their union has a finite subcover

variable {α : Type*} [Fintype α]
variable {ι : Type}
variable {a b : ℝ} (aleb : a ≤ b)

theorem has_finite_subcover_of_partition (P : α → Set ℝ) (C : ι → Set ℝ) 
  : (∀ i, HasFiniteSubcover (P i) C) → HasFiniteSubcover (⋃ i, P i) C := by
  intro hfsC
  dsimp [HasFiniteSubcover] at hfsC

  have subcovered : ∀ i : α, ∃ t : Finset ι, P i ⊆ ⋃ j ∈ t, C j := by apply hfsC
    
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

theorem isCompact_of_has_finite_subcover (s : Set ℝ) :
  (∀ (ι : Type) (C : ι → Set ℝ), IsOpenCover s C → HasFiniteSubcover s C) ↔ IsCompact s := by
  constructor
  . intro h
    rw [isCompact_iff_finite_subcover]
    intro idx U hU ssU
    specialize h idx U
    have : IsOpenCover s U := by
      rw [IsOpenCover]
      constructor <;> assumption
    apply h at this
    rw [HasFiniteSubcover] at this
    assumption
  . intro cmpt
    rw [isCompact_iff_finite_subcover] at cmpt
    intro idx C
    specialize cmpt C
    intro ⟨h1, h2⟩
    apply cmpt at h1
    apply h1 at h2
    exact h2

theorem lemm1 (a b : ℝ) (aleb : a ≤ b) (C : ι → Set ℝ) (h : NoFiniteSubcover (Icc a b) C) 
  : ∃ c d, NoFiniteSubcover (Icc c d) C ∧
    c ≤ d ∧
    Icc c d ⊆ Icc a b ∧
    2 * diam (Icc c d) = diam (Icc a b) := by

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
          trans avg
          assumption
          apply avg_le_b
        . rw [←hi] at h2
          simp only [mem_Icc] at h2
          rcases h2 with ⟨h2, h22⟩
          constructor
          trans avg
          apply a_le_avg
          exact h2
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
      simp [diam_Icc (aleb), diam_Icc (a_le_avg ), avg]
      linarith
    . use avg, b
      constructor
      . exact h
      constructor
      . linarith
      constructor
      . apply Icc_subset_Icc <;> linarith
      simp [diam_Icc (aleb), diam_Icc (avg_le_b), avg]
      linarith

structure ncIcc (C : ι → Set ℝ) where
  low : ℝ
  high : ℝ
  nempty : low ≤ high
  nfs : NoFiniteSubcover (Icc low high) C

set_option pp.proofs true
noncomputable def Ts (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : ℕ → @ncIcc ι C
  | 0 => ⟨a, b, aleb, abnc⟩
  | n + 1 => by
              have prev := lemm1 (Ts C abnc n).low (Ts C abnc n).high (Ts C abnc n).nempty C (Ts C abnc n).nfs
              let r := Classical.choose prev
              let h := Classical.choose_spec prev
              let s := Classical.choose h
              let g := Classical.choose_spec h
              exact ⟨r, s, g.2.1, g.1⟩

noncomputable def T  (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) (n : ℕ) : Set ℝ := let S := Ts aleb C abnc n; Icc S.low S.high

theorem T0_eq_ab (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : T aleb C abnc 0 = Icc a b := by
  simp [T, Ts]

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

theorem T_diam (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) 
  : ∀ i, diam (T aleb C abnc i) = diam (T aleb C abnc 0) * ((1/2)^i) := by
  intro i
  induction' i with i ih
  . simp
  simp [T, Ts]
  simp [T, Ts] at ih
  rw [pow_succ, mul_inv, ←mul_assoc, ←ih]
  rw [eq_mul_inv_iff_mul_eq₀, mul_comm]
  apply (Classical.choose_spec (Ts.proof_9 aleb C abnc i (Ts.proof_8 aleb C abnc i))).2.2.2
  norm_num

theorem T_diam_conv_zero (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C)
  : Filter.Tendsto (fun x ↦ diam (T aleb C abnc x)) Filter.atTop (nhds 0) := by
  rw [tendsto_atTop]
  intro ε hε
  use Nat.floor ( logb (1/2) (ε / (diam (T aleb C abnc 0)))) + 1
  intro n hn
  rw [dist_0_eq_abs, abs_of_nonneg, T_diam]
  swap
  . exact diam_nonneg
  by_cases z: 0 = diam (T aleb C abnc 0)
  . rwa [←z, zero_mul]
  refine (lt_div_iff₀' ?h.hc).mp ?h.a

  have pos : 0 < diam (Icc a b) := by
    have : 0 ≤ diam (Icc a b) := by apply diam_nonneg
    simp at *
    apply lt_of_le_of_ne this
    simpa

  . simp [T, Ts] at *
    rw [diam_Icc]
    rw [diam_Icc] at pos
    linarith
    assumption
    assumption

  refine (pow_lt_iff_lt_log ?h.a.hx ?h.a.hy).mpr ?h.a.a
  . norm_num
  . simp [T, Ts]
    have pos : 0 < diam (Icc a b) := by
      have : 0 ≤ diam (Icc a b) := by apply diam_nonneg
      simp at *
      apply lt_of_le_of_ne this
      simpa
    have : 0 < b-a := by rw [←diam_Icc]; apply pos; apply aleb
    rw [diam_Icc]
    apply div_pos <;> linarith
    apply aleb
  rw [←div_lt_iff_of_neg, log_div_log, ←gt_iff_lt]
  simp at *
  apply Nat.lt_of_floor_lt
  linarith
  apply log_neg <;> norm_num

theorem T_bounded (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) (i : ℕ) :
  Bornology.IsBounded (T aleb C abnc i) := by
  have ssT0 : (T aleb C abnc i) ⊆ T aleb C abnc 0 := by
    induction' i with i ih
    . simp
    trans (T aleb C abnc i)
    apply nested
    assumption

  suffices h : Bornology.IsBounded (T aleb C abnc 0)
  exact Bornology.IsBounded.subset h ssT0

  simp [T, Ts]
  exact isBounded_Icc a b

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
  rw [←isCompact_of_has_finite_subcover]
  intro idx C oC

  by_contra! hC

  choose x hx using bad_limit aleb C hC
  simp [IsOpenCover] at oC
  rcases oC with ⟨Copen, Ccover⟩

  simp [isOpen_iff] at Copen

  simp [mem_iInter] at hx

  have bad_cover : ∃ i, x ∈ C i := by
    refine mem_iUnion.mp ?_
    apply Ccover
    rw [←T0_eq_ab aleb C hC]
    apply hx 0

  rcases bad_cover with ⟨u, hu⟩

  have bad_ball : ∃ δ > 0, ball x δ ⊆ C u := by 
    exact Copen u x hu

  rcases bad_ball with ⟨δ, δpos, hδ⟩

  have bad_T' : ∃ n, T aleb C hC n ⊆ ball x δ := by
    have conv := T_diam_conv_zero aleb C hC
    rw [tendsto_atTop] at conv
    have : ∃ n, ∀ p ∈ T aleb C hC n, dist p x < δ := by
      rcases conv δ δpos with ⟨N, hN⟩
      specialize hN N (le_refl N)
      rw [dist_zero_right, norm_of_nonneg] at hN
      use N
      intro p hp
      calc dist p x ≤ diam (T aleb C hC N) := by apply dist_le_diam_of_mem (T_bounded aleb C hC N) hp (hx N)
        _ < δ := hN
      exact diam_nonneg
    rcases this with ⟨n, hn⟩
    use n
    intro p hp
    simp
    apply hn p
    apply hp

  rcases bad_T' with ⟨n, hn⟩

  have bad_T : T aleb C hC n ⊆ C u := by exact fun ⦃a_1⦄ a ↦ hδ (hn a)

  have no : ¬ HasFiniteSubcover (T aleb C hC n) C := by 
    simp [T]
    apply (Ts aleb C hC n).nfs

  have T_sub : HasFiniteSubcover (T aleb C hC n) C := by 
    simp [HasFiniteSubcover]
    use singleton u
    simp
    apply bad_T
    
  contradiction

-- theorem isCompact_of_ss_isCompact (F K : Set ℝ) (hs : IsClosed F) (hK : IsCompact K) (hsK : F ⊆ K) : IsCompact F := by
--   rw [←isCompact_of_has_finite_subcover]
--   rw [←isCompact_of_has_finite_subcover] at hK
--   intro idx V hV
--   
--
--
--   have hV' : IsOpenCover F (V') := sorry
--   have hVK : IsOpenCover K (V') := sorry
--   
--   rcases hK idx (V' true) hVK with ⟨t, ht⟩
--
--   -- cases on if t includes Fᶜ
--   
--   sorry
