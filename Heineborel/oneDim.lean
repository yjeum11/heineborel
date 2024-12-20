import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Topology.Defs.Basic

-- closed interval is compact

open Set Metric Real Classical

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
    simp only [toFinite_toFinset, mem_toFinset, mem_iUnion, Finset.mem_coe, exists_prop,
      iUnion_exists, biUnion_and']
    use a
    constructor
    apply Fintype.complete
    simp only [mem_iUnion, exists_prop] at hx
    apply hx
  use Set.Finite.toFinset T_finite
  simp only [iUnion_subset_iff]
  apply this
 
theorem no_finite_subcover_of_partition (P : α → (Set ℝ)) (C : ι → Set ℝ) 
  : NoFiniteSubcover (⋃ i, P i) C → (∃ i, NoFiniteSubcover (P i) C) := by
  simp only [NoFiniteSubcover]
  contrapose!
  apply has_finite_subcover_of_partition

theorem isCompact_iff_has_finite_subcover (s : Set ℝ) :
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

-- set_option pp.proofs true
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
  simp only [T, Ts]

theorem bad_sequence (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : ∃ (x : ℕ → ℝ), ∀ i, x i ∈ T aleb C abnc i := by
  have : ∀ i, ∃ x, x ∈ T aleb C abnc i := by
    intro i
    dsimp [T]
    have := (Ts aleb C abnc i).nempty
    refine nonempty_def.mp ?_
    simpa only [nonempty_Icc]
  choose f hf using this
  use f

theorem nested : ∀ i, T aleb C abnc (i+1) ⊆ T aleb C abnc i := by
  intro i
  simp only [T] at *
  simp only [Ts]
  apply (Classical.choose_spec (Ts.proof_9 aleb C abnc i (Ts.proof_8 aleb C abnc i))).2.2.1

theorem T_diam (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) 
  : ∀ i, diam (T aleb C abnc i) = diam (T aleb C abnc 0) * ((1/2)^i) := by
  intro i
  induction' i with i ih
  . simp only [one_div, pow_zero, mul_one]
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
    simp only [gt_iff_lt, one_div, ge_iff_le] at *
    apply lt_of_le_of_ne this
    simpa only [ne_eq]

  . simp only [gt_iff_lt, one_div, T, Ts, ge_iff_le] at *
    rw [diam_Icc]
    rw [diam_Icc] at pos
    linarith
    assumption
    assumption

  refine (pow_lt_iff_lt_log ?h.a.hx ?h.a.hy).mpr ?h.a.a
  . norm_num
  . simp only [T, Ts]
    have pos : 0 < diam (Icc a b) := by
      have : 0 ≤ diam (Icc a b) := by apply diam_nonneg
      simp only [gt_iff_lt, one_div, ge_iff_le] at *
      apply lt_of_le_of_ne this
      simpa only [ne_eq]
    have : 0 < b-a := by rw [←diam_Icc]; apply pos; apply aleb
    rw [diam_Icc]
    apply div_pos <;> linarith
    apply aleb
  rw [←div_lt_iff_of_neg, log_div_log, ←gt_iff_lt]
  simp only [gt_iff_lt, one_div, ge_iff_le] at *
  apply Nat.lt_of_floor_lt
  linarith
  apply log_neg <;> norm_num

theorem T_bounded (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) (i : ℕ) :
  Bornology.IsBounded (T aleb C abnc i) := by
  have ssT0 : (T aleb C abnc i) ⊆ T aleb C abnc 0 := by
    induction' i with i ih
    . simp only [subset_refl]
    trans (T aleb C abnc i)
    apply nested
    assumption

  suffices h : Bornology.IsBounded (T aleb C abnc 0)
  exact Bornology.IsBounded.subset h ssT0

  simp only [T, Ts]
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
    simp only [Icc_subset_Icc_iff hs'] at hnest
    apply hnest

  have hnest_left (n : ℕ) (N : ℕ) (h : n ≤ N) : (s n).1 ≤ (s N).1 := by
    induction' N, h using Nat.le_induction with N _ ih
    . simp only [le_refl]
    trans (s N).1
    apply ih
    apply (hnest' N).1
      
  have hnest_right (n : ℕ) (N : ℕ) (h : n ≤ N) : (s N).2 ≤ (s n).2 := by
    induction' N, h using Nat.le_induction with N _ ih
    . simp only [le_refl]
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
  simp only [mem_iInter, mem_Icc]
  intro n
  constructor
  . apply le_ciSup_of_le
    simp only [BddAbove, upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    use (s 0).2
    simp only [mem_setOf_eq]
    intro a
    trans (s a).2
    apply hs a
    have : 0 ≤ a := by exact Nat.zero_le a
    apply hnest_right 0 a this
    use le_refl (s n).1
  . apply this

theorem bad_limit (C : ι → Set ℝ) (abnc : NoFiniteSubcover (Icc a b) C) : ∃ x, x ∈ ⋂ i, T aleb C abnc i := by
  simp only [T, mem_iInter, mem_Icc]
  let s (i : ℕ) : ℝ × ℝ := ⟨(Ts aleb C abnc i).low, (Ts aleb C abnc i).high⟩
  have hs : ∀ i, (Ts aleb C abnc i).low ≤ (Ts aleb C abnc i).high := by
    intro i
    apply (Ts aleb C abnc i).nempty
  have := nested_closed s hs (nested aleb)
  simp only [mem_iInter, mem_Icc] at this
  exact this

theorem isCompact_of_closed_interval (a b : ℝ) (aleb : a ≤ b) : IsCompact (Icc a b) := by
  rw [←isCompact_iff_has_finite_subcover]
  intro idx C oC

  by_contra! hC

  choose x hx using bad_limit aleb C hC
  simp only [IsOpenCover] at oC
  rcases oC with ⟨Copen, Ccover⟩

  simp only [isOpen_iff, gt_iff_lt] at Copen

  simp only [mem_iInter] at hx

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
    simp only [mem_ball]
    apply hn p
    apply hp

  rcases bad_T' with ⟨n, hn⟩

  have bad_T : T aleb C hC n ⊆ C u := by exact fun ⦃a_1⦄ a ↦ hδ (hn a)

  have no : ¬ HasFiniteSubcover (T aleb C hC n) C := by 
    simp only [T]
    apply (Ts aleb C hC n).nfs

  have T_sub : HasFiniteSubcover (T aleb C hC n) C := by 
    simp only [HasFiniteSubcover]
    use singleton u
    simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
    apply bad_T
    
  contradiction

-- set_option diagnostics true
theorem isCompact_of_ss_isCompact (F K : Set ℝ) (hF : IsClosed F) (hK : IsCompact K) (hsK : F ⊆ K) : IsCompact F := by
  rw [←isCompact_iff_has_finite_subcover]
  rw [←isCompact_iff_has_finite_subcover] at hK
  intro idx V hV

  let V' : Option idx → Set ℝ 
    | none => Fᶜ
    | some i => V i

  have hVK : IsOpenCover K V' := by
    rw [IsOpenCover]
    constructor
    . intro i
      cases i with
      | none => simpa only [isOpen_compl_iff, V']
      | some i => simp only [V']; apply hV.1
    . intro x _
      by_cases h : x ∈ F
      . simp only [mem_iUnion]
        simp only [IsOpenCover] at hV
        rcases hV with ⟨_, hV2⟩
        have : ∀ f ∈ F, ∃ i, f ∈ V i := by
          intro f hf
          exact mem_iUnion.mp (hV2 hf)
        rcases this x h with ⟨i, hi⟩
        use some i
      . simp only [mem_iUnion]
        use none
        simpa only [mem_compl_iff, V']

  rcases hK (Option idx) V' hVK with ⟨t, ht⟩
  have hF : F ⊆ ⋃ i ∈ t, V' i := by exact fun ⦃a⦄ a_1 ↦ ht (hsK a_1)
  -- cases on if t includes Fᶜ
  simp only [HasFiniteSubcover]
  have inj : ∀ a a' : Option idx, ∀ b ∈ id a, b ∈ id a' → a = a' := by
    intro a a' b hb hb'
    simp only [id_eq, Option.mem_def] at *
    rw [hb, hb']
  use Finset.filterMap id t inj
  simp only [Finset.mem_filterMap, id_eq, exists_eq_right]
  simp only [IsOpenCover, and_imp, id_eq, Option.mem_def] at *
  intro f hf
  specialize hF hf
  simp only [mem_iUnion, exists_prop] at hF
  simp only [mem_iUnion, exists_prop]
  rcases hF with ⟨i, hi⟩
  have : ∃ i', i = some i' := by
    by_contra h
    simp_rw [←Option.ne_none_iff_exists'] at h
    simp only [ne_eq, Decidable.not_not] at h
    rw [h] at hi
    simp only [mem_compl_iff, V'] at hi
    rcases hi with ⟨_, hi2⟩
    contradiction
  rcases this with ⟨i', hi'⟩
  use i'
  constructor
  . simp only [hi', V'] at hi
    apply hi.1
  . simp only [hi', V'] at hi
    apply hi.2
    
theorem isCompact_of_closed_bounded (F : Set ℝ) (hF : IsClosed F) (hFb : Bornology.IsBounded F) : IsCompact F := by
  rw [isBounded_iff_subset_closedBall 0] at hFb
  simp only [closedBall_eq_Icc, zero_sub, zero_add] at hFb
  rcases hFb with ⟨a, ha⟩
  by_cases h : 0 ≤ a
  . have : IsCompact (Icc (-a) a) := by apply isCompact_of_closed_interval; linarith
    apply isCompact_of_ss_isCompact F (Icc (-a) a) <;> assumption
  . simp only [not_le] at h
    have : Icc (-a) a = ∅ := by 
      simp [Set.eq_empty_iff_forall_not_mem]
      intro x hx
      linarith
    simp only [this, subset_empty_iff] at ha
    rw [ha]
    simp only [isCompact_empty]

theorem isClosed_of_isCompact (K : Set ℝ) (hK : IsCompact K) : IsClosed K := by
  by_cases Nh : Kᶜ.Nonempty
  swap
  . simp only [not_nonempty_iff_eq_empty, compl_empty_iff] at Nh
    rw [Nh]
    exact isClosed_univ
  rw [←isOpen_compl_iff, isOpen_iff]

  intro p hp

  let V (q : {x // x ∈ K}) : Set ℝ := ball p ((dist ↑q p) / 2)
  let W (q : {x // x ∈ K}) : Set ℝ := ball ↑q ((dist ↑q p) / 2)

  have ocW : IsOpenCover K W := by
    simp only [IsOpenCover, Subtype.forall, iUnion_coe_set]
    constructor
    . intro i hi; exact isOpen_ball
    simp only [W]
    intro k hk
    simp only [mem_iUnion, mem_ball, exists_prop]
    use k
    simp only [dist_self, Nat.ofNat_pos, div_pos_iff_of_pos_right, dist_pos, ne_eq]
    constructor
    . assumption
    . aesop

  have hfsW : HasFiniteSubcover K W := by 
    rw [←isCompact_iff_has_finite_subcover K] at hK
    exact hK {x // x ∈ K} W ocW

  rw [HasFiniteSubcover] at hfsW
  rcases hfsW with ⟨T, hT⟩

  let V' := ⋂ q ∈ T, V q
  let W' := ⋃ q ∈ T, W q

  have VWdisj : V' ∩ W' = ∅ := by 
    dsimp [V', W']
    ext x
    constructor
    . intro hx
      simp only [mem_empty_iff_false]
      simp only [iInter_coe_set, iUnion_coe_set, mem_inter_iff, mem_iInter, mem_ball, mem_iUnion,
        exists_prop, exists_and_right, V, W] at hx
      rcases hx with ⟨hx1, q', ⟨hq1, hq2⟩, hq3⟩
      specialize hx1 q' hq1 hq2
      have := calc dist q' p ≤ dist x q' + dist x p := by exact dist_triangle_left q' p x
        _ < dist q' p := by linarith
      linarith
    . intro f
      exfalso
      simp only [mem_empty_iff_false] at f

  have : V' ⊆ Kᶜ := by 
    dsimp [IsOpenCover] at ocW
    by_contra h
    rw [not_subset] at h
    rcases h with ⟨x, hx1, hx2⟩
    simp only [mem_compl_iff, Decidable.not_not] at hx2
    have : x ∉ W' := by
      rw [←Set.disjoint_iff_inter_eq_empty, Set.disjoint_left] at VWdisj
      apply VWdisj at hx1
      exact hx1
    dsimp [W'] at VWdisj
    apply hT at hx2
    contradiction

  have pV : p ∈ V' := by 
    dsimp [V', V]
    suffices : ∀ q ∈ T, p ∈ ball p (dist (↑q) p / 2)
    . exact mem_iInter₂_of_mem this
    intro q hq
    simp only [mem_ball, dist_self, Nat.ofNat_pos, div_pos_iff_of_pos_right, dist_pos, ne_eq]
    have : ↑q ∈ K := by exact Subtype.coe_prop q
    aesop

  have opV : IsOpen V' := by
    dsimp [V']
    apply isOpen_biInter_finset 
    intro i _
    simp only [V]
    exact isOpen_ball

  rw [isOpen_iff] at opV

  specialize opV p pV
  rcases opV with ⟨ε, εpos, hε⟩
  use ε, εpos
  trans V' <;> assumption

theorem isBounded_of_isCompact (K : Set ℝ) (hK : IsCompact K) : Bornology.IsBounded K := by
  by_cases nK : K.Nonempty
  swap
  . rw [@not_nonempty_iff_eq_empty] at nK
    rw [nK]
    apply Bornology.isBounded_empty

  let U (q : {x // x ∈ K}) : Set ℝ := ball q 1

  have ocU : IsOpenCover K U := by
    simp only [IsOpenCover, Subtype.forall, iUnion_coe_set]
    constructor
    . intro i hi; exact isOpen_ball
    simp only [U]
    intro k hk
    simp only [mem_iUnion, mem_ball, exists_prop]
    use k
    simp only [dist_self, zero_lt_one, and_true]
    assumption

  have hfsU : HasFiniteSubcover K U := by 
    rw [←isCompact_iff_has_finite_subcover K] at hK
    exact hK {x // x ∈ K} U ocU

  rw [HasFiniteSubcover] at hfsU
  rcases hfsU with ⟨T, hT⟩
  
  have nT : T.Nonempty := by 
    rcases nK with ⟨k, hk⟩
    apply hT at hk
    rw [mem_iUnion₂] at hk
    rcases hk with ⟨i, j, _⟩
    use i

  rw [isBounded_iff_exists_ge 0]
  use (dist (T.max' nT) (T.min' nT)) + 2

  constructor
  . have : 0 ≤ dist (T.max' nT) (T.min' nT) := by exact dist_nonneg
    trans dist (T.max' nT) (T.min' nT)
    apply this
    simp only [le_add_iff_nonneg_right, Nat.ofNat_nonneg]

  intro x hx y hy
  have xmem : ∃ tx ∈ T, x ∈ ball ↑tx 1 := by
    apply hT at hx
    dsimp [U] at hx
    simp only [iUnion_coe_set, mem_iUnion, mem_ball, exists_prop, exists_and_right] at hx
    rcases hx with ⟨cx, hcx1, hcx2⟩
    simp only [mem_ball, Subtype.exists, exists_and_right]
    use cx, hcx1
  have ymem : ∃ ty ∈ T, y ∈ ball ↑ty 1 := by
    apply hT at hy
    dsimp [U] at hy
    simp only [iUnion_coe_set, mem_iUnion, mem_ball, exists_prop, exists_and_right] at hy
    rcases hy with ⟨cy, hcy1, hcy2⟩
    simp only [mem_ball, Subtype.exists, exists_and_right]
    use cy, hcy1

  rcases xmem with ⟨cx, hcx1, hcx2⟩
  rcases ymem with ⟨cy, hcy1, hcy2⟩

  simp only [iUnion_coe_set, mem_ball, ge_iff_le] at *

  calc dist x y ≤ dist x ↑cx + dist ↑cx y := by exact dist_triangle x (↑cx) y
    _ ≤ dist x ↑cx + dist ↑cx ↑cy + dist ↑cy y := by 
      rw [add_assoc, add_le_add_iff_left (dist x ↑cx)]
      apply dist_triangle (↑cx) (↑cy) y
    _ ≤ 1 + dist ↑cx ↑cy + dist ↑cy y := by
      simp only [add_assoc, add_le_add_iff_right]
      apply le_of_lt hcx2
    _ ≤ 1 + dist ↑cx ↑cy + 1 := by
      simp only [add_assoc, add_le_add_iff_left]
      have := (le_of_lt hcy2)
      rw [dist_comm] at this
      exact this
    _ ≤ dist cx cy + 2 := by rw [add_comm, ←add_assoc, add_comm]; simp only [add_le_add_iff_left]; apply le_of_eq; norm_num

  simp only [dist, add_le_add_iff_right]

  have : |↑(T.max' nT) - (↑(T.min' nT) : ℝ)| = (↑(T.max' nT) - ↑(T.min' nT) : ℝ) := by
    rw [abs_eq_self]
    rw [@sub_nonneg]
    refine Subtype.coe_le_coe.mpr ?_
    apply Finset.le_max'
    apply Finset.min'_mem

  rw [this]

  by_cases h : ↑cy  ≤ (↑cx : ℝ)
  . have : |↑cx - (↑cy:ℝ)| = ↑cx - ↑cy := by
      rw [abs_eq_self]
      rw [@sub_nonneg]
      exact h
    rw [this]
    apply sub_le_sub
    refine Subtype.coe_le_coe.mpr ?_
    apply Finset.le_max'
    exact hcx1
    refine Subtype.coe_le_coe.mpr ?_
    apply Finset.min'_le
    exact hcy1
  . have : |↑cx - (↑cy:ℝ)| = -(↑cx - ↑cy) := by
      simp only [Subtype.coe_le_coe, not_le] at h
      apply le_of_lt at h
      rw [abs_eq_neg_self, @sub_nonpos, Subtype.coe_le_coe]
      exact h
    rw [this]
    rw [neg_sub]
    apply sub_le_sub
    refine Subtype.coe_le_coe.mpr ?_
    apply Finset.le_max'
    exact hcy1
    refine Subtype.coe_le_coe.mpr ?_
    apply Finset.min'_le
    exact hcx1

theorem heine_borel (K : Set ℝ) : IsCompact K ↔ Bornology.IsBounded K ∧ IsClosed K := by
  constructor
  . intro cpk
    exact ⟨isBounded_of_isCompact K cpk, isClosed_of_isCompact K cpk⟩
  . intro ⟨c, b⟩
    exact isCompact_of_closed_bounded K b c
