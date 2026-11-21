import Mathlib

/-!
# 2-designs and Fisher's inequality

Formalisation of Sections 1-4 of the accompanying notes (finite incidence structures, designs,
incidence matrix, Fisher's inequality, rank version).

An incidence structure is a type of points `P` (finite) together with a finite set `𝓑` of blocks,
each block a finset of points (as in the notes: blocks are subsets of the point set).
-/

open Finset Matrix

namespace FisherNotes

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `2-(v,k,λ)` design: every block has `k` points and every two distinct points lie in exactly
`l` blocks. (`v = Fintype.card P`.) -/
structure IsDesign2 (𝓑 : Finset (Finset P)) (k l : ℕ) : Prop where
  card_block : ∀ B ∈ 𝓑, B.card = k
  count : ∀ p q : P, p ≠ q → (𝓑.filter (fun B => p ∈ B ∧ q ∈ B)).card = l

/-- The incidence matrix (`b × v`): entry `(B,p)` is `1` if `p ∈ B` and `0` otherwise. -/
def incMat (𝓑 : Finset (Finset P)) : Matrix 𝓑 P ℚ :=
  Matrix.of fun B p => if p ∈ (B : Finset P) then 1 else 0

/-- Number of blocks through a point (replication number of that point). -/
def repl (𝓑 : Finset (Finset P)) (p : P) : ℕ := (𝓑.filter (fun B => p ∈ B)).card

variable {𝓑 : Finset (Finset P)}

/-- Entries of `Aᵀ A`: number of blocks containing both points. -/
lemma gram_apply (p q : P) :
    ((incMat 𝓑)ᵀ * incMat 𝓑) p q = ((𝓑.filter (fun B => p ∈ B ∧ q ∈ B)).card : ℚ) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incMat, Matrix.of_apply]
  rw [Finset.card_filter, Nat.cast_sum]
  rw [← Finset.sum_coe_sort 𝓑]
  refine Finset.sum_congr rfl fun B _ => ?_
  by_cases hp : p ∈ (B : Finset P) <;> by_cases hq : q ∈ (B : Finset P) <;> simp [hp, hq]

/-- Double counting: `r (k-1) = (v-1) λ` for every point. -/
lemma repl_mul {k l : ℕ} (h : IsDesign2 𝓑 k l) (p : P) :
    repl 𝓑 p * (k - 1) = (Fintype.card P - 1) * l := by
  have h1 : ∑ q ∈ univ.erase p, (𝓑.filter (fun B => p ∈ B ∧ q ∈ B)).card
      = (Fintype.card P - 1) * l := by
    rw [Finset.sum_congr rfl
      (fun q hq => h.count p q (Finset.ne_of_mem_erase hq).symm)]
    simp [Finset.card_erase_of_mem]
  have h2 : ∑ q ∈ univ.erase p, (𝓑.filter (fun B => p ∈ B ∧ q ∈ B)).card
      = ∑ B ∈ 𝓑.filter (fun B => p ∈ B), (B.erase p).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun B _ => ?_
    by_cases hp : p ∈ B
    · have : (univ.erase p).filter (fun q => q ∈ B) = B.erase p := by
        ext q; simp [and_comm]
      simp only [hp, true_and, ite_true]
      rw [← Finset.card_filter, this]
    · simp [hp]
  have h3 : ∑ B ∈ 𝓑.filter (fun B => p ∈ B), (B.erase p).card
      = repl 𝓑 p * (k - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => k - 1)]
    · simp [repl]
    · intro B hB
      rw [Finset.mem_filter] at hB
      rw [Finset.card_erase_of_mem hB.2, h.card_block B hB.1]
  rw [← h1, h2, h3]

/-- In a nondegenerate 2-design `l ≥ 1`. -/
lemma one_le_lambda {k l : ℕ} (h : IsDesign2 𝓑 k l) (hk : 2 ≤ k) (hne : 𝓑.Nonempty) :
    1 ≤ l := by
  obtain ⟨B, hB⟩ := hne
  have hc : 1 < B.card := by rw [h.card_block B hB]; omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hc
  rw [← h.count p q hpq]
  exact Finset.card_pos.mpr ⟨B, by simp [hB, hp, hq]⟩

/-- The replication number is the same for all points. -/
lemma repl_const {k l : ℕ} (h : IsDesign2 𝓑 k l) (hk : 2 ≤ k) (p q : P) :
    repl 𝓑 p = repl 𝓑 q := by
  have hp := repl_mul h p
  have hq := repl_mul h q
  have hk' : 0 < k - 1 := by omega
  exact Nat.eq_of_mul_eq_mul_right hk' (hp.trans hq.symm)

/-- `Aᵀ A = (r - λ) I + λ J`. -/
lemma gram_eq {k l : ℕ} (h : IsDesign2 𝓑 k l) (r : ℕ) (hr : ∀ p, repl 𝓑 p = r) (p q : P) :
    ((incMat 𝓑)ᵀ * incMat 𝓑) q p = ((r : ℚ) - l) * (if q = p then 1 else 0) + l := by
  rw [gram_apply]
  by_cases hqp : q = p
  · subst hqp
    have : (𝓑.filter (fun B => q ∈ B ∧ q ∈ B)).card = r := by
      rw [← hr q, repl]; simp only [and_self]
    rw [this]; simp
  · rw [h.count q p hqp]; simp [hqp]

/-- Fisher's inequality, matrix form: for a nontrivial 2-design the incidence matrix has
trivial kernel. -/
lemma incMat_mulVec_injective {k l : ℕ} (h : IsDesign2 𝓑 k l) (hk : 2 ≤ k)
    (hkv : k < Fintype.card P) (hne : 𝓑.Nonempty) :
    Function.Injective (incMat 𝓑).mulVec := by
  classical
  have hl := one_le_lambda h hk hne
  obtain ⟨p0⟩ : Nonempty P := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := Fintype.card_eq_zero (α := P)
    omega
  set r := repl 𝓑 p0 with hrdef
  have hr : ∀ p, repl 𝓑 p = r := fun p => repl_const h hk p p0
  -- r > λ
  have hrl : l < r := by
    have h0 := repl_mul h p0
    rw [← hrdef] at h0
    by_contra hcon
    push_neg at hcon
    have h1 : r * (k - 1) ≤ l * (k - 1) := Nat.mul_le_mul_right _ hcon
    have h2 : l * (k - 1) < (Fintype.card P - 1) * l := by
      rw [mul_comm l]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have hrl' : (0 : ℚ) < (r : ℚ) - l := by
    have : (l : ℚ) < r := by exact_mod_cast hrl
    linarith
  have hl' : (0 : ℚ) ≤ l := Nat.cast_nonneg l
  have key : ∀ x : P → ℚ, (incMat 𝓑) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hG : ((incMat 𝓑)ᵀ * incMat 𝓑) *ᵥ x = 0 := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have hq : ∀ q, ((r : ℚ) - l) * x q + l * ∑ p, x p = 0 := by
      intro q
      have h1 := congrFun hG q
      have e : ∑ p, (((r : ℚ) - l) * (if q = p then 1 else 0) + l) * x p
          = ((r : ℚ) - l) * x q + l * ∑ p, x p := by
        simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      simp only [Matrix.mulVec, dotProduct, gram_eq h r hr, Pi.zero_apply] at h1
      rw [e] at h1
      exact h1
    have hs : ∑ p, x p = 0 := by
      have h2 : ∑ q, (((r : ℚ) - l) * x q + l * ∑ p, x p) = 0 :=
        Finset.sum_eq_zero fun q _ => hq q
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] at h2
      have hv : (0 : ℚ) < ((r : ℚ) - l) + (Fintype.card P : ℚ) * l := by
        have : (0 : ℚ) ≤ (Fintype.card P : ℚ) * l := mul_nonneg (Nat.cast_nonneg _) hl'
        linarith
      have h3 : (((r : ℚ) - l) + (Fintype.card P : ℚ) * l) * ∑ p, x p = 0 := by
        linarith
      exact (mul_eq_zero.mp h3).resolve_left hv.ne'
    funext q
    have := hq q
    rw [hs, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hrl'.ne'
  intro x y hxy
  have : (incMat 𝓑) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ this)

/-- **Fisher's inequality** (rank version): a nontrivial 2-design has at least as many blocks
as points. -/
theorem fisher {k l : ℕ} (h : IsDesign2 𝓑 k l) (hk : 2 ≤ k) (hkv : k < Fintype.card P)
    (hne : 𝓑.Nonempty) : Fintype.card P ≤ 𝓑.card := by
  have hinj := incMat_mulVec_injective h hk hkv hne
  have := LinearMap.finrank_le_finrank_of_injective
    (f := Matrix.mulVecLin (incMat 𝓑)) hinj
  simpa using this

end FisherNotes
