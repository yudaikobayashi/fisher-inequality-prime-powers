import FisherNotes.Basic

/-!
# Fisher's inequality, original proof by the variance of block intersections

Fix a block `B₀`. For every other block `C` put `μ C = |B₀ ∩ C|`. Double counting gives
`∑ μ = k (r-1)` and `∑ μ (μ-1) = k (k-1) (λ-1)`; non-negativity of the variance
(Cauchy–Schwarz) then yields `r ≥ k`, hence `b ≥ v` from `b k = v r`.
-/

open Finset

namespace FisherNotes

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓑 : Finset (Finset P)} {k l : ℕ}

/-- `μ B₀ C = |B₀ ∩ C|`. -/
def mu (B₀ C : Finset P) : ℕ := (B₀.filter (fun p => p ∈ C)).card

/-- `b k = v r`. -/
lemma b_mul_k (h : IsDesign2 𝓑 k l) (r : ℕ) (hr : ∀ p, repl 𝓑 p = r) :
    𝓑.card * k = Fintype.card P * r := by
  have h1 : ∑ B ∈ 𝓑, B.card = 𝓑.card * k := by
    rw [Finset.sum_congr rfl (g := fun _ => k) h.card_block]; simp
  have h2 : ∑ B ∈ 𝓑, B.card = ∑ p : P, repl 𝓑 p := by
    simp_rw [repl, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← Finset.card_filter]; simp
  rw [← h1, h2, Finset.sum_congr rfl (fun p _ => hr p)]
  simp

/-- First moment: `∑_{C ≠ B₀} |B₀ ∩ C| = k (r - 1)`. -/
lemma sum_mu {B₀ : Finset P} (hB₀ : B₀ ∈ 𝓑) (h : IsDesign2 𝓑 k l) (r : ℕ)
    (hr : ∀ p, repl 𝓑 p = r) :
    ∑ C ∈ 𝓑.erase B₀, mu B₀ C = k * (r - 1) := by
  have h1 : ∑ C ∈ 𝓑.erase B₀, mu B₀ C
      = ∑ p ∈ B₀, ((𝓑.erase B₀).filter (fun C => p ∈ C)).card := by
    simp_rw [mu, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [h1]
  have h2 : ∀ p ∈ B₀, ((𝓑.erase B₀).filter (fun C => p ∈ C)).card = r - 1 := by
    intro p hp
    rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp [hB₀, hp])]
    have := hr p
    rw [repl] at this
    rw [this]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, h.card_block B₀ hB₀]

/-- Second moment: `∑_{C ≠ B₀} |B₀ ∩ C| (|B₀ ∩ C| - 1) = k (k-1) (λ-1)`, in the form
`∑ μ² = k (k-1) (λ-1) + ∑ μ`. -/
lemma sum_mu_sq {B₀ : Finset P} (hB₀ : B₀ ∈ 𝓑) (h : IsDesign2 𝓑 k l) :
    ∑ C ∈ 𝓑.erase B₀, (mu B₀ C) * (mu B₀ C)
      = (k * k - k) * (l - 1) + ∑ C ∈ 𝓑.erase B₀, mu B₀ C := by
  have hμ : ∀ C, mu B₀ C * mu B₀ C
      = (B₀.offDiag.filter (fun x : P × P => x.1 ∈ C ∧ x.2 ∈ C)).card + mu B₀ C := by
    intro C
    have e : (B₀.filter (fun p => p ∈ C)).offDiag
        = B₀.offDiag.filter (fun x : P × P => x.1 ∈ C ∧ x.2 ∈ C) := by
      ext x
      simp only [Finset.mem_offDiag, Finset.mem_filter]
      tauto
    rw [← e, Finset.offDiag_card, mu]
    exact (Nat.sub_add_cancel (Nat.le_mul_self _)).symm
  rw [Finset.sum_congr rfl (fun C _ => hμ C), Finset.sum_add_distrib]
  congr 1
  have h1 : ∑ C ∈ 𝓑.erase B₀, (B₀.offDiag.filter (fun x : P × P => x.1 ∈ C ∧ x.2 ∈ C)).card
      = ∑ x ∈ B₀.offDiag, ((𝓑.erase B₀).filter (fun C => x.1 ∈ C ∧ x.2 ∈ C)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [h1]
  have h2 : ∀ x ∈ B₀.offDiag, ((𝓑.erase B₀).filter (fun C => x.1 ∈ C ∧ x.2 ∈ C)).card = l - 1 := by
    intro x hx
    rw [Finset.mem_offDiag] at hx
    rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp [hB₀, hx.1, hx.2.1]),
      h.count x.1 x.2 hx.2.2]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.offDiag_card,
    h.card_block B₀ hB₀]

/-- **Fisher's inequality** (original proof via the variance): a nontrivial 2-design has `r ≥ k`,
hence `b ≥ v`. -/
theorem fisher_variance (h : IsDesign2 𝓑 k l) (hk : 2 ≤ k) (hkv : k < Fintype.card P)
    (hne : 𝓑.Nonempty) : Fintype.card P ≤ 𝓑.card := by
  obtain ⟨B₀, hB₀⟩ := hne
  have hl := one_le_lambda h hk ⟨B₀, hB₀⟩
  obtain ⟨p0⟩ : Nonempty P := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := Fintype.card_eq_zero (α := P)
    omega
  set r := repl 𝓑 p0 with hrdef
  have hr : ∀ p, repl 𝓑 p = r := fun p => repl_const h hk p p0
  have hbk := b_mul_k h r hr
  have hrk := repl_mul h p0
  rw [← hrdef] at hrk
  have hS1 := sum_mu hB₀ h r hr
  have hS2 := sum_mu_sq hB₀ h
  set v := Fintype.card P with hv
  set b := 𝓑.card with hb
  have hb1 : 1 ≤ b := Finset.card_pos.mpr ⟨B₀, hB₀⟩
  have hr1 : 1 ≤ r := by
    by_contra hcon
    have h0 : r = 0 := by omega
    rw [h0, zero_mul] at hrk
    have : 0 < (v - 1) * l := Nat.mul_pos (by omega) (by omega)
    omega
  -- casts to ℚ
  have hcs : (∑ C ∈ 𝓑.erase B₀, (mu B₀ C : ℚ)) ^ 2
      ≤ ((𝓑.erase B₀).card : ℚ) * ∑ C ∈ 𝓑.erase B₀, (mu B₀ C : ℚ) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := 𝓑.erase B₀) (f := fun C => (mu B₀ C : ℚ))
  have hcard : ((𝓑.erase B₀).card : ℚ) = (b : ℚ) - 1 := by
    rw [Finset.card_erase_of_mem hB₀, Nat.cast_sub hb1]; simp
  have hS1q : ∑ C ∈ 𝓑.erase B₀, (mu B₀ C : ℚ) = (k : ℚ) * ((r : ℚ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hS1
    simp only [Nat.cast_sum, Nat.cast_mul] at this
    rw [this, Nat.cast_sub hr1]; simp
  have hS2q : ∑ C ∈ 𝓑.erase B₀, (mu B₀ C : ℚ) ^ 2
      = ((k : ℚ) * k - k) * ((l : ℚ) - 1) + (k : ℚ) * ((r : ℚ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hS2
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add] at this
    rw [Nat.cast_sub (Nat.le_mul_self k), Nat.cast_sub hl] at this
    simp only [Nat.cast_mul, Nat.cast_one] at this
    rw [← hS1q]
    simpa [sq] using this
  have hbq : (b : ℚ) * k = v * r := by exact_mod_cast hbk
  have hrq : (r : ℚ) * ((k : ℚ) - 1) = ((v : ℚ) - 1) * l := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hrk
    simp only [Nat.cast_mul] at this
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ v)] at this
    simpa using this
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hkvq : (k : ℚ) < v := by exact_mod_cast hkv
  have hrq0 : (1 : ℚ) ≤ r := by exact_mod_cast hr1
  have hk0 : (k : ℚ) ≠ 0 := by linarith
  have hv1 : (v : ℚ) - 1 ≠ 0 := by linarith
  have hbe : (b : ℚ) = v * r / k := by
    rw [eq_div_iff hk0]; linarith
  have hle : (l : ℚ) = r * (k - 1) / (v - 1) := by
    rw [eq_div_iff hv1]; linarith
  rw [hS1q, hS2q, hcard] at hcs
  have hE : ((b : ℚ) - 1) * (((k : ℚ) * k - k) * ((l : ℚ) - 1) + (k : ℚ) * ((r : ℚ) - 1))
      - ((k : ℚ) * ((r : ℚ) - 1)) ^ 2 = r * (r - k) * (v - k) ^ 2 / (v - 1) := by
    rw [hbe, hle]
    field_simp
    ring
  have hX : 0 ≤ (r : ℚ) * (r - k) * (v - k) ^ 2 / (v - 1) := by rw [← hE]; linarith
  have hX' : 0 ≤ (r : ℚ) * (r - k) * (v - k) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have := div_neg_of_neg_of_pos hcon (by linarith : (0 : ℚ) < v - 1)
    linarith
  have hrk' : (k : ℚ) ≤ r := by
    by_contra hcon
    push_neg at hcon
    have : (r : ℚ) * (r - k) * (v - k) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith))
        (by have : (0 : ℚ) < v - k := by linarith
            positivity)
    linarith
  have : (v : ℚ) ≤ b := by
    have h1 : (v : ℚ) * k ≤ b * k := by rw [hbq]; nlinarith
    exact le_of_mul_le_mul_right h1 (by linarith)
  exact_mod_cast this

