import FisherNotes.Basic

/-!
# `det (Aᵀ A) = r k n^(v-1)` for a 2-design (Section 3 of the notes)
-/

open Finset Matrix

namespace FisherNotes

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓑 : Finset (Finset P)} {k l : ℕ}

/-- `det(a I + c J) = a^(v-1) (a + v c)` (`J` the all-ones matrix), over a field, `a ≠ 0`. -/
lemma det_scalar_add_ones [Nonempty P] {K : Type*} [Field K] (a c : K) (ha : a ≠ 0) :
    (Matrix.of fun i j : P => a * (if i = j then (1 : K) else 0) + c).det
      = a ^ (Fintype.card P - 1) * (a + Fintype.card P * c) := by
  have hM : (Matrix.of fun i j : P => a * (if i = j then (1 : K) else 0) + c)
      = a • (1 + Matrix.replicateCol Unit (fun _ : P => c / a)
          * Matrix.replicateRow Unit (fun _ : P => (1 : K))) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij] <;> field_simp
  rw [hM, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
  have hpos : 0 < Fintype.card P := Fintype.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card P = n + 1 := ⟨Fintype.card P - 1, by omega⟩
  rw [hn]
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- **`det(Aᵀ A) = r k n^(v-1)`** with `n = r - λ`, for a 2-design with `r ≠ λ`. -/
theorem det_gram {r : ℕ} (h : IsDesign2 𝓑 k l) (hk : 1 ≤ k) [Nonempty P]
    (hr : ∀ p, repl 𝓑 p = r) (hrl : (r : ℚ) - l ≠ 0) :
    ((incMat 𝓑)ᵀ * incMat 𝓑).det
      = (r : ℚ) * k * ((r : ℚ) - l) ^ (Fintype.card P - 1) := by
  have hmat : (incMat 𝓑)ᵀ * incMat 𝓑
      = Matrix.of fun i j : P => ((r : ℚ) - l) * (if i = j then (1 : ℚ) else 0) + l := by
    ext i j
    exact gram_eq h r hr j i |>.trans (by simp [eq_comm])
  rw [hmat, det_scalar_add_ones _ _ hrl]
  have hrk := repl_mul h (Classical.arbitrary P)
  rw [hr] at hrk
  have hv : 1 ≤ Fintype.card P := Fintype.card_pos
  have hq : (r : ℚ) * ((k : ℚ) - 1) = ((Fintype.card P : ℚ) - 1) * l := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hrk
    simp only [Nat.cast_mul] at this
    rw [Nat.cast_sub hk, Nat.cast_sub hv] at this
    simpa using this
  have : ((r : ℚ) - l) + Fintype.card P * l = r * k := by nlinarith [hq]
  rw [this]; ring

end FisherNotes
