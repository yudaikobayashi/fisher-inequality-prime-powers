import Mathlib

/-!
# Computations with the parameters only (Section 5 of the notes)

Using only `b k = v r`, `r (k-1) = λ (v-1)` (and non-triviality), without the structure of the
design.
-/

namespace FisherNotes

/-- For `λ = 1`: `b > r` iff `r (r-1) (k-1) > 0`. -/
theorem b_gt_r_iff {b r k v : ℝ} (hk : 0 < k) (h1 : b * k = v * r) (h2 : r * (k - 1) = v - 1) :
    r < b ↔ 0 < r * (r - 1) * (k - 1) := by
  have hv : v = r * (k - 1) + 1 := by linarith
  have key : (b - r) * k = r * (r - 1) * (k - 1) := by
    rw [hv] at h1
    nlinarith [h1]
  constructor
  · intro h
    rw [← key]; exact mul_pos (by linarith) hk
  · intro h
    rw [← key] at h
    have : 0 < b - r := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith

/-- `b ≥ v` iff `λ (v-1) ≥ k (k-1)` for real parameters satisfying the two basic relations. -/
theorem b_ge_v_iff {b r k v l : ℝ} (hk : 1 < k) (hv : 0 < v)
    (h1 : b * k = v * r) (h2 : r * (k - 1) = l * (v - 1)) :
    v ≤ b ↔ k * (k - 1) ≤ l * (v - 1) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  constructor
  · intro hb
    have e : b * k * (k - 1) = l * v * (v - 1) := by
      have : v * r * (k - 1) = v * (l * (v - 1)) := by rw [mul_assoc, h2]
      nlinarith [this, h1]
    have : v * (k * (k - 1)) ≤ v * (l * (v - 1)) := by
      nlinarith [mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ k * (k - 1))]
    exact le_of_mul_le_mul_left this hv
  · intro hl
    have hr : k ≤ r := by
      have : k * (k - 1) ≤ r * (k - 1) := by rw [h2]; linarith
      exact le_of_mul_le_mul_right this hk1
    have : v * k ≤ b * k := by rw [h1]; nlinarith
    exact le_of_mul_le_mul_right this hk0

/-- Integral parameters `(v, k, λ, b, r)` below Fisher's bound (`b < v`, equivalently
`λ (v-1) < k (k-1)`) with `v > k`, `λ ≥ 1`. -/
def HasIntParams (k : ℕ) : Prop :=
  ∃ v l : ℕ, 1 ≤ l ∧ k + 1 ≤ v ∧ l * (v - 1) < k * (k - 1) ∧
    k * (k - 1) ∣ l * (v * (v - 1)) ∧ (k - 1) ∣ l * (v - 1)

/-- If `k` is a prime power there are no integral parameters in the range. -/
theorem not_hasIntParams_of_isPrimePow {k : ℕ} (hk : 2 ≤ k) (hpp : IsPrimePow k) :
    ¬ HasIntParams k := by
  rintro ⟨v, l, hl, hv, hlv, hb, hr⟩
  obtain ⟨p, e, hp, he, rfl⟩ := hpp
  have hp' : p.Prime := hp.nat_prime
  set k := p ^ e with hkdef
  have hcop : Nat.Coprime (v - 1) v := by
    have : v = (v - 1) + 1 := by omega
    conv_rhs => rw [this]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hkb : k ∣ l * (v * (v - 1)) := (Dvd.intro _ rfl).trans hb
  have hkk : Nat.Coprime k (k - 1) := by
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _) |>.symm.symm
  by_cases hpv : p ∣ v
  · -- case (i): k ∣ l v and (k-1) ∣ l (v-1)
    have hpv1 : ¬ p ∣ (v - 1) := by
      intro h1
      have := (Nat.dvd_sub hpv h1)
      have h2 : v - (v - 1) = 1 := by omega
      rw [h2] at this
      exact hp'.one_lt.ne' (Nat.dvd_one.mp this)
    have hc : Nat.Coprime k (v - 1) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp').mpr hpv1)
    have hkv : k ∣ l * v := by
      have : k ∣ l * v * (v - 1) := by
        have e1 : l * v * (v - 1) = l * (v * (v - 1)) := by ring
        rw [e1]; exact hkb
      exact hc.dvd_of_dvd_mul_right this
    obtain ⟨m1, hm1⟩ := hkv
    obtain ⟨m2, hm2⟩ := hr
    rcases lt_trichotomy m1 m2 with h | h | h
    · have h1 : (k - 1) * m2 < k * (k - 1) := by
        rw [← hm2]; exact hlv
      have hm2k : m2 < k := by
        by_contra hc'
        push Not at hc'
        have : (k - 1) * k ≤ (k - 1) * m2 := Nat.mul_le_mul_left _ hc'
        nlinarith
      have hl' : (l : ℤ) = (m1 - m2) * k + m2 := by
        have h3 : (l : ℤ) * v = k * m1 := by exact_mod_cast hm1
        have h4 : (l : ℤ) * ((v : ℤ) - 1) = ((k : ℤ) - 1) * m2 := by
          have := congrArg (fun n : ℕ => (n : ℤ)) hm2
          simp only [Nat.cast_mul] at this
          rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ v)] at this
          simpa using this
        nlinarith
      have : (m1 : ℤ) + 1 ≤ m2 := by exact_mod_cast h
      have hk2 : (m2 : ℤ) + 1 ≤ k := by exact_mod_cast hm2k
      have : (0 : ℤ) < l := by exact_mod_cast hl
      nlinarith
    · subst h
      have h3 : (l : ℤ) * v = k * m1 := by exact_mod_cast hm1
      have h4 : (l : ℤ) * ((v : ℤ) - 1) = ((k : ℤ) - 1) * m1 := by
        have := congrArg (fun n : ℕ => (n : ℤ)) hm2
        simp only [Nat.cast_mul] at this
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ v)] at this
        simpa using this
      have hlm : (l : ℤ) = m1 := by nlinarith
      have hvk : (v : ℤ) = k := by
        have hm : (0 : ℤ) < m1 := by rw [← hlm]; exact_mod_cast hl
        have : (m1 : ℤ) * v = m1 * k := by rw [← hlm] at h3 ⊢; nlinarith
        exact mul_left_cancel₀ hm.ne' this
      have : (k : ℤ) + 1 ≤ v := by exact_mod_cast hv
      omega
    · have hl' : (l : ℤ) = (m1 - m2) * k + m2 := by
        have h3 : (l : ℤ) * v = k * m1 := by exact_mod_cast hm1
        have h4 : (l : ℤ) * ((v : ℤ) - 1) = ((k : ℤ) - 1) * m2 := by
          have := congrArg (fun n : ℕ => (n : ℤ)) hm2
          simp only [Nat.cast_mul] at this
          rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ v)] at this
          simpa using this
        nlinarith
      have h5 : (m2 : ℤ) + 1 ≤ m1 := by exact_mod_cast h
      have hk0 : (2 : ℤ) ≤ k := by exact_mod_cast hk
      have hlk : (k : ℤ) ≤ l := by nlinarith
      have h7 : (l : ℤ) * ((v : ℤ) - 1) < k * (k - 1) := by
        have h8 : ((l * (v - 1) : ℕ) : ℤ) < ((k * (k - 1) : ℕ) : ℤ) := by exact_mod_cast hlv
        simpa [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ v)] using h8
      have hv' : (k : ℤ) ≤ (v : ℤ) - 1 := by
        have : (k : ℤ) + 1 ≤ v := by exact_mod_cast hv
        linarith
      nlinarith [mul_le_mul hlk hv' (by positivity) (by positivity)]
  · -- case (ii): k ∣ l (v-1), together with (k-1) ∣ l (v-1)
    have hc : Nat.Coprime k v :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp').mpr hpv)
    have hkv : k ∣ l * (v - 1) := by
      have : k ∣ l * (v - 1) * v := by
        have e1 : l * (v - 1) * v = l * (v * (v - 1)) := by ring
        rw [e1]; exact hkb
      exact hc.dvd_of_dvd_mul_right this
    have hboth : k * (k - 1) ∣ l * (v - 1) := Nat.Coprime.mul_dvd_of_dvd_of_dvd hkk hkv hr
    have hpos : 0 < l * (v - 1) := Nat.mul_pos hl (by omega)
    exact absurd (Nat.le_of_dvd hpos hboth) (not_le.mpr hlv)

/-- If `k` is not a prime power (`k ≥ 2`) there is `n` with `2 ≤ n ≤ k - 1` and `k ∣ n (n-1)`. -/
lemma exists_idempotent {k : ℕ} (hk : 2 ≤ k) (hpp : ¬ IsPrimePow k) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ k - 1 ∧ k ∣ n * (n - 1) := by
  set p := k.minFac with hp
  have hpp' : p.Prime := Nat.minFac_prime (by omega)
  set a := p ^ k.factorization p with ha
  set b := k / a with hb
  have hab : a * b = k := Nat.mul_div_cancel' (Nat.ordProj_dvd k p)
  have hcop : Nat.Coprime a b :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hpp' (by omega : k ≠ 0))
  have ha1 : 1 < a := by
    have : 0 < k.factorization p := hpp'.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd k)
    exact Nat.one_lt_pow this.ne' hpp'.one_lt
  have hb1 : 1 < b := by
    by_contra hcon
    have hb' : b = 1 := by
      have : 0 < b := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hab; omega)
      omega
    rw [hb', mul_one] at hab
    exact hpp ⟨p, k.factorization p, hpp'.prime, hpp'.factorization_pos_of_dvd (by omega)
      (Nat.minFac_dvd k) |>.trans_le le_rfl, by rw [← ha]; exact hab⟩
  obtain ⟨n0, h0a, h0b⟩ := Nat.chineseRemainder hcop 0 1
  set n := n0 % k with hn
  have hnk : n < k := Nat.mod_lt _ (by omega)
  have han : a ∣ n := by
    have : n0 ≡ n [MOD a] := by
      rw [hn]; exact ((Nat.mod_modEq n0 k).symm.of_dvd ⟨b, hab.symm⟩ |>.symm).symm
    have h' : n ≡ 0 [MOD a] := this.symm.trans h0a
    exact (Nat.modEq_zero_iff_dvd).mp h'
  have hbn : n ≡ 1 [MOD b] := by
    have : n0 ≡ n [MOD b] := by
      rw [hn]; exact ((Nat.mod_modEq n0 k).symm.of_dvd ⟨a, by rw [mul_comm]; exact hab.symm⟩ |>.symm).symm
    exact this.symm.trans h0b
  have hbn1 : b ∣ n - 1 := by
    have hn1 : 1 ≤ n := by
      by_contra hcon
      have h0 : n = 0 := by omega
      rw [h0] at hbn
      have : b ∣ 1 := by
        have := (Nat.modEq_iff_dvd' (by omega : 0 ≤ 1)).mp hbn
        simpa using this
      exact absurd (Nat.dvd_one.mp this) hb1.ne'
    exact (Nat.modEq_iff_dvd' hn1).mp hbn.symm
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hbn1
    have : b ∣ 1 := by
      have := (Nat.modEq_iff_dvd' (by omega : 0 ≤ 1)).mp (h0 ▸ hbn)
      simpa using this
    exact absurd (Nat.dvd_one.mp this) hb1.ne'
  have hn1' : n ≠ 1 := by
    intro h1
    rw [h1] at han
    exact absurd (Nat.dvd_one.mp han) ha1.ne'
  refine ⟨n, by omega, by omega, ?_⟩
  rw [← hab]
  exact Nat.mul_dvd_mul han hbn1 |>.trans (by rfl)

/-- If `k` is not a prime power there are integral parameters (with `λ = 1`). -/
theorem hasIntParams_of_not_isPrimePow {k : ℕ} (hk : 2 ≤ k) (hpp : ¬ IsPrimePow k) :
    HasIntParams k := by
  obtain ⟨n, hn2, hnk, hdvd⟩ := exists_idempotent hk hpp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hnk hdvd ⊢
  refine ⟨1 + n * j, 1, le_rfl, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have h1 : (1 + n * j) - 1 = n * j := by omega
    rw [h1, Nat.add_sub_cancel, one_mul]; nlinarith
  · have h1 : (1 + n * j) - 1 = n * j := by omega
    rw [h1, one_mul]
    -- `k ∣ v n` where `v = 1 + n j`, `k = j + 1`
    have hk' : ((j : ℤ) + 1) ∣ ((1 + n * j : ℕ) : ℤ) * n := by
      have hd : ((j : ℤ) + 1) ∣ (n : ℤ) * ((n : ℤ) - 1) := by
        have := Int.natCast_dvd_natCast.mpr hdvd
        simpa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)] using this
      have e : ((1 + n * j : ℕ) : ℤ) * n
          = (n : ℤ) ^ 2 * ((j : ℤ) + 1) - (n : ℤ) * ((n : ℤ) - 1) := by
        push_cast; ring
      rw [e]
      exact dvd_sub (Dvd.intro_left _ rfl) hd
    have hk'' : (j + 1) ∣ (1 + n * j) * n := by exact_mod_cast hk'
    have : (j + 1) * j ∣ (1 + n * j) * n * j := mul_dvd_mul_right hk'' j
    have e2 : (1 + n * j) * (n * j) = (1 + n * j) * n * j := by ring
    rw [e2]; exact this
  · have h1 : (1 + n * j) - 1 = n * j := by omega
    rw [h1, one_mul]
    exact Dvd.intro_left n rfl

/-- **Theorem** (prime-power criterion): for `k ≥ 2`, integral parameters `b, r` exist in the range
`k+1 ≤ v ≤ k(k-1)/λ` iff `k` is not a prime power. -/
theorem hasIntParams_iff {k : ℕ} (hk : 2 ≤ k) : HasIntParams k ↔ ¬ IsPrimePow k :=
  ⟨fun h hpp => not_hasIntParams_of_isPrimePow hk hpp h,
   fun h => hasIntParams_of_not_isPrimePow hk h⟩

/-- **Main theorem.** For `k ≥ 2`: integrality of the parameters alone forces Fisher's
inequality `b ≥ v` (for every `v > k`, `λ ≥ 1` and natural `b, r` satisfying
`b k = v r`, `r (k-1) = λ (v-1)`) if and only if `k` is a prime power. -/
theorem fisher_of_integral_iff {k : ℕ} (hk : 2 ≤ k) :
    (∀ v l b r : ℕ, k < v → 1 ≤ l → b * k = v * r → r * (k - 1) = l * (v - 1) → v ≤ b)
      ↔ IsPrimePow k := by
  have hk1 : 0 < k - 1 := by omega
  constructor
  · intro H
    by_contra hpp
    obtain ⟨v, l, hl, hv, hlv, hb, hr⟩ := hasIntParams_of_not_isPrimePow hk hpp
    obtain ⟨b, hb'⟩ := hb
    obtain ⟨r, hr'⟩ := hr
    have hbk : b * k = v * r := by
      apply Nat.eq_of_mul_eq_mul_right hk1
      calc b * k * (k - 1) = k * (k - 1) * b := by ring
        _ = l * (v * (v - 1)) := hb'.symm
        _ = v * (l * (v - 1)) := by ring
        _ = v * r * (k - 1) := by rw [hr']; ring
    have hrl : r * (k - 1) = l * (v - 1) := by rw [hr']; ring
    have hvb := H v l b r (by omega) hl hbk hrl
    have hkk : 0 < k * (k - 1) := Nat.mul_pos (by omega) hk1
    have : v * (l * (v - 1)) < v * (k * (k - 1)) :=
      Nat.mul_lt_mul_of_pos_left hlv (by omega)
    have h2 : k * (k - 1) * b < k * (k - 1) * v := by
      calc k * (k - 1) * b = l * (v * (v - 1)) := hb'.symm
        _ = v * (l * (v - 1)) := by ring
        _ < v * (k * (k - 1)) := this
        _ = k * (k - 1) * v := by ring
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  · intro hpp v l b r hv hl hbk hrl
    by_contra hlt
    push Not at hlt
    apply not_hasIntParams_of_isPrimePow hk hpp
    refine ⟨v, l, hl, by omega, ?_, ?_, ?_⟩
    · by_contra hge
      push Not at hge
      have e : b * k * (k - 1) = v * (l * (v - 1)) := by
        calc b * k * (k - 1) = v * r * (k - 1) := by rw [hbk]
          _ = v * (r * (k - 1)) := by ring
          _ = v * (l * (v - 1)) := by rw [hrl]
      have : v * (k * (k - 1)) ≤ v * (l * (v - 1)) := Nat.mul_le_mul_left _ hge
      have h3 : v * (k * (k - 1)) ≤ b * k * (k - 1) := by rw [e]; exact this
      have h4 : v * (k * (k - 1)) ≤ b * (k * (k - 1)) := by
        calc v * (k * (k - 1)) ≤ b * k * (k - 1) := h3
          _ = b * (k * (k - 1)) := by ring
      have := Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos (by omega) hk1)
      omega
    · refine ⟨b, ?_⟩
      calc l * (v * (v - 1)) = v * (l * (v - 1)) := by ring
        _ = v * (r * (k - 1)) := by rw [hrl]
        _ = (v * r) * (k - 1) := by ring
        _ = b * k * (k - 1) := by rw [hbk]
        _ = k * (k - 1) * b := by ring
    · exact ⟨r, by rw [← hrl]; ring⟩

end FisherNotes
