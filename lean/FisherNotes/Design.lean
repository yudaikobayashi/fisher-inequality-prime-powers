import FisherNotes.Basic

/-!
# `t`-designs and the recursion for `λ_s` (Section 2 of the notes)

For a `t-(v,k,λ)` design and `S` with `|S| = s ≤ t`, the number `m` of blocks containing `S`
satisfies `m * C(k-s, t-s) = λ * C(v-s, t-s)`.  Hence (for `t ≤ k`) the design is an
`s-(v,k,λ_s)` design for every `s ≤ t`.
-/

open Finset

namespace FisherNotes

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓑 : Finset (Finset P)} {t k l : ℕ}

/-- `t-(v,k,λ)` design. -/
structure IsDesign (𝓑 : Finset (Finset P)) (t k l : ℕ) : Prop where
  card_block : ∀ B ∈ 𝓑, B.card = k
  count : ∀ T : Finset P, T.card = t → (𝓑.filter (fun B => T ⊆ B)).card = l

/-- Number of `t`-sets `T` with `S ⊆ T ⊆ X`. -/
lemma card_between {X S : Finset P} (hS : S ⊆ X) (hst : S.card ≤ t) :
    ((X.powersetCard t).filter (fun T => S ⊆ T)).card
      = (X.card - S.card).choose (t - S.card) := by
  have hc := Finset.card_powersetCard (t - S.card) (X \ S)
  rw [Finset.card_sdiff_of_subset hS] at hc
  rw [← hc]
  refine Finset.card_nbij' (fun T => T \ S) (fun U => U ∪ S) ?_ ?_ ?_ ?_
  · intro T hT
    have hT := Finset.mem_filter.mp hT
    obtain ⟨hTp, hST⟩ := hT
    obtain ⟨hTX, hTt⟩ := Finset.mem_powersetCard.mp hTp
    refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hTX (Finset.Subset.refl S), ?_⟩
    rw [Finset.card_sdiff_of_subset hST, hTt]
  · intro U hU
    obtain ⟨hUX, hUc⟩ := Finset.mem_powersetCard.mp hU
    have hdisj : Disjoint U S := by
      rw [Finset.disjoint_left]
      intro x hxU hxS
      exact (Finset.mem_sdiff.mp (hUX hxU)).2 hxS
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.union_subset (hUX.trans Finset.sdiff_subset) hS, ?_⟩, Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, hUc]
    omega
  · intro T hT
    have hT := Finset.mem_filter.mp hT
    exact Finset.sdiff_union_of_subset hT.2
  · intro U hU
    obtain ⟨hUX, hUc⟩ := Finset.mem_powersetCard.mp hU
    have hdisj : Disjoint U S := by
      rw [Finset.disjoint_left]
      intro x hxU hxS
      exact (Finset.mem_sdiff.mp (hUX hxU)).2 hxS
    show (U ∪ S) \ S = U
    rw [Finset.union_sdiff_right, hdisj.sdiff_eq_left]

/-- Double counting of `(T, B)` with `S ⊆ T ⊆ B`, `|T| = t`, `B ∈ 𝓑`. -/
lemma lambda_rel (h : IsDesign 𝓑 t k l) {S : Finset P} (hs : S.card ≤ t) :
    (𝓑.filter (fun B => S ⊆ B)).card * (k - S.card).choose (t - S.card)
      = l * (Fintype.card P - S.card).choose (t - S.card) := by
  set 𝒯 : Finset (Finset P) := (Finset.univ.powersetCard t).filter (fun T => S ⊆ T) with h𝒯
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := 𝓑.filter (fun B => S ⊆ B)) (t := 𝒯) (fun B T => T ⊆ B)
  have hL : ∀ B ∈ 𝓑.filter (fun B => S ⊆ B),
      (Finset.bipartiteAbove (fun B T => T ⊆ B) 𝒯 B).card = (k - S.card).choose (t - S.card) := by
    intro B hB
    rw [Finset.mem_filter] at hB
    have : Finset.bipartiteAbove (fun B T => T ⊆ B) 𝒯 B
        = (B.powersetCard t).filter (fun T => S ⊆ T) := by
      ext T
      simp only [Finset.bipartiteAbove, h𝒯, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      tauto
    rw [this, card_between hB.2 hs, h.card_block B hB.1]
  have hR : ∀ T ∈ 𝒯,
      (Finset.bipartiteBelow (fun B T => T ⊆ B) (𝓑.filter (fun B => S ⊆ B)) T).card = l := by
    intro T hT
    simp only [h𝒯, Finset.mem_filter, Finset.mem_powersetCard] at hT
    have : Finset.bipartiteBelow (fun B T => T ⊆ B) (𝓑.filter (fun B => S ⊆ B)) T
        = 𝓑.filter (fun B => T ⊆ B) := by
      ext B
      simp only [Finset.bipartiteBelow, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hB, _⟩, hTB⟩; exact ⟨hB, hTB⟩
      · rintro ⟨hB, hTB⟩; exact ⟨⟨hB, hT.2.trans hTB⟩, hTB⟩
    rw [this]
    exact h.count T hT.1.2
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, h𝒯, card_between (Finset.subset_univ S) hs, Finset.card_univ] at hdc
  rw [hdc, mul_comm]

/-- A `t-(v,k,λ)` design with `t ≤ k` is also an `s-(v,k,λ_s)` design for `s ≤ t`,
with `λ_s = λ C(v-s,t-s) / C(k-s,t-s)`. -/
theorem IsDesign.of_le (h : IsDesign 𝓑 t k l) (htk : t ≤ k) {s : ℕ} (hst : s ≤ t) :
    IsDesign 𝓑 s k (l * (Fintype.card P - s).choose (t - s) / (k - s).choose (t - s)) := by
  refine ⟨h.card_block, fun S hS => ?_⟩
  have hrel := lambda_rel h (S := S) (by omega)
  rw [hS] at hrel
  have hpos : 0 < (k - s).choose (t - s) := Nat.choose_pos (by omega)
  rw [← hrel, Nat.mul_div_cancel _ hpos]

/-- A `t`-design with `t ≥ 2` is a `2`-design (in the pair form `IsDesign2`). -/
theorem IsDesign.toDesign2 (h : IsDesign 𝓑 t k l) (htk : t ≤ k) (ht : 2 ≤ t) :
    ∃ m, IsDesign2 𝓑 k m := by
  have h2 := h.of_le htk ht
  refine ⟨l * (Fintype.card P - 2).choose (t - 2) / (k - 2).choose (t - 2),
    ⟨h.card_block, fun p q hpq => ?_⟩⟩
  have := h2.count {p, q} (Finset.card_pair hpq)
  simpa [Finset.insert_subset_iff] using this

/-- `λ_i^j`: the Pascal-type recursion `λ_i^{j+1} = λ_i^j - λ_{i+1}^j`, starting from `λ_i^0 = Λ i`. -/
def lamIJ (Λ : ℕ → ℕ) : ℕ → ℕ → ℕ
  | i, 0 => Λ i
  | i, j + 1 => lamIJ Λ i j - lamIJ Λ (i + 1) j

/-- Number of blocks containing `I` and disjoint from `J`. -/
def nIJ (𝓑 : Finset (Finset P)) (I J : Finset P) : ℕ :=
  (𝓑.filter (fun B => I ⊆ B ∧ Disjoint J B)).card

/-- Inclusion–exclusion step: `n(I,J ∪ {p}) = n(I,J) - n(I ∪ {p}, J)`. -/
lemma nIJ_insert {I J : Finset P} {p : P} (hpJ : p ∉ J) (hpI : p ∉ I) :
    nIJ 𝓑 I (insert p J) = nIJ 𝓑 I J - nIJ 𝓑 (insert p I) J := by
  have hsplit : nIJ 𝓑 I J = nIJ 𝓑 I (insert p J) + nIJ 𝓑 (insert p I) J := by
    unfold nIJ
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext B
      simp only [Finset.mem_union, Finset.mem_filter, Finset.insert_subset_iff,
        Finset.disjoint_insert_left]
      by_cases hp : p ∈ B <;> tauto
    · rw [Finset.disjoint_left]
      intro B h1 h2
      simp only [Finset.mem_filter, Finset.insert_subset_iff, Finset.disjoint_insert_left] at h1 h2
      tauto
  omega

/-- `λ_i^j` does not depend on the choice of `I`, `J` (`|I| + |J| ≤ t`), for a design in which
every `s`-set (`s ≤ t`) lies in `Λ s` blocks. -/
theorem nIJ_eq (Λ : ℕ → ℕ) (hΛ : ∀ s ≤ t, ∀ S : Finset P, S.card = s →
      (𝓑.filter (fun B => S ⊆ B)).card = Λ s) :
    ∀ j : ℕ, ∀ I J : Finset P, Disjoint I J → I.card + J.card ≤ t → J.card = j →
      nIJ 𝓑 I J = lamIJ Λ I.card j := by
  intro j
  induction j with
  | zero =>
    intro I J _ hIJ hj
    rw [Finset.card_eq_zero] at hj
    subst hj
    simp only [lamIJ, nIJ, Finset.disjoint_empty_left, and_true]
    exact hΛ _ (by simpa using hIJ) I rfl
  | succ j ih =>
    intro I J hdisj hIJ hj
    obtain ⟨p, hp⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
    have hpI : p ∉ I := fun hpI => Finset.disjoint_left.mp hdisj hpI hp
    have hJe : J = insert p (J.erase p) := (Finset.insert_erase hp).symm
    have hcJ : (J.erase p).card = j := by rw [Finset.card_erase_of_mem hp]; omega
    rw [hJe, nIJ_insert (Finset.notMem_erase p J) hpI]
    have e1 := ih I (J.erase p) (Finset.disjoint_of_subset_right (Finset.erase_subset p J) hdisj)
      (by omega) hcJ
    have e2 := ih (insert p I) (J.erase p) (by
        rw [Finset.disjoint_insert_left]
        exact ⟨Finset.notMem_erase p J,
          Finset.disjoint_of_subset_right (Finset.erase_subset p J) hdisj⟩)
      (by rw [Finset.card_insert_of_notMem hpI]; omega) hcJ
    rw [e1, e2, Finset.card_insert_of_notMem hpI, lamIJ]

/-- For a `t-(v,k,λ)` design with `t ≤ k`, the number of blocks containing `I` and disjoint
from `J` depends only on `|I|` and `|J|` when `|I| + |J| ≤ t`. -/
theorem IsDesign.nIJ_eq (h : IsDesign 𝓑 t k l) (htk : t ≤ k) {I J I' J' : Finset P}
    (hd : Disjoint I J) (hd' : Disjoint I' J') (hc : I.card + J.card ≤ t)
    (hi : I.card = I'.card) (hj : J.card = J'.card) :
    nIJ 𝓑 I J = nIJ 𝓑 I' J' := by
  set Λ : ℕ → ℕ := fun s => l * (Fintype.card P - s).choose (t - s) / (k - s).choose (t - s)
    with hΛdef
  have hΛ : ∀ s ≤ t, ∀ S : Finset P, S.card = s → (𝓑.filter (fun B => S ⊆ B)).card = Λ s :=
    fun s hs S hS => (h.of_le htk hs).count S hS
  rw [FisherNotes.nIJ_eq Λ hΛ J.card I J hd hc rfl,
    FisherNotes.nIJ_eq Λ hΛ J'.card I' J' hd' (by omega) rfl, hi, hj]

end FisherNotes
