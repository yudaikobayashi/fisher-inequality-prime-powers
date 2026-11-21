import FisherNotes.Basic

/-!
# Isomorphism of incidence structures and incidence matrices (Section 3 of the notes)

An isomorphism is a bijection `e : P ≃ Q` of points carrying the blocks onto the blocks.
(This is equivalent to the notes' bijection on points ∪ blocks preserving incidence, because a
block is determined by the set of points it contains.)  Two structures are isomorphic iff their
incidence matrices differ by a permutation of rows and of columns.
-/

open Finset

namespace FisherNotes

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- `e` is an isomorphism from `(P, 𝓑)` to `(Q, 𝓒)`. -/
def IsIso (𝓑 : Finset (Finset P)) (𝓒 : Finset (Finset Q)) (e : P ≃ Q) : Prop :=
  ∀ B : Finset P, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓒

/-- Isomorphic iff the incidence matrices agree after permuting rows and columns. -/
theorem isIso_iff (𝓑 : Finset (Finset P)) (𝓒 : Finset (Finset Q)) :
    (∃ e : P ≃ Q, IsIso 𝓑 𝓒 e) ↔
      ∃ (σ : 𝓑 ≃ 𝓒) (e : P ≃ Q), ∀ (B : 𝓑) (p : P),
        incMat 𝓒 (σ B) (e p) = incMat 𝓑 B p := by
  constructor
  · rintro ⟨e, he⟩
    let f : 𝓑 → 𝓒 := fun B => ⟨(B : Finset P).map e.toEmbedding, (he B).mp B.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro B B' h
        have := congrArg Subtype.val h
        simp only [f] at this
        exact Subtype.ext (Finset.map_injective _ this)
      · rintro ⟨C, hC⟩
        refine ⟨⟨C.map e.symm.toEmbedding, ?_⟩, ?_⟩
        · rw [he]
          simpa [Finset.map_map] using hC
        · apply Subtype.ext
          simp [f, Finset.map_map]
    refine ⟨Equiv.ofBijective f hf, e, fun B p => ?_⟩
    simp [incMat, f]
  · rintro ⟨σ, e, h⟩
    refine ⟨e, fun B => ⟨fun hB => ?_, fun hC => ?_⟩⟩
    · have : ((σ ⟨B, hB⟩ : 𝓒) : Finset Q) = B.map e.toEmbedding := by
        ext q
        obtain ⟨p, rfl⟩ := e.surjective q
        have := h ⟨B, hB⟩ p
        simp only [incMat, Matrix.of_apply] at this
        by_cases hp : p ∈ B <;> simp [hp] at this ⊢ <;> assumption
      rw [← this]; exact (σ ⟨B, hB⟩).2
    · obtain ⟨B', hB'⟩ := σ.surjective ⟨B.map e.toEmbedding, hC⟩
      have hmap : ((σ B' : 𝓒) : Finset Q) = (B' : Finset P).map e.toEmbedding := by
        ext q
        obtain ⟨p, rfl⟩ := e.surjective q
        have := h B' p
        simp only [incMat, Matrix.of_apply] at this
        by_cases hp : p ∈ (B' : Finset P) <;> simp [hp] at this ⊢ <;> assumption
      rw [hB'] at hmap
      have := Finset.map_injective e.toEmbedding (by simpa using hmap)
      rw [this]; exact B'.2

end FisherNotes
