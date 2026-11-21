import FisherNotes.Basic
import FisherNotes.Design

/-!
# Example: the Fano plane is a symmetric `2-(7,3,1)` design (Section 1 of the notes)
-/

namespace FisherNotes

/-- The Fano plane on `{0,…,6}` (the notes number the points `1,…,7`). -/
def fano : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 6}, {1, 4, 5}, {2, 4, 6}, {2, 3, 5}}

set_option maxRecDepth 100000 in
theorem fano_isDesign2 : IsDesign2 fano 3 1 := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem fano_symmetric : fano.card = Fintype.card (Fin 7) := by decide +kernel

/-- Fisher's inequality is sharp here: `b = v`. -/
example : Fintype.card (Fin 7) ≤ fano.card := fisher fano_isDesign2 (by norm_num) (by decide +kernel) (by decide +kernel)

end FisherNotes
