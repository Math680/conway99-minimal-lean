import ImageGap
import TriangleCount

/-!
The cubic Gram lower bound is deduced from the actual SRG hypothesis.
Its rational rescaling is intentionally called a cubic defect here: the
identification with the combinatorial delta requires the separate cubic count.
-/

namespace Conway99

open scoped BigOperators
open Finset Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_integer_cubic_sum_ge_660 (h : G.IsSRGWith 99 14 1 2) :
    660 ≤ ∑ L, ∑ M, integerTriangleGram G L M ^ 3 := by
  have hc : Fintype.card (TriangleIndex G) = 231 := by
    simpa only [TriangleIndex, Fintype.card_coe] using triangle_count_231 G h
  have hb := sum_le_sum (s := (univ : Finset (TriangleIndex G)))
    (fun J _ => graph_diagonal_contraction_ge_sixty G h J)
  simp only [sum_const, card_univ, hc, nsmul_eq_mul,
    graph_contraction_total G h] at hb
  omega

def triangleCubicDefect : ℚ :=
  (1 / 4 : ℚ) * ∑ L, ∑ M, triangleGram G L M ^ 3

theorem graph_triangleCubicDefect_ge_165 (h : G.IsSRGWith 99 14 1 2) :
    165 ≤ triangleCubicDefect G := by
  have hi := graph_integer_cubic_sum_ge_660 G h
  have hq : (660 : ℚ) ≤ ∑ L, ∑ M, triangleGram G L M ^ 3 := by
    simp_rw [← integerTriangleGram_cast G]
    exact_mod_cast hi
  unfold triangleCubicDefect
  linarith

#print axioms graph_integer_cubic_sum_ge_660
#print axioms graph_triangleCubicDefect_ge_165

end Conway99
