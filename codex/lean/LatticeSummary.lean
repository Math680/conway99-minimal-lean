import LatticeRank
import LatticeQuadratic

/-! One graph-level statement collecting the completed lattice foundations.
It deliberately does not assert determinant 49, an overlattice, or a root bound. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def CanonicalLatticeFoundations : Prop :=
  Module.finrank ℤ (canonicalLattice G) = 44 ∧
  (canonicalLattice G).FG ∧
  vertexLattice G ≤ triangleLattice G ∧
  triangleLattice G ≤ canonicalLattice G ∧
  (∀ x ∈ canonicalLattice G, ∀ y ∈ canonicalLattice G,
    ∃ n : ℤ, codePair x y = (n : ℚ)) ∧
  (∀ x ∈ canonicalLattice G, ∃ n : ℤ, codePair x x = (2 * n : ℤ)) ∧
  (∀ x ∈ canonicalLattice G, x ≠ 0 → 0 < codePair x x) ∧
  Finite (CanonicalDiscriminant G) ∧
  (∀ q : CanonicalDiscriminant G, (7 : ℤ) • q = 0) ∧
  ∃ e : ℕ, Nat.card (CanonicalDiscriminant G) = 7 ^ e

theorem graph_canonical_lattice_foundations (h : G.IsSRGWith 99 14 1 2) :
    CanonicalLatticeFoundations G := by
  exact ⟨canonicalLattice_finrank G h, canonicalLattice_fg G,
    vertexLattice_le_triangle G h, triangleLattice_le_canonical G,
    fun _ hx _ hy => canonicalLattice_integral G h hx hy,
    fun _ hx => canonicalLattice_even G h hx,
    fun x _ hx => codePair_pos x hx,
    canonicalDiscriminant_finite G h,
    canonicalDiscriminant_annihilated_seven G h,
    canonicalDiscriminant_card_power_seven G h⟩

#print axioms graph_canonical_lattice_foundations

end Conway99
