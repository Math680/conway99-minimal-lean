import DualMinimum
import RootBiplane

/-! Root codes and their biplanes for every canonical intermediate lift. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalDual_root_biplane (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) (hn : codePair x x = 2) :
    ∃ b : V → ℤ, x = (3 : ℚ) • (fun u => (b u : ℚ)) ∧
      (fun u => (b u : ℚ)) ∈ rationalAmbient G ∧
      (∑ u, b u = 0) ∧ (∑ u, b u ^ 2 = 14) ∧ SignedBiplaneCode G b := by
  obtain ⟨b, he, hE, hs, h14, _⟩ := canonicalDual_root_integral_code G h hx hn
  exact ⟨b, he, hE, hs, h14, integer_eigen_norm_fourteen_biplane G h b hs
    (integerAmbient_eigen G h b hE) h14⟩

theorem canonicalLift_root_biplane (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) {x : V → ℚ}
    (hx : x ∈ canonicalLift G H) (hn : codePair x x = 2) :
    ∃ b : V → ℤ, x = (3 : ℚ) • (fun u => (b u : ℚ)) ∧
      (fun u => (b u : ℚ)) ∈ rationalAmbient G ∧
      (∑ u, b u = 0) ∧ (∑ u, b u ^ 2 = 14) ∧ SignedBiplaneCode G b :=
  canonicalDual_root_biplane G h (canonicalLift_le_dual G H hx) hn

#print axioms canonicalDual_root_biplane
#print axioms canonicalLift_root_biplane

end Conway99
