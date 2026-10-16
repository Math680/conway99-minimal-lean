import DiscriminantNondegenerate
import FiniteWittReduction
import LatticeLift

/-! The unconditional graph-to-Witt-to-overlattice bridge. No Milgram hypothesis is used
in the main existence theorem. The exact codimension-two variant states its two extra
hypotheses explicitly.
-/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section SevenModule

variable [Module (ZMod 7) (CanonicalDiscriminant G)]

theorem canonicalLift_seven_index (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule (ZMod 7) (CanonicalDiscriminant G)) :
    Nat.card ((canonicalLift G (H.restrictScalars ℤ)) ⧸
      canonicalInsideLift G (H.restrictScalars ℤ)) =
      7 ^ Module.finrank (ZMod 7) H := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Module.Finite (ZMod 7) H := Module.Finite.of_finite
  rw [canonicalLift_index]
  change Nat.card H = 7 ^ Module.finrank (ZMod 7) H
  simpa using Module.natCard_eq_pow_finrank (K := ZMod 7) (V := H)

theorem canonicalLift_seven_quotient_finite (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule (ZMod 7) (CanonicalDiscriminant G)) :
    Finite ((canonicalLift G (H.restrictScalars ℤ)) ⧸
      canonicalInsideLift G (H.restrictScalars ℤ)) := by
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  exact Finite.of_equiv (H.restrictScalars ℤ)
    (canonicalLiftQuotientEquiv G (H.restrictScalars ℤ)).symm.toEquiv

theorem canonicalDiscriminant_exists_witt_subspace (h : G.IsSRGWith 99 14 1 2) :
    ∃ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
      (∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0) ∧
      2 * Module.finrank (ZMod 7) H ≤ Module.finrank (ZMod 7) (CanonicalDiscriminant G) ∧
      Module.finrank (ZMod 7) (CanonicalDiscriminant G) ≤
        2 * Module.finrank (ZMod 7) H + 2 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Module.Finite (ZMod 7) (CanonicalDiscriminant G) := Module.Finite.of_finite
  obtain ⟨H, hH, hlo, hhi⟩ := seven_exists_large_isotropic
    (canonicalDiscriminantForm G h) (canonicalDiscriminantForm_polar_nondegenerate G h)
  exact ⟨H, hH, hlo, hhi⟩

theorem canonicalDiscriminant_exists_codim_two_subspace
    (h : G.IsSRGWith 99 14 1 2)
    (heven : Even (Module.finrank (ZMod 7) (CanonicalDiscriminant G)))
    (hno : ∀ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
      (∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0) →
      2 * Module.finrank (ZMod 7) H ≠ Module.finrank (ZMod 7) (CanonicalDiscriminant G)) :
    ∃ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
      (∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0) ∧
      Module.finrank (ZMod 7) (CanonicalDiscriminant G) =
        2 * Module.finrank (ZMod 7) H + 2 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Module.Finite (ZMod 7) (CanonicalDiscriminant G) := Module.Finite.of_finite
  obtain ⟨H, hH, he⟩ := seven_exists_half_rank_minus_one_isotropic
    (canonicalDiscriminantForm G h) (canonicalDiscriminantForm_polar_nondegenerate G h)
    heven hno
  exact ⟨H, hH, he⟩

end SevenModule

/-- A concrete even full-rank overlattice, with its finite index and Witt bounds. -/
structure CanonicalWittLiftData where
  lattice : Submodule ℤ (V → ℚ)
  exponent : ℕ
  isotropicRank : ℕ
  contains_canonical : canonicalLattice G ≤ lattice
  contained_dual : lattice ≤ canonicalDual G
  finitely_generated : lattice.FG
  rank : Module.finrank ℤ lattice = 44
  integral : ∀ x ∈ lattice, ∀ y ∈ lattice, ∃ a : ℤ, codePair x y = (a : ℚ)
  even : ∀ x ∈ lattice, ∃ a : ℤ, codePair x x = (2 * a : ℤ)
  positive : ∀ x ∈ lattice, x ≠ 0 → 0 < codePair x x
  discriminant_card : Nat.card (CanonicalDiscriminant G) = 7 ^ exponent
  quotient_finite : Finite (lattice ⧸ (canonicalLattice G).comap lattice.subtype)
  index : Nat.card (lattice ⧸ (canonicalLattice G).comap lattice.subtype) = 7 ^ isotropicRank
  lower : 2 * isotropicRank ≤ exponent
  upper : exponent ≤ 2 * isotropicRank + 2

noncomputable def canonicalWittLiftOfSubspace (h : G.IsSRGWith 99 14 1 2)
    [Module (ZMod 7) (CanonicalDiscriminant G)]
    (H : Submodule (ZMod 7) (CanonicalDiscriminant G))
    (hH : ∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0)
    (hlo : 2 * Module.finrank (ZMod 7) H ≤ Module.finrank (ZMod 7) (CanonicalDiscriminant G))
    (hhi : Module.finrank (ZMod 7) (CanonicalDiscriminant G) ≤ 2 * Module.finrank (ZMod 7) H + 2) :
    CanonicalWittLiftData G := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Module.Finite (ZMod 7) (CanonicalDiscriminant G) := Module.Finite.of_finite
  exact {
    lattice := canonicalLift G (H.restrictScalars ℤ)
    exponent := Module.finrank (ZMod 7) (CanonicalDiscriminant G)
    isotropicRank := Module.finrank (ZMod 7) H
    contains_canonical := canonicalLattice_le_lift G h _
    contained_dual := canonicalLift_le_dual G _
    finitely_generated := canonicalLift_fg G h _
    rank := canonicalLift_finrank G h _
    integral := fun x hx y hy => canonicalLift_integral G h _ hH hx hy
    even := fun x hx => canonicalLift_even G h _ hH hx
    positive := fun x _ hx => codePair_pos x hx
    discriminant_card := by
      simpa using Module.natCard_eq_pow_finrank
        (K := ZMod 7) (V := CanonicalDiscriminant G)
    quotient_finite := canonicalLift_seven_quotient_finite G h H
    index := canonicalLift_seven_index G h H
    lower := hlo
    upper := hhi
  }

theorem canonicalWittLiftData_nonempty (h : G.IsSRGWith 99 14 1 2) :
    Nonempty (CanonicalWittLiftData G) := by
  letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
  obtain ⟨H, hH, hlo, hhi⟩ := canonicalDiscriminant_exists_witt_subspace G h
  exact ⟨canonicalWittLiftOfSubspace G h H hH hlo hhi⟩

/-- Conditional only in the two explicitly stated finite-form consequences of Milgram. -/
theorem canonicalWittLiftData_exact_codim_two (h : G.IsSRGWith 99 14 1 2)
    [Module (ZMod 7) (CanonicalDiscriminant G)]
    (heven : Even (Module.finrank (ZMod 7) (CanonicalDiscriminant G)))
    (hno : ∀ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
      (∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0) →
      2 * Module.finrank (ZMod 7) H ≠ Module.finrank (ZMod 7) (CanonicalDiscriminant G)) :
    ∃ data : CanonicalWittLiftData G, data.exponent = 2 * data.isotropicRank + 2 := by
  obtain ⟨H, hH, he⟩ := canonicalDiscriminant_exists_codim_two_subspace G h heven hno
  have hlo : 2 * Module.finrank (ZMod 7) H ≤ Module.finrank (ZMod 7) (CanonicalDiscriminant G) := by
    omega
  have hhi : Module.finrank (ZMod 7) (CanonicalDiscriminant G) ≤ 2 * Module.finrank (ZMod 7) H + 2 :=
    he.le
  exact ⟨canonicalWittLiftOfSubspace G h H hH hlo hhi, he⟩

theorem canonicalWittLiftData_index_half_exponent (data : CanonicalWittLiftData G)
    (he : data.exponent = 2 * data.isotropicRank + 2) :
    Nat.card (data.lattice ⧸ (canonicalLattice G).comap data.lattice.subtype) =
      7 ^ ((data.exponent - 2) / 2) := by
  rw [data.index]
  congr 1
  omega

theorem canonicalWittLiftData_card_ratio_forty_nine (data : CanonicalWittLiftData G)
    (he : data.exponent = 2 * data.isotropicRank + 2) :
    Nat.card (CanonicalDiscriminant G) =
      49 * Nat.card (data.lattice ⧸ (canonicalLattice G).comap data.lattice.subtype) ^ 2 := by
  rw [data.discriminant_card, data.index, he, pow_add]
  rw [show 2 * data.isotropicRank = data.isotropicRank * 2 from Nat.mul_comm _ _, pow_mul]
  norm_num
  ring

#print axioms canonicalLift_seven_index
#print axioms canonicalDiscriminant_exists_witt_subspace
#print axioms canonicalWittLiftData_nonempty
#print axioms canonicalDiscriminant_exists_codim_two_subspace
#print axioms canonicalWittLiftData_exact_codim_two
#print axioms canonicalWittLiftData_card_ratio_forty_nine

end Conway99
