import LatticeQuadratic
import LatticeRank

/-! Preimages of isotropic subspaces give genuine even integral overlattices. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def canonicalLift (H : Submodule ℤ (CanonicalDiscriminant G)) : Submodule ℤ (V → ℚ) :=
  (H.comap (canonicalInsideDual G).mkQ).map (canonicalDual G).subtype

theorem canonicalLift_le_dual (H : Submodule ℤ (CanonicalDiscriminant G)) :
    canonicalLift G H ≤ canonicalDual G := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

theorem canonicalLift_le_ambient (H : Submodule ℤ (CanonicalDiscriminant G)) :
    canonicalLift G H ≤ (rationalAmbient G).restrictScalars ℤ := by
  intro x hx
  exact (canonicalLift_le_dual G H hx).1

theorem canonicalLattice_le_lift (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) : canonicalLattice G ≤ canonicalLift G H := by
  intro x hx
  let xd : canonicalDual G := ⟨x, canonicalLattice_mem_dual G h hx⟩
  refine ⟨xd, ?_, rfl⟩
  change Submodule.Quotient.mk xd ∈ H
  have hz : (Submodule.Quotient.mk xd : CanonicalDiscriminant G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  rw [hz]
  exact H.zero_mem

theorem canonicalLift_fg (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) : (canonicalLift G H).FG := by
  letI : Module.Finite ℤ (canonicalDual G) := canonicalDual_finiteModule G h
  exact (IsNoetherian.noetherian (H.comap (canonicalInsideDual G).mkQ)).map _

theorem canonicalLift_even (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {x : V → ℚ} (hx : x ∈ canonicalLift G H) :
    ∃ a : ℤ, codePair x x = (2 * a : ℤ) := by
  obtain ⟨xd, hxd, rfl⟩ := hx
  have hz := hH _ hxd
  change (canonicalDualHalfNorm G h xd : ZMod 7) = 0 at hz
  obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hn := canonicalDualHalfNorm_spec G h xd
  rw [ha] at hn
  norm_num at hn
  refine ⟨a, ?_⟩
  change codePair (xd : V → ℚ) (xd : V → ℚ) = ((2 * a : ℤ) : ℚ)
  push_cast
  linarith

theorem canonicalLift_integral (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {x y : V → ℚ} (hx : x ∈ canonicalLift G H) (hy : y ∈ canonicalLift G H) :
    ∃ a : ℤ, codePair x y = (a : ℚ) := by
  obtain ⟨a, ha⟩ := canonicalLift_even G h H hH hx
  obtain ⟨b, hb⟩ := canonicalLift_even G h H hH hy
  obtain ⟨c, hc⟩ := canonicalLift_even G h H hH ((canonicalLift G H).add_mem hx hy)
  have hn := codePair_norm_add x y
  refine ⟨c - a - b, ?_⟩
  push_cast at ha hb hc ⊢
  linarith

def canonicalLiftInAmbient (H : Submodule ℤ (CanonicalDiscriminant G)) :
    Submodule ℤ (rationalAmbient G) :=
  (canonicalLift G H).comap ((rationalAmbient G).restrictScalars ℤ).subtype

theorem canonicalLiftInAmbient_isLattice (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) :
    Submodule.IsLattice ℚ (canonicalLiftInAmbient G H) := by
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  have hle : canonicalInAmbient G ≤ canonicalLiftInAmbient G H :=
    fun _ hx => canonicalLattice_le_lift G h H hx
  let e : canonicalLiftInAmbient G H ≃ₗ[ℤ] canonicalLift G H :=
    Submodule.comapSubtypeEquivOfLe (canonicalLift_le_ambient G H)
  letI : Module.Finite ℤ (canonicalLift G H) :=
    Module.Finite.iff_fg.mpr (canonicalLift_fg G h H)
  letI : Module.Finite ℤ (canonicalLiftInAmbient G H) := Module.Finite.equiv e.symm
  exact Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ hle
    (Module.Finite.iff_fg.mp inferInstance)

theorem canonicalLift_finrank (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) :
    Module.finrank ℤ (canonicalLift G H) = 44 := by
  let e : canonicalLiftInAmbient G H ≃ₗ[ℤ] canonicalLift G H :=
    Submodule.comapSubtypeEquivOfLe (canonicalLift_le_ambient G H)
  letI : Submodule.IsLattice ℚ (canonicalLiftInAmbient G H) :=
    canonicalLiftInAmbient_isLattice G h H
  rw [← e.finrank_eq]
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' ℚ, ← Module.finrank_eq_rank, rationalAmbient_finrank G h]

def canonicalInsideLift (H : Submodule ℤ (CanonicalDiscriminant G)) :
    Submodule ℤ (canonicalLift G H) :=
  (canonicalLattice G).comap (canonicalLift G H).subtype

def canonicalLiftProjection (H : Submodule ℤ (CanonicalDiscriminant G)) :
    canonicalLift G H →ₗ[ℤ] CanonicalDiscriminant G :=
  (canonicalInsideDual G).mkQ.comp (Submodule.inclusion (canonicalLift_le_dual G H))

theorem canonicalLiftProjection_ker (H : Submodule ℤ (CanonicalDiscriminant G)) :
    LinearMap.ker (canonicalLiftProjection G H) = canonicalInsideLift G H := by
  ext x
  change Submodule.Quotient.mk (Submodule.inclusion (canonicalLift_le_dual G H) x) = 0 ↔
    (x : V → ℚ) ∈ canonicalLattice G
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem canonicalLiftProjection_range (H : Submodule ℤ (CanonicalDiscriminant G)) :
    LinearMap.range (canonicalLiftProjection G H) = H := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨xd, hxd, he⟩ := x.property
    have hx : Submodule.inclusion (canonicalLift_le_dual G H) x = xd :=
      Subtype.ext he.symm
    change Submodule.Quotient.mk (Submodule.inclusion (canonicalLift_le_dual G H) x) ∈ H
    rw [hx]
    exact hxd
  · intro hq
    obtain ⟨xd, he⟩ := Submodule.Quotient.mk_surjective (canonicalInsideDual G) q
    have hm : (xd : V → ℚ) ∈ canonicalLift G H := by
      refine ⟨xd, ?_, rfl⟩
      change Submodule.Quotient.mk xd ∈ H
      rw [he]
      exact hq
    exact ⟨⟨xd, hm⟩, he⟩

noncomputable def canonicalLiftQuotientEquiv (H : Submodule ℤ (CanonicalDiscriminant G)) :
    ((canonicalLift G H) ⧸ canonicalInsideLift G H) ≃ₗ[ℤ] H := by
  have e := (canonicalLiftProjection G H).quotKerEquivRange
  rw [canonicalLiftProjection_ker, canonicalLiftProjection_range] at e
  exact e

theorem canonicalLift_index (H : Submodule ℤ (CanonicalDiscriminant G)) :
    Nat.card ((canonicalLift G H) ⧸ canonicalInsideLift G H) = Nat.card H :=
  Nat.card_congr (canonicalLiftQuotientEquiv G H).toEquiv

#print axioms canonicalLift_even
#print axioms canonicalLift_integral
#print axioms canonicalLift_finrank
#print axioms canonicalLiftQuotientEquiv

end Conway99
