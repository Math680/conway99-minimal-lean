import LatticeRank
import LatticeQuadratic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-! The rational pairing is nondegenerate and the canonical lattice equals its bidual. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def ambientPairing : LinearMap.BilinForm ℚ (rationalAmbient G) where
  toFun x :=
    { toFun := fun y => codePair (x : V → ℚ) (y : V → ℚ)
      map_add' := fun y z => codePair_add_right _ _ _
      map_smul' := fun a y => codePair_smul_right _ _ _ }
  map_add' x y := by ext z; exact codePair_add_left _ _ _
  map_smul' a x := by ext y; exact codePair_smul_left _ _ _

theorem ambientPairing_symm : (ambientPairing G).IsSymm := by
  exact ⟨fun x y => codePair_symm _ _⟩

theorem ambientPairing_nondegenerate : (ambientPairing G).Nondegenerate := by
  intro x hx
  by_contra hne
  have hv : (x : V → ℚ) ≠ 0 := by
    intro he
    exact hne (Subtype.ext he)
  have hp := codePair_pos (x : V → ℚ) hv
  exact (ne_of_gt hp) (hx x)

theorem canonicalInAmbient_bidual :
    (ambientPairing G).dualSubmodule
      ((ambientPairing G).dualSubmodule (canonicalInAmbient G)) = canonicalInAmbient G := by
  classical
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  let b := Module.Free.chooseBasis ℤ (canonicalInAmbient G)
  let bq := b.extendOfIsLattice ℚ
  have hspan : Submodule.span ℤ (Set.range bq) = canonicalInAmbient G := by
    have hr : Set.range bq = (canonicalInAmbient G).subtype '' Set.range b := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, by simp [bq]⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp [bq]⟩
    rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [← hspan]
  exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _
    (ambientPairing_nondegenerate G) (ambientPairing_symm G) bq

theorem ambient_dual_iff (x : rationalAmbient G) :
    x ∈ (ambientPairing G).dualSubmodule (canonicalInAmbient G) ↔
      IsCanonicalDual G (x : V → ℚ) := by
  constructor
  · intro hx
    refine ⟨x.property, ?_⟩
    intro y hy
    let ya : rationalAmbient G := ⟨y, canonicalLattice_le_ambient G hy⟩
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hx ya hy)
    exact ⟨a, ha.symm⟩
  · intro hx y hy
    obtain ⟨a, ha⟩ := hx.2 y hy
    exact Submodule.mem_one.mpr ⟨a, ha.symm⟩

theorem canonicalLattice_bidual (x : V → ℚ) (hx : x ∈ rationalAmbient G)
    (hp : ∀ y, IsCanonicalDual G y → ∃ a : ℤ, codePair x y = (a : ℚ)) :
    x ∈ canonicalLattice G := by
  let xa : rationalAmbient G := ⟨x, hx⟩
  have hm : xa ∈ (ambientPairing G).dualSubmodule
      ((ambientPairing G).dualSubmodule (canonicalInAmbient G)) := by
    intro y hy
    obtain ⟨a, ha⟩ := hp y ((ambient_dual_iff G y).mp hy)
    exact Submodule.mem_one.mpr ⟨a, ha.symm⟩
  rw [canonicalInAmbient_bidual] at hm
  exact hm

#print axioms canonicalInAmbient_bidual
#print axioms canonicalLattice_bidual

end Conway99
