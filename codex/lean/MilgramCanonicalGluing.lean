import MilgramOrthogonalPairing
import MilgramFiniteGluing
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The canonical lattice is an actual isotropic glue subgroup in M*/M.
Its annihilator consists exactly of the images of the true canonical dual. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace Conway99
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (h : G.IsSRGWith 99 14 1 2)
variable (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
variable (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)

def canonicalIntoOrthogonalDual : canonicalInAmbient G →ₗ[ℤ] orthogonalDual G e where
  toFun x := ⟨x.val, by
    intro y hy
    obtain ⟨n,hn⟩ := canonicalLattice_integral G h x.property
      (orthogonalSublattice_le_canonical G e he hy)
    exact Submodule.mem_one.mpr ⟨n,hn.symm⟩⟩
  map_add' x y := rfl
  map_smul' a x := rfl

def canonicalGlueToDiscriminant : canonicalInAmbient G →ₗ[ℤ] OrthogonalDiscriminant G e :=
  (orthogonalInsideOrthogonalDual G e).mkQ.comp (canonicalIntoOrthogonalDual G h e he)

def canonicalGlue : AddSubgroup (OrthogonalDiscriminant G e) :=
  (LinearMap.range (canonicalGlueToDiscriminant G h e he)).toAddSubgroup

theorem canonicalGlue_isotropic : ∀ x ∈ canonicalGlue G h e he,
    orthogonalDiscriminantPhase G h e he x = 1 := by
  rintro _ ⟨x,rfl⟩
  change milgramPhase (codePair ((x : rationalAmbient G) : V → ℚ)
    ((x : rationalAmbient G) : V → ℚ)) = 1
  obtain ⟨n,hn⟩ := canonicalLattice_even G h x.property
  change codePair ((x : rationalAmbient G) : V → ℚ)
    ((x : rationalAmbient G) : V → ℚ) = (2*n : ℤ) at hn
  rw [hn]
  simpa only [Int.cast_mul, Int.cast_ofNat] using milgramPhase_even_int n

def canonicalDualToOrthogonalDiscriminant : canonicalDual G →ₗ[ℤ] OrthogonalDiscriminant G e :=
  (orthogonalInsideOrthogonalDual G e).mkQ.comp (canonicalDualIntoOrthogonalDual G e he)

theorem canonicalGlue_annihilator_eq_range :
    phaseAnnihilator (orthogonalDiscriminantCharacter G h e he) (canonicalGlue G h e he) =
      (LinearMap.range (canonicalDualToOrthogonalDiscriminant G e he)).toAddSubgroup := by
  ext d
  constructor
  · refine Submodule.Quotient.induction_on _ d ?_
    intro x hx
    have hxd : IsCanonicalDual G ((x : rationalAmbient G) : V → ℚ) := by
      refine ⟨(x : rationalAmbient G).property, ?_⟩
      intro y hy
      let ya : canonicalInAmbient G := ⟨⟨y, canonicalLattice_le_ambient G hy⟩,hy⟩
      have hp := hx (canonicalGlueToDiscriminant G h e he ya) ⟨ya,rfl⟩
      change orthogonalDiscriminantPair G h e he
        (Submodule.Quotient.mk (canonicalIntoOrthogonalDual G h e he ya))
        (Submodule.Quotient.mk x) = 1 at hp
      rw [orthogonalDiscriminantPair_mk] at hp
      obtain ⟨n,hn⟩ := (milgramPhase_two_eq_one_iff _).mp hp
      exact ⟨n, (codePair_symm _ _).trans hn⟩
    exact ⟨⟨((x : rationalAmbient G) : V → ℚ), hxd⟩, rfl⟩
  · rintro ⟨x,rfl⟩ y ⟨n,rfl⟩
    change orthogonalDiscriminantPair G h e he
      (Submodule.Quotient.mk (canonicalIntoOrthogonalDual G h e he n))
      (Submodule.Quotient.mk (canonicalDualIntoOrthogonalDual G e he x)) = 1
    rw [orthogonalDiscriminantPair_mk, codePair_symm]
    obtain ⟨a,ha⟩ := x.property.2 ((n : rationalAmbient G) : V → ℚ) n.property
    change milgramPhase (2 * codePair (x : V → ℚ) ((n : rationalAmbient G) : V → ℚ)) = 1
    rw [ha]
    exact milgramPhase_even_int a

theorem canonicalDualToOrthogonalDiscriminant_ker :
    LinearMap.ker (canonicalDualToOrthogonalDiscriminant G e he) = orthogonalInsideDual G e := by
  ext x
  change Submodule.Quotient.mk (canonicalDualIntoOrthogonalDual G e he x) = 0 ↔
    (x : V → ℚ) ∈ orthogonalVectorLattice G e
  rw [Submodule.Quotient.mk_eq_zero]
  change (⟨(x : V → ℚ),x.property.1⟩ : rationalAmbient G) ∈ orthogonalSublattice G e ↔ _
  constructor
  · intro hx
    exact Submodule.mem_map.mpr ⟨⟨x.val,x.property.1⟩,hx,rfl⟩
  · rintro ⟨y,hy,hxy⟩
    have heq : y = (⟨(x : V → ℚ),x.property.1⟩ : rationalAmbient G) := Subtype.ext hxy
    simpa only [heq] using hy

abbrev CanonicalGlueAnnihilator :=
  phaseAnnihilator (orthogonalDiscriminantCharacter G h e he) (canonicalGlue G h e he)

def canonicalOrthogonalRangeEquivAnnihilator :
    LinearMap.range (canonicalDualToOrthogonalDiscriminant G e he) ≃+
      CanonicalGlueAnnihilator G h e he where
  toFun x := ⟨x.val, by
    change x.val ∈ phaseAnnihilator (orthogonalDiscriminantCharacter G h e he) (canonicalGlue G h e he)
    rw [canonicalGlue_annihilator_eq_range]
    exact x.property⟩
  invFun x := ⟨x.val, by
    have hh := x.property
    change x.val ∈ phaseAnnihilator (orthogonalDiscriminantCharacter G h e he) (canonicalGlue G h e he) at hh
    rw [canonicalGlue_annihilator_eq_range] at hh
    exact hh⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def canonicalDualQuotientEquivAnnihilator :
    ((canonicalDual G) ⧸ orthogonalInsideDual G e) ≃+
      CanonicalGlueAnnihilator G h e he :=
  ((Submodule.quotEquivOfEq _ _ (canonicalDualToOrthogonalDiscriminant_ker G e he).symm).trans
    (canonicalDualToOrthogonalDiscriminant G e he).quotKerEquivRange).toAddEquiv.trans
      (canonicalOrthogonalRangeEquivAnnihilator G h e he)

@[simp] theorem canonicalDualQuotientEquivAnnihilator_mk (x : canonicalDual G) :
    ((canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk x) :
      CanonicalGlueAnnihilator G h e he) : OrthogonalDiscriminant G e) =
        canonicalDualToOrthogonalDiscriminant G e he x := rfl

def canonicalAnnihilatorToDiscriminant :
    CanonicalGlueAnnihilator G h e he →+ CanonicalDiscriminant G :=
  (Submodule.mapQ (orthogonalInsideDual G e) (canonicalInsideDual G) LinearMap.id
    (orthogonalInsideDual_le_canonical G e he)).toAddMonoidHom.comp
      (canonicalDualQuotientEquivAnnihilator G h e he).symm.toAddMonoidHom

@[simp] theorem canonicalAnnihilatorToDiscriminant_image (x : canonicalDual G) :
    canonicalAnnihilatorToDiscriminant G h e he
      (canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x := by
  change (Submodule.mapQ (orthogonalInsideDual G e) (canonicalInsideDual G) LinearMap.id
    (orthogonalInsideDual_le_canonical G e he))
    ((canonicalDualQuotientEquivAnnihilator G h e he).symm
      (canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk x))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem canonicalAnnihilatorToDiscriminant_surjective :
    Function.Surjective (canonicalAnnihilatorToDiscriminant G h e he) := by
  intro d
  refine Submodule.Quotient.induction_on _ d ?_
  intro x
  exact ⟨canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk x),
    canonicalAnnihilatorToDiscriminant_image G h e he x⟩

theorem canonicalDual_image_mem_glue_iff (x : canonicalDual G) :
    canonicalDualToOrthogonalDiscriminant G e he x ∈ canonicalGlue G h e he ↔
      x ∈ canonicalInsideDual G := by
  constructor
  · rintro ⟨n,hn⟩
    let nd : canonicalDual G := ⟨((n : rationalAmbient G) : V → ℚ),
      canonicalLattice_mem_dual G h n.property⟩
    have hnd : canonicalDualToOrthogonalDiscriminant G e he nd =
        canonicalGlueToDiscriminant G h e he n := rfl
    have hdiff : x-nd ∈ LinearMap.ker (canonicalDualToOrthogonalDiscriminant G e he) := by
      change canonicalDualToOrthogonalDiscriminant G e he (x-nd) = 0
      rw [map_sub, hnd, hn, sub_self]
    rw [canonicalDualToOrthogonalDiscriminant_ker] at hdiff
    have hm := orthogonalInsideDual_le_canonical G e he hdiff
    have hn' : nd ∈ canonicalInsideDual G := n.property
    simpa using (canonicalInsideDual G).add_mem hm hn'
  · intro hx
    exact ⟨⟨⟨x.val,x.property.1⟩,hx⟩,rfl⟩

theorem canonicalAnnihilatorToDiscriminant_ker :
    (canonicalAnnihilatorToDiscriminant G h e he).ker =
      (canonicalGlue G h e he).addSubgroupOf (CanonicalGlueAnnihilator G h e he) := by
  ext p
  obtain ⟨q,rfl⟩ := (canonicalDualQuotientEquivAnnihilator G h e he).surjective p
  refine Submodule.Quotient.induction_on _ q ?_
  intro x
  change canonicalAnnihilatorToDiscriminant G h e he
    (canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk x)) = 0 ↔ _
  rw [canonicalAnnihilatorToDiscriminant_image, Submodule.Quotient.mk_eq_zero]
  change x ∈ canonicalInsideDual G ↔
    ((canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk x) :
      CanonicalGlueAnnihilator G h e he) : OrthogonalDiscriminant G e) ∈ canonicalGlue G h e he
  rw [canonicalDualQuotientEquivAnnihilator_mk, canonicalDual_image_mem_glue_iff]

def canonicalGluedDiscriminantEquiv :
    ((CanonicalGlueAnnihilator G h e he) ⧸
      (canonicalGlue G h e he).addSubgroupOf (CanonicalGlueAnnihilator G h e he)) ≃+
        CanonicalDiscriminant G :=
  (QuotientAddGroup.quotientAddEquivOfEq (canonicalAnnihilatorToDiscriminant_ker G h e he).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (canonicalAnnihilatorToDiscriminant G h e he)
      (canonicalAnnihilatorToDiscriminant_surjective G h e he))

@[simp] theorem canonicalGluedDiscriminantEquiv_mk (p : CanonicalGlueAnnihilator G h e he) :
    canonicalGluedDiscriminantEquiv G h e he (QuotientAddGroup.mk p) =
      canonicalAnnihilatorToDiscriminant G h e he p := rfl

theorem canonicalGluedDiscriminantEquiv_phase [Fintype (OrthogonalDiscriminant G e)] :
    ∀ x, gluedPhase (orthogonalDiscriminantPhase G h e he)
      (orthogonalDiscriminantCharacter G h e he) (canonicalGlue G h e he)
      (orthogonalDiscriminantPhase_quadratic G h e he)
      (orthogonalDiscriminantPair_symmetric G h e he)
      (canonicalGlue_isotropic G h e he) x =
      canonicalDiscriminantPhase G h (canonicalGluedDiscriminantEquiv G h e he x) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro p
  rw [canonicalGluedDiscriminantEquiv_mk]
  obtain ⟨q,rfl⟩ := (canonicalDualQuotientEquivAnnihilator G h e he).surjective p
  refine Submodule.Quotient.induction_on _ q ?_
  intro y
  rw [canonicalAnnihilatorToDiscriminant_image]
  change orthogonalDiscriminantPhase G h e he
    ((canonicalDualQuotientEquivAnnihilator G h e he (Submodule.Quotient.mk y) :
      CanonicalGlueAnnihilator G h e he) : OrthogonalDiscriminant G e) = _
  rw [canonicalDualQuotientEquivAnnihilator_mk]
  rfl

theorem canonicalDiscriminant_normalized_gauss_eq_orthogonal
    [Fintype (OrthogonalDiscriminant G e)] [Fintype (CanonicalDiscriminant G)] :
    (∑ x : CanonicalDiscriminant G, canonicalDiscriminantPhase G h x) /
      (Real.sqrt (Fintype.card (CanonicalDiscriminant G)) : ℂ) =
    (∑ x : OrthogonalDiscriminant G e, orthogonalDiscriminantPhase G h e he x) /
      (Real.sqrt (Fintype.card (OrthogonalDiscriminant G e)) : ℂ) := by
  classical
  let B := ((CanonicalGlueAnnihilator G h e he) ⧸
      (canonicalGlue G h e he).addSubgroupOf (CanonicalGlueAnnihilator G h e he))
  let eqv := canonicalGluedDiscriminantEquiv G h e he
  letI : Fintype B := Fintype.ofEquiv (CanonicalDiscriminant G) eqv.symm.toEquiv
  have hg := quadratic_phase_gluing_normalized
    (orthogonalDiscriminantPhase G h e he) (orthogonalDiscriminantCharacter G h e he)
    (canonicalGlue G h e he) (orthogonalDiscriminantPhase_quadratic G h e he)
    (orthogonalDiscriminantPair_symmetric G h e he) (canonicalGlue_isotropic G h e he)
    (orthogonalDiscriminantCharacter_nondegenerate G h e he)
  have hs : (∑ x : B, gluedPhase (orthogonalDiscriminantPhase G h e he)
      (orthogonalDiscriminantCharacter G h e he) (canonicalGlue G h e he)
      (orthogonalDiscriminantPhase_quadratic G h e he)
      (orthogonalDiscriminantPair_symmetric G h e he) (canonicalGlue_isotropic G h e he) x) =
      ∑ x : CanonicalDiscriminant G, canonicalDiscriminantPhase G h x := by
    simp_rw [canonicalGluedDiscriminantEquiv_phase]
    exact eqv.toEquiv.sum_comp _
  have hc : Fintype.card B = Fintype.card (CanonicalDiscriminant G) := Fintype.card_congr eqv.toEquiv
  rw [hs, hc] at hg
  exact hg.symm

#print axioms canonicalGlue_isotropic
#print axioms canonicalGlue_annihilator_eq_range
#print axioms canonicalDualToOrthogonalDiscriminant_ker
#print axioms canonicalAnnihilatorToDiscriminant_ker
#print axioms canonicalGluedDiscriminantEquiv_phase
#print axioms canonicalDiscriminant_normalized_gauss_eq_orthogonal
end Conway99
