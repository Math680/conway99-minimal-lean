import ZeroCaseRowEquations

/-! The sizes of the eight simple classes are determined by actual core signatures. -/

namespace Conway99
namespace FourDirectionSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

def coreSignatures : Finset RootSignature := F.coreVertices.image F.signature

theorem signed_support_core_simple (a : Fin 4 × Bool) :
    signedCodeSupport (F.code a.1) a.2 =
      (F.coreVertices ∩ signedCodeSupport (F.code a.1) a.2) ∪ F.singleClass a := by
  ext u
  constructor
  · intro hu
    have hC : u ∈ rootSupport (F.code a.1) := signedCodeSupport_subset _ _ hu
    have hW := F.support_subset_W a.1 hC
    have hw0 : F.weight u ≠ 0 := by
      intro hw
      exact (F.weight_zero_iff u).mp hw a.1 hC
    have hlo := F.weight_nonneg u
    by_cases hw1 : F.weight u = 1
    · exact Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hW, hw1⟩, hu⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hW, by omega⟩, hu⟩)
  · intro hu
    rcases Finset.mem_union.mp hu with hc | hs
    · exact (Finset.mem_inter.mp hc).2
    · exact (Finset.mem_inter.mp hs).2

theorem singleClass_card_from_core (a : Fin 4 × Bool) :
    (F.singleClass a).card =
      7 - (F.coreVertices ∩ signedCodeSupport (F.code a.1) a.2).card := by
  have hd : Disjoint (F.coreVertices ∩ signedCodeSupport (F.code a.1) a.2)
      (F.singleClass a) := by
    apply Finset.disjoint_left.mpr
    intro u hcore hsingle
    have hw2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hcore).1).2
    have hw1 := (F.singleClass_mem hsingle).2.1
    omega
  have hs : (signedCodeSupport (F.code a.1) a.2).card = 7 := by
    cases hb : a.2
    · simpa [signedCodeSupport, hb] using (F.biplane a.1).negative_card
    · simpa [signedCodeSupport, hb] using (F.biplane a.1).positive_card
  rw [F.signed_support_core_simple a, Finset.card_union_of_disjoint hd] at hs
  omega

theorem coreSignatures_injective (hc : F.HasSignedCells) :
    Set.InjOn F.signature F.coreVertices := by
  intro u hu v hv heq
  exact F.signature_injective_on_heavy hc
    (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 heq

theorem coreSignatures_card (hc : F.HasSignedCells) :
    F.coreSignatures.card = F.coreVertices.card :=
  Finset.card_image_of_injOn (F.coreSignatures_injective hc)

theorem core_signed_coordinate_count (hc : F.HasSignedCells) (a : Fin 4 × Bool) :
    (F.coreSignatures.filter (fun w => w a.1 = if a.2 then 2 else 0)).card =
      (F.coreVertices ∩ signedCodeSupport (F.code a.1) a.2).card := by
  have htest (u : V) :
      F.signature u a.1 = (if a.2 then 2 else 0) ↔
        u ∈ signedCodeSupport (F.code a.1) a.2 := by
    rw [signedCodeSupport_mem]
    have hs := F.signature_val u a.1
    cases hb : a.2
    · simp only [hb, Bool.false_eq_true, ite_false]
      constructor
      · intro he
        have hh := congrArg Fin.val he
        norm_num at hh
        omega
      · intro he
        apply Fin.ext
        change (F.signature u a.1).val = 0
        omega
    · simp only [hb, ite_true]
      constructor
      · intro he
        have hh := congrArg Fin.val he
        norm_num at hh
        omega
      · intro he
        apply Fin.ext
        change (F.signature u a.1).val = 2
        omega
  have heq : F.coreSignatures.filter (fun w => w a.1 = if a.2 then 2 else 0) =
      (F.coreVertices ∩ signedCodeSupport (F.code a.1) a.2).image F.signature := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw, hs⟩ := Finset.mem_filter.mp hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, (htest u).mp hs⟩, rfl⟩
    · intro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨u, (Finset.mem_inter.mp hu).1, rfl⟩,
        (htest u).mpr (Finset.mem_inter.mp hu).2⟩
  rw [heq]
  apply Finset.card_image_of_injOn
  intro u hu v hv he
  exact F.coreSignatures_injective hc (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1 he

theorem singleClass_card_from_signatures (hc : F.HasSignedCells) (a : Fin 4 × Bool) :
    (F.singleClass a).card =
      7 - (F.coreSignatures.filter (fun w => w a.1 = if a.2 then 2 else 0)).card := by
  rw [F.core_signed_coordinate_count hc, F.singleClass_card_from_core]

#print axioms singleClass_card_from_signatures

end FourDirectionSystem
end Conway99
