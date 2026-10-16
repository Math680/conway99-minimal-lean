import ZeroCaseOrbitData
import ZeroCaseNormalizedPacking

/-! Small kernel-checked certificates for the five-orbit classification.
The previously proved 64-packing cardinality is reused, not recomputed. -/

namespace Conway99

set_option maxRecDepth 100000
set_option maxHeartbeats 32000000

theorem packingOrbitTable0_card : packingOrbitTable0.card = 64 := by decide +kernel

theorem packingOrbitRows0_valid : ∀ r ∈ packingOrbitRows0,
    r.packing.card = 7 ∧ (∀ w ∈ r.packing, signatureWeight w = 3) ∧
      (∀ w ∈ r.packing, ∀ z ∈ r.packing, w ≠ z → (matchingSignatureCoords w z).card ≤ 1) := by
  decide +kernel

theorem packingOrbitRows0_correct : ∀ r ∈ packingOrbitRows0,
    signatureSetAct r.symmetry r.packing = zeroCaseOrbitRepresentative r.representative := by
  decide +kernel

theorem packingOrbitRows1_correct : ∀ r ∈ packingOrbitRows1,
    signatureSetAct r.symmetry r.packing = zeroCaseOrbitRepresentative r.representative := by
  decide +kernel

theorem packingOrbitRows2_correct : ∀ r ∈ packingOrbitRows2,
    signatureSetAct r.symmetry r.packing = zeroCaseOrbitRepresentative r.representative := by
  decide +kernel

theorem normalizedHighPackings_one_table : normalizedHighPackings 1 = packingOrbitTable1 := by
  decide +kernel

theorem normalizedHighPackings_two_table : normalizedHighPackings 2 = packingOrbitTable2 := by
  decide +kernel

theorem packingOrbitTable0_eq_noFull : packingOrbitTable0 = noFullHighPackings := by
  apply Finset.eq_of_subset_of_card_le
  · intro S hS
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
    have hv := packingOrbitRows0_valid r hr
    apply FinitePacking.search_complete signatureCells tripleSignatureList 7 ∅ r.packing
    · intro w hw
      apply (mem_tripleSignatureList w).mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv.2.1 w hw⟩
    · exact hv.1
    · intro w hw z hz hwz
      exact (signatureCells_disjoint_iff w z).mpr (hv.2.2 w hw z hz hwz)
    · intro w _
      exact Finset.disjoint_empty_right _
  · rw [packingOrbitTable0_card,noFullHighPackings_card]

theorem packingOrbitTable0_covered {S : Finset RootSignature} (hS : S ∈ packingOrbitTable0) :
    ∃ g : SignatureSymmetry, ∃ j : Fin 5,
      signatureSetAct g S = zeroCaseOrbitRepresentative j := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
  exact ⟨r.symmetry,r.representative,packingOrbitRows0_correct r hr⟩

theorem packingOrbitTable1_covered {S : Finset RootSignature} (hS : S ∈ packingOrbitTable1) :
    ∃ g : SignatureSymmetry, ∃ j : Fin 5,
      signatureSetAct g S = zeroCaseOrbitRepresentative j := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
  exact ⟨r.symmetry,r.representative,packingOrbitRows1_correct r hr⟩

theorem packingOrbitTable2_covered {S : Finset RootSignature} (hS : S ∈ packingOrbitTable2) :
    ∃ g : SignatureSymmetry, ∃ j : Fin 5,
      signatureSetAct g S = zeroCaseOrbitRepresentative j := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
  exact ⟨r.symmetry,r.representative,packingOrbitRows2_correct r hr⟩

#print axioms packingOrbitTable0_eq_noFull
#print axioms normalizedHighPackings_one_table
#print axioms normalizedHighPackings_two_table

end Conway99
