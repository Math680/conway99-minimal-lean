import ZeroCaseOrbitCertificate

/-! The graph-level five-orbit classification of the complete high-signature
packing. No neighbour-table feasibility or exclusion is assumed here. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem actual_zero_case_high_packing_data (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0) :
    IsZeroCaseHighPacking F.highSignatures (F.weightCount 4) := by
  refine ⟨fun _ hw => F.highSignatures_weights hw,
    F.highSignatures_weight_count hc 4 (by omega),?_,F.highSignatures_packing hc⟩
  have h3 := F.highSignatures_weight_count hc 3 (by omega)
  norm_num only [Nat.cast_ofNat] at h3
  have hb := F.weight_count_balance h
  omega

theorem zero_case_high_signatures_five_orbits (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0) :
    ∃ g : SignatureSymmetry, ∃ j : Fin 5,
      signatureSetAct g F.highSignatures = zeroCaseOrbitRepresentative j := by
  have hdata := actual_zero_case_high_packing_data F h hc hz
  rcases F.zero_case_high_counts h hz with h0 | h1 | h2
  · have hm := zero_full_actual_packing_mem F h hc hz h0.1
    rw [← packingOrbitTable0_eq_noFull] at hm
    exact packingOrbitTable0_covered hm
  · obtain ⟨g,hplus⟩ := exists_full_normalization hdata (by omega)
    have hm := normalizedHighPackings_complete (hdata.act g) hplus
    rw [h1.1,normalizedHighPackings_one_table] at hm
    obtain ⟨g',j,hj⟩ := packingOrbitTable1_covered hm
    exact ⟨signatureSymmetryComp g' g,j,by rwa [signatureSetAct_comp]⟩
  · obtain ⟨g,hplus⟩ := exists_full_normalization hdata (by omega)
    have hm := normalizedHighPackings_complete (hdata.act g) hplus
    rw [h2.1,normalizedHighPackings_two_table] at hm
    obtain ⟨g',j,hj⟩ := packingOrbitTable2_covered hm
    exact ⟨signatureSymmetryComp g' g,j,by rwa [signatureSetAct_comp]⟩

#print axioms zero_case_high_signatures_five_orbits

end Conway99
