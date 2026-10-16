import ZeroCaseHighCertificate

/-! Algebraic elimination of high-row counts and completeness of the
kernel-checked search for an arbitrary HighConfiguration. -/

namespace Conway99.ZeroHighRows

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 32000000

theorem high_counts_reconstruction (j : Fin 5) (i : High j)
    (ns : Finset (Core j)) (c : Fin 8 → ℤ) (h : HighRowOK j i ns c) :
    c = candidateCounts j i ns := by
  have ha := h.2.2.1
  have hd := h.2.2.2.1
  have hp := h.2.2.2.2
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hct : c = ![c 0,c 1,c 2,c 3,c 4,c 5,c 6,c 7] := by
    funext g
    fin_cases g <;> rfl
  have hpt : coreMoment j ns = ![coreMoment j ns 0,coreMoment j ns 1,
      coreMoment j ns 2,coreMoment j ns 3] := by
    funext k
    fin_cases k <;> rfl
  have hst : highSign j i = ![highSign j i 0,highSign j i 1,highSign j i 2,highSign j i 3] := by
    funext k
    fin_cases k <;> rfl
  funext g
  unfold candidateCounts remainingDegree activeCounts zeroCoord
  rw [hct] at ha0 ha1 ha2 ha3 hp0 hp1 hp2 hp3 hd ⊢
  rw [hpt] at hp0 hp1 hp2 hp3 ⊢
  rw [hst] at ha0 ha1 ha2 ha3 hp0 hp1 hp2 hp3 ⊢
  simp only [Fin.sum_univ_succ] at hd
  clear h ha hp hct hpt hst
  fin_cases j <;> fin_cases i
  all_goals
    norm_num [highSign, zeroCaseHighWord, zeroCaseHighCodes, decodeRootSignature,
      zeroCoord, minus, plus, groupCoord, groupSign, Fin.sum_univ_succ,
      Fin.mk.injEq, Fin.reduceFinMk] at ha0 ha1 ha2 ha3 hp0 hp1 hp2 hp3 hd ⊢
  all_goals
    try dsimp only [Fin.succ,Fin.castSucc,Matrix.vecCons,Fin.cons,Fin.induction,Fin.cases,Fin.ofNat] at *
    try norm_num [Fin.ext_iff,Fin.isValue] at *
    try simp [Fin.induction.go] at *
  all_goals
    fin_cases g
  all_goals
    (try norm_num [highSign, zeroCaseHighWord, zeroCaseHighCodes, decodeRootSignature,
      zeroCoord, minus, plus, groupCoord, groupSign, Fin.sum_univ_succ,
      Fin.mk.injEq, Fin.reduceFinMk]) <;>
      (try dsimp only [Fin.succ,Fin.castSucc,Matrix.vecCons,Fin.cons,Fin.induction,Fin.cases,Fin.ofNat]) <;>
      (try norm_num [Fin.ext_iff,Fin.isValue]) <;>
      (try simp [Fin.induction.go]) <;> omega

theorem high_row_complete (j : Fin 5) (i : High j)
    (ns : Finset (Core j)) (c : Fin 8 → ℤ) (h : HighRowOK j i ns c) : ns ∈ rowOptions j i := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr h.1,?_⟩
  rw [← high_counts_reconstruction j i ns c h]
  exact h

def configurationTrace {j : Fin 5} (C : HighConfiguration j) : List (High j × Finset (Core j)) :=
  ((List.finRange (zeroCaseHighCount j)).map (fun i => (i,C.neighbors i))).reverse

theorem high_configuration_search_complete {j : Fin 5} (C : HighConfiguration j) :
    configurationTrace C ∈ highSolutions j := by
  have hrows (i : High j) : C.neighbors i ∈ rowOptions j i :=
    high_row_complete j i (C.neighbors i) (C.counts i) (C.rows i)
  have hpairs (i k : High j) : compatible j i (C.neighbors i) k (C.neighbors k) := by
    by_cases he : i = k
    · exact Or.inl he
    · apply Or.inr
      have hi := high_counts_reconstruction j i _ _ (C.rows i)
      have hk := high_counts_reconstruction j k _ _ (C.rows k)
      rw [← hi,← hk]
      exact C.pairs i k he
  simpa only [configurationTrace,highSolutions,List.append_nil] using
    FiniteRowSearch.search_complete (rowOptions j) (compatible j) C.neighbors hrows hpairs
      (List.finRange (zeroCaseHighCount j)) [] (by simp)

theorem high_configuration_trace_certificate {j : Fin 5} (C : HighConfiguration j) :
    encodeRows (configurationTrace C) ∈ expectedSolutionCodes j := by
  rw [← high_array_certificate j]
  exact Finset.mem_image.mpr ⟨configurationTrace C,high_configuration_search_complete C,rfl⟩

theorem high_configuration_orbit_zero_impossible (C : HighConfiguration 0) : False := by
  have hh := high_configuration_trace_certificate C
  change _ ∈ (∅ : Finset (List (ℕ × Finset ℕ))) at hh
  exact Finset.notMem_empty _ hh

theorem high_configuration_orbit_two_impossible (C : HighConfiguration 2) : False := by
  have hh := high_configuration_trace_certificate C
  change _ ∈ (∅ : Finset (List (ℕ × Finset ℕ))) at hh
  exact Finset.notMem_empty _ hh

#print axioms high_counts_reconstruction
#print axioms high_configuration_search_complete
#print axioms high_configuration_orbit_zero_impossible
#print axioms high_configuration_orbit_two_impossible

end Conway99.ZeroHighRows
