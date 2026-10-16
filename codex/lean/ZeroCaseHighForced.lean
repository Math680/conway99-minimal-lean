import ZeroCaseHighComplete

/-! The three surviving high arrays as exact function equalities. -/

namespace Conway99.ZeroHighRows

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def functionTrace (j : Fin 5) (f : High j → Finset (Core j)) : List (High j × Finset (Core j)) :=
  ((List.finRange (zeroCaseHighCount j)).map (fun i => (i,f i))).reverse

theorem encode_functionTrace_injective (j : Fin 5) :
    Function.Injective (fun f : High j → Finset (Core j) => encodeRows (functionTrace j f)) := by
  intro f g heq
  change encodeRows (functionTrace j f) = encodeRows (functionTrace j g) at heq
  funext i
  have hi : (i.val,(f i).image Fin.val) ∈ encodeRows (functionTrace j f) := by
    simp only [encodeRows,functionTrace,List.map_reverse,List.map_map,List.mem_reverse,List.mem_map]
    exact ⟨i,List.mem_finRange i,rfl⟩
  rw [heq] at hi
  simp only [encodeRows,functionTrace,List.map_reverse,List.map_map,List.mem_reverse,List.mem_map] at hi
  obtain ⟨k,_,hk⟩ := hi
  have hki : k = i := Fin.ext (congrArg Prod.fst hk)
  subst k
  have himg := congrArg Prod.snd hk
  exact (Finset.image_injective Fin.val_injective) himg.symm

def orbitOneNeighbors : High 1 → Finset (Core 1) :=
  (show Fin 5 → Finset (Fin 11) from ![{4},{6,9,10},{7,8,9},{5,7,10},{0}])
def orbitThreeNeighbors : High 3 → Finset (Core 3) :=
  (show Fin 5 → Finset (Fin 11) from ![{2,7},{3,10},{0,8},{1,5},{6,9}])
def orbitFourNeighbors : High 4 → Finset (Core 4) :=
  (show Fin 3 → Finset (Fin 12) from ![{6,10},{4,5,8},{9,11}])

def orbitOneCounts : High 1 → Fin 8 → ℤ :=
  ![![0,3,0,3,0,3,1,0],![0,3,0,1,2,0,0,2],![0,1,2,0,0,3,0,2],
    ![2,0,0,3,0,1,0,2],![3,0,3,0,3,0,4,0]]
def orbitThreeCounts : High 3 → Fin 8 → ℤ :=
  ![![0,3,0,3,0,1,2,0],![0,3,0,1,2,0,0,3],![0,1,2,0,0,3,0,3],
    ![2,0,0,3,0,3,0,1],![3,0,3,0,3,0,3,0]]
def orbitFourCounts : High 4 → Fin 8 → ℤ :=
  ![![0,3,0,3,0,4,2,0],![0,2,0,0,2,0,0,4],![4,0,3,0,3,0,2,0]]

private theorem expected_one : expectedSolutionCodes 1 = {encodeRows (functionTrace 1 orbitOneNeighbors)} := by decide
private theorem expected_three : expectedSolutionCodes 3 = {encodeRows (functionTrace 3 orbitThreeNeighbors)} := by decide
private theorem expected_four : expectedSolutionCodes 4 = {encodeRows (functionTrace 4 orbitFourNeighbors)} := by decide

theorem high_configuration_one_neighbors (C : HighConfiguration 1) : C.neighbors = orbitOneNeighbors := by
  apply encode_functionTrace_injective 1
  have hh := high_configuration_trace_certificate C
  rw [expected_one,Finset.mem_singleton] at hh
  exact hh

theorem high_configuration_three_neighbors (C : HighConfiguration 3) : C.neighbors = orbitThreeNeighbors := by
  apply encode_functionTrace_injective 3
  have hh := high_configuration_trace_certificate C
  rw [expected_three,Finset.mem_singleton] at hh
  exact hh

theorem high_configuration_four_neighbors (C : HighConfiguration 4) : C.neighbors = orbitFourNeighbors := by
  apply encode_functionTrace_injective 4
  have hh := high_configuration_trace_certificate C
  rw [expected_four,Finset.mem_singleton] at hh
  exact hh

private theorem counts_one : ∀ i, candidateCounts 1 i (orbitOneNeighbors i) = orbitOneCounts i := by decide
private theorem counts_three : ∀ i, candidateCounts 3 i (orbitThreeNeighbors i) = orbitThreeCounts i := by decide
private theorem counts_four : ∀ i, candidateCounts 4 i (orbitFourNeighbors i) = orbitFourCounts i := by decide

theorem high_configuration_one_counts (C : HighConfiguration 1) : C.counts = orbitOneCounts := by
  funext i
  rw [high_counts_reconstruction 1 i _ _ (C.rows i),high_configuration_one_neighbors C,counts_one i]

theorem high_configuration_three_counts (C : HighConfiguration 3) : C.counts = orbitThreeCounts := by
  funext i
  rw [high_counts_reconstruction 3 i _ _ (C.rows i),high_configuration_three_neighbors C,counts_three i]

theorem high_configuration_four_counts (C : HighConfiguration 4) : C.counts = orbitFourCounts := by
  funext i
  rw [high_counts_reconstruction 4 i _ _ (C.rows i),high_configuration_four_neighbors C,counts_four i]

#print axioms high_configuration_one_neighbors
#print axioms high_configuration_three_counts
#print axioms high_configuration_four_counts

end Conway99.ZeroHighRows
