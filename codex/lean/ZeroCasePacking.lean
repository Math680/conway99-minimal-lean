import FinitePackingSearch

/-! First exhaustive stage of the no-zero-signature case.
Search completeness is linked to the actual graph. Further neighbour
constraints are required before this can exclude that case. -/

namespace Conway99

def rootSignatureList : List RootSignature :=
  (List.finRange 3).flatMap (fun a =>
    (List.finRange 3).flatMap (fun b =>
      (List.finRange 3).flatMap (fun c =>
        (List.finRange 3).map (fun d => ![a,b,c,d]))))

theorem mem_rootSignatureList (w : RootSignature) : w ∈ rootSignatureList := by
  simp only [rootSignatureList, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  refine ⟨w 0, w 1, w 2, w 3, ?_⟩
  ext i
  fin_cases i <;> rfl

def tripleSignatureList : List RootSignature :=
  rootSignatureList.filter (fun w => signatureWeight w = 3)

theorem mem_tripleSignatureList (w : RootSignature) :
    w ∈ tripleSignatureList ↔ w ∈ tripleSignatures := by
  simp [tripleSignatureList, mem_rootSignatureList, tripleSignatures]

def noFullHighPackings : Finset (Finset RootSignature) :=
  FinitePacking.search signatureCells 7 tripleSignatureList ∅

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem zero_full_actual_packing_mem (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) (hf : F.weightCount 4 = 0) :
    F.highSignatures ∈ noFullHighPackings := by
  obtain ⟨hcard, hsub⟩ := F.zero_full_highSignatures_triples h hc hz hf
  apply FinitePacking.search_complete signatureCells tripleSignatureList 7 ∅ F.highSignatures
  · intro w hw
    exact (mem_tripleSignatureList w).mpr (hsub hw)
  · exact hcard
  · exact F.highSignatures_packing hc
  · intro w hw
    exact Finset.disjoint_empty_right _

#print axioms zero_full_actual_packing_mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem noFullHighPackings_card : noFullHighPackings.card = 64 := by decide +kernel

#print axioms noFullHighPackings_card

end Conway99
