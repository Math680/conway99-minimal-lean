import ZeroCasePacking

/-! Complete enumeration input for all three high-weight distributions.
No quotient by sign/permutation symmetry is assumed in this enumeration. -/

namespace Conway99

def fullSignatureList : List RootSignature :=
  rootSignatureList.filter (fun w => signatureWeight w = 4)

theorem mem_fullSignatureList (w : RootSignature) :
    w ∈ fullSignatureList ↔ signatureWeight w = 4 := by
  simp [fullSignatureList, mem_rootSignatureList]

def zeroCaseHighPackings (nfull : ℕ) : Finset (Finset RootSignature) :=
  (FinitePacking.search signatureCells nfull fullSignatureList ∅).biUnion (fun A =>
    (FinitePacking.search signatureCells (7 - 3 * nfull) tripleSignatureList
      (A.biUnion signatureCells)).image (fun B => A ∪ B))

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem zero_case_actual_high_packing_mem (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) :
    F.highSignatures ∈ zeroCaseHighPackings (F.weightCount 4) := by
  let A := F.highSignatures.filter (fun w => signatureWeight w = 4)
  let B := F.highSignatures.filter (fun w => signatureWeight w = 3)
  have ha : A.card = F.weightCount 4 := F.highSignatures_weight_count hc 4 (by omega)
  have hb : B.card = 7 - 3 * F.weightCount 4 := by
    have hcard := F.highSignatures_weight_count hc 3 (by omega)
    norm_num only [Nat.cast_ofNat] at hcard
    have hbal := F.weight_count_balance h
    dsimp only [B]
    omega
  have hp := F.highSignatures_packing hc
  have hma : A ∈ FinitePacking.search signatureCells (F.weightCount 4) fullSignatureList ∅ := by
    apply FinitePacking.search_complete signatureCells fullSignatureList (F.weightCount 4) ∅ A
    · intro w hw
      exact (mem_fullSignatureList w).mpr (Finset.mem_filter.mp hw).2
    · exact ha
    · intro w hw z hz hwz
      exact hp (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hz).1 hwz
    · intro w hw
      exact Finset.disjoint_empty_right _
  have hmb : B ∈ FinitePacking.search signatureCells (7 - 3 * F.weightCount 4)
      tripleSignatureList (A.biUnion signatureCells) := by
    apply FinitePacking.search_complete signatureCells tripleSignatureList
      (7 - 3 * F.weightCount 4) (A.biUnion signatureCells) B
    · intro w hw
      apply (mem_tripleSignatureList w).mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩
    · exact hb
    · intro w hw z hz hwz
      exact hp (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hz).1 hwz
    · intro w hw
      apply (Finset.disjoint_biUnion_right _ _ _).mpr
      intro z hz
      apply hp (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hz).1
      intro heq
      have hw3 := (Finset.mem_filter.mp hw).2
      have hz4 := (Finset.mem_filter.mp hz).2
      rw [heq] at hw3
      omega
  have heq : A ∪ B = F.highSignatures := by
    ext w
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
    · intro hw
      rcases F.highSignatures_weights hw with hw3 | hw4
      · exact Or.inr ⟨hw, hw3⟩
      · exact Or.inl ⟨hw, hw4⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨A, hma, Finset.mem_image.mpr ⟨B, hmb, heq⟩⟩

#print axioms zero_case_actual_high_packing_mem

end Conway99
