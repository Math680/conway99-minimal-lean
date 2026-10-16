import ZeroCaseActualHighConfiguration
import ZeroCaseTripleCertificate

/-! Actual positive singleton classes and their common-neighbour budgets.
The budgets subtract actual core common neighbours, not a relaxed oracle. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

def positiveSingleClasses (k : Fin 4) : Finset V := F.singleClass (k,true)
def positiveSingleUnion : Finset V := Finset.univ.biUnion F.positiveSingleClasses

theorem positiveSingle_disjoint : Pairwise (fun i k => Disjoint (F.positiveSingleClasses i) (F.positiveSingleClasses k)) := by
  intro i k hik
  exact F.singleClass_pairwise_disjoint (fun he => hik (congrArg Prod.fst he))

theorem positiveSingleUnion_subset : F.positiveSingleUnion ⊆ F.singleUnion := by
  intro u hu
  obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hu
  exact Finset.mem_biUnion.mpr ⟨(k,true),Finset.mem_univ _,hk⟩

def firstFourHigh (_F : FourDirectionSystem G) (j : Fin 5) (h4 : 4 ≤ zeroCaseHighCount j) (i : Fin 4) : ZeroHighRows.High j :=
  ⟨i.val,lt_of_lt_of_le i.isLt h4⟩

noncomputable def tripleNeighborhood (hc : F.HasSignedCells) (j : Fin 5)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative j) (h4 : 4 ≤ zeroCaseHighCount j)
    (i : Fin 4) : Finset V :=
  Finset.univ.filter (G.Adj ((F.coreSignatureData_of_representative hc j hrep).point
    (zeroCaseHighIndex j (F.firstFourHigh j h4 i))))

theorem triple_margins_count (hc : F.HasSignedCells) (j : Fin 5)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative j) (h4 : 4 ≤ zeroCaseHighCount j)
    (k i : Fin 4) :
    ((F.positiveSingleClasses k ∩ F.tripleNeighborhood hc j hrep h4 i).card : ℤ) =
      F.actualHighCounts hc j hrep (F.firstFourHigh j h4 i) (ZeroHighRows.plus k) := by
  rw [actualHighCounts,ZeroHighRows.group_plus]
  unfold CoreSignatureData.rowCount singleNeighborCount
  congr 2
  ext u
  simp [positiveSingleClasses,tripleNeighborhood,and_comm]

theorem triple_common_budget (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (j : Fin 5) (hrep : F.highSignatures = zeroCaseOrbitRepresentative j)
    (h4 : 4 ≤ zeroCaseHighCount j) (i k : Fin 4) (hik : i ≠ k) :
    (F.actualHighNeighbors hc j hrep (F.firstFourHigh j h4 i) ∩
      F.actualHighNeighbors hc j hrep (F.firstFourHigh j h4 k)).card +
      (F.positiveSingleUnion ∩ F.tripleNeighborhood hc j hrep h4 i ∩
        F.tripleNeighborhood hc j hrep h4 k).card ≤
      if zeroCaseHighIndex j (F.firstFourHigh j h4 k) ∈
        F.actualHighNeighbors hc j hrep (F.firstFourHigh j h4 i) then 1 else 2 := by
  let D := F.coreSignatureData_of_representative hc j hrep
  let a := zeroCaseHighIndex j (F.firstFourHigh j h4 i)
  let b := zeroCaseHighIndex j (F.firstFourHigh j h4 k)
  have hab : a ≠ b := by
    intro he
    apply hik
    exact Fin.ext (congrArg (fun r : Fin (zeroCaseCoreCount j) => r.val) he)
  let C := F.coreVertices.filter (fun u => G.Adj (D.point a) u ∧ G.Adj (D.point b) u)
  let B := F.positiveSingleUnion ∩ F.tripleNeighborhood hc j hrep h4 i ∩
    F.tripleNeighborhood hc j hrep h4 k
  have hdis : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have huC := (Finset.mem_filter.mp hu).1
    have hvP := (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1
    exact Finset.disjoint_left.mp F.core_single_disjoint huC (F.positiveSingleUnion_subset hvP)
  have hsub : C ∪ B ⊆ (G.commonNeighbors (D.point a) (D.point b)).toFinset := by
    intro u hu
    apply Set.mem_toFinset.mpr
    rcases Finset.mem_union.mp hu with hu | hu
    · exact (Finset.mem_filter.mp hu).2
    · have h1 := (Finset.mem_filter.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hu).1).2).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2
      exact ⟨h1,h2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,Set.toFinset_card] at hcard
  have hcn := D.row_common_card hc a b
  change (D.rowNeighbors a ∩ D.rowNeighbors b).card = C.card at hcn
  rw [← hcn] at hcard
  change (D.rowNeighbors a ∩ D.rowNeighbors b).card + B.card ≤
    if b ∈ D.rowNeighbors a then 1 else 2
  by_cases ha : G.Adj (D.point a) (D.point b)
  · rw [h.of_adj _ _ ha] at hcard
    simpa only [CoreSignatureData.rowNeighbors,Finset.mem_filter,Finset.mem_univ,true_and,if_pos ha] using hcard
  · rw [h.of_not_adj (D.point_injective.ne hab) ha] at hcard
    simpa only [CoreSignatureData.rowNeighbors,Finset.mem_filter,Finset.mem_univ,true_and,if_neg ha] using hcard

#print axioms triple_common_budget

end FourDirectionSystem
end Conway99
