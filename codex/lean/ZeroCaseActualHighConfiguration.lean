import ZeroCaseHighRows
import CoreSignatureRows

/-! Actual normalized four-direction systems realize every equation and
common-neighbour condition of the finite HighConfiguration model. -/

namespace Conway99

open scoped BigOperators

namespace ZeroHighRows

def groupEquiv : Fin 8 ≃ (Fin 4 × Bool) where
  toFun := group
  invFun := zeroCaseGroupIndex
  left_inv := by decide
  right_inv := by decide

theorem group_minus (k : Fin 4) : group (minus k) = (k,false) := by revert k; decide
theorem group_plus (k : Fin 4) : group (plus k) = (k,true) := by revert k; decide
theorem group_index (g : Fin 8) : zeroCaseGroupIndex (group g) = g := groupEquiv.left_inv g

theorem simple_moment_collapse (c : Fin 4 × Bool → ℤ) (k : Fin 4) :
    (∑ a : Fin 4 × Bool, c a * (if k = a.1 then (if a.2 then 1 else -1) else 0)) =
      c (k,true) - c (k,false) := by
  fin_cases k <;>
    simp [Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ] <;> ring

end ZeroHighRows

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G) (hc : F.HasSignedCells) (j : Fin 5)
variable (hrep : F.highSignatures = zeroCaseOrbitRepresentative j)

noncomputable def actualHighNeighbors (i : ZeroHighRows.High j) : Finset (ZeroHighRows.Core j) :=
  (F.coreSignatureData_of_representative hc j hrep).rowNeighbors (zeroCaseHighIndex j i)

noncomputable def actualHighCounts (i : ZeroHighRows.High j) (g : Fin 8) : ℤ :=
  (F.coreSignatureData_of_representative hc j hrep).rowCount (zeroCaseHighIndex j i) (ZeroHighRows.group g)

theorem actualCore_rowCode (r : ZeroHighRows.Core j) (k : Fin 4) :
    (F.coreSignatureData_of_representative hc j hrep).rowCode r k = ZeroHighRows.coreSign j r k := rfl

theorem actualHigh_rowCode (i : ZeroHighRows.High j) (k : Fin 4) :
    (F.coreSignatureData_of_representative hc j hrep).rowCode (zeroCaseHighIndex j i) k =
      ZeroHighRows.highSign j i k := by
  change (((zeroCaseCoreWord j (zeroCaseHighIndex j i) k).val : ℤ) - 1) = _
  rw [zeroCaseCoreWord_high]
  rfl

theorem actualCore_rowSize (g : Fin 8) :
    (F.coreSignatureData_of_representative hc j hrep).rowSize (ZeroHighRows.group g) =
      ZeroHighRows.sizes j g := by
  dsimp only [CoreSignatureData.rowSize]
  rw [F.singleClass_card_of_representative hc j hrep]
  simp only [zeroCaseSingleSize,ZeroHighRows.group_index,ZeroHighRows.sizes]

theorem actualHighRowOK (h : G.IsSRGWith 99 14 1 2) (hz : F.weightCount 0 = 0)
    (i : ZeroHighRows.High j) :
    ZeroHighRows.HighRowOK j i (F.actualHighNeighbors hc j hrep i) (F.actualHighCounts hc j hrep i) := by
  let D := F.coreSignatureData_of_representative hc j hrep
  have hhigh (k : Fin 4) : D.rowCode (zeroCaseHighIndex j i) k = ZeroHighRows.highSign j i k :=
    F.actualHigh_rowCode hc j hrep i k
  have hcore (r : ZeroHighRows.Core j) (k : Fin 4) : D.rowCode r k = ZeroHighRows.coreSign j r k := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro he
      subst r
      exact D.row_no_loop _ hr
    · intro k hs
      have ha : G.Adj (D.point (zeroCaseHighIndex j i)) (D.point r) := (Finset.mem_filter.mp hr).2
      have hp := D.point_code (zeroCaseHighIndex j i) k
      have hq := D.point_code r k
      change F.code k (D.point (zeroCaseHighIndex j i)) = D.rowCode (zeroCaseHighIndex j i) k at hp
      change F.code k (D.point r) = D.rowCode r k at hq
      rw [hhigh] at hp
      rw [hcore] at hq
      exact F.same_nonzero_coordinate_not_adj k (hp ▸ hs.1) (by rw [hp,hq]; exact hs.2) ha
  · intro g
    have hb := D.row_bounds (zeroCaseHighIndex j i) (ZeroHighRows.group g)
    rwa [F.actualCore_rowSize hc j hrep g] at hb
  · intro k hne
    have hsign := (F.biplane k).signs (D.point (zeroCaseHighIndex j i))
    have hp := D.point_code (zeroCaseHighIndex j i) k
    change F.code k (D.point (zeroCaseHighIndex j i)) = D.rowCode (zeroCaseHighIndex j i) k at hp
    rw [hhigh] at hp
    rw [hp] at hsign
    by_cases hm : ZeroHighRows.highSign j i k = -1
    · simp only [if_pos hm,actualHighCounts,ZeroHighRows.group_minus]
      apply D.row_same_sign_zero
      simpa only [Bool.false_eq_true,if_false,hhigh] using hm
    · have hplus : ZeroHighRows.highSign j i k = 1 := by omega
      simp only [if_neg hm,actualHighCounts,ZeroHighRows.group_plus]
      apply D.row_same_sign_zero
      simpa only [if_true,hhigh] using hplus
  · have hd := D.row_degree h hc hz (zeroCaseHighIndex j i)
    rw [← Equiv.sum_comp ZeroHighRows.groupEquiv (D.rowCount (zeroCaseHighIndex j i))] at hd
    change ((F.actualHighNeighbors hc j hrep i).card : ℤ) +
      ∑ g, F.actualHighCounts hc j hrep i g = _ at hd
    have hw : D.word (zeroCaseHighIndex j i) = zeroCaseHighWord j i := zeroCaseCoreWord_high j i
    rw [hw] at hd
    simpa only [ZeroHighRows.highDegree,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hd
  · intro k
    have hm := D.row_moment hc hz (zeroCaseHighIndex j i) k
    rw [ZeroHighRows.simple_moment_collapse,hhigh] at hm
    change (∑ r ∈ F.actualHighNeighbors hc j hrep i, ZeroHighRows.coreSign j r k) +
      (D.rowCount (zeroCaseHighIndex j i) (k,true) -
        D.rowCount (zeroCaseHighIndex j i) (k,false)) = _ at hm
    simp only [ZeroHighRows.coreMoment,actualHighCounts,ZeroHighRows.group_plus,ZeroHighRows.group_minus]
    linarith [hm]

theorem actualHighPairOK (h : G.IsSRGWith 99 14 1 2) (hz : F.weightCount 0 = 0)
    (i k : ZeroHighRows.High j) (hik : i ≠ k) :
    ZeroHighRows.HighPairOK j i (F.actualHighNeighbors hc j hrep i) (F.actualHighCounts hc j hrep i)
      k (F.actualHighNeighbors hc j hrep k) (F.actualHighCounts hc j hrep k) := by
  let D := F.coreSignatureData_of_representative hc j hrep
  have hind : zeroCaseHighIndex j i ≠ zeroCaseHighIndex j k := by
    intro he
    apply hik
    exact Fin.ext (congrArg (fun a : Fin (zeroCaseCoreCount j) => a.val) he)
  have hsize (g : Fin 8) : D.rowSize (ZeroHighRows.group g) = ZeroHighRows.sizes j g :=
    F.actualCore_rowSize hc j hrep g
  have hhigh (a : ZeroHighRows.High j) (l : Fin 4) :
      D.rowCode (zeroCaseHighIndex j a) l = ZeroHighRows.highSign j a l :=
    F.actualHigh_rowCode hc j hrep a l
  refine ⟨D.row_symmetric _ _,?_,?_⟩
  · have hh := D.row_common_lower h hc hz hind
    rw [← Equiv.sum_comp ZeroHighRows.groupEquiv (fun a =>
      max 0 (D.rowCount (zeroCaseHighIndex j i) a + D.rowCount (zeroCaseHighIndex j k) a - D.rowSize a))] at hh
    change ((F.actualHighNeighbors hc j hrep i ∩ F.actualHighNeighbors hc j hrep k).card : ℤ) +
      (∑ g : Fin 8, max 0 (F.actualHighCounts hc j hrep i g + F.actualHighCounts hc j hrep k g -
        D.rowSize (ZeroHighRows.group g))) ≤ _ at hh
    simp_rw [hsize] at hh
    exact hh
  · intro hno
    have hh := D.row_common_upper h hc hz hind (by
      intro l
      rw [hhigh,hhigh]
      exact hno l)
    rw [← Equiv.sum_comp ZeroHighRows.groupEquiv (fun a =>
      min (D.rowCount (zeroCaseHighIndex j i) a) (D.rowCount (zeroCaseHighIndex j k) a))] at hh
    exact hh

noncomputable def actualHighConfiguration (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 0) : ZeroHighRows.HighConfiguration j where
  neighbors := F.actualHighNeighbors hc j hrep
  counts := F.actualHighCounts hc j hrep
  rows := F.actualHighRowOK hc j hrep h hz
  pairs := F.actualHighPairOK hc j hrep h hz

#print axioms actualHighConfiguration

end FourDirectionSystem
end Conway99
