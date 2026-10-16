import ZeroCaseResidualRows
import ZeroCaseCoreData
import CoreSignatureRows

/-! Transport the residual high-row tables to the actual graph. The double
row constraints are consequences of the graph equations, not premises. -/

noncomputable section
namespace Conway99.ZeroResidual
open scoped BigOperators

def groupEquiv : Fin 8 ≃ (Fin 4 × Bool) where
  toFun := group
  invFun := zeroCaseGroupIndex
  left_inv := by decide
  right_inv := by decide

theorem group_minus (k : Fin 4) : group (minus k) = (k, false) := by revert k; decide
theorem group_plus (k : Fin 4) : group (plus k) = (k, true) := by revert k; decide

def highPart (s : Finset (Fin 12)) : Finset (Fin 3) :=
  Finset.univ.filter (fun h => highIndex h ∈ s)
def doublePart (s : Finset (Fin 12)) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => doubleIndex i ∈ s)

theorem highPart_inter (s t : Finset (Fin 12)) : highPart (s ∩ t) = highPart s ∩ highPart t := by
  ext h
  simp [highPart]

theorem doublePart_inter (s t : Finset (Fin 12)) : doublePart (s ∩ t) = doublePart s ∩ doublePart t := by
  ext i
  simp [doublePart]

theorem core_sum_split (s : Finset (Fin 12)) (f : Fin 12 → ℤ) :
    (∑ j ∈ s, f j) = (∑ h ∈ highPart s, f (highIndex h)) +
      ∑ i ∈ doublePart s, f (doubleIndex i) := by
  have hh := Fin.sum_univ_add (a := 3) (b := 9) (fun j => if j ∈ s then f j else 0)
  simpa [highPart, doublePart, highIndex, doubleIndex, ← Finset.sum_filter] using hh

theorem core_card_split (s : Finset (Fin 12)) :
    (s.card : ℤ) = (highPart s).card + (doublePart s).card := by
  simpa using core_sum_split s (fun _ => 1)

theorem group_sum (f : (Fin 4 × Bool) → ℤ) : (∑ a, f a) = ∑ g, f (group g) :=
  (Equiv.sum_comp groupEquiv f).symm

theorem group_moment (f : (Fin 4 × Bool) → ℤ) (k : Fin 4) :
    (∑ a : Fin 4 × Bool, f a * (if k = a.1 then (if a.2 then 1 else -1) else 0)) =
      f (k,true) - f (k,false) := by
  fin_cases k <;> simp [Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

theorem high_table_code (h : Fin 3) (k : Fin 4) :
    ((zeroCaseCoreWord 4 (highIndex h) k).val : ℤ) - 1 = highSign h k := by
  revert h k
  decide

theorem double_table_code (i : Fin 9) (k : Fin 4) :
    ((zeroCaseCoreWord 4 (doubleIndex i) k).val : ℤ) - 1 = doubleSign i k := by
  revert i k
  decide

theorem double_table_weight (i : Fin 9) :
    signatureWeight (zeroCaseCoreWord 4 (doubleIndex i)) = 2 := by revert i; decide

theorem single_table_size (g : Fin 8) :
    (zeroCaseSingleSize 4 (group g) : ℤ) = singleSizes g := by revert g; decide

theorem high_double_ne (i : Fin 9) (h : Fin 3) : doubleIndex i ≠ highIndex h := by
  intro he
  have hh := congrArg Fin.val he
  simp only [doubleIndex, highIndex] at hh
  have := h.isLt
  omega

theorem doubleIndex_injective : Function.Injective doubleIndex := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [doubleIndex] at hh
  omega

theorem double_table_allowed (i j : Fin 9) (hne : i ≠ j)
    (ha : signatureEdgeAllowed (zeroCaseCoreWord 4 (doubleIndex i))
      (zeroCaseCoreWord 4 (doubleIndex j))) : edgeAllowed i j := by
  unfold signatureEdgeAllowed at ha
  revert i j
  decide

theorem double_same_sign (i : Fin 9) (k : Fin 4) (hn : doubleSign i k ≠ 0) :
    (if (group (if doubleSign i k = -1 then minus k else plus k)).2 then 1 else -1) =
      doubleSign i k := by
  revert i k
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {F : FourDirectionSystem G}

section ActualRows
variable (D : CoreSignatureData F 12)
variable (hword : D.word = zeroCaseCoreWord 4)
variable (hsizes : ∀ g, D.rowSize (group g) = singleSizes g)
variable (hhigh : ∀ h k, highIndex k ∉ D.rowNeighbors (highIndex h))
variable (hdouble : ∀ h i, doubleIndex i ∈ D.rowNeighbors (highIndex h) ↔ i ∈ highDoubles h)
variable (hcounts : ∀ h g, D.rowCount (highIndex h) (group g) = highCounts h g)

def actualDoubles (i : Fin 9) : Finset (Fin 9) := doublePart (D.rowNeighbors (doubleIndex i))
def actualCounts (i : Fin 9) (g : Fin 8) : ℤ := D.rowCount (doubleIndex i) (group g)

include hword in
theorem actual_high_code (h : Fin 3) (k : Fin 4) : D.rowCode (highIndex h) k = highSign h k := by
  change ((D.word (highIndex h) k).val : ℤ) - 1 = _
  rw [hword]
  exact high_table_code h k

include hword in
theorem actual_double_code (i : Fin 9) (k : Fin 4) : D.rowCode (doubleIndex i) k = doubleSign i k := by
  change ((D.word (doubleIndex i) k).val : ℤ) - 1 = _
  rw [hword]
  exact double_table_code i k

include hword in
theorem actual_double_weight (i : Fin 9) : signatureWeight (D.word (doubleIndex i)) = 2 := by
  rw [hword]
  exact double_table_weight i

include hhigh in
theorem highPart_high (h : Fin 3) : highPart (D.rowNeighbors (highIndex h)) = ∅ := by
  ext k
  simp [highPart, hhigh h k]

include hdouble in
theorem doublePart_high (h : Fin 3) : doublePart (D.rowNeighbors (highIndex h)) = highDoubles h := by
  ext i
  simp [doublePart, hdouble h i]

include hdouble in
theorem highPart_double (i : Fin 9) : highPart (D.rowNeighbors (doubleIndex i)) = highNeighbors i := by
  ext h
  simp only [highPart, highNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (D.row_symmetric (doubleIndex i) (highIndex h)).trans (hdouble h i)

include hdouble in
theorem actual_core_degree (i : Fin 9) :
    ((D.rowNeighbors (doubleIndex i)).card : ℤ) = coreDegree i (actualDoubles D i) := by
  rw [core_card_split, highPart_double D hdouble]
  unfold coreDegree actualDoubles
  omega

include hword hdouble in
theorem actual_core_moment (i : Fin 9) (k : Fin 4) :
    (∑ j ∈ D.rowNeighbors (doubleIndex i), D.rowCode j k) =
      coreMoment i (actualDoubles D i) k := by
  rw [core_sum_split, highPart_double D hdouble]
  simp_rw [actual_high_code D hword, actual_double_code D hword]
  rfl

include hhigh hdouble in
theorem actual_core_common (i : Fin 9) (h : Fin 3) :
    ((D.rowNeighbors (doubleIndex i) ∩ D.rowNeighbors (highIndex h)).card : ℤ) =
      coreCommon (actualDoubles D i) h := by
  rw [core_card_split, highPart_inter, doublePart_inter,
    highPart_high D hhigh, doublePart_high D hdouble, Finset.inter_empty]
  simp only [Finset.card_empty, Nat.cast_zero, zero_add]
  rfl

include hdouble in
theorem actual_high_edge (i : Fin 9) (h : Fin 3) :
    highIndex h ∈ D.rowNeighbors (doubleIndex i) ↔ i ∈ highDoubles h :=
  (D.row_symmetric (doubleIndex i) (highIndex h)).trans (hdouble h i)

include hword in
theorem actual_doubles_allowed (i : Fin 9) : actualDoubles D i ⊆ allowedDoubles i := by
  intro j hj
  have hmem : doubleIndex j ∈ D.rowNeighbors (doubleIndex i) := (Finset.mem_filter.mp hj).2
  have hne : i ≠ j := by
    intro he
    subst j
    exact D.row_no_loop (doubleIndex i) hmem
  have ha := D.row_allowed hmem
  rw [hword] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, double_table_allowed i j hne ha⟩

include hsizes in
theorem actual_counts_bounds (i : Fin 9) (g : Fin 8) :
    0 ≤ actualCounts D i g ∧ actualCounts D i g ≤ singleSizes g := by
  have hh := D.row_bounds (doubleIndex i) (group g)
  rw [hsizes g] at hh
  exact hh

include hword in
theorem actual_same_sign_zero (i : Fin 9) (k : Fin 4) (hn : doubleSign i k ≠ 0) :
    actualCounts D i (if doubleSign i k = -1 then minus k else plus k) = 0 := by
  apply D.row_same_sign_zero (doubleIndex i)
    (group (if doubleSign i k = -1 then minus k else plus k))
  have hcoord : (group (if doubleSign i k = -1 then minus k else plus k)).1 = k := by
    split <;> simp [group_minus, group_plus]
  rw [hcoord, actual_double_code D hword]
  exact (double_same_sign i k hn).symm

include hword hdouble in
theorem actual_degree (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) (i : Fin 9) :
    coreDegree i (actualDoubles D i) + ∑ g, actualCounts D i g = 8 := by
  have hh := D.row_degree h hc hz (doubleIndex i)
  rw [actual_core_degree D hdouble, actual_double_weight D hword, group_sum] at hh
  norm_num at hh
  exact hh

include hword hdouble in
theorem actual_moment (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (i : Fin 9) (k : Fin 4) :
    coreMoment i (actualDoubles D i) k + actualCounts D i (plus k) -
      actualCounts D i (minus k) = -4 * doubleSign i k := by
  have hh := D.row_moment hc hz (doubleIndex i) k
  rw [actual_core_moment D hword hdouble, group_moment, actual_double_code D hword] at hh
  simpa only [actualCounts, group_plus, group_minus, add_sub_assoc] using hh

include hsizes hhigh hdouble hcounts in
theorem actual_common_lower (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) (i : Fin 9) (a : Fin 3) :
    coreCommon (actualDoubles D i) a +
      ∑ g, max 0 (actualCounts D i g + highCounts a g - singleSizes g) ≤ commonNeed i a := by
  have hh := D.row_common_lower h hc hz (high_double_ne i a)
  rw [actual_core_common D hhigh hdouble, group_sum] at hh
  simp only [actual_high_edge D hdouble] at hh
  simp_rw [hcounts, hsizes] at hh
  exact hh

include hword hhigh hdouble hcounts in
theorem actual_common_upper (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) (i : Fin 9) (a : Fin 3) (hno : noSharedZero i a) :
    commonNeed i a ≤ coreCommon (actualDoubles D i) a +
      ∑ g, min (actualCounts D i g) (highCounts a g) := by
  have hn : ∀ k, D.rowCode (doubleIndex i) k ≠ 0 ∨ D.rowCode (highIndex a) k ≠ 0 := by
    simpa only [noSharedZero, actual_double_code D hword, actual_high_code D hword] using hno
  have hh := D.row_common_upper h hc hz (high_double_ne i a) hn
  rw [actual_core_common D hhigh hdouble, group_sum] at hh
  simp only [actual_high_edge D hdouble] at hh
  simp_rw [hcounts] at hh
  exact hh

include hword hsizes hhigh hdouble hcounts in
def configuration_of_actual_rows (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0) : Configuration where
  doubles := actualDoubles D
  counts := actualCounts D
  rows i := ⟨actual_doubles_allowed D hword i, actual_counts_bounds D hsizes i,
    actual_same_sign_zero D hword i, actual_degree D hword hdouble h hc hz i,
    actual_moment D hword hdouble hc hz i,
    actual_common_lower D hsizes hhigh hdouble hcounts h hc hz i,
    actual_common_upper D hword hhigh hdouble hcounts h hc hz i⟩
  symmetric i j := by
    simp only [actualDoubles, doublePart, Finset.mem_filter, Finset.mem_univ, true_and]
    exact D.row_symmetric (doubleIndex i) (doubleIndex j)

end ActualRows
end Conway99.ZeroResidual

namespace Conway99.FourDirectionSystem
open ZeroResidual

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

def residual_graph_configuration (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative 4)
    (hhigh : ∀ a b, highIndex b ∉
      (F.coreSignatureData_of_representative hc 4 hrep).rowNeighbors (highIndex a))
    (hdouble : ∀ a i, doubleIndex i ∈
      (F.coreSignatureData_of_representative hc 4 hrep).rowNeighbors (highIndex a) ↔ i ∈ highDoubles a)
    (hcounts : ∀ a g,
      (F.coreSignatureData_of_representative hc 4 hrep).rowCount (highIndex a) (group g) =
        highCounts a g) : Configuration := by
  let D : CoreSignatureData F 12 := F.coreSignatureData_of_representative hc 4 hrep
  have hword : D.word = zeroCaseCoreWord 4 := rfl
  have hsizes : ∀ g, D.rowSize (group g) = singleSizes g := by
    intro g
    change ((F.singleClass (group g)).card : ℤ) = _
    rw [F.singleClass_card_of_representative hc 4 hrep]
    exact single_table_size g
  exact configuration_of_actual_rows D hword hsizes hhigh hdouble hcounts h hc hz

theorem residual_graph_impossible (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative 4)
    (hhigh : ∀ a b, highIndex b ∉
      (F.coreSignatureData_of_representative hc 4 hrep).rowNeighbors (highIndex a))
    (hdouble : ∀ a i, doubleIndex i ∈
      (F.coreSignatureData_of_representative hc 4 hrep).rowNeighbors (highIndex a) ↔ i ∈ highDoubles a)
    (hcounts : ∀ a g,
      (F.coreSignatureData_of_representative hc 4 hrep).rowCount (highIndex a) (group g) =
        highCounts a g) : False :=
  residual_configuration_impossible
    (F.residual_graph_configuration h hc hz hrep hhigh hdouble hcounts)

#print axioms residual_graph_configuration
#print axioms residual_graph_impossible

end Conway99.FourDirectionSystem
