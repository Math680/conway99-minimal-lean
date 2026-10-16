import Mathlib.Tactic

/-! A kernel-checkable local certificate for the fifth residual packing.
The input is the explicit three-high/nine-double row model below. This file
does not assume or prove the reduction of an arbitrary SRG to that model. -/

namespace Conway99.ZeroResidual

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def highSign : Fin 3 → Fin 4 → ℤ :=
  ![![-1,-1,-1,1],![-1,0,1,-1],![1,1,1,1]]

def doubleSign : Fin 9 → Fin 4 → ℤ :=
  ![![-1,1,0,0],![1,-1,0,0],![1,0,-1,0],![1,0,0,-1],
    ![0,-1,1,0],![0,1,-1,0],![0,-1,0,-1],![0,1,0,-1],![0,0,-1,-1]]

def singleSizes : Fin 8 → ℤ := ![4,3,3,3,3,4,2,5]

def highCounts : Fin 3 → Fin 8 → ℤ :=
  ![![0,3,0,3,0,4,2,0],![0,2,0,0,2,0,0,4],![4,0,3,0,3,0,2,0]]

def highDoubles : Fin 3 → Finset (Fin 9) := ![{3,7},{1,2,5},{6,8}]

def minus (k : Fin 4) : Fin 8 := ⟨2*k.val,by omega⟩
def plus (k : Fin 4) : Fin 8 := ⟨2*k.val+1,by omega⟩
def groupCoord (g : Fin 8) : Fin 4 := ⟨g.val/2,by omega⟩
def groupSign (g : Fin 8) : ℤ := if g.val % 2 = 0 then -1 else 1
def highIndex (h : Fin 3) : Fin 12 := ⟨h.val,by omega⟩
def doubleIndex (d : Fin 9) : Fin 12 := ⟨3+d.val,by omega⟩
def group (g : Fin 8) : Fin 4 × Bool := (groupCoord g,decide (g.val % 2 ≠ 0))

def edgeAllowed (i j : Fin 9) : Prop :=
  i ≠ j ∧ ∀ k, ¬(doubleSign i k ≠ 0 ∧ doubleSign i k = doubleSign j k)
instance (i j : Fin 9) : Decidable (edgeAllowed i j) := by unfold edgeAllowed; infer_instance

def allowedDoubles (i : Fin 9) : Finset (Fin 9) := Finset.univ.filter (edgeAllowed i)
def highNeighbors (i : Fin 9) : Finset (Fin 3) := Finset.univ.filter (fun h => i ∈ highDoubles h)

def coreDegree (i : Fin 9) (ds : Finset (Fin 9)) : ℤ := ds.card + (highNeighbors i).card
def coreMoment (i : Fin 9) (ds : Finset (Fin 9)) (k : Fin 4) : ℤ :=
  (∑ h ∈ highNeighbors i, highSign h k) + ∑ j ∈ ds, doubleSign j k

def noSharedZero (i : Fin 9) (h : Fin 3) : Prop := ∀ k, doubleSign i k ≠ 0 ∨ highSign h k ≠ 0
instance (i : Fin 9) (h : Fin 3) : Decidable (noSharedZero i h) := by unfold noSharedZero; infer_instance

def commonNeed (i : Fin 9) (h : Fin 3) : ℤ := if i ∈ highDoubles h then 1 else 2
def coreCommon (ds : Finset (Fin 9)) (h : Fin 3) : ℤ := (ds ∩ highDoubles h).card

def RowOK (i : Fin 9) (ds : Finset (Fin 9)) (c : Fin 8 → ℤ) : Prop :=
  ds ⊆ allowedDoubles i ∧
  (∀ g, 0 ≤ c g ∧ c g ≤ singleSizes g) ∧
  (∀ k, doubleSign i k ≠ 0 →
    c (if doubleSign i k = -1 then minus k else plus k) = 0) ∧
  coreDegree i ds + ∑ g, c g = 8 ∧
  (∀ k, coreMoment i ds k + c (plus k) - c (minus k) = -4 * doubleSign i k) ∧
  (∀ h, coreCommon ds h + ∑ g, max 0 (c g + highCounts h g - singleSizes g) ≤ commonNeed i h) ∧
  (∀ h, noSharedZero i h → commonNeed i h ≤ coreCommon ds h + ∑ g, min (c g) (highCounts h g))

instance (i : Fin 9) (ds : Finset (Fin 9)) (c : Fin 8 → ℤ) : Decidable (RowOK i ds c) := by
  unfold RowOK
  infer_instance

def zeroFirst : Fin 9 → Fin 4 := ![2,2,1,1,0,0,0,0,0]
def zeroSecond : Fin 9 → Fin 4 := ![3,3,3,2,3,3,2,2,1]

def activeCounts (i : Fin 9) (ds : Finset (Fin 9)) (g : Fin 8) : ℤ :=
  let a := doubleSign i (groupCoord g)
  if a = 0 ∨ a = groupSign g then 0 else 4 + a * coreMoment i ds (groupCoord g)

def remainingDegree (i : Fin 9) (ds : Finset (Fin 9)) (m : ℤ) : ℤ :=
  8 - coreDegree i ds - (∑ g, activeCounts i ds g) - (2*m - coreMoment i ds (zeroFirst i))

def candidateCounts (i : Fin 9) (ds : Finset (Fin 9)) (m : Fin 5) (g : Fin 8) : ℤ :=
  if groupCoord g = zeroFirst i then
    if g.val % 2 = 0 then m.val else (m.val : ℤ) - coreMoment i ds (zeroFirst i)
  else if groupCoord g = zeroSecond i then
    if g.val % 2 = 0 then (remainingDegree i ds m.val + coreMoment i ds (zeroSecond i))/2
    else (remainingDegree i ds m.val - coreMoment i ds (zeroSecond i))/2
  else activeCounts i ds g

def parameters (i : Fin 9) : Finset (Finset (Fin 9) × Fin 5) :=
  (allowedDoubles i).powerset ×ˢ Finset.univ

def validParameters (i : Fin 9) : Finset (Finset (Fin 9) × Fin 5) :=
  (parameters i).filter (fun p => RowOK i p.1 (candidateCounts i p.1 p.2))

def forcedDoubles : Fin 9 → Finset (Fin 9) :=
  ![{1,2,3,4},{0,5},{0,4},{0},{0,2,5,8},{1,4},{0},{4},{4}]
def forcedParameter : Fin 9 → Fin 5 := ![0,0,0,0,0,0,0,0,1]

/- This equality computes the complete row option set, not just membership of
the nine proposed options. `decide` is kernel reduction, never native evaluation. -/
theorem residual_row_validator :
    ∀ i : Fin 9, validParameters i = {(forcedDoubles i, forcedParameter i)} := by
  decide

theorem row_counts_reconstruction (i : Fin 9) (ds : Finset (Fin 9)) (c : Fin 8 → ℤ) (m : Fin 5)
    (ha : ∀ k, doubleSign i k ≠ 0 →
      c (if doubleSign i k = -1 then minus k else plus k) = 0)
    (hd : coreDegree i ds + ∑ g, c g = 8)
    (hp : ∀ k, coreMoment i ds k + c (plus k) - c (minus k) = -4 * doubleSign i k)
    (hm : (m.val : ℤ) = c (minus (zeroFirst i))) : c = candidateCounts i ds m := by
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
  have hpt : coreMoment i ds = ![coreMoment i ds 0,coreMoment i ds 1,
      coreMoment i ds 2,coreMoment i ds 3] := by
    funext k
    fin_cases k <;> rfl
  funext g
  unfold candidateCounts remainingDegree activeCounts
  rw [hct] at ha0 ha1 ha2 ha3 hp0 hp1 hp2 hp3 hd hm ⊢
  rw [hpt] at hp0 hp1 hp2 hp3 ⊢
  simp only [Fin.sum_univ_succ] at hd
  fin_cases i <;> fin_cases g <;>
    norm_num [candidateCounts, remainingDegree, activeCounts, zeroFirst, zeroSecond,
      doubleSign, minus, plus, groupCoord, groupSign, Fin.sum_univ_succ,
      Fin.mk.injEq, Fin.reduceFinMk] at ha0 ha1 ha2 ha3 hp0 hp1 hp2 hp3 hd hm ⊢ <;>
    dsimp only [Fin.succ, Fin.castSucc, Matrix.vecCons, Fin.cons, Fin.induction, Fin.cases, Fin.ofNat] at * <;>
    norm_num [Fin.ext_iff, Fin.isValue] at * <;>
    simp [Fin.induction.go] at * <;> omega

theorem residual_row_complete (i : Fin 9) (ds : Finset (Fin 9)) (c : Fin 8 → ℤ)
    (h : RowOK i ds c) : ∃ m : Fin 5, (ds,m) ∈ validParameters i ∧ c = candidateCounts i ds m := by
  have hb := h.2.1 (minus (zeroFirst i))
  have hsize : singleSizes (minus (zeroFirst i)) ≤ 4 := by
    fin_cases i <;> decide
  let m : Fin 5 := ⟨(c (minus (zeroFirst i))).toNat,by omega⟩
  have hm : (m.val : ℤ) = c (minus (zeroFirst i)) := by
    exact Int.toNat_of_nonneg hb.1
  have heq := row_counts_reconstruction i ds c m h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hm
  refine ⟨m,?_,heq⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr h.1,Finset.mem_univ _⟩
  · rw [← heq]
    exact h

theorem residual_row_forced (i : Fin 9) (ds : Finset (Fin 9)) (c : Fin 8 → ℤ)
    (h : RowOK i ds c) : ds = forcedDoubles i := by
  obtain ⟨m,hm,_⟩ := residual_row_complete i ds c h
  rw [residual_row_validator i,Finset.mem_singleton] at hm
  exact congrArg Prod.fst hm

structure Configuration where
  doubles : Fin 9 → Finset (Fin 9)
  counts : Fin 9 → Fin 8 → ℤ
  rows : ∀ i, RowOK i (doubles i) (counts i)
  symmetric : ∀ i j, j ∈ doubles i ↔ i ∈ doubles j

theorem residual_configuration_impossible (C : Configuration) : False := by
  have h0 := residual_row_forced 0 (C.doubles 0) (C.counts 0) (C.rows 0)
  have h6 := residual_row_forced 6 (C.doubles 6) (C.counts 6) (C.rows 6)
  have hs := C.symmetric 0 6
  rw [h0,h6] at hs
  have hn : (6 : Fin 9) ∉ forcedDoubles 0 := by decide
  have hp : (0 : Fin 9) ∈ forcedDoubles 6 := by decide
  exact hn (hs.mpr hp)

#print axioms residual_row_validator
#print axioms row_counts_reconstruction
#print axioms residual_row_complete
#print axioms residual_configuration_impossible

end Conway99.ZeroResidual
