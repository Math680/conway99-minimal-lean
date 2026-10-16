import ZeroCaseCoreData

/-! Finite local high-row model for the five representatives. Core masks refer
to the shared ordered high+double data of ZeroCaseCoreData, not arbitrary words. -/

namespace Conway99.ZeroHighRows

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

abbrev High (j : Fin 5) := Fin (zeroCaseHighCount j)
abbrev Core (j : Fin 5) := Fin (zeroCaseCoreCount j)

def minus (k : Fin 4) : Fin 8 := ⟨2*k.val,by omega⟩
def plus (k : Fin 4) : Fin 8 := ⟨2*k.val+1,by omega⟩
def groupCoord (g : Fin 8) : Fin 4 := ⟨g.val/2,by omega⟩
def groupSign (g : Fin 8) : ℤ := if g.val % 2 = 0 then -1 else 1
def group (g : Fin 8) : Fin 4 × Bool := (groupCoord g,decide (g.val % 2 ≠ 0))

def highSign (j : Fin 5) (i : High j) (k : Fin 4) : ℤ := ((zeroCaseHighWord j i k).val : ℤ) - 1
def coreSign (j : Fin 5) (i : Core j) (k : Fin 4) : ℤ := ((zeroCaseCoreWord j i k).val : ℤ) - 1
def sizes (j : Fin 5) (g : Fin 8) : ℤ := zeroCaseSingleSizes j g
def highDegree (j : Fin 5) (i : High j) : ℤ := 2 + 3 * signatureWeight (zeroCaseHighWord j i)

def edgeAllowed (j : Fin 5) (i : High j) (r : Core j) : Prop :=
  r ≠ zeroCaseHighIndex j i ∧ ∀ k, ¬(highSign j i k ≠ 0 ∧ highSign j i k = coreSign j r k)
instance (j : Fin 5) (i : High j) (r : Core j) : Decidable (edgeAllowed j i r) := by
  unfold edgeAllowed
  infer_instance

def allowedCore (j : Fin 5) (i : High j) : Finset (Core j) := Finset.univ.filter (edgeAllowed j i)
def coreMoment (j : Fin 5) (ns : Finset (Core j)) (k : Fin 4) : ℤ := ∑ r ∈ ns, coreSign j r k
def noSharedZero (j : Fin 5) (i k : High j) : Prop := ∀ l, highSign j i l ≠ 0 ∨ highSign j k l ≠ 0
instance (j : Fin 5) (i k : High j) : Decidable (noSharedZero j i k) := by
  unfold noSharedZero
  infer_instance

def HighRowOK (j : Fin 5) (i : High j) (ns : Finset (Core j)) (c : Fin 8 → ℤ) : Prop :=
  ns ⊆ allowedCore j i ∧
  (∀ g, 0 ≤ c g ∧ c g ≤ sizes j g) ∧
  (∀ k, highSign j i k ≠ 0 → c (if highSign j i k = -1 then minus k else plus k) = 0) ∧
  (ns.card : ℤ) + ∑ g, c g = highDegree j i ∧
  (∀ k, coreMoment j ns k + c (plus k) - c (minus k) = -4 * highSign j i k)

instance (j : Fin 5) (i : High j) (ns : Finset (Core j)) (c : Fin 8 → ℤ) : Decidable (HighRowOK j i ns c) := by
  unfold HighRowOK
  infer_instance

def HighPairOK (j : Fin 5) (i : High j) (ns : Finset (Core j)) (c : Fin 8 → ℤ)
    (k : High j) (nt : Finset (Core j)) (d : Fin 8 → ℤ) : Prop :=
  (zeroCaseHighIndex j k ∈ ns ↔ zeroCaseHighIndex j i ∈ nt) ∧
  ((ns ∩ nt).card : ℤ) + ∑ g, max 0 (c g + d g - sizes j g) ≤
    (if zeroCaseHighIndex j k ∈ ns then 1 else 2) ∧
  (noSharedZero j i k →
    (if zeroCaseHighIndex j k ∈ ns then (1 : ℤ) else 2) ≤
      ((ns ∩ nt).card : ℤ) + ∑ g, min (c g) (d g))

instance (j : Fin 5) (i k : High j) (ns nt : Finset (Core j)) (c d : Fin 8 → ℤ) :
    Decidable (HighPairOK j i ns c k nt d) := by
  unfold HighPairOK
  infer_instance

structure HighConfiguration (j : Fin 5) where
  neighbors : High j → Finset (Core j)
  counts : High j → Fin 8 → ℤ
  rows : ∀ i, HighRowOK j i (neighbors i) (counts i)
  pairs : ∀ i k, i ≠ k → HighPairOK j i (neighbors i) (counts i) k (neighbors k) (counts k)

def zeroCoord (j : Fin 5) (i : High j) : Fin 4 :=
  if highSign j i 0 = 0 then 0 else if highSign j i 1 = 0 then 1
  else if highSign j i 2 = 0 then 2 else 3

def activeCounts (j : Fin 5) (i : High j) (ns : Finset (Core j)) (g : Fin 8) : ℤ :=
  let a := highSign j i (groupCoord g)
  if a = 0 ∨ a = groupSign g then 0 else 4 + a * coreMoment j ns (groupCoord g)

def remainingDegree (j : Fin 5) (i : High j) (ns : Finset (Core j)) : ℤ :=
  highDegree j i - ns.card - ∑ g, activeCounts j i ns g

def candidateCounts (j : Fin 5) (i : High j) (ns : Finset (Core j)) (g : Fin 8) : ℤ :=
  if highSign j i (groupCoord g) = 0 then
    if g.val % 2 = 0 then (remainingDegree j i ns + coreMoment j ns (zeroCoord j i))/2
    else (remainingDegree j i ns - coreMoment j ns (zeroCoord j i))/2
  else activeCounts j i ns g

def rowOptions (j : Fin 5) (i : High j) : Finset (Finset (Core j)) :=
  (allowedCore j i).powerset.filter (fun ns => HighRowOK j i ns (candidateCounts j i ns))

end Conway99.ZeroHighRows
