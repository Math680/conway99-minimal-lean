import ZeroCaseHighRows
import FiniteRowSearch

/-! Exhaustive high-row search. The encoded solution lists retain every row,
not merely a count of survivors. -/

namespace Conway99.ZeroHighRows

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 32000000

def compatible (j : Fin 5) (i : High j) (ns : Finset (Core j))
    (k : High j) (nt : Finset (Core j)) : Prop :=
  i = k ∨ HighPairOK j i ns (candidateCounts j i ns) k nt (candidateCounts j k nt)

instance (j : Fin 5) (i k : High j) (ns nt : Finset (Core j)) : Decidable (compatible j i ns k nt) := by
  unfold compatible
  infer_instance

def highSolutions (j : Fin 5) : Finset (List (High j × Finset (Core j))) :=
  FiniteRowSearch.search (rowOptions j) (compatible j) (List.finRange (zeroCaseHighCount j)) []

def encodeRows {j : Fin 5} (L : List (High j × Finset (Core j))) : List (ℕ × Finset ℕ) :=
  L.map (fun p => (p.1.val,p.2.image Fin.val))

def highSolutionCodes (j : Fin 5) : Finset (List (ℕ × Finset ℕ)) :=
  (highSolutions j).image encodeRows

def expectedSolutionCodes : Fin 5 → Finset (List (ℕ × Finset ℕ)) :=
  ![∅, {[(4,{0}),(3,{5,7,10}),(2,{7,8,9}),(1,{6,9,10}),(0,{4})]}, ∅,
    {[(4,{6,9}),(3,{1,5}),(2,{0,8}),(1,{3,10}),(0,{2,7})]},
    {[(2,{9,11}),(1,{4,5,8}),(0,{6,10})]}]

theorem high_array_certificate : ∀ j : Fin 5, highSolutionCodes j = expectedSolutionCodes j := by
  decide

theorem high_array_counts : ∀ j : Fin 5, (highSolutions j).card = ![0,1,0,1,1] j := by
  decide

#print axioms high_array_certificate
#print axioms high_array_counts

end Conway99.ZeroHighRows
