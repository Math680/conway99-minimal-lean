import ZeroCaseOrbitData
import ZeroCaseDoubleSignatures
import CoreSignatureRealization

/-! Ordered, kernel-certified core data for the five high-packing representatives.
The order is exactly `certificat/high_neighbour_counts.py`: high words first,
then `setup()`'s lexicographic coordinate-pair/sign order for doubles; the eight
simple classes are ordered (coordinate 0 negative, positive, ..., 3 positive).
-/

namespace Conway99

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def zeroCaseHighCodes (j : Fin 5) : List ℕ :=
  ![[1,15,23,35,45,57,65], [1,15,45,57,80], [5,15,19,55,80],
    [5,15,45,55,80], [2,15,80]] j

def zeroCaseDoubleCodes (j : Fin 5) : List ℕ :=
  ![[76,70,52], [22,64,14,34,32,38], [66,34,30,48,36,38],
    [22,10,66,34,30,38], [22,58,64,66,34,46,30,48,36]] j

def zeroCaseCoreCodes (j : Fin 5) : List ℕ :=
  zeroCaseHighCodes j ++ zeroCaseDoubleCodes j

def zeroCaseHighCount (j : Fin 5) : ℕ := (zeroCaseHighCodes j).length
def zeroCaseDoubleCount (j : Fin 5) : ℕ := (zeroCaseDoubleCodes j).length
def zeroCaseCoreCount (j : Fin 5) : ℕ := (zeroCaseCoreCodes j).length

def zeroCaseHighWord (j : Fin 5) (k : Fin (zeroCaseHighCount j)) : RootSignature :=
  decodeRootSignature ((zeroCaseHighCodes j).get k)

def zeroCaseDoubleWord (j : Fin 5) (k : Fin (zeroCaseDoubleCount j)) : RootSignature :=
  decodeRootSignature ((zeroCaseDoubleCodes j).get k)

def zeroCaseCoreWord (j : Fin 5) (k : Fin (zeroCaseCoreCount j)) : RootSignature :=
  decodeRootSignature ((zeroCaseCoreCodes j).get k)

def zeroCaseSingleSizes (j : Fin 5) : Fin 8 → ℕ :=
  ![![4,3,4,3,4,3,4,4], ![3,4,3,4,3,4,4,3], ![4,4,3,4,3,4,2,4],
    ![3,4,3,4,3,4,3,4], ![4,3,3,3,3,4,2,5]] j

def zeroCaseGroupIndex (a : Fin 4 × Bool) : Fin 8 :=
  ⟨2 * a.1.val + if a.2 then 1 else 0, by have := a.1.isLt; split <;> omega⟩

def zeroCaseSingleSize (j : Fin 5) (a : Fin 4 × Bool) : ℕ :=
  zeroCaseSingleSizes j (zeroCaseGroupIndex a)

theorem zeroCaseHighCount_values (j : Fin 5) : zeroCaseHighCount j = ![7,5,5,5,3] j := by
  revert j
  decide

theorem zeroCaseDoubleCount_values (j : Fin 5) : zeroCaseDoubleCount j = ![3,6,6,6,9] j := by
  revert j
  decide

theorem zeroCaseCoreCount_values (j : Fin 5) : zeroCaseCoreCount j = ![10,11,11,11,12] j := by
  revert j
  decide

theorem zeroCaseCoreCount_eq (j : Fin 5) :
    zeroCaseCoreCount j = zeroCaseHighCount j + zeroCaseDoubleCount j := List.length_append

def zeroCaseHighIndex (j : Fin 5) (k : Fin (zeroCaseHighCount j)) :
    Fin (zeroCaseCoreCount j) :=
  ⟨k.val, by have := k.isLt; rw [zeroCaseCoreCount_eq]; omega⟩

def zeroCaseDoubleIndex (j : Fin 5) (k : Fin (zeroCaseDoubleCount j)) :
    Fin (zeroCaseCoreCount j) :=
  ⟨zeroCaseHighCount j + k.val, by have := k.isLt; rw [zeroCaseCoreCount_eq]; omega⟩

theorem zeroCaseCoreWord_high (j : Fin 5) (k : Fin (zeroCaseHighCount j)) :
    zeroCaseCoreWord j (zeroCaseHighIndex j k) = zeroCaseHighWord j k := by
  revert j
  decide

theorem zeroCaseCoreWord_double (j : Fin 5) (k : Fin (zeroCaseDoubleCount j)) :
    zeroCaseCoreWord j (zeroCaseDoubleIndex j k) = zeroCaseDoubleWord j k := by
  revert j
  decide

theorem zeroCaseHighWord_injective (j : Fin 5) : Function.Injective (zeroCaseHighWord j) := by
  revert j
  decide

theorem zeroCaseDoubleWord_injective (j : Fin 5) : Function.Injective (zeroCaseDoubleWord j) := by
  revert j
  decide

theorem zeroCaseCoreWord_injective (j : Fin 5) : Function.Injective (zeroCaseCoreWord j) := by
  revert j
  decide

theorem zeroCaseHighWord_cover (j : Fin 5) :
    Finset.univ.image (zeroCaseHighWord j) = zeroCaseOrbitRepresentative j := by
  revert j
  decide

theorem zeroCaseDoubleWord_cover (j : Fin 5) :
    Finset.univ.image (zeroCaseDoubleWord j) = doubleCandidates (zeroCaseOrbitRepresentative j) := by
  revert j
  decide

theorem zeroCaseCoreWord_cover (j : Fin 5) :
    Finset.univ.image (zeroCaseCoreWord j) =
      zeroCaseOrbitRepresentative j ∪ doubleCandidates (zeroCaseOrbitRepresentative j) := by
  revert j
  decide

theorem zeroCaseSingleSize_eq_signatures (j : Fin 5) (a : Fin 4 × Bool) :
    zeroCaseSingleSize j a =
      7 - ((zeroCaseOrbitRepresentative j ∪ doubleCandidates (zeroCaseOrbitRepresentative j)).filter
        (fun w => w a.1 = if a.2 then 2 else 0)).card := by
  revert j a
  decide

namespace FourDirectionSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

def coreSignatureData_of_representative (hc : F.HasSignedCells) (j : Fin 5)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative j) :
    CoreSignatureData F (zeroCaseCoreCount j) where
  word := zeroCaseCoreWord j
  injective := zeroCaseCoreWord_injective j
  cover := by rw [zeroCaseCoreWord_cover, F.coreSignatures_eq_high_union_double hc, hrep]

theorem singleClass_card_of_representative (hc : F.HasSignedCells) (j : Fin 5)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative j) (a : Fin 4 × Bool) :
    (F.singleClass a).card = zeroCaseSingleSize j a := by
  rw [F.singleClass_card_from_high hc, hrep]
  exact (zeroCaseSingleSize_eq_signatures j a).symm

#print axioms coreSignatureData_of_representative
#print axioms singleClass_card_of_representative

end FourDirectionSystem
end Conway99
