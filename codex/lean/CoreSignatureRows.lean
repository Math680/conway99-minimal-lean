import CoreSignatureRealization

/-! Finite indexed rows realized by actual core vertices. These provide
the graph-to-certificate interface, including both common-neighbour bounds. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {F : FourDirectionSystem G} {n : ℕ}

namespace CoreSignatureData

variable (D : CoreSignatureData F n)

noncomputable def rowNeighbors (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => G.Adj (D.point i) (D.point j))

noncomputable def rowCount (i : Fin n) (a : Fin 4 × Bool) : ℤ :=
  F.singleNeighborCount (D.point i) a

def rowSize (_D : CoreSignatureData F n) (a : Fin 4 × Bool) : ℤ := (F.singleClass a).card

def rowCode (i : Fin n) (k : Fin 4) : ℤ := ((D.word i k).val : ℤ) - 1

theorem point_weight (i : Fin n) : F.weight (D.point i) = signatureWeight (D.word i) := by
  have hs := F.signature_active_card (D.point i)
  change (signatureWeight (F.signature (D.point i)) : ℤ) = _ at hs
  rw [D.point_signature i] at hs
  exact hs.symm

theorem row_symmetric (i j : Fin n) : j ∈ D.rowNeighbors i ↔ i ∈ D.rowNeighbors j := by
  simp only [rowNeighbors, Finset.mem_filter, Finset.mem_univ, true_and, G.adj_comm]

theorem row_no_loop (i : Fin n) : i ∉ D.rowNeighbors i := by
  simp [rowNeighbors]

theorem row_allowed {i j : Fin n} (hij : j ∈ D.rowNeighbors i) :
    signatureEdgeAllowed (D.word i) (D.word j) := by
  have ha := (Finset.mem_filter.mp hij).2
  have hh := F.adjacent_signatures_allowed ha
  simpa only [D.point_signature] using hh

theorem row_bounds (i : Fin n) (a : Fin 4 × Bool) :
    0 ≤ D.rowCount i a ∧ D.rowCount i a ≤ D.rowSize a := by
  dsimp only [rowCount, rowSize]
  constructor
  · exact Nat.cast_nonneg _
  · exact_mod_cast F.singleNeighborCount_le (D.point i) a

theorem row_same_sign_zero (i : Fin n) (a : Fin 4 × Bool)
    (hs : D.rowCode i a.1 = if a.2 then 1 else -1) : D.rowCount i a = 0 := by
  have hc : F.code a.1 (D.point i) = if a.2 then 1 else -1 := by
    rw [D.point_code]
    exact hs
  dsimp only [rowCount]
  exact_mod_cast F.singleNeighborCount_zero_same_sign a hc

theorem row_degree (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) (i : Fin n) :
    ((D.rowNeighbors i).card : ℤ) + ∑ a, D.rowCount i a =
      2 + 3 * signatureWeight (D.word i) := by
  have hh := F.zero_case_row_degree h hz (Finset.mem_filter.mp (D.point_mem i)).1
  have he := D.filtered_card hc (G.Adj (D.point i))
  change (D.rowNeighbors i).card = _ at he
  rw [← he, D.point_weight i] at hh
  norm_num only [Int.toNat_natCast] at hh
  dsimp only [rowCount]
  exact_mod_cast hh

theorem row_moment (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (i : Fin n) (k : Fin 4) :
    (∑ j ∈ D.rowNeighbors i, D.rowCode j k) +
      ∑ a : Fin 4 × Bool, D.rowCount i a *
        (if k = a.1 then (if a.2 then 1 else -1) else 0) = -4 * D.rowCode i k := by
  have hh := F.zero_case_row_moment hz (D.point i) k
  have he := D.filtered_code_sum hc (G.Adj (D.point i)) k
  rw [← he, D.point_code i k] at hh
  exact hh

theorem row_common_card (hc : F.HasSignedCells) (i j : Fin n) :
    (D.rowNeighbors i ∩ D.rowNeighbors j).card =
      (F.coreVertices.filter (fun u => G.Adj (D.point i) u ∧ G.Adj (D.point j) u)).card := by
  have heq : D.rowNeighbors i ∩ D.rowNeighbors j =
      Finset.univ.filter (fun k => G.Adj (D.point i) (D.point k) ∧ G.Adj (D.point j) (D.point k)) := by
    ext k
    simp [rowNeighbors]
  rw [heq]
  exact D.filtered_card hc (fun u => G.Adj (D.point i) u ∧ G.Adj (D.point j) u)

theorem row_common_lower (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) {i j : Fin n} (hij : i ≠ j) :
    ((D.rowNeighbors i ∩ D.rowNeighbors j).card : ℤ) +
      (∑ a : Fin 4 × Bool, max 0 (D.rowCount i a + D.rowCount j a - D.rowSize a)) ≤
      if j ∈ D.rowNeighbors i then 1 else 2 := by
  have hh := F.zero_case_row_common_budget_int h hz (D.point_injective.ne hij)
  rw [← D.row_common_card hc i j] at hh
  simpa only [rowNeighbors, rowCount, rowSize, Finset.mem_filter, Finset.mem_univ, true_and] using hh

theorem row_common_upper (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) {i j : Fin n} (hij : i ≠ j)
    (hno : ∀ k, D.rowCode i k ≠ 0 ∨ D.rowCode j k ≠ 0) :
    (if j ∈ D.rowNeighbors i then (1 : ℤ) else 2) ≤
      ((D.rowNeighbors i ∩ D.rowNeighbors j).card : ℤ) +
        ∑ a : Fin 4 × Bool, min (D.rowCount i a) (D.rowCount j a) := by
  have hh := F.zero_case_row_common_upper_int h hz (D.point_injective.ne hij)
    (by intro k; simpa only [D.point_code] using hno k)
  rw [← D.row_common_card hc i j] at hh
  simpa only [rowNeighbors, rowCount, Finset.mem_filter, Finset.mem_univ, true_and] using hh

#print axioms row_degree
#print axioms row_moment
#print axioms row_common_lower
#print axioms row_common_upper

end CoreSignatureData
end Conway99
