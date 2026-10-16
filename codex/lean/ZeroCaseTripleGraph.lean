import ZeroCaseTripleCommon
import ZeroCaseHighForced

/-! The two non-residual high arrays contradict actual singleton-class
incidences. The closed theorems derive the arrays from HighConfiguration. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

theorem normalized_orbit_one_impossible_of_forced (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hrep : F.highSignatures = zeroCaseOrbitRepresentative 1)
    (hN : F.actualHighNeighbors hc 1 hrep = ZeroHighRows.orbitOneNeighbors)
    (hC : F.actualHighCounts hc 1 hrep = ZeroHighRows.orbitOneCounts) : False := by
  apply ZeroCaseTriple.orbit_one_singletons_impossible F.positiveSingleClasses
    (F.tripleNeighborhood hc 1 hrep (by decide)) F.positiveSingle_disjoint
  · intro k
    change (F.singleClass (k,true)).card = _
    rw [F.singleClass_card_of_representative hc 1 hrep]
    revert k
    decide
  · intro k i
    have hm := F.triple_margins_count hc 1 hrep (by decide) k i
    rw [hC] at hm
    have ht : ZeroHighRows.orbitOneCounts (F.firstFourHigh 1 (by decide) i) (ZeroHighRows.plus k) =
        (ZeroCaseTriple.marginsOne k i : ℤ) := by
      clear hm
      dsimp only [firstFourHigh]
      revert k i
      decide
    exact_mod_cast hm.trans ht
  · intro p hp
    have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
    have hb := F.triple_common_budget h hc 1 hrep (by decide) p.1 p.2 hne
    rw [hN] at hb
    have ht :
        (ZeroHighRows.orbitOneNeighbors (F.firstFourHigh 1 (by decide) p.1) ∩
          ZeroHighRows.orbitOneNeighbors (F.firstFourHigh 1 (by decide) p.2)).card +
          ZeroCaseTriple.budgetsOne p.1 p.2 =
          if zeroCaseHighIndex 1 (F.firstFourHigh 1 (by decide) p.2) ∈
            ZeroHighRows.orbitOneNeighbors (F.firstFourHigh 1 (by decide) p.1) then 1 else 2 := by
      have hall : ∀ q ∈ ZeroCaseTriple.pairs,
          (ZeroHighRows.orbitOneNeighbors (F.firstFourHigh 1 (by decide) q.1) ∩
            ZeroHighRows.orbitOneNeighbors (F.firstFourHigh 1 (by decide) q.2)).card +
            ZeroCaseTriple.budgetsOne q.1 q.2 =
            if zeroCaseHighIndex 1 (F.firstFourHigh 1 (by decide) q.2) ∈
              ZeroHighRows.orbitOneNeighbors (F.firstFourHigh 1 (by decide) q.1) then 1 else 2 := by
        dsimp only [firstFourHigh]
        decide
      exact hall p hp
    rw [← ht] at hb
    exact Nat.le_of_add_le_add_left hb

theorem normalized_orbit_three_impossible_of_forced (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hrep : F.highSignatures = zeroCaseOrbitRepresentative 3)
    (hN : F.actualHighNeighbors hc 3 hrep = ZeroHighRows.orbitThreeNeighbors)
    (hC : F.actualHighCounts hc 3 hrep = ZeroHighRows.orbitThreeCounts) : False := by
  apply ZeroCaseTriple.orbit_three_singletons_impossible F.positiveSingleClasses
    (F.tripleNeighborhood hc 3 hrep (by decide)) F.positiveSingle_disjoint
  · intro k
    change (F.singleClass (k,true)).card = _
    rw [F.singleClass_card_of_representative hc 3 hrep]
    revert k
    decide
  · intro k i
    have hm := F.triple_margins_count hc 3 hrep (by decide) k i
    rw [hC] at hm
    have ht : ZeroHighRows.orbitThreeCounts (F.firstFourHigh 3 (by decide) i) (ZeroHighRows.plus k) =
        (ZeroCaseTriple.marginsThree k i : ℤ) := by
      clear hm
      dsimp only [firstFourHigh]
      revert k i
      decide
    exact_mod_cast hm.trans ht
  · intro p hp
    have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
    have hb := F.triple_common_budget h hc 3 hrep (by decide) p.1 p.2 hne
    rw [hN] at hb
    have ht :
        (ZeroHighRows.orbitThreeNeighbors (F.firstFourHigh 3 (by decide) p.1) ∩
          ZeroHighRows.orbitThreeNeighbors (F.firstFourHigh 3 (by decide) p.2)).card +
          ZeroCaseTriple.budgetsThree p.1 p.2 =
          if zeroCaseHighIndex 3 (F.firstFourHigh 3 (by decide) p.2) ∈
            ZeroHighRows.orbitThreeNeighbors (F.firstFourHigh 3 (by decide) p.1) then 1 else 2 := by
      have hall : ∀ q ∈ ZeroCaseTriple.pairs,
          (ZeroHighRows.orbitThreeNeighbors (F.firstFourHigh 3 (by decide) q.1) ∩
            ZeroHighRows.orbitThreeNeighbors (F.firstFourHigh 3 (by decide) q.2)).card +
            ZeroCaseTriple.budgetsThree q.1 q.2 =
            if zeroCaseHighIndex 3 (F.firstFourHigh 3 (by decide) q.2) ∈
              ZeroHighRows.orbitThreeNeighbors (F.firstFourHigh 3 (by decide) q.1) then 1 else 2 := by
        dsimp only [firstFourHigh]
        decide
      exact hall p hp
    rw [← ht] at hb
    exact Nat.le_of_add_le_add_left hb

theorem normalized_orbit_one_impossible (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative 1) : False := by
  let C := F.actualHighConfiguration hc 1 hrep h hz
  exact F.normalized_orbit_one_impossible_of_forced h hc hrep
    (ZeroHighRows.high_configuration_one_neighbors C) (ZeroHighRows.high_configuration_one_counts C)

theorem normalized_orbit_three_impossible (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative 3) : False := by
  let C := F.actualHighConfiguration hc 3 hrep h hz
  exact F.normalized_orbit_three_impossible_of_forced h hc hrep
    (ZeroHighRows.high_configuration_three_neighbors C) (ZeroHighRows.high_configuration_three_counts C)

#print axioms normalized_orbit_one_impossible
#print axioms normalized_orbit_three_impossible

end FourDirectionSystem
end Conway99
