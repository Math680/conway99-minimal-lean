import ZeroCaseActualHighConfiguration
import ZeroCaseHighForced
import ZeroCaseResidualGraph

/-! The fifth normalized packing is impossible in the actual graph.
The previously explicit residual high tables are now derived from the complete
high-row certificate; no table or row-model hypothesis remains. -/

namespace Conway99.ZeroResidual

theorem highIndex_eq_shared (h : Fin 3) : highIndex h = zeroCaseHighIndex 4 h := rfl
theorem doubleIndex_eq_shared (i : Fin 9) : doubleIndex i = zeroCaseDoubleIndex 4 i := rfl
theorem group_eq_highGroup (g : Fin 8) : group g = ZeroHighRows.group g := rfl

theorem forced_high_no_high (a b : Fin 3) :
    highIndex b ∉ ZeroHighRows.orbitFourNeighbors a := by revert a b; decide

theorem forced_high_doubles (a : Fin 3) (i : Fin 9) :
    doubleIndex i ∈ ZeroHighRows.orbitFourNeighbors a ↔ i ∈ highDoubles a := by
  revert a i
  decide

theorem forced_high_counts (a : Fin 3) (g : Fin 8) :
    ZeroHighRows.orbitFourCounts a g = highCounts a g := by revert a g; decide

end Conway99.ZeroResidual

namespace Conway99.FourDirectionSystem
open ZeroResidual

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

theorem zero_case_orbit_four_impossible (h : G.IsSRGWith 99 14 1 2)
    (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0)
    (hrep : F.highSignatures = zeroCaseOrbitRepresentative 4) : False := by
  let D : CoreSignatureData F 12 := F.coreSignatureData_of_representative hc 4 hrep
  let C : ZeroHighRows.HighConfiguration 4 := F.actualHighConfiguration hc 4 hrep h hz
  have hneighbors (a : Fin 3) : D.rowNeighbors (highIndex a) = ZeroHighRows.orbitFourNeighbors a := by
    have hh := congrFun (ZeroHighRows.high_configuration_four_neighbors C) a
    simpa only [C, actualHighConfiguration, actualHighNeighbors, D, highIndex_eq_shared] using hh
  have hcounts (a : Fin 3) (g : Fin 8) : D.rowCount (highIndex a) (group g) = highCounts a g := by
    have hh := congrFun (congrFun (ZeroHighRows.high_configuration_four_counts C) a) g
    change D.rowCount (zeroCaseHighIndex 4 a) (ZeroHighRows.group g) = _ at hh
    rw [← highIndex_eq_shared, ← group_eq_highGroup] at hh
    exact hh.trans (forced_high_counts a g)
  apply F.residual_graph_impossible h hc hz hrep
  · intro a b
    change highIndex b ∉ D.rowNeighbors (highIndex a)
    rw [hneighbors a]
    exact forced_high_no_high a b
  · intro a i
    change doubleIndex i ∈ D.rowNeighbors (highIndex a) ↔ i ∈ highDoubles a
    rw [hneighbors a]
    exact forced_high_doubles a i
  · exact hcounts

#print axioms zero_case_orbit_four_impossible

end Conway99.FourDirectionSystem
