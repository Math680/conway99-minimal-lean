import FourDirectionsGeometry

/-! Signed cells of four genuine orthogonal root directions.
These one-point cells retain the information needed for both finite cases. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def signedCodeSupport (b : V → ℤ) (s : Bool) : Finset V :=
  if s then positiveCodeSupport b else negativeCodeSupport b

theorem rootSignedHoffman_eq_union (b : V → ℤ) (s : Bool) :
    rootSignedHoffman G b s = signedCodeSupport b s ∪ rootIsolated G b := by
  cases s <;> rfl

theorem signedCodeSupport_subset (b : V → ℤ) (s : Bool) :
    signedCodeSupport b s ⊆ rootSupport b := by
  cases s
  · exact Finset.subset_union_right
  · exact Finset.subset_union_left

theorem signedCodeSupport_mem (b : V → ℤ) (s : Bool) (u : V) :
    u ∈ signedCodeSupport b s ↔ b u = if s then 1 else -1 := by
  cases s <;> simp [signedCodeSupport, positiveCodeSupport, negativeCodeSupport]

namespace FourDirectionSystem

variable {G} (F : FourDirectionSystem G)

def HasSignedCells : Prop := ∀ i j : Fin 4, i ≠ j → ∀ s t : Bool,
  (signedCodeSupport (F.code i) s ∩ signedCodeSupport (F.code j) t).card = 1

theorem signed_cell_unique (hc : F.HasSignedCells) (i j : Fin 4) (hij : i ≠ j)
    (s t : Bool) {u v : V}
    (hu : F.code i u = if s then 1 else -1)
    (hu' : F.code j u = if t then 1 else -1)
    (hv : F.code i v = if s then 1 else -1)
    (hv' : F.code j v = if t then 1 else -1) : u = v := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hc i j hij s t)
  have hmu : u ∈ signedCodeSupport (F.code i) s ∩ signedCodeSupport (F.code j) t :=
    Finset.mem_inter.mpr ⟨(signedCodeSupport_mem _ _ _).mpr hu,
      (signedCodeSupport_mem _ _ _).mpr hu'⟩
  have hmv : v ∈ signedCodeSupport (F.code i) s ∩ signedCodeSupport (F.code j) t :=
    Finset.mem_inter.mpr ⟨(signedCodeSupport_mem _ _ _).mpr hv,
      (signedCodeSupport_mem _ _ _).mpr hv'⟩
  rw [ha, Finset.mem_singleton] at hmu hmv
  exact hmu.trans hmv.symm

theorem equal_nonzero_coordinates_unique (hc : F.HasSignedCells)
    (i j : Fin 4) (hij : i ≠ j) {u v : V}
    (hi : F.code i u ≠ 0) (hj : F.code j u ≠ 0)
    (hei : F.code i u = F.code i v) (hej : F.code j u = F.code j v) : u = v := by
  rcases (F.biplane i).signs u with hmi | hzi | hpi
  · rcases (F.biplane j).signs u with hmj | hzj | hpj
    · exact F.signed_cell_unique hc i j hij false false hmi hmj (hei.symm.trans hmi) (hej.symm.trans hmj)
    · exact (hj hzj).elim
    · exact F.signed_cell_unique hc i j hij false true hmi hpj (hei.symm.trans hmi) (hej.symm.trans hpj)
  · exact (hi hzi).elim
  · rcases (F.biplane j).signs u with hmj | hzj | hpj
    · exact F.signed_cell_unique hc i j hij true false hpi hmj (hei.symm.trans hpi) (hej.symm.trans hmj)
    · exact (hj hzj).elim
    · exact F.signed_cell_unique hc i j hij true true hpi hpj (hei.symm.trans hpi) (hej.symm.trans hpj)

end FourDirectionSystem

theorem cross_orthogonal_signed_cells
    (h : G.IsSRGWith 99 14 1 2) (b : Fin 4 → V → ℤ)
    (hb : ∀ i, SignedBiplaneCode G (b i))
    (hE : ∀ i, (fun u => (b i u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ i u, (∑ v, if G.Adj u v then b i v else 0) = -4 * b i u)
    (ho : ∀ i j, i ≠ j → ∀ s : Bool,
      codePair (hoffmanCocliqueCode G (rootSignedHoffman G (b i) s))
        ((3 : ℚ) • (fun u => (b j u : ℚ))) = 0) :
    (fourDirectionSystem_of_cross_orthogonal G h b hb hE he ho).HasSignedCells := by
  intro i j hij s t
  let F := fourDirectionSystem_of_cross_orthogonal G h b hb hE he ho
  have hp := hoffman_orthogonal_root_intersections G h (b j) (hb j) (hE j) (he j)
    (rootSignedHoffman G (b i) s)
    (rootSignedHoffman_specs G h (b i) (hb i) (he i) s).2
    (rootSignedHoffman_specs G h (b i) (hb i) (he i) s).1 (ho i j hij s)
  have hd : Disjoint (rootIsolated G (b i)) (signedCodeSupport (b j) t) := by
    exact (Finset.disjoint_of_subset_left (signedCodeSupport_subset (b j) t)
      (F.support_avoids_isolated j i)).symm
  have heq : rootSignedHoffman G (b i) s ∩ signedCodeSupport (b j) t =
      signedCodeSupport (b i) s ∩ signedCodeSupport (b j) t := by
    rw [rootSignedHoffman_eq_union, Finset.union_inter_distrib_right,
      Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.union_empty]
  change (signedCodeSupport (b i) s ∩ signedCodeSupport (b j) t).card = 1
  rw [← heq]
  cases t
  · exact hp.2.1
  · exact hp.1

#print axioms cross_orthogonal_signed_cells
#print axioms FourDirectionSystem.equal_nonzero_coordinates_unique

end Conway99
