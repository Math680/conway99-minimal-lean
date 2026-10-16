import FourDirectionRootBridge
import FourDirectionSignatures

/-! Four actual root directions retain the signed one-point cells. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem fourDirectionSystemOfRoots_hasSignedCells (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (r : Fin 4 → V → ℚ) (hr : ∀ i, r i ∈ canonicalLift G H)
    (hn : ∀ i, codePair (r i) (r i) = 2)
    (hne : ∀ i j, i ≠ j → r i ≠ r j)
    (hnopp : ∀ i j, i ≠ j → r i ≠ -r j) :
    (fourDirectionSystemOfRoots G h H hH r hr hn hne hnopp).HasSignedCells := by
  unfold fourDirectionSystemOfRoots
  exact cross_orthogonal_signed_cells G h _ _ _ _ _

theorem canonicalLift_four_root_signed_cover (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (r : Fin 4 → V → ℚ) (hr : ∀ i, r i ∈ canonicalLift G H)
    (hn : ∀ i, codePair (r i) (r i) = 2)
    (hne : ∀ i j, i ≠ j → r i ≠ r j)
    (hnopp : ∀ i j, i ≠ j → r i ≠ -r j) :
    let F := fourDirectionSystemOfRoots G h H hH r hr hn hne hnopp
    F.HasSignedCells ∧ F.W.card = 39 ∧ F.weightCount 0 ≤ 1 := by
  exact ⟨fourDirectionSystemOfRoots_hasSignedCells G h H hH r hr hn hne hnopp,
    canonicalLift_four_root_cover G h H hH r hr hn hne hnopp⟩

theorem canonicalLift_root_rank_four_signed_cover (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (hrank : Module.finrank ℚ (rootSubspace G H) = 4) :
    ∃ F : FourDirectionSystem G,
      F.HasSignedCells ∧ F.W.card = 39 ∧ F.weightCount 0 ≤ 1 := by
  classical
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (canonicalLiftRoots G H)
  have hrank' : Module.finrank ℚ (Submodule.span ℚ (canonicalLiftRoots G H)) = 4 := hrank
  rw [hrank'] at hex
  obtain ⟨r, hr, _hspan, hli⟩ := hex
  have hne (i j : Fin 4) (hij : i ≠ j) : r i ≠ r j := fun heq => hij (hli.injective heq)
  have hnopp (i j : Fin 4) (hij : i ≠ j) : r i ≠ -r j := by
    intro heq
    exact hij (hli.eq_of_smul_apply_eq_smul_apply (1 : ℚ) (-1 : ℚ) i j
      (by norm_num) (by simpa using heq))
  exact ⟨fourDirectionSystemOfRoots G h H hH r (fun i => (hr i).1) (fun i => (hr i).2)
      hne hnopp,
    canonicalLift_four_root_signed_cover G h H hH r (fun i => (hr i).1)
      (fun i => (hr i).2) hne hnopp⟩

#print axioms fourDirectionSystemOfRoots_hasSignedCells
#print axioms canonicalLift_root_rank_four_signed_cover

end Conway99
