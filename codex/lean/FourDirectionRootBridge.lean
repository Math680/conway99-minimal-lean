import RootRankFour
import RootSpanRank
import FourDirectionsGeometry

/-! The four-direction cover constructed directly from four actual root directions. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def fourDirectionSystemOfRoots (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (r : Fin 4 → V → ℚ) (hr : ∀ i, r i ∈ canonicalLift G H)
    (hn : ∀ i, codePair (r i) (r i) = 2)
    (hne : ∀ i j, i ≠ j → r i ≠ r j)
    (hnopp : ∀ i j, i ≠ j → r i ≠ -r j) : FourDirectionSystem G := by
  classical
  have hcodes (i : Fin 4) : ∃ b : V → ℤ,
      r i = (3 : ℚ) • (fun u => (b u : ℚ)) ∧
      (fun u => (b u : ℚ)) ∈ rationalAmbient G ∧ SignedBiplaneCode G b := by
    obtain ⟨b, heq, hE, _, _, hb⟩ := canonicalLift_root_biplane G h H (hr i) (hn i)
    exact ⟨b, heq, hE, hb⟩
  choose b heq hE hb using hcodes
  have he := fun i => integerAmbient_eigen G h (b i) (hE i)
  apply fourDirectionSystem_of_cross_orthogonal G h b hb hE he
  intro i j hij s
  have hri : (3 : ℚ) • (fun u => (b i u : ℚ)) ∈ canonicalLift G H := by rw [← heq]; exact hr i
  have hrj : (3 : ℚ) • (fun u => (b j u : ℚ)) ∈ canonicalLift G H := by rw [← heq]; exact hr j
  apply canonicalHoffman_cross_orthogonal G h H hH (b i) (hb i) (hE i) (he i) hri
  · rw [← heq]; exact hn i
  · exact hrj
  · rw [← heq]; exact hn j
  · rw [← heq, ← heq]
    exact canonicalLift_distinct_root_directions_orthogonal G h H hH (hr i) (hr j)
      (hn i) (hn j) (hne i j hij) (hnopp i j hij)

theorem canonicalLift_four_root_cover (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (r : Fin 4 → V → ℚ) (hr : ∀ i, r i ∈ canonicalLift G H)
    (hn : ∀ i, codePair (r i) (r i) = 2)
    (hne : ∀ i j, i ≠ j → r i ≠ r j)
    (hnopp : ∀ i j, i ≠ j → r i ≠ -r j) :
    let F := fourDirectionSystemOfRoots G h H hH r hr hn hne hnopp
    F.W.card = 39 ∧ F.weightCount 0 ≤ 1 := by
  let F := fourDirectionSystemOfRoots G h H hH r hr hn hne hnopp
  exact ⟨F.W_card h, F.zero_weight_count_le_one h⟩

theorem canonicalLift_root_rank_four_cover (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (hrank : Module.finrank ℚ (rootSubspace G H) = 4) :
    ∃ F : FourDirectionSystem G, F.W.card = 39 ∧ F.weightCount 0 ≤ 1 := by
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
    canonicalLift_four_root_cover G h H hH r (fun i => (hr i).1) (fun i => (hr i).2) hne hnopp⟩

#print axioms fourDirectionSystemOfRoots
#print axioms canonicalLift_four_root_cover
#print axioms canonicalLift_root_rank_four_cover

end Conway99
