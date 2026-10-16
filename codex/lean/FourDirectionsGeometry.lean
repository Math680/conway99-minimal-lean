import FourDirectionsCover

/-! Construction of the four-direction geometry from actual signed root biplanes
and the cross-Hoffman orthogonality already obtained from single activity. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rootSupport_disjoint_isolated (b : V → ℤ) :
    Disjoint (rootSupport b) (rootIsolated G b) := by
  apply Finset.disjoint_left.mpr
  intro u hu hi
  have hz := (Finset.mem_filter.mp hi).2.1
  rcases Finset.mem_union.mp hu with hp | hn
  · have hh := (Finset.mem_filter.mp hp).2
    omega
  · have hh := (Finset.mem_filter.mp hn).2
    omega

noncomputable def fourDirectionSystem_of_cross_orthogonal
    (h : G.IsSRGWith 99 14 1 2) (b : Fin 4 → V → ℤ)
    (hb : ∀ i, SignedBiplaneCode G (b i))
    (hE : ∀ i, (fun u => (b i u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ i u, (∑ v, if G.Adj u v then b i v else 0) = -4 * b i u)
    (ho : ∀ i j, i ≠ j → ∀ s : Bool,
      codePair (hoffmanCocliqueCode G (rootSignedHoffman G (b i) s))
        ((3 : ℚ) • (fun u => (b j u : ℚ))) = 0) : FourDirectionSystem G := by
  have hp (i j : Fin 4) (hij : i ≠ j) (s : Bool) :=
    hoffman_orthogonal_root_intersections G h (b j) (hb j) (hE j) (he j)
      (rootSignedHoffman G (b i) s)
      (rootSignedHoffman_specs G h (b i) (hb i) (he i) s).2
      (rootSignedHoffman_specs G h (b i) (hb i) (he i) s).1 (ho i j hij s)
  have hsI (i j : Fin 4) : Disjoint (rootSupport (b i)) (rootIsolated G (b j)) := by
    by_cases hij : i = j
    · subst j
      exact rootSupport_disjoint_isolated G (b i)
    · apply Finset.disjoint_left.mpr
      intro u hu hv
      rcases Finset.mem_union.mp hu with hu | hu
      · have hmem : u ∈ rootSignedHoffman G (b i) true ∩ rootIsolated G (b j) := by
          exact Finset.mem_inter.mpr ⟨by simp [rootSignedHoffman, rootPositiveHoffman, hu], hv⟩
        rw [(hp i j hij true).2.2] at hmem
        exact Finset.notMem_empty _ hmem
      · have hmem : u ∈ rootSignedHoffman G (b i) false ∩ rootIsolated G (b j) := by
          exact Finset.mem_inter.mpr ⟨by simp [rootSignedHoffman, rootNegativeHoffman, hu], hv⟩
        rw [(hp i j hij false).2.2] at hmem
        exact Finset.notMem_empty _ hmem
  refine {
    code := b
    biplane := hb
    eigen := he
    support_avoids_isolated := hsI
    isolated_disjoint := ?_
    support_intersections := ?_ }
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hmem : u ∈ rootSignedHoffman G (b i) true ∩ rootIsolated G (b j) := by
      exact Finset.mem_inter.mpr ⟨by simp [rootSignedHoffman, rootPositiveHoffman, hu], hv⟩
    rw [(hp i j hij true).2.2] at hmem
    exact Finset.notMem_empty _ hmem
  · intro i j hij
    have hcard (s : Bool) :
        (rootSignedHoffman G (b i) s ∩ rootSupport (b j)).card = 2 := by
      have hd : Disjoint (positiveCodeSupport (b j)) (negativeCodeSupport (b j)) := by
        apply Finset.disjoint_left.mpr
        intro u hu hv
        have hu' := (Finset.mem_filter.mp hu).2
        have hv' := (Finset.mem_filter.mp hv).2
        omega
      rw [rootSupport, Finset.inter_union_distrib_left,
        Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hd)),
        (hp i j hij s).1, (hp i j hij s).2.1]
    have hEq : rootSupport (b i) ∩ rootSupport (b j) =
        (rootSignedHoffman G (b i) true ∩ rootSupport (b j)) ∪
        (rootSignedHoffman G (b i) false ∩ rootSupport (b j)) := by
      ext u
      have hnot : ¬ (u ∈ rootIsolated G (b i) ∧ u ∈ rootSupport (b j)) := by
        rintro ⟨hi, hc⟩
        exact Finset.disjoint_left.mp (hsI j i) hc hi
      simp only [rootSupport, rootSignedHoffman, ite_true, Bool.false_eq_true, ite_false,
        rootPositiveHoffman, rootNegativeHoffman, Finset.mem_union, Finset.mem_inter] at *
      tauto
    have hd : Disjoint
        (rootSignedHoffman G (b i) true ∩ rootSupport (b j))
        (rootSignedHoffman G (b i) false ∩ rootSupport (b j)) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      have hh : u ∈ rootPositiveHoffman G (b i) ∩ rootNegativeHoffman G (b i) := by
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hv).1⟩
      rw [root_canonical_hoffman_intersection] at hh
      exact Finset.disjoint_left.mp (hsI j i) (Finset.mem_inter.mp hu).2 hh
    rw [hEq, Finset.card_union_of_disjoint hd, hcard true, hcard false]

theorem four_cross_orthogonal_cover_at_most_one
    (h : G.IsSRGWith 99 14 1 2) (b : Fin 4 → V → ℤ)
    (hb : ∀ i, SignedBiplaneCode G (b i))
    (hE : ∀ i, (fun u => (b i u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ i u, (∑ v, if G.Adj u v then b i v else 0) = -4 * b i u)
    (ho : ∀ i j, i ≠ j → ∀ s : Bool,
      codePair (hoffmanCocliqueCode G (rootSignedHoffman G (b i) s))
        ((3 : ℚ) • (fun u => (b j u : ℚ))) = 0) :
    (fourDirectionSystem_of_cross_orthogonal G h b hb hE he ho).weightCount 0 ≤ 1 :=
  FourDirectionSystem.zero_weight_count_le_one _ h

#print axioms fourDirectionSystem_of_cross_orthogonal
#print axioms four_cross_orthogonal_cover_at_most_one

end Conway99
