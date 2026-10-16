import ZeroCaseSupportSizes

/-! A complete list of distinct core words determines actual core vertices.
This transports finite row certificates to the graph without adding an
unproved labelling or adjacency realization assumption. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

structure CoreSignatureData (F : FourDirectionSystem G) (n : ℕ) where
  word : Fin n → RootSignature
  injective : Function.Injective word
  cover : Finset.univ.image word = F.coreSignatures

namespace CoreSignatureData

variable {F : FourDirectionSystem G} {n : ℕ} (D : CoreSignatureData F n)

theorem exists_point (k : Fin n) : ∃ u ∈ F.coreVertices, F.signature u = D.word k := by
  have hm : D.word k ∈ F.coreSignatures := by
    rw [← D.cover]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  exact Finset.mem_image.mp hm

noncomputable def point (k : Fin n) : V := Classical.choose (D.exists_point k)

theorem point_mem (k : Fin n) : D.point k ∈ F.coreVertices :=
  (Classical.choose_spec (D.exists_point k)).1

theorem point_signature (k : Fin n) : F.signature (D.point k) = D.word k :=
  (Classical.choose_spec (D.exists_point k)).2

theorem point_injective : Function.Injective D.point := by
  intro i j he
  apply D.injective
  rw [← D.point_signature i, ← D.point_signature j, he]

theorem point_surjective (hc : F.HasSignedCells) {u : V} (hu : u ∈ F.coreVertices) :
    ∃ k, D.point k = u := by
  have hm : F.signature u ∈ F.coreSignatures := Finset.mem_image.mpr ⟨u, hu, rfl⟩
  rw [← D.cover] at hm
  obtain ⟨k, hk, hku⟩ := Finset.mem_image.mp hm
  refine ⟨k, ?_⟩
  apply F.coreSignatures_injective hc (D.point_mem k) hu
  exact (D.point_signature k).trans hku

theorem point_code (k : Fin n) (i : Fin 4) :
    F.code i (D.point k) = ((D.word k i).val : ℤ) - 1 := by
  have hs := F.signature_val (D.point k) i
  rw [D.point_signature k] at hs
  omega

theorem filtered_card (hc : F.HasSignedCells) (p : V → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun k => p (D.point k))).card = (F.coreVertices.filter p).card := by
  apply Finset.card_bij (fun k _ => D.point k)
  · intro k hk
    exact Finset.mem_filter.mpr ⟨D.point_mem k, (Finset.mem_filter.mp hk).2⟩
  · intro i hi j hj hij
    exact D.point_injective hij
  · intro u hu
    obtain ⟨k, rfl⟩ := D.point_surjective hc (Finset.mem_filter.mp hu).1
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩, rfl⟩

theorem filtered_code_sum (hc : F.HasSignedCells) (p : V → Prop) [DecidablePred p]
    (i : Fin 4) :
    (∑ k ∈ Finset.univ.filter (fun k => p (D.point k)), (((D.word k i).val : ℤ) - 1)) =
      ∑ u ∈ F.coreVertices.filter p, F.code i u := by
  apply Finset.sum_bij (fun k _ => D.point k)
  · intro k hk
    exact Finset.mem_filter.mpr ⟨D.point_mem k, (Finset.mem_filter.mp hk).2⟩
  · intro i hi j hj hij
    exact D.point_injective hij
  · intro u hu
    obtain ⟨k, rfl⟩ := D.point_surjective hc (Finset.mem_filter.mp hu).1
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩, rfl⟩
  · intro k hk
    exact (D.point_code k i).symm

#print axioms point_surjective
#print axioms filtered_card
#print axioms filtered_code_sum

end CoreSignatureData
end Conway99
