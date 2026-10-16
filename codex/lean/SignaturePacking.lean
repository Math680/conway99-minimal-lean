import FourDirectionSignatures

/-! The actual graph supplies a finite packing of ternary signatures.
In particular, repeated heavy signatures are impossible; this is not
an abstract packing assumption on unrelated words. -/

namespace Conway99

open scoped BigOperators

abbrev RootSignature := Fin 4 → Fin 3

def signatureCells (w : RootSignature) : Finset (Fin 4 × Fin 4 × Fin 3 × Fin 3) :=
  ((Finset.univ.product Finset.univ).filter
    (fun p : Fin 4 × Fin 4 => p.1 < p.2 ∧ w p.1 ≠ 1 ∧ w p.2 ≠ 1)).image
      (fun p => (p.1, p.2, w p.1, w p.2))

def signatureWeight (w : RootSignature) : ℕ :=
  ((Finset.univ : Finset (Fin 4)).filter (fun i => w i ≠ 1)).card

def tripleSignatures : Finset RootSignature := Finset.univ.filter (fun w => signatureWeight w = 3)

def fullSignatures : Finset RootSignature := Finset.univ.filter (fun w => signatureWeight w = 4)

theorem tripleSignatures_card : tripleSignatures.card = 32 := by decide

theorem fullSignatures_card : fullSignatures.card = 16 := by decide

namespace FourDirectionSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

def signature (u : V) : RootSignature := fun i =>
  ⟨(F.code i u + 1).toNat, by
    rcases (F.biplane i).signs u with hz | hz | hz <;> simp [hz]⟩

theorem signature_val (u : V) (i : Fin 4) :
    ((F.signature u i).val : ℤ) = F.code i u + 1 := by
  dsimp only [signature]
  rcases (F.biplane i).signs u with hz | hz | hz <;> simp [hz]

theorem signature_nonzero_iff (u : V) (i : Fin 4) :
    F.signature u i ≠ 1 ↔ F.code i u ≠ 0 := by
  have hv := F.signature_val u i
  constructor
  · intro hh hz
    apply hh
    apply Fin.ext
    change (F.signature u i).val = 1
    omega
  · intro hh hz
    have hh' := congrArg Fin.val hz
    norm_num at hh'
    omega

theorem signature_active_card (u : V) :
    (((Finset.univ : Finset (Fin 4)).filter (fun i => F.signature u i ≠ 1)).card : ℤ) =
      F.weight u := by
  have hp (i : Fin 4) : (F.signature u i ≠ 1) ↔ u ∈ rootSupport (F.code i) := by
    rw [F.signature_nonzero_iff]
    rcases (F.biplane i).signs u with hz | hz | hz <;>
      simp [rootSupport, positiveCodeSupport, negativeCodeSupport, hz]
  simp_rw [hp]
  simp [weight]

theorem signature_equal_code {u v : V} (hs : F.signature u = F.signature v) (i : Fin 4) :
    F.code i u = F.code i v := by
  have hh := congrArg (fun w : RootSignature => ((w i).val : ℤ)) hs
  change ((F.signature u i).val : ℤ) = ((F.signature v i).val : ℤ) at hh
  rw [F.signature_val, F.signature_val] at hh
  omega

theorem signature_injective_on_heavy (hc : F.HasSignedCells) :
    Set.InjOn F.signature {u | 2 ≤ F.weight u} := by
  intro u hu v hv heq
  change 2 ≤ F.weight u at hu
  change 2 ≤ F.weight v at hv
  have hcard : 1 < ((Finset.univ : Finset (Fin 4)).filter
      (fun i => F.signature u i ≠ 1)).card := by
    have hh := F.signature_active_card u
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  apply F.equal_nonzero_coordinates_unique hc i j hij
  · exact (F.signature_nonzero_iff u i).mp (Finset.mem_filter.mp hi).2
  · exact (F.signature_nonzero_iff u j).mp (Finset.mem_filter.mp hj).2
  · exact F.signature_equal_code heq i
  · exact F.signature_equal_code heq j

theorem distinct_signature_cells_disjoint (hc : F.HasSignedCells) {u v : V}
    (hne : u ≠ v) : Disjoint (signatureCells (F.signature u)) (signatureCells (F.signature v)) := by
  apply Finset.disjoint_left.mpr
  intro c hcu hcv
  obtain ⟨⟨i,j⟩, hij, heq⟩ := Finset.mem_image.mp hcu
  obtain ⟨⟨k,l⟩, hkl, heq'⟩ := Finset.mem_image.mp hcv
  have he : (i,j,F.signature u i,F.signature u j) =
      (k,l,F.signature v k,F.signature v l) := heq.trans heq'.symm
  have hik : i = k := congrArg Prod.fst he
  have hjl : j = l := congrArg (fun x => x.2.1) he
  subst k; subst l
  have hsi : F.signature u i = F.signature v i := congrArg (fun x => x.2.2.1) he
  have hsj : F.signature u j = F.signature v j := congrArg (fun x => x.2.2.2) he
  have hcij := (Finset.mem_filter.mp hij).2
  apply hne
  apply F.equal_nonzero_coordinates_unique hc i j (ne_of_lt hcij.1)
  · exact (F.signature_nonzero_iff u i).mp hcij.2.1
  · exact (F.signature_nonzero_iff u j).mp hcij.2.2
  · have hh := congrArg (fun a : Fin 3 => (a.val : ℤ)) hsi
    change ((F.signature u i).val : ℤ) = ((F.signature v i).val : ℤ) at hh
    rw [F.signature_val, F.signature_val] at hh
    omega
  · have hh := congrArg (fun a : Fin 3 => (a.val : ℤ)) hsj
    change ((F.signature u j).val : ℤ) = ((F.signature v j).val : ℤ) at hh
    rw [F.signature_val, F.signature_val] at hh
    omega

def highSignatureVertices : Finset V := F.W.filter (fun u => 3 ≤ F.weight u)

def highSignatures : Finset RootSignature := F.highSignatureVertices.image F.signature

theorem highSignatures_card (hc : F.HasSignedCells) :
    F.highSignatures.card = F.highSignatureVertices.card := by
  apply Finset.card_image_of_injOn
  intro u hu v hv heq
  exact F.signature_injective_on_heavy hc
    (by change 2 ≤ F.weight u; have := (Finset.mem_filter.mp hu).2; omega)
    (by change 2 ≤ F.weight v; have := (Finset.mem_filter.mp hv).2; omega) heq

theorem highSignatures_packing (hc : F.HasSignedCells) :
    (F.highSignatures : Set RootSignature).Pairwise
      (fun w z => Disjoint (signatureCells w) (signatureCells z)) := by
  intro w hw z hz hwz
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  exact F.distinct_signature_cells_disjoint hc (fun heq => hwz (congrArg F.signature heq))

theorem highSignatures_weight_count (hc : F.HasSignedCells) (k : ℕ) (hk : 3 ≤ k) :
    (F.highSignatures.filter (fun w => signatureWeight w = k)).card = F.weightCount k := by
  have heq : F.highSignatures.filter (fun w => signatureWeight w = k) =
      (F.W.filter (fun u => F.weight u = k)).image F.signature := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw, hkw⟩ := Finset.mem_filter.mp hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hs := F.signature_active_card u
      change (signatureWeight (F.signature u) : ℤ) = F.weight u at hs
      apply Finset.mem_image.mpr
      refine ⟨u, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, ?_⟩, rfl⟩
      rw [← hs, hkw]
    · intro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hkw := (Finset.mem_filter.mp hu).2
      have hs := F.signature_active_card u
      change (signatureWeight (F.signature u) : ℤ) = F.weight u at hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨u, ?_, rfl⟩, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨(Finset.mem_filter.mp hu).1, by omega⟩
      · omega
  rw [heq, Finset.card_image_of_injOn]
  · rfl
  · intro u hu v hv huv
    apply F.signature_injective_on_heavy hc ?_ ?_ huv
    · change 2 ≤ F.weight u
      have := (Finset.mem_filter.mp hu).2
      omega
    · change 2 ≤ F.weight v
      have := (Finset.mem_filter.mp hv).2
      omega

theorem highSignatures_weights {w : RootSignature} (hw : w ∈ F.highSignatures) :
    signatureWeight w = 3 ∨ signatureWeight w = 4 := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  have hs := F.signature_active_card u
  change (signatureWeight (F.signature u) : ℤ) = F.weight u at hs
  have hlo := (Finset.mem_filter.mp hu).2
  have hhi := F.weight_le_four u
  omega

theorem highSignatureVertices_card :
    F.highSignatureVertices.card = F.weightCount 3 + F.weightCount 4 := by
  have heq : F.highSignatureVertices =
      (F.W.filter (fun u => F.weight u = 3)) ∪ (F.W.filter (fun u => F.weight u = 4)) := by
    ext u
    have hlo := F.weight_nonneg u
    have hhi := F.weight_le_four u
    simp only [highSignatureVertices, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hw, hl⟩
      by_cases he : F.weight u = 3
      · exact Or.inl ⟨hw, he⟩
      · exact Or.inr ⟨hw, by omega⟩
    · rintro (⟨hw, he⟩ | ⟨hw, he⟩) <;> exact ⟨hw, by omega⟩
  have hd : Disjoint (F.W.filter (fun u => F.weight u = 3))
      (F.W.filter (fun u => F.weight u = 4)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    omega
  rw [heq, Finset.card_union_of_disjoint hd]
  rfl

theorem zero_case_high_counts (h : G.IsSRGWith 99 14 1 2) (hz : F.weightCount 0 = 0) :
    (F.weightCount 4 = 0 ∧ F.weightCount 3 = 7) ∨
    (F.weightCount 4 = 1 ∧ F.weightCount 3 = 4) ∨
    (F.weightCount 4 = 2 ∧ F.weightCount 3 = 1) := by
  have hh := F.weight_count_balance h
  omega

theorem zero_full_highSignatures_triples
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) (hf : F.weightCount 4 = 0) :
    F.highSignatures.card = 7 ∧ F.highSignatures ⊆ tripleSignatures := by
  have hb := F.weight_count_balance h
  have ht : F.weightCount 3 = 7 := by omega
  refine ⟨?_, ?_⟩
  · rw [F.highSignatures_card hc, F.highSignatureVertices_card, ht, hf]
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have hwu := (Finset.mem_filter.mp hu).1
    have hlo := (Finset.mem_filter.mp hu).2
    have hhi := F.weight_le_four u
    have hnot : F.weight u ≠ 4 := by
      intro heq
      have hm : u ∈ F.W.filter (fun u => F.weight u = 4) := Finset.mem_filter.mpr ⟨hwu, heq⟩
      have he : F.W.filter (fun u => F.weight u = 4) = ∅ := Finset.card_eq_zero.mp hf
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    have hh : F.weight u = 3 := by omega
    have hsig := F.signature_active_card u
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change signatureWeight (F.signature u) = 3
    change (signatureWeight (F.signature u) : ℤ) = F.weight u at hsig
    omega

#print axioms signature_injective_on_heavy
#print axioms highSignatures_packing
#print axioms zero_full_highSignatures_triples

end FourDirectionSystem
end Conway99
