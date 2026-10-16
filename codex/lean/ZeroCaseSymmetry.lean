import ZeroCaseAllPackings

/-! Signed coordinate permutations act faithfully on signatures and preserve
their occupied-cell packing condition. -/

namespace Conway99

open scoped BigOperators

abbrev SignatureSymmetry := Equiv.Perm (Fin 4) × (Fin 4 → Bool)

def signatureFlip (s : Bool) : Equiv.Perm (Fin 3) :=
  if s then Equiv.swap 0 2 else Equiv.refl _

theorem signatureFlip_one (s : Bool) : signatureFlip s 1 = 1 := by
  cases s <;> decide

theorem signatureFlip_ne_one (s : Bool) (x : Fin 3) : signatureFlip s x ≠ 1 ↔ x ≠ 1 := by
  have he : signatureFlip s x = 1 ↔ x = 1 := by
    constructor
    · intro hh
      exact (signatureFlip s).injective (hh.trans (signatureFlip_one s).symm)
    · rintro rfl
      exact signatureFlip_one s
  exact not_congr he

def signatureAct (g : SignatureSymmetry) (w : RootSignature) : RootSignature :=
  fun i => signatureFlip (g.2 i) (w (g.1 i))

def signatureSetAct (g : SignatureSymmetry) (S : Finset RootSignature) : Finset RootSignature :=
  S.image (signatureAct g)

theorem signatureAct_injective (g : SignatureSymmetry) : Function.Injective (signatureAct g) := by
  intro w z h
  funext k
  have hh := congrFun h (g.1.symm k)
  have hi := (signatureFlip (g.2 (g.1.symm k))).injective hh
  simpa only [Equiv.apply_symm_apply] using hi

theorem signatureAct_equal_iff (g : SignatureSymmetry) (w z : RootSignature) (i : Fin 4) :
    signatureAct g w i = signatureAct g z i ↔ w (g.1 i) = z (g.1 i) :=
  (signatureFlip (g.2 i)).injective.eq_iff

theorem signatureAct_nonzero_iff (g : SignatureSymmetry) (w : RootSignature) (i : Fin 4) :
    signatureAct g w i ≠ 1 ↔ w (g.1 i) ≠ 1 := signatureFlip_ne_one _ _

theorem signature_filter_card_equiv (p : Fin 4 → Prop) [DecidablePred p]
    (e : Equiv.Perm (Fin 4)) :
    (Finset.univ.filter (fun i => p (e i))).card = (Finset.univ.filter p).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa using hi
  · intro i _ j _ he
    exact e.injective he
  · intro j hj
    refine ⟨e.symm j,?_,by simp⟩
    simpa using hj

theorem signatureAct_weight (g : SignatureSymmetry) (w : RootSignature) :
    signatureWeight (signatureAct g w) = signatureWeight w := by
  unfold signatureWeight
  simp_rw [signatureAct_nonzero_iff]
  exact signature_filter_card_equiv (fun i => w i ≠ 1) g.1

theorem signatureSetAct_card (g : SignatureSymmetry) (S : Finset RootSignature) :
    (signatureSetAct g S).card = S.card :=
  Finset.card_image_of_injective S (signatureAct_injective g)

def matchingSignatureCoords (w z : RootSignature) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => w i ≠ 1 ∧ w i = z i)

theorem signatureCells_disjoint_iff (w z : RootSignature) :
    Disjoint (signatureCells w) (signatureCells z) ↔ (matchingSignatureCoords w z).card ≤ 1 := by
  constructor
  · intro hd
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hbad (a b : Fin 4) (hab : a < b)
        (ha : w a ≠ 1 ∧ w a = z a) (hb : w b ≠ 1 ∧ w b = z b) : False := by
      have hw : (a,b,w a,w b) ∈ signatureCells w :=
        Finset.mem_image.mpr ⟨(a,b),Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hab,ha.1,hb.1⟩,rfl⟩
      have hz : (a,b,w a,w b) ∈ signatureCells z := by
        apply Finset.mem_image.mpr
        refine ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,?_,?_⟩,?_⟩
        · rw [← ha.2]; exact ha.1
        · rw [← hb.2]; exact hb.1
        · simp only [ha.2,hb.2]
      exact Finset.disjoint_left.mp hd hw hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hbad i j hlt hi' hj'
    · exact hbad j i hgt hj' hi'
  · intro hc
    apply Finset.disjoint_left.mpr
    intro c hw hz
    obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_image.mp hw
    obtain ⟨⟨k,l⟩,hkl,he'⟩ := Finset.mem_image.mp hz
    have htuple : (i,j,w i,w j) = (k,l,z k,z l) := he.trans he'.symm
    have hik : i = k := congrArg Prod.fst htuple
    have hjl : j = l := congrArg (fun x => x.2.1) htuple
    subst k; subst l
    have hwi := congrArg (fun x => x.2.2.1) htuple
    have hwj := congrArg (fun x => x.2.2.2) htuple
    have hactive := (Finset.mem_filter.mp hij).2
    have hi : i ∈ matchingSignatureCoords w z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hactive.2.1,hwi⟩
    have hj : j ∈ matchingSignatureCoords w z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hactive.2.2,hwj⟩
    exact (ne_of_lt hactive.1) (Finset.card_le_one.mp hc i hi j hj)

theorem matchingSignatureCoords_act_card (g : SignatureSymmetry) (w z : RootSignature) :
    (matchingSignatureCoords (signatureAct g w) (signatureAct g z)).card =
      (matchingSignatureCoords w z).card := by
  unfold matchingSignatureCoords
  simp_rw [signatureAct_nonzero_iff,signatureAct_equal_iff]
  exact signature_filter_card_equiv (fun i => w i ≠ 1 ∧ w i = z i) g.1

theorem signatureAct_disjoint (g : SignatureSymmetry) (w z : RootSignature)
    (h : Disjoint (signatureCells w) (signatureCells z)) :
    Disjoint (signatureCells (signatureAct g w)) (signatureCells (signatureAct g z)) := by
  rw [signatureCells_disjoint_iff,matchingSignatureCoords_act_card]
  exact (signatureCells_disjoint_iff w z).mp h

theorem signatureSetAct_packing (g : SignatureSymmetry) (S : Finset RootSignature)
    (hS : (S : Set RootSignature).Pairwise
      (fun w z => Disjoint (signatureCells w) (signatureCells z))) :
    (signatureSetAct g S : Set RootSignature).Pairwise
      (fun w z => Disjoint (signatureCells w) (signatureCells z)) := by
  intro w hw z hz hwz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
  exact signatureAct_disjoint g a b (hS ha hb (fun he => hwz (he ▸ rfl)))

#print axioms signatureSetAct_packing

end Conway99
