import ZeroCaseFiveOrbits

/-! Realization of every signed coordinate permutation on the actual
four-direction system, not just on an abstract set of signatures. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def signedCodeFlip (s : Bool) (b : V → ℤ) : V → ℤ :=
  if s then fun u => -b u else b

theorem positiveCodeSupport_neg (b : V → ℤ) :
    positiveCodeSupport (fun u => -b u) = negativeCodeSupport b := by
  ext u
  simp only [positiveCodeSupport,negativeCodeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

theorem negativeCodeSupport_neg (b : V → ℤ) :
    negativeCodeSupport (fun u => -b u) = positiveCodeSupport b := by
  ext u
  simp only [positiveCodeSupport,negativeCodeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

theorem SignedBiplaneCode.neg {b : V → ℤ} (hb : SignedBiplaneCode G b) :
    SignedBiplaneCode G (fun u => -b u) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro u
    rcases hb.signs u with hm | hz | hp <;> omega
  · rw [positiveCodeSupport_neg]; exact hb.negative_card
  · rw [negativeCodeSupport_neg]; exact hb.positive_card
  · rw [positiveCodeSupport_neg]; exact hb.negative_internal
  · rw [negativeCodeSupport_neg]; exact hb.positive_internal
  · rw [positiveCodeSupport_neg,negativeCodeSupport_neg]; exact hb.negative_cross
  · rw [negativeCodeSupport_neg,positiveCodeSupport_neg]; exact hb.positive_cross
  · rw [positiveCodeSupport_neg,negativeCodeSupport_neg]; exact hb.negative_pairs
  · rw [negativeCodeSupport_neg,positiveCodeSupport_neg]; exact hb.positive_pairs

theorem signedCodeFlip_biplane (s : Bool) {b : V → ℤ} (hb : SignedBiplaneCode G b) :
    SignedBiplaneCode G (signedCodeFlip s b) := by
  cases s
  · exact hb
  · exact hb.neg

theorem signedCodeFlip_eigen (s : Bool) (b : V → ℤ)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    ∀ u, (∑ v, if G.Adj u v then signedCodeFlip s b v else 0) =
      -4 * signedCodeFlip s b u := by
  cases s
  · exact he
  · intro u
    have hh : (∑ v, if G.Adj u v then -b v else 0) = -(∑ v, if G.Adj u v then b v else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    change (∑ v, if G.Adj u v then -b v else 0) = -4 * (-b u)
    rw [hh,he]
    ring

theorem rootSupport_signedCodeFlip (s : Bool) (b : V → ℤ) :
    rootSupport (signedCodeFlip s b) = rootSupport b := by
  cases s
  · rfl
  · change rootSupport (fun u => -b u) = _
    rw [rootSupport,positiveCodeSupport_neg,negativeCodeSupport_neg,Finset.union_comm]
    rfl

theorem rootIsolated_neg (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    rootIsolated G (fun u => -b u) = rootIsolated G b := by
  ext u
  by_cases hz : b u = 0
  · have hh := sign_code_neighbor_sum G b hb.signs u
    rw [he,hz] at hh
    simp only [rootIsolated,positiveCodeSupport_neg,Finset.mem_filter,Finset.mem_univ,true_and,
      neg_eq_zero,hz,true_and]
    omega
  · simp [rootIsolated,hz]

theorem rootIsolated_signedCodeFlip (s : Bool) (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    rootIsolated G (signedCodeFlip s b) = rootIsolated G b := by
  cases s
  · rfl
  · exact rootIsolated_neg b hb he

theorem signedCodeSupport_signedCodeFlip (s t : Bool) (b : V → ℤ) :
    signedCodeSupport (signedCodeFlip s b) t = signedCodeSupport b (Bool.xor s t) := by
  cases s <;> cases t <;>
    simp [signedCodeFlip,signedCodeSupport,positiveCodeSupport_neg,negativeCodeSupport_neg]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

def act (g : SignatureSymmetry) : FourDirectionSystem G where
  code i := signedCodeFlip (g.2 i) (F.code (g.1 i))
  biplane i := signedCodeFlip_biplane (g.2 i) (F.biplane (g.1 i))
  eigen i := signedCodeFlip_eigen (g.2 i) (F.code (g.1 i)) (F.eigen (g.1 i))
  isolated_disjoint := by
    intro i j hij
    rw [rootIsolated_signedCodeFlip _ _ (F.biplane (g.1 i)) (F.eigen (g.1 i)),
      rootIsolated_signedCodeFlip _ _ (F.biplane (g.1 j)) (F.eigen (g.1 j))]
    exact F.isolated_disjoint (fun he => hij (g.1.injective he))
  support_avoids_isolated := by
    intro i j
    rw [rootSupport_signedCodeFlip,
      rootIsolated_signedCodeFlip _ _ (F.biplane (g.1 j)) (F.eigen (g.1 j))]
    exact F.support_avoids_isolated _ _
  support_intersections := by
    intro i j hij
    rw [rootSupport_signedCodeFlip,rootSupport_signedCodeFlip]
    exact F.support_intersections _ _ (fun he => hij (g.1.injective he))

theorem act_signedCells (g : SignatureSymmetry) (hc : F.HasSignedCells) :
    (F.act g).HasSignedCells := by
  intro i j hij s t
  change (signedCodeSupport (signedCodeFlip (g.2 i) (F.code (g.1 i))) s ∩
    signedCodeSupport (signedCodeFlip (g.2 j) (F.code (g.1 j))) t).card = 1
  rw [signedCodeSupport_signedCodeFlip,signedCodeSupport_signedCodeFlip]
  exact hc _ _ (fun he => hij (g.1.injective he)) _ _

theorem act_isolatedUnion (g : SignatureSymmetry) : (F.act g).isolatedUnion = F.isolatedUnion := by
  ext u
  simp only [isolatedUnion,Finset.mem_biUnion,Finset.mem_univ,true_and]
  change (∃ i, u ∈ rootIsolated G (signedCodeFlip (g.2 i) (F.code (g.1 i)))) ↔ _
  simp_rw [rootIsolated_signedCodeFlip _ _ (F.biplane _) (F.eigen _)]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨g.1 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨g.1.symm i,by simpa using hi⟩

theorem act_W (g : SignatureSymmetry) : (F.act g).W = F.W := by
  rw [W,F.act_isolatedUnion]
  rfl

theorem act_weight (g : SignatureSymmetry) (u : V) : (F.act g).weight u = F.weight u := by
  unfold weight
  change (∑ i : Fin 4, if u ∈ rootSupport (signedCodeFlip (g.2 i) (F.code (g.1 i))) then (1 : ℤ) else 0) = _
  simp_rw [rootSupport_signedCodeFlip]
  exact Equiv.sum_comp g.1 (fun i => if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0)

theorem act_weightCount (g : SignatureSymmetry) (k : ℤ) : (F.act g).weightCount k = F.weightCount k := by
  simp only [weightCount,F.act_W,F.act_weight]

theorem signatureFlip_value (s : Bool) (x : Fin 3) :
    ((signatureFlip s x).val : ℤ) = if s then 2 - (x.val : ℤ) else x.val := by
  cases s <;> fin_cases x <;> decide

theorem act_signature (g : SignatureSymmetry) (u : V) :
    (F.act g).signature u = signatureAct g (F.signature u) := by
  funext i
  apply Fin.ext
  have hnew := (F.act g).signature_val u i
  have hold := F.signature_val u (g.1 i)
  have hflip := signatureFlip_value (g.2 i) (F.signature u (g.1 i))
  change (((F.act g).signature u i).val : ℤ) =
    signedCodeFlip (g.2 i) (F.code (g.1 i)) u + 1 at hnew
  change ((signatureAct g (F.signature u) i).val : ℤ) = _ at hflip
  by_cases hs : g.2 i = true
  · simp only [signedCodeFlip,hs,if_true] at hnew
    simp only [hs,if_true] at hflip
    omega
  · have hf : g.2 i = false := Bool.eq_false_iff.mpr hs
    simp only [signedCodeFlip,hf,Bool.false_eq_true,if_false] at hnew
    simp only [hf,Bool.false_eq_true,if_false] at hflip
    omega

theorem act_highSignatureVertices (g : SignatureSymmetry) :
    (F.act g).highSignatureVertices = F.highSignatureVertices := by
  simp only [highSignatureVertices,F.act_W,F.act_weight]

theorem act_highSignatures (g : SignatureSymmetry) :
    (F.act g).highSignatures = signatureSetAct g F.highSignatures := by
  simp only [highSignatures,F.act_highSignatureVertices,signatureSetAct,Finset.image_image]
  apply Finset.image_congr
  intro u _
  exact F.act_signature g u

end FourDirectionSystem

theorem zero_case_exists_normalized_system (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells) (hz : F.weightCount 0 = 0) :
    ∃ F' : FourDirectionSystem G, ∃ j : Fin 5,
      F'.HasSignedCells ∧ F'.weightCount 0 = 0 ∧ F'.highSignatures = zeroCaseOrbitRepresentative j := by
  obtain ⟨g,j,hj⟩ := zero_case_high_signatures_five_orbits F h hc hz
  exact ⟨F.act g,j,F.act_signedCells g hc,by rwa [F.act_weightCount],by rwa [F.act_highSignatures]⟩

#print axioms FourDirectionSystem.act
#print axioms zero_case_exists_normalized_system

end Conway99
