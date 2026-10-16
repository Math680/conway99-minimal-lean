import MilgramFiniteGauss
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Actual quadratic phases of an even rank-one lattice.  The representative
invariance is proved, rather than postulated, before any finite Fourier algebra. -/

noncomputable section

set_option linter.unusedSectionVars false

namespace Conway99.CyclicPhase

open scoped BigOperators Real

variable (M : ℕ) [NeZero M]

def intPhase (a : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (a : ℂ) ^ 2 / (M : ℂ))

def phase (a : ZMod M) : ℂ := intPhase M a.val

def pairing (a b : ZMod M) : ℂ := ZMod.stdAddChar (-a * b)

theorem val_div_eq_of_intCast (r : ZMod M) (a : ℤ) (ha : (a : ZMod M) = r) :
    ∃ k : ℤ, (r.val : ℂ) / (M : ℂ) = (a : ℂ) / (M : ℂ) + k := by
  refine ⟨-(a / (M : ℤ)), ?_⟩
  have hr : (r.val : ℤ) = a + (M : ℤ) * (-(a / (M : ℤ))) := by
    rw [← ha, ZMod.val_intCast]
    linear_combination Int.emod_add_mul_ediv a (M : ℤ)
  have hr' : (r.val : ℂ) = (a : ℂ) + (M : ℂ) * (-(a / (M : ℤ)) : ℤ) := by
    exact_mod_cast hr
  rw [hr']
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

theorem neg_val_div (r : ZMod M) :
    ∃ k : ℤ, ((-r).val : ℂ) / (M : ℂ) = -(r.val : ℂ) / (M : ℂ) + k := by
  simpa using val_div_eq_of_intCast M (-r) (-(r.val : ℤ)) (by simp)

theorem add_val_div (r s : ZMod M) :
    ∃ k : ℤ, ((r + s).val : ℂ) / (M : ℂ) =
      (r.val : ℂ) / (M : ℂ) + (s.val : ℂ) / (M : ℂ) + k := by
  simpa [add_div] using
    val_div_eq_of_intCast M (r + s) ((r.val : ℤ) + s.val) (by simp)

theorem intPhase_shift (hM : Even M) (a t : ℤ) :
    intPhase M (a + (M : ℤ) * t) = intPhase M a := by
  obtain ⟨m, hm⟩ := hM
  have hn : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨a * t + (m : ℤ) * t ^ 2, ?_⟩
  have hm' : (M : ℂ) = (m : ℂ) + m := by exact_mod_cast hm
  push_cast
  field_simp
  rw [hm']
  ring

theorem intPhase_cast (hM : Even M) (a : ℤ) :
    phase M (a : ZMod M) = intPhase M a := by
  have hh : ((a : ZMod M).val : ℤ) = a +
      (M : ℤ) * (-(a / (M : ℤ))) := by
    rw [ZMod.val_intCast]
    linear_combination Int.emod_add_mul_ediv a (M : ℤ)
  unfold phase
  rw [hh, intPhase_shift M hM]

theorem phase_eq_of_intCast (hM : Even M) (a b : ℤ)
    (hab : (a : ZMod M) = (b : ZMod M)) : intPhase M a = intPhase M b := by
  rw [← intPhase_cast M hM a, ← intPhase_cast M hM b, hab]

theorem phase_zero : phase M 0 = 1 := by
  simp [phase, intPhase]

theorem phase_ne_zero (a : ZMod M) : phase M a ≠ 0 :=
  Complex.exp_ne_zero _

theorem phase_neg (hM : Even M) (a : ZMod M) : phase M (-a) = phase M a := by
  have ha : ((a.val : ℤ) : ZMod M) = a := by simp
  rw [← ha, ← Int.cast_neg, intPhase_cast M hM, intPhase_cast M hM]
  simp [intPhase]

theorem pairing_symm (a b : ZMod M) : pairing M a b = pairing M b a := by
  simp [pairing, mul_comm]

theorem pairing_add (a b c : ZMod M) :
    pairing M (a + b) c = pairing M a c * pairing M b c := by
  have he : -(a + b) * c = (-a * c) + (-b * c) := by ring
  unfold pairing
  rw [he, AddChar.map_add_eq_mul]

theorem phase_quadratic (hM : Even M) (a b : ZMod M) :
    phase M (a + b) * pairing M a b = phase M a * phase M b := by
  have ha : ((a.val : ℤ) : ZMod M) = a := by simp
  have hb : ((b.val : ℤ) : ZMod M) = b := by simp
  rw [← ha, ← hb, ← Int.cast_add, intPhase_cast M hM,
    intPhase_cast M hM, intPhase_cast M hM]
  have hp : pairing M ((a.val : ℤ) : ZMod M) ((b.val : ℤ) : ZMod M) =
      Complex.exp (2 * Real.pi * Complex.I * (-(a.val : ℤ) * (b.val : ℤ)) / M) := by
    unfold pairing
    rw [← Int.cast_neg, ← Int.cast_mul, ZMod.stdAddChar_coe]
    push_cast
    rfl
  rw [hp]
  unfold intPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pairing_orthogonality (a : ZMod M) :
    (∑ b, pairing M a b) = if a = 0 then (Fintype.card (ZMod M) : ℂ) else 0 := by
  simpa [pairing, mul_comm, neg_eq_zero] using
    (AddChar.sum_mulShift (-a) (ZMod.isPrimitive_stdAddChar M))

def pairingChar (a : ZMod M) : AddChar (ZMod M) ℂ where
  toFun := pairing M a
  map_zero_eq_one' := by simp [pairing]
  map_add_eq_mul' b c := by
    unfold pairing
    rw [mul_add, AddChar.map_add_eq_mul]

theorem phase_add_positive (hM : Even M) (a b : ZMod M) :
    phase M (a + b) = phase M a * phase M b * pairing M (-a) b := by
  have hinv : pairing M a b * pairing M (-a) b = 1 := by
    rw [← pairing_add]
    simp [pairing]
  calc
    phase M (a + b) = phase M (a + b) * (pairing M a b * pairing M (-a) b) :=
      by rw [hinv, mul_one]
    _ = _ := by rw [← mul_assoc, phase_quadratic M hM]

theorem pairing_nondegenerate (a : ZMod M) (ha : ∀ b, pairing M a b = 1) : a = 0 := by
  have he : ZMod.stdAddChar (-a) = ZMod.stdAddChar (0 : ZMod M) := by
    simpa [pairing] using ha 1
  have hz := ZMod.injective_stdAddChar he
  simpa using hz

theorem positive_pairing_exp_val (a b : ZMod M) :
    pairing M (-a) b = Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (a.val : ℂ) / M) := by
  have ha : ((a.val : ℤ) : ZMod M) = a := by simp
  have hb : ((b.val : ℤ) : ZMod M) = b := by simp
  conv_lhs =>
    unfold pairing
    rw [neg_neg, ← ha, ← hb, ← Int.cast_mul, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem finEquiv_val (r : Fin M) : ((ZMod.finEquiv M) r).val = r.val := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem normalized_fourier_cube (hM : Even M) (v : ℂ) (hv : v ≠ 0)
    (hcard : (M : ℂ) = v ^ 2) (f : ZMod M → ℂ) :
    Conway99.normalizedTwistedFourier (phase M) (pairing M) v
      (Conway99.normalizedTwistedFourier (phase M) (pairing M) v
        (Conway99.normalizedTwistedFourier (phase M) (pairing M) v f)) =
      ((∑ b, phase M b) / v) • (fun a => f (-a)) := by
  apply Conway99.normalizedTwistedFourier_cube (phase M) (pairing M) v hv
  · simpa using hcard
  · exact phase_ne_zero M
  · exact phase_zero M
  · exact phase_neg M hM
  · exact pairing_symm M
  · exact pairing_add M
  · exact phase_quadratic M hM
  · exact pairing_orthogonality M

#print axioms intPhase_cast
#print axioms phase_quadratic
#print axioms normalized_fourier_cube

end Conway99.CyclicPhase

namespace Conway99.DiagonalPhase

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ι → ℕ) [∀ i, NeZero (M i)]

abbrev Discriminant := ∀ i, ZMod (M i)

def phase (a : Discriminant M) : ℂ := ∏ i, CyclicPhase.phase (M i) (a i)

def pairing (a b : Discriminant M) : ℂ :=
  ∏ i, CyclicPhase.pairing (M i) (a i) (b i)

def finEquiv : (∀ i, Fin (M i)) ≃ Discriminant M :=
  Equiv.piCongrRight (fun i => (ZMod.finEquiv (M i)).toEquiv)

theorem finEquiv_val (r : ∀ i, Fin (M i)) (i : ι) :
    ((finEquiv M r) i).val = (r i).val := CyclicPhase.finEquiv_val (M i) (r i)

theorem sum_finEquiv (f : Discriminant M → ℂ) :
    (∑ r : ∀ i, Fin (M i), f (finEquiv M r)) = ∑ r, f r :=
  Equiv.sum_comp (finEquiv M) f

theorem phase_exp_sum (a : Discriminant M) :
    phase M a = Complex.exp ((Real.pi : ℂ) * Complex.I *
      ∑ i, ((a i).val : ℂ) ^ 2 / (M i : ℂ)) := by
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  unfold CyclicPhase.phase CyclicPhase.intPhase
  congr 1
  push_cast
  ring

theorem phase_intCast_sum (hM : ∀ i, Even (M i)) (z : ι → ℤ) :
    phase M (fun i => (z i : ZMod (M i))) =
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ∑ i, (z i : ℂ) ^ 2 / (M i : ℂ)) := by
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [CyclicPhase.intPhase_cast (M i) (hM i)]
  unfold CyclicPhase.intPhase
  congr 1
  ring

theorem positive_pairing_exp_val (a b : Discriminant M) :
    pairing M (-a) b =
      ∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((b i).val : ℂ) * ((a i).val : ℂ) / M i) := by
  apply Finset.prod_congr rfl
  intro i _
  exact CyclicPhase.positive_pairing_exp_val (M i) (a i) (b i)

theorem phase_zero : phase M 0 = 1 := by
  simp [phase, CyclicPhase.phase_zero]

theorem phase_ne_zero (a : Discriminant M) : phase M a ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => CyclicPhase.phase_ne_zero (M i) (a i))

theorem phase_neg (hM : ∀ i, Even (M i)) (a : Discriminant M) :
    phase M (-a) = phase M a := by
  apply Finset.prod_congr rfl
  intro i _
  exact CyclicPhase.phase_neg (M i) (hM i) (a i)

theorem pairing_symm (a b : Discriminant M) : pairing M a b = pairing M b a := by
  apply Finset.prod_congr rfl
  intro i _
  exact CyclicPhase.pairing_symm (M i) (a i) (b i)

theorem pairing_add (a b c : Discriminant M) :
    pairing M (a + b) c = pairing M a c * pairing M b c := by
  unfold pairing
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact CyclicPhase.pairing_add (M i) (a i) (b i) (c i)

theorem pairing_neg_right (a b : Discriminant M) :
    pairing M a (-b) = pairing M (-a) b := by
  apply Finset.prod_congr rfl
  intro i _
  unfold CyclicPhase.pairing
  congr 1
  change -(a i) * -(b i) = -(-(a i)) * b i
  ring

theorem positive_fourier_eq_negative (a : Discriminant M) (f : Discriminant M → ℂ)
    (hf : ∀ b, f (-b) = f b) :
    (∑ b, pairing M (-a) b * f b) = ∑ b, pairing M a b * f b := by
  have hh := Equiv.sum_comp (Equiv.neg (Discriminant M))
    (fun b => pairing M a b * f b)
  change (∑ b, pairing M a (-b) * f (-b)) = _ at hh
  simp_rw [pairing_neg_right, hf] at hh
  exact hh

theorem phase_quadratic (hM : ∀ i, Even (M i)) (a b : Discriminant M) :
    phase M (a + b) * pairing M a b = phase M a * phase M b := by
  unfold phase pairing
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact CyclicPhase.phase_quadratic (M i) (hM i) (a i) (b i)

theorem pairing_orthogonality (a : Discriminant M) :
    (∑ b, pairing M a b) = if a = 0 then (Fintype.card (Discriminant M) : ℂ) else 0 := by
  unfold pairing
  rw [← Fintype.prod_sum]
  simp_rw [CyclicPhase.pairing_orthogonality]
  by_cases ha : a = 0
  · subst a
    simp [Fintype.card_pi]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      apply ha
      funext j
      simpa using not_exists.mp h j
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem gauss_product :
    (∑ a, phase M a) = ∏ i, ∑ a, CyclicPhase.phase (M i) a := by
  exact (Fintype.prod_sum (fun i => CyclicPhase.phase (M i))).symm

def pairingChar (a : Discriminant M) : AddChar (Discriminant M) ℂ where
  toFun := pairing M a
  map_zero_eq_one' := by simp [pairing, CyclicPhase.pairing]
  map_add_eq_mul' b c := by
    rw [pairing_symm M a (b + c), pairing_add, pairing_symm M b a,
      pairing_symm M c a]

theorem phase_add_positive (hM : ∀ i, Even (M i)) (a b : Discriminant M) :
    phase M (a + b) = phase M a * phase M b * pairing M (-a) b := by
  have hinv : pairing M a b * pairing M (-a) b = 1 := by
    rw [← pairing_add]
    simp [pairing, CyclicPhase.pairing]
  calc
    phase M (a + b) = phase M (a + b) * (pairing M a b * pairing M (-a) b) :=
      by rw [hinv, mul_one]
    _ = _ := by rw [← mul_assoc, phase_quadratic M hM]

theorem pairing_single (a : Discriminant M) (i : ι) (b : ZMod (M i)) :
    pairing M a (Pi.single i b) = CyclicPhase.pairing (M i) (a i) b := by
  classical
  unfold pairing
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji, CyclicPhase.pairing]
  · simp

theorem pairing_nondegenerate (a : Discriminant M)
    (ha : ∀ b, pairing M a b = 1) : a = 0 := by
  funext i
  apply CyclicPhase.pairing_nondegenerate
  intro b
  rw [← pairing_single]
  exact ha (Pi.single i b)

theorem normalized_fourier_cube (hM : ∀ i, Even (M i)) (v : ℂ) (hv : v ≠ 0)
    (hcard : (Fintype.card (Discriminant M) : ℂ) = v ^ 2)
    (f : Discriminant M → ℂ) :
    Conway99.normalizedTwistedFourier (phase M) (pairing M) v
      (Conway99.normalizedTwistedFourier (phase M) (pairing M) v
        (Conway99.normalizedTwistedFourier (phase M) (pairing M) v f)) =
      ((∑ b, phase M b) / v) • (fun a => f (-a)) := by
  exact Conway99.normalizedTwistedFourier_cube (phase M) (pairing M) v hv hcard
    (phase_ne_zero M) (phase_zero M) (phase_neg M hM)
    (pairing_symm M) (pairing_add M) (phase_quadratic M hM) (pairing_orthogonality M) f

#print axioms gauss_product
#print axioms pairing_nondegenerate
#print axioms normalized_fourier_cube

end Conway99.DiagonalPhase
