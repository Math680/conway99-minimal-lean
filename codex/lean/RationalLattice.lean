import MixedConsequences
import FrameRank
import Mathlib.Algebra.Module.Lattice

/-!
The auxiliary lattice is represented by rational 99-coordinate codes.
The pairing is dot product divided by 63, as forced by the vertex frame.
No discriminant or existence-of-overlattice statement is assumed here.
-/

namespace Conway99

open scoped BigOperators Matrix
open Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rationalAmbient : Submodule ℚ (V → ℚ) :=
  LinearMap.range (vertexGram G).mulVecLin

def codePair (x y : V → ℚ) : ℚ := (x ⬝ᵥ y) / 63

def vertexCode (u : V) : V → ℚ := fun v => vertexGram G v u

def triangleCode (L : TriangleIndex G) : V → ℚ := fun v => mixedGram G v L

def coefficientCode : (V → ℤ) →ₗ[ℤ] (V → ℚ) where
  toFun c := (1 / 3 : ℚ) • ((vertexGram G) *ᵥ (fun u => (c u : ℚ)))
  map_add' c d := by
    ext u
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    change (1 / 3 : ℚ) • ((vertexGram G) *ᵥ
        ((a : ℚ) • (fun u => (c u : ℚ)))) = _
    rw [Matrix.mulVec_smul, smul_comm]
    rfl

def canonicalCoefficients : Submodule ℤ (V → ℤ) where
  carrier := {c | 3 ∣ ∑ u, c u}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd
    change 3 ∣ ∑ u, c u at hc
    change 3 ∣ ∑ u, d u at hd
    change 3 ∣ ∑ u, (c + d) u
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using dvd_add hc hd
  smul_mem' := by
    intro a c hc
    change 3 ∣ ∑ u, c u at hc
    change 3 ∣ ∑ u, (a • c) u
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact dvd_mul_of_dvd_right hc a

def canonicalLattice : Submodule ℤ (V → ℚ) :=
  (canonicalCoefficients (V := V)).map (coefficientCode G)

def vertexLattice : Submodule ℤ (V → ℚ) :=
  Submodule.span ℤ (Set.range (vertexCode G))

def triangleLattice : Submodule ℤ (V → ℚ) :=
  Submodule.span ℤ (Set.range (triangleCode G))

theorem codePair_symm (x y : V → ℚ) : codePair x y = codePair y x := by
  simp only [codePair, dotProduct_comm]

theorem codePair_pos (x : V → ℚ) (hx : x ≠ 0) : 0 < codePair x x := by
  have he : ∃ u, x u ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hx (funext hn)
  obtain ⟨u, hu⟩ := he
  have ht : 0 < ∑ v, x v * x v := by
    exact Finset.sum_pos' (fun v _ => mul_self_nonneg _) ⟨u, Finset.mem_univ _, by nlinarith [sq_pos_of_ne_zero hu]⟩
  exact div_pos ht (by norm_num)

theorem rationalAmbient_fixed (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ rationalAmbient G) :
    vertexGram G *ᵥ x = (63 : ℚ) • x := by
  obtain ⟨c, rfl⟩ := hx
  change vertexGram G *ᵥ (vertexGram G *ᵥ c) = _
  rw [Matrix.mulVec_mulVec, vertexGram_square G h, Matrix.smul_mulVec]
  rfl

theorem rationalAmbient_sum_zero (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ rationalAmbient G) : ∑ u, x u = 0 := by
  obtain ⟨c, rfl⟩ := hx
  change (∑ u, ∑ v, vertexGram G u v * c v) = 0
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, vertexGram_column_sum_zero G h]
  simp

theorem vertexCode_mem_ambient (u : V) : vertexCode G u ∈ rationalAmbient G := by
  refine ⟨Pi.single u 1, ?_⟩
  ext v
  simp [vertexCode, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]

theorem triangleCode_mem_ambient (L : TriangleIndex G) :
    triangleCode G L ∈ rationalAmbient G := by
  refine ⟨(1 / 3 : ℚ) • (fun u => vertexTriangleIncidence G u L), ?_⟩
  ext v
  simp [triangleCode, mixedGram, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc, mul_left_comm]

theorem coefficientCode_mem_ambient (c : V → ℤ) :
    coefficientCode G c ∈ rationalAmbient G := by
  refine ⟨(1 / 3 : ℚ) • (fun u => (c u : ℚ)), ?_⟩
  change vertexGram G *ᵥ ((1 / 3 : ℚ) • _) = (1 / 3 : ℚ) • _
  rw [Matrix.mulVec_smul]

theorem canonicalLattice_le_ambient :
    canonicalLattice G ≤ (rationalAmbient G).restrictScalars ℤ := by
  rintro x ⟨c, _, rfl⟩
  exact coefficientCode_mem_ambient G c

theorem codePair_vertexCode (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ rationalAmbient G) (u : V) :
    codePair x (vertexCode G u) = x u := by
  have hf := congrFun (rationalAmbient_fixed G h hx) u
  have he : x ⬝ᵥ vertexCode G u = (vertexGram G *ᵥ x) u := by
    simp only [dotProduct, vertexCode, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro v _
    have hs : vertexGram G v u = vertexGram G u v := by
      exact congrArg (fun M : Matrix V V ℚ => M u v) (vertexGram_transpose G)
    rw [hs, mul_comm]
  rw [codePair, he, hf]
  simp

theorem codePair_vertices (h : G.IsSRGWith 99 14 1 2) (u v : V) :
    codePair (vertexCode G u) (vertexCode G v) = vertexGram G v u :=
  codePair_vertexCode G h (vertexCode_mem_ambient G u) v

theorem vertexCode_mem_canonical (u : V) : vertexCode G u ∈ canonicalLattice G := by
  refine ⟨Pi.single u 3, ?_, ?_⟩
  · change 3 ∣ ∑ v, (Pi.single u (3 : ℤ)) v
    simp
  · ext v
    simp [coefficientCode, vertexCode, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
    ring

theorem triangleCode_mem_canonical (L : TriangleIndex G) :
    triangleCode G L ∈ canonicalLattice G := by
  refine ⟨(fun u => if u ∈ L.val then 1 else 0), ?_, ?_⟩
  · change 3 ∣ ∑ u, (if u ∈ L.val then (1 : ℤ) else 0)
    have hc : L.val.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp L.property).card_eq
    simp [hc]
  · ext v
    simp only [coefficientCode, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, triangleCode, mixedGram, Matrix.smul_apply,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, vertexTriangleIncidence]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> norm_num

theorem vertexLattice_le_canonical : vertexLattice G ≤ canonicalLattice G := by
  apply Submodule.span_le.mpr
  rintro x ⟨u, rfl⟩
  exact vertexCode_mem_canonical G u

theorem triangleLattice_le_canonical : triangleLattice G ≤ canonicalLattice G := by
  apply Submodule.span_le.mpr
  rintro x ⟨L, rfl⟩
  exact triangleCode_mem_canonical G L

theorem rationalAmbient_finrank (h : G.IsSRGWith 99 14 1 2) :
    Module.finrank ℚ (rationalAmbient G) = 44 := vertexGram_rank G h

theorem codePair_coefficientCode (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ rationalAmbient G) (c : V → ℤ) :
    codePair x (coefficientCode G c) =
      (1 / 3 : ℚ) * ∑ u, x u * (c u : ℚ) := by
  change (x ⬝ᵥ ((1 / 3 : ℚ) • (vertexGram G *ᵥ _))) / 63 = _
  rw [dotProduct_smul, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    vertexGram_transpose G, rationalAmbient_fixed G h hx, smul_dotProduct]
  simp only [smul_eq_mul, dotProduct]
  ring

theorem coefficientCode_pair_expansion (h : G.IsSRGWith 99 14 1 2)
    (c d : V → ℤ) :
    codePair (coefficientCode G c) (coefficientCode G d) =
      (1 / 9 : ℚ) * ∑ u, ∑ v, (c u : ℚ) * vertexGram G u v * (d v : ℚ) := by
  rw [codePair_symm, codePair_coefficientCode G h (coefficientCode_mem_ambient G d)]
  change (1 / 3 : ℚ) * (∑ u, ((1 / 3 : ℚ) *
    (∑ v, vertexGram G u v * (d v : ℚ))) * (c u : ℚ)) = _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

def coefficientBilinear (c d : V → ℤ) : ℤ :=
  ∑ u, ∑ v, c u * (3 * (if u = v then 1 else 0) -
    (if G.Adj u v then 1 else 0)) * d v

theorem coefficientCode_pair_formula (h : G.IsSRGWith 99 14 1 2)
    (c d : V → ℤ) :
    codePair (coefficientCode G c) (coefficientCode G d) =
      (∑ u, (c u : ℚ)) * (∑ v, (d v : ℚ)) / 9 +
        (coefficientBilinear G c d : ℚ) := by
  rw [coefficientCode_pair_expansion G h]
  simp only [coefficientBilinear, Int.cast_sum, Int.cast_mul, Int.cast_sub,
    Int.cast_ofNat, Int.cast_ite, Int.cast_one, Int.cast_zero]
  simp_rw [vertexGram_entry_linear]
  rw [show (∑ u, (c u : ℚ)) * (∑ v, (d v : ℚ)) =
      ∑ u, ∑ v, (c u : ℚ) * (d v : ℚ) by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem canonicalLattice_integral (h : G.IsSRGWith 99 14 1 2)
    {x y : V → ℚ} (hx : x ∈ canonicalLattice G) (hy : y ∈ canonicalLattice G) :
    ∃ n : ℤ, codePair x y = (n : ℚ) := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  obtain ⟨a, ha⟩ := hc
  obtain ⟨b, hb⟩ := hd
  refine ⟨a * b + coefficientBilinear G c d, ?_⟩
  rw [coefficientCode_pair_formula G h]
  have hca : (∑ u, (c u : ℚ)) = 3 * (a : ℚ) := by exact_mod_cast ha
  have hdb : (∑ u, (d u : ℚ)) = 3 * (b : ℚ) := by exact_mod_cast hb
  rw [hca, hdb]
  push_cast
  ring

#print axioms codePair_vertexCode
#print axioms triangleLattice_le_canonical
#print axioms canonicalLattice_integral

end Conway99
