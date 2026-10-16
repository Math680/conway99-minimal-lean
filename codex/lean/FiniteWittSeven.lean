import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The anisotropic remainder of a quadratic space over F7 has dimension at most two.
The only finite computation is a 7-element-field statement checked by `decide`.
-/

namespace Conway99

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_binary_represents (a b c : ZMod 7) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : ZMod 7, a * x ^ 2 + b * y ^ 2 + c = 0 := by
  revert a b c
  decide

variable {M : Type*} [AddCommGroup M] [Module (ZMod 7) M]
variable [FiniteDimensional (ZMod 7) M]

theorem quadratic_seven_anisotropic_finrank_le_two
    (Q : QuadraticForm (ZMod 7) M) (hQ : Q.Anisotropic) :
    Module.finrank (ZMod 7) M ≤ 2 := by
  classical
  letI : Invertible (2 : ZMod 7) := invertibleOfNonzero (by decide)
  by_contra hd
  have hdim : 3 ≤ Module.finrank (ZMod 7) M := by omega
  let B := QuadraticMap.associatedHom (ZMod 7) Q
  have hB : B.IsSymm := Q.associated_isSymm (ZMod 7)
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  let i : Fin (Module.finrank (ZMod 7) M) := ⟨0, by omega⟩
  let j : Fin (Module.finrank (ZMod 7) M) := ⟨1, by omega⟩
  let k : Fin (Module.finrank (ZMod 7) M) := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hik : i ≠ k := by simp [i, k]
  have hjk : j ≠ k := by simp [j, k]
  have hqi : Q (e i) ≠ 0 := fun hi => e.ne_zero i (hQ _ hi)
  have hqj : Q (e j) ≠ 0 := fun hj => e.ne_zero j (hQ _ hj)
  obtain ⟨x, y, hxy⟩ := seven_binary_represents (Q (e i)) (Q (e j)) (Q (e k)) hqi hqj
  let v : M := x • e i + y • e j + e k
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrArg (fun t : M => e.repr t k) hz
    simp [v, hij, hik, hjk, Ne.symm hik, Ne.symm hjk] at hh
  have heij : B (e i) (e j) = 0 := he hij
  have heik : B (e i) (e k) = 0 := he hik
  have hejk : B (e j) (e k) = 0 := he hjk
  have heji : B (e j) (e i) = 0 := he hij.symm
  have heki : B (e k) (e i) = 0 := he hik.symm
  have hekj : B (e k) (e j) = 0 := he hjk.symm
  have hdiag (t : M) : B t t = Q t := QuadraticMap.associated_eq_self_apply (ZMod 7) Q t
  have hvQ : Q v = 0 := by
    rw [← hdiag v]
    dsimp only [v]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, heij, heik, hejk, heji, heki, hekj, mul_zero, add_zero,
      zero_add, hdiag]
    linear_combination hxy
  exact hv (hQ _ hvQ)

theorem quadratic_seven_exists_isotropic_of_finrank_ge_three
    (Q : QuadraticForm (ZMod 7) M) (hdim : 3 ≤ Module.finrank (ZMod 7) M) :
    ∃ x : M, x ≠ 0 ∧ Q x = 0 := by
  apply Q.not_anisotropic_iff_exists.mp
  intro hQ
  have hh := quadratic_seven_anisotropic_finrank_le_two Q hQ
  omega

#print axioms quadratic_seven_anisotropic_finrank_le_two
#print axioms quadratic_seven_exists_isotropic_of_finrank_ge_three

end Conway99
