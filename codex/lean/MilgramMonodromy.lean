import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! The rank 44 Milgram sign can be extracted from the three-point S/T
cycle at i.  This replaces all the cusp asymptotics in the written appendix
by three exact Poisson identities.  These identities themselves, and the
finite Fourier/Gauss identity, are explicit premises here. -/

noncomputable section

namespace Conway99

theorem milgram44_cycle_scalar :
    ((1 - Complex.I) / 2) ^ 22 * (1 - Complex.I) ^ 22 = (-1 : ℂ) := by
  rw [← mul_pow]
  have hbase : ((1 - Complex.I) / 2) * (1 - Complex.I) = -Complex.I := by
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hbase]
  calc
    _ = ((-Complex.I) ^ 2) ^ 11 := by rw [← pow_mul]
    _ = (-1 : ℂ) ^ 11 := by rw [neg_sq, Complex.I_sq]
    _ = -1 := by norm_num

theorem milgram44_from_three_point_cycle
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (R : E →ₗ[ℂ] E) (u₀ u₁ u₂ : E) (γ : ℂ)
    (h₁ : u₁ = (1 - Complex.I) ^ 22 • R u₀)
    (h₂ : u₂ = ((1 - Complex.I) / 2) ^ 22 • R u₁)
    (h₃ : u₀ = R u₂)
    (hGauss : R (R (R u₀)) = γ • u₀)
    (hu : u₀ ≠ 0) : γ = -1 := by
  have he : u₀ = (-γ) • u₀ := by
    calc
      u₀ = R u₂ := h₃
      _ = ((1 - Complex.I) / 2) ^ 22 • R (R u₁) := by rw [h₂, map_smul]
      _ = (((1 - Complex.I) / 2) ^ 22 * (1 - Complex.I) ^ 22) •
          R (R (R u₀)) := by rw [h₁, map_smul, map_smul, smul_smul]
      _ = (-1 : ℂ) • (γ • u₀) := by rw [milgram44_cycle_scalar, hGauss]
      _ = (-γ) • u₀ := by rw [smul_smul, neg_one_mul]
  have hs : (1 + γ) • u₀ = 0 := by
    rw [add_smul, one_smul]
    calc
      u₀ + γ • u₀ = (-γ) • u₀ + γ • u₀ := congrArg (fun v => v + γ • u₀) he
      _ = 0 := by simp
  have hz : (1 + γ : ℂ) = 0 := (smul_eq_zero.mp hs).resolve_right hu
  linear_combination hz

#print axioms milgram44_from_three_point_cycle

end Conway99
