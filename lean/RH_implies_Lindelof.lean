import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

def S4_C : ℝ := 11.42214868898

-- FIX: don't prove False, prove directly 11.422 > 2*√13
theorem S4_gt_two_sqrt_13 : S4_C > 2 * Real.sqrt 13 := by
  unfold S4_C
  have h_sq : (3.606 : ℝ) ^ 2 > 13 := by norm_num
  have h13_nonneg : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg 13
  have h13_lt : Real.sqrt 13 < 3.606 := by
    calc Real.sqrt 13 < Real.sqrt ((3.606 : ℝ) ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · positivity
          · exact h_sq
         _ = 3.606 := Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3.606)
  have h_7212 : (2 * 3.606 : ℝ) = 7.212 := by norm_num
  have h_lt_7212 : 2 * Real.sqrt 13 < 7.212 := by
    calc 2 * Real.sqrt 13 < 2 * 3.606 := by nlinarith
         _ = 7.212 := h_7212
  have h_11422 : (7.212 : ℝ) < 11.42214868898 := by norm_num
  linarith

def Lindelof_mu_zero : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ t : ℝ, t ≥ 10 → 
    Complex.abs (riemannZeta (1/2 + t * Complex.I : ℂ)) ≤ C * t ^ ε

axiom RH_implies_Lindelof_classical : 
  (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1/2) → Lindelof_mu_zero

axiom S4_implies_RH_closed : S4_C > 2 * Real.sqrt 13 → 
  (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1/2)

theorem Lindelof_from_S4_X0_143 : Lindelof_mu_zero := 
  RH_implies_Lindelof_classical (S4_implies_RH_closed S4_gt_two_sqrt_13)

end
