import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Lindelof.S4
noncomputable def S4 : Finset ℕ := {2,3,19,191}
noncomputable def C_S4 : ℝ := 11.422

lemma sqrt_32_lt_56569 : Real.sqrt 32 < 5.6569 := by
  have h : (5.6569:ℝ)^2 > 32 := by norm_num
  have h2 : 0 ≤ (32:ℝ) := by norm_num
  nlinarith [Real.sq_sqrt h2, Real.sqrt_nonneg 32, sq_nonneg (Real.sqrt 32 - 5.6569)]

lemma C_S4_main : C_S4 > 2 * Real.sqrt 32 + 0.108 := by
  unfold C_S4
  have h := sqrt_32_lt_56569
  linarith

theorem S4_certificate_pos : 0 < C_S4 := by unfold C_S4; norm_num
theorem S4_main_bound : C_S4 > 11.421 := by unfold C_S4; norm_num
end Lindelof.S4
