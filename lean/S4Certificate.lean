import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Lindelof.S4Cert

noncomputable def C_S4 : ℝ := 11.422

lemma sqrt_32_lt_56569 : Real.sqrt 32 < 5.6569 := by
  have h32 : (32:ℝ) < (5.6569:ℝ)^2 := by norm_num
  have hmono : Real.sqrt 32 < Real.sqrt ((5.6569:ℝ)^2) :=
    Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (32:ℝ)) h32
  have hsq : Real.sqrt ((5.6569:ℝ)^2) = 5.6569 :=
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5.6569)
  linarith

theorem C_S4_main : C_S4 > 2 * Real.sqrt 32 + 0.108 := by
  unfold C_S4
  have h := sqrt_32_lt_56569
  -- 2*5.6569 +0.108 = 11.4218 < 11.422
  have h2 : 2 * (5.6569:ℝ) + 0.108 < 11.422 := by norm_num
  linarith

theorem C_S4_pos : 0 < C_S4 := by unfold C_S4; norm_num

end Lindelof.S4Cert
