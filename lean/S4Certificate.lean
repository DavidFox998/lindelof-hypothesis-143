import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Lindelof.S4Cert

noncomputable def S4_set : Finset ℕ := {2,3,19,191}
noncomputable def C_S4 : ℝ := 11.422

-- 32 < 5.6569² = 32.0005... so √32 < 5.6569
lemma sqrt_32_lt : Real.sqrt 32 < 5.6569 := by
  rw [Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 5.6569)]
  norm_num

theorem C_S4_gt : C_S4 > 2 * Real.sqrt 32 + 0.108 := by
  unfold C_S4
  have h := sqrt_32_lt
  linarith

theorem C_S4_pos : 0 < C_S4 := by
  unfold C_S4; norm_num

theorem C_S4_gt_11 : C_S4 > 11.421 := by
  unfold C_S4; norm_num

end Lindelof.S4Cert
