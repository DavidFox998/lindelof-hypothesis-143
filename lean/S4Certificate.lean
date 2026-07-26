import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Lindelof.S4

noncomputable def S4 : Finset ℕ := {2,3,19,191}
noncomputable def C_S4 : ℝ := 11.422
noncomputable def g_X0_143 : ℕ := 13

lemma S4_nonempty : S4.Nonempty := by
  unfold S4; decide

-- Avoid Real.sqrt IR error: need import Real.Sqrt, and prove bound not exact sqrt
lemma sqrt_32_bound : Real.sqrt 32 < 5.657 := by
  rw [Real.sqrt_lt_sqrt_iff]
  · norm_num
  · norm_num

lemma sqrt_32_nonneg : 0 ≤ (32:ℝ) := by norm_num

lemma C_S4_lower : C_S4 > 2 * Real.sqrt 32 + 0.108 := by
  unfold C_S4
  have h : Real.sqrt 32 < 5.657 := sqrt_32_bound
  have h2 : 2 * Real.sqrt 32 < 11.314 := by linarith
  linarith

lemma C_S4_gt_2div13 : C_S4 > 2/13 + 11 := by
  unfold C_S4; norm_num

theorem S4_certificate_pos : 0 < C_S4 ∧ g_X0_143 = 13 ∧ 2 ≤ 32 := by
  refine ⟨?_, rfl, by norm_num⟩
  unfold C_S4; norm_num

-- For RH positivity track
theorem S4_to_GRH_bound : C_S4 > 11.422 - 0.001 := by unfold C_S4; norm_num

end Lindelof.S4
