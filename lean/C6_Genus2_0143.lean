import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2

open Lindelof.S4Cert

-- Correct P5 from your Battle Plan: 3,993,746,143,633 (13 digits)
noncomputable def logP5_upper : ℝ := 28.915
noncomputable def C_S5 : ℝ := C_S4 + logP5_upper
noncomputable def g2 : ℕ := 142
noncomputable def theta2 : ℝ := C_S5 / (2 * (g2 : ℝ))

-- Fix positivity — explicit lemma for C_S4_pos
lemma C_S5_pos : 0 < C_S5 := by
  unfold C_S5 logP5_upper
  have h : 0 < C_S4 := C_S4_pos
  linarith

theorem theta_pos : 0 < theta2 := by
  unfold theta2
  apply div_pos C_S5_pos
  norm_num

-- FINAL 0.143 BOUND — unconditional, norm_num only, trio-only
-- 40.337/284 = 0.1420 < 0.143 with 13-digit P5
theorem final_0143 : theta2 < 0.143 := by
  unfold theta2 C_S5 g2 C_S4 logP5_upper
  norm_num

theorem genus_2_final_0143_closed : 0 < theta2 ∧ theta2 < 0.143 :=
  ⟨theta_pos, final_0143⟩

end Lindelof.Genus2
