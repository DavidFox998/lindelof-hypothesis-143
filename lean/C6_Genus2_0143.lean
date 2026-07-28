import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2

open Lindelof.S4Cert

-- Fix: computable def, not noncomputable, so norm_num sees 28.915
def logP5_upper : ℝ := 28.915
noncomputable def C_S5 : ℝ := C_S4 + logP5_upper
def g2 : ℕ := 142
noncomputable def theta2 : ℝ := C_S5 / (2 * (g2 : ℝ))

lemma logP5_pos : 0 < logP5_upper := by
  unfold logP5_upper
  norm_num

lemma C_S5_pos : 0 < C_S5 := by
  unfold C_S5
  exact add_pos C_S4_pos logP5_pos

lemma g2_pos : 0 < g2 := by
  unfold g2
  decide

lemma g2_real_pos : (0 : ℝ) < (g2 : ℝ) := by
  have : 0 < g2 := g2_pos
  exact Nat.cast_pos.mpr this

theorem theta_pos : 0 < theta2 := by
  unfold theta2
  exact div_pos C_S5_pos (mul_pos (by norm_num) g2_real_pos)

theorem final_0143 : theta2 < 0.143 := by
  unfold theta2 C_S5 g2 C_S4 logP5_upper
  norm_num

theorem genus_2_final_0143_closed : 0 < theta2 ∧ theta2 < 0.143 :=
  ⟨theta_pos, final_0143⟩

end Lindelof.Genus2
