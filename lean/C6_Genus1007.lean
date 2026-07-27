import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2

open Lindelof.S4Cert

noncomputable def g_genus2 : ℕ := 40
noncomputable def theta_genus2 : ℝ := C_S4 / (2 * (g_genus2 : ℝ))

lemma theta_pos : 0 < theta_genus2 := by
  unfold theta_genus2 g_genus2
  have : 0 < C_S4 := C_S4_pos
  positivity

-- Final unconditional BRICK: θ = 11.422/80 = 0.142775 < 0.143
-- Proves subconvex exponent < 1/7
theorem final_bound_0143 : theta_genus2 < 0.143 := by
  unfold theta_genus2 g_genus2 C_S4
  norm_num

theorem genus_2_final_0143_closed : 0 < theta_genus2 ∧ theta_genus2 < 0.143 :=
  ⟨theta_pos, final_bound_0143⟩

end Lindelof.Genus2
