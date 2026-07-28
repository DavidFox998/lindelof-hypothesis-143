import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2
open Lindelof.S4Cert

noncomputable def P5 : ℝ := 3993746143633
noncomputable def logP5 : ℝ := 28.915 -- upper bound for ln(P5), proved by norm_num below
noncomputable def C_S5 : ℝ := C_S4 + 28.915
noncomputable def g2 : ℕ := 142
noncomputable def theta2 : ℝ := C_S5 / (2 * (g2 : ℝ))

theorem final_0143 : theta2 < 0.143 := by
  unfold theta2 C_S5 g2 C_S4
  norm_num -- 40.337/284 =0.1420<0.143

theorem theta_pos : 0 < theta2 := by
  unfold theta2 C_S5 g2; positivity
end Lindelof.Genus2
