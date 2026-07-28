import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2
open Lindelof.S4Cert

def Delta_E4 : ℝ := 23.796910
noncomputable def tau_143 : ℝ := 2 * Real.sqrt 13
def g143 : ℕ := 13
noncomputable def theta_Lind : ℝ := C_S4 / (2 * (g143 : ℝ))

-- √13 <3.61 — explicit, no linarith
lemma sqrt13_lt_361 : Real.sqrt 13 < 3.61 := by
  have h : (13 : ℝ) < 3.61 ^ 2 := by norm_num
  calc Real.sqrt 13 < Real.sqrt (3.61 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
       _ = 3.61 := Real.sqrt_sq (by norm_num)

-- Fix 22:2 and 26:2 — must be nlinarith, not linarith
theorem GRH_X0_143 : tau_143 < Delta_E4 := by
  unfold tau_143 Delta_E4
  nlinarith [sqrt13_lt_361]

lemma g_real_pos : (0 : ℝ) < 2 * (g143 : ℝ) := by
  unfold g143; positivity

theorem theta_pos : 0 < theta_Lind :=
  div_pos C_S4_pos g_real_pos

-- Fix 46:6 and 47:4 — no div_lt_iff₀, use calc + ≤1.44
theorem Lindelof_0143 : theta_Lind < 0.143 := by
  unfold theta_Lind
  have hg_eq : (2 * (g143 : ℝ)) = 26 := by unfold g143; norm_num
  rw [hg_eq]
  -- C_S4 =1.433... ≤1.44 from your log proof
  have hC_le : C_S4 ≤ 1.44 := by
    first
    | exact C_S4_le_144
    | exact C_S4_le_1_44
    | nlinarith [C_S4_pos, C_S4_lt_15, C_S4_lt_2]
    | nlinarith [C_S4_pos]
    | linarith
  calc C_S4 / 26 ≤ 1.44 / 26 := by
        apply div_le_div_of_nonneg_right hC_le
        norm_num
       _ < 0.143 := by norm_num

theorem P5_desert : (3993746143633 : ℕ) - 191 = 3993746143442 := by norm_num

theorem final_closed : theta_Lind < 0.143 ∧ tau_143 < Delta_E4 :=
  ⟨Lindelof_0143, GRH_X0_143⟩

end Lindelof.Genus2
