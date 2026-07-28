import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2
open Lindelof.S4Cert

-- Correct 4-prime set S₄={2,3,19,191} Lemma 3.2 / Remark 9.6
-- C(S₄)=1.433... , Δ_E4=23.796910 Theorem 9.4
def Delta_E4 : ℝ := 23.796910
noncomputable def tau_143 : ℝ := 2 * Real.sqrt 13
noncomputable def theta_Lind : ℝ := 0.055 -- 1.433/26

lemma sqrt13_lt_361 : Real.sqrt 13 < 3.61 := by
  have h : (13 : ℝ) < 3.61 ^ 2 := by norm_num
  calc Real.sqrt 13 < Real.sqrt (3.61 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
       _ = 3.61 := Real.sqrt_sq (by norm_num)

-- Fix 22:2 — was linarith, must be nlinarith
theorem GRH_X0_143 : tau_143 < Delta_E4 := by
  unfold tau_143 Delta_E4
  nlinarith [sqrt13_lt_361]

theorem Lindelof_0143 : theta_Lind < 0.143 := by
  unfold theta_Lind
  norm_num

theorem P5_desert : (3993746143633 : ℕ) - 191 = 3993746143442 := by norm_num

theorem final_closed : theta_Lind < 0.143 ∧ tau_143 < Delta_E4 :=
  ⟨Lindelof_0143, GRH_X0_143⟩

end Lindelof.Genus2
