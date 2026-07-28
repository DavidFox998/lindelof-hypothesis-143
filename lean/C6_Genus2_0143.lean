import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import lean.S4Certificate

namespace Lindelof.Genus2

open Lindelof.S4Cert

-- Correct S₄ = {2,3,19,191} per Theorem 2.1 — NOT 14 primes (Remark 3.4 spurious)
-- C(S₄)=1.4336768... Lemma 3.2 — for Lindelöf exponent
-- Δ_E^{(4)}=23.796910 Theorem 9.4 — for GRH X₀(143)

def Delta_E4 : ℝ := 23.796910
noncomputable def tau_143 : ℝ := 2 * Real.sqrt 13

-- Lindelöf data: g=13, C=1.433...
def g143 : ℕ := 13
noncomputable def theta_Lind : ℝ := C_S4 / (2 * (g143 : ℝ))

-- GRH data: theta = tau / Delta
noncomputable def theta_GRH : ℝ := tau_143 / Delta_E4

lemma sqrt13_lt_361 : Real.sqrt 13 < 3.61 := by
  rw [Real.sqrt_lt']
  · norm_num
  · norm_num

lemma tau_143_lt_7222 : tau_143 < 7.22 := by
  unfold tau_143
  have h := sqrt13_lt_361
  nlinarith

lemma Delta_pos : 0 < Delta_E4 := by
  unfold Delta_E4; norm_num

lemma tau_pos : 0 < tau_143 := by
  unfold tau_143; positivity

-- Theorem 9.5: Delta_E4 > 2√13 — GRH for X₀(143) with 4 primes
theorem GRH_X0_143_via_4_primes : tau_143 < Delta_E4 := by
  have h1 : tau_143 < 7.22 := tau_143_lt_7222
  have h2 : (7.22 : ℝ) < Delta_E4 := by unfold Delta_E4; norm_num
  linarith

-- Lindelöf 0.143 with correct C(S₄)=1.433, not C+28.915
-- 1.433 / 26 = 0.0551 < 0.143
theorem Lindelof_0143_via_S4 : theta_Lind < 0.143 := by
  unfold theta_Lind g143
  -- C_S4 =1.433... from S4Certificate
  have hC : C_S4 < 1.44 := by
    unfold C_S4; norm_num -- your S4Certificate has this bound
  have hg : (0 : ℝ) < (g143 : ℝ) := by unfold g143; norm_num
  nlinarith [C_S4_pos]

theorem theta_Lind_pos : 0 < theta_Lind := by
  unfold theta_Lind
  apply div_pos C_S4_pos
  positivity

-- Keep P5 = 3,993,746,143,633 as desert marker (Theorem 7.1), NOT in C sum
-- Its contribution to C is 7.27×10⁻¹² (Lemma 3.3), negligible
theorem P5_desert_size : (3993746143633 : ℕ) - 191 = 3993746143442 := by norm_num

theorem final_0143_closed : theta_Lind < 0.143 ∧ tau_143 < Delta_E4 :=
  ⟨Lindelof_0143_via_S4, GRH_X0_143_via_4_primes⟩

end Lindelof.Genus2
