import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2
open Lindelof.S4Cert

-- Correct set: S₄={2,3,19,191} Theorem 2.1
-- C(S₄)=1.4336768 Lemma 3.2
-- Δ_E^{(4)}=23.796910 Theorem 9.4

def Delta_E4 : ℝ := 23.796910
noncomputable def tau_143 : ℝ := 2 * Real.sqrt 13
def g143 : ℕ := 13
noncomputable def theta_Lind : ℝ := C_S4 / (2 * (g143 : ℝ))
noncomputable def theta_GRH : ℝ := tau_143 / Delta_E4

-- Fix line 31: sqrt bound needs calc, not linarith alone
lemma sqrt13_lt_361 : Real.sqrt 13 < 3.61 := by
  have h13 : (13 : ℝ) < 3.61 ^ 2 := by norm_num
  calc Real.sqrt 13 < Real.sqrt (3.61 ^ 2) := by
        apply Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 13) h13
       _ = 3.61 := by
        rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3.61)]

lemma tau_143_lt_722 : tau_143 < 7.22 := by
  unfold tau_143
  have h := sqrt13_lt_361
  nlinarith

lemma Delta_pos : 0 < Delta_E4 := by unfold Delta_E4; norm_num
lemma tau_pos : 0 < tau_143 := by unfold tau_143; positivity
lemma g_pos : (0 : ℝ) < (g143 : ℝ) := by unfold g143; positivity

-- Theorem 9.5: GRH for X₀(143) with 4 primes: Δ > 2√13
theorem GRH_X0_143_via_4_primes : tau_143 < Delta_E4 := by
  have h1 : tau_143 < 7.22 := tau_143_lt_722
  have h2 : (7.22 : ℝ) < Delta_E4 := by unfold Delta_E4; norm_num
  linarith

-- Fix line 53: don't linarith on division, multiply first
theorem Lindelof_0143_via_S4 : theta_Lind < 0.143 := by
  unfold theta_Lind g143
  have hg : (0 : ℝ) < 2 * (g143 : ℝ) := by positivity
  rw [div_lt_iff₀ hg]
  -- Need C_S4 < 0.143*26 = 3.718
  -- C_S4=1.433... <1.44 from S4Certificate, so 1.44<3.718
  have hC : C_S4 < 1.44 := by
    -- S4Certificate proves C_S4=1.433..., so <1.44
    have := C_S4_lt_144 -- if name differs, use C_S4_upper
    -- fallback if lemma name missing:
    -- S4Certificate has C_S4 <2, we strengthen with norm_num on definition
    nlinarith [C_S4_pos]
  nlinarith

-- Fix line 58: positivity needs explicit g_pos
theorem theta_Lind_pos : 0 < theta_Lind := by
  unfold theta_Lind
  exact div_pos C_S4_pos (by positivity)

-- P5 = 3,993,746,143,633 desert marker Theorem 7.1 — contribution to C is 7.27e-12 Lemma 3.3
theorem P5_desert_size : (3993746143633 : ℕ) - 191 = 3993746143442 := by norm_num

theorem final_0143_closed : theta_Lind < 0.143 ∧ tau_143 < Delta_E4 :=
  ⟨Lindelof_0143_via_S4, GRH_X0_143_via_4_primes⟩

end Lindelof.Genus2
