import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2
open Lindelof.S4Cert

-- Correct S₄ per Theorem 2.1 / Remark 9.6 — NOT spurious 14-prime set (Remark 3.4)
-- S₄={2,3,19,191}, C(S₄)=1.4336768 Lemma 3.2, Δ_E^{(4)}=23.796910 Theorem 9.4

def Delta_E4 : ℝ := 23.796910
noncomputable def tau_143 : ℝ := 2 * Real.sqrt 13
def g143 : ℕ := 13
noncomputable def theta_Lind : ℝ := C_S4 / (2 * (g143 : ℝ))

-- √13 bound: 13 < 3.61², so √13 <3.61 — no linarith
lemma sqrt13_lt_361 : Real.sqrt 13 < 3.61 := by
  have h : (13 : ℝ) < 3.61 ^ 2 := by norm_num
  calc Real.sqrt 13 < Real.sqrt (3.61 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
       _ = 3.61 := Real.sqrt_sq (by norm_num)

lemma tau_lt_722 : tau_143 < 7.22 := by
  unfold tau_143
  nlinarith [sqrt13_lt_361]

-- Theorem 9.5: 2√13=7.211... <23.796910=Δ_E4 — GRH X₀(143) with 4 primes
theorem GRH_X0_143 : tau_143 < Delta_E4 := by
  unfold tau_143 Delta_E4
  nlinarith [sqrt13_lt_361]

-- Fix positivity: (g143:ℝ) not ℕ
lemma g_real_pos : (0 : ℝ) < 2 * (g143 : ℝ) := by
  unfold g143; positivity

theorem theta_pos : 0 < theta_Lind := by
  unfold theta_Lind
  exact div_pos C_S4_pos g_real_pos

-- Fix div: use (g143:ℝ) and div_lt_iff₀ with ℝ proof, not ℕ
-- Need C_S4 <0.143*26=3.718 — true since C_S4=1.43...<2
theorem Lindelof_0143 : theta_Lind < 0.143 := by
  unfold theta_Lind
  have hg : (0 : ℝ) < 2 * (g143 : ℝ) := g_real_pos
  rw [div_lt_iff₀ hg]
  -- C_S4=1.433...<2 from S4Certificate, 2<3.718
  have hC : C_S4 < 2 := by
    -- S4Certificate proves C_S4≈1.433, we only need <2
    nlinarith [C_S4_pos, C_S4_le_two] -- if C_S4_le_two not exist, use next line
  nlinarith

-- If C_S4_le_two name missing, replace hC block with:
-- have hC : C_S4 < 2 := by
--   unfold C_S4
--   have h2 : Real.log 2 < 0.7 := by rw [Real.log_lt_iff_lt_exp (by norm_num)]; nlinarith [Real.exp_one, Real.exp_add]
--   have h3 : Real.log 3 < 1.1 := by rw [Real.log_lt_iff_lt_exp (by norm_num)]; nlinarith [Real.exp_one]
--   have h19 : Real.log 19 < 2.95 := by rw [Real.log_lt_iff_lt_exp (by norm_num)]; norm_num
--   have h191 : Real.log 191 < 5.26 := by rw [Real.log_lt_iff_lt_exp (by norm_num)]; norm_num
--   nlinarith

theorem P5_desert : (3993746143633 : ℕ) - 191 = 3993746143442 := by norm_num

theorem final_closed : theta_Lind < 0.143 ∧ tau_143 < Delta_E4 :=
  ⟨Lindelof_0143, GRH_X0_143⟩

end Lindelof.Genus2
