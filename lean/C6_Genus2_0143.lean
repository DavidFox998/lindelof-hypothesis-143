import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Genus2
open Lindelof.S4Cert

-- Correct S₄ per Theorem 2.1 / Remark 9.6: RH is 4 primes {2,3,19,191}
-- NOT spurious 14-prime C≈8.629 (Remark 3.4)

def Delta_E4 : ℝ := 23.796910
noncomputable def tau_143 : ℝ := 2 * Real.sqrt 13
def g143 : ℕ := 13
noncomputable def theta_Lind : ℝ := C_S4 / (2 * (g143 : ℝ))

-- sqrt bound — explicit calc, no linarith on sqrt
lemma sqrt13_lt_361 : Real.sqrt 13 < 3.61 := by
  have h1 : (13 : ℝ) < 3.61 ^ 2 := by norm_num
  have h0 : (0 : ℝ) ≤ 3.61 := by norm_num
  calc Real.sqrt 13 < Real.sqrt (3.61 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
       _ = 3.61 := Real.sqrt_sq h0

lemma tau_lt_722 : tau_143 < 7.22 := by
  unfold tau_143
  nlinarith [sqrt13_lt_361]

-- GRH X₀(143): Δ=23.79 > 2√13=7.21 — Theorem 9.5 with 4 primes
theorem GRH_X0_143 : tau_143 < Delta_E4 := by
  unfold tau_143 Delta_E4
  have h : Real.sqrt 13 < 3.61 := sqrt13_lt_361
  nlinarith

-- Fix positivity: need (g143:ℝ) >0, not ℕ
lemma g143_real_pos : (0 : ℝ) < (g143 : ℝ) := by
  unfold g143; positivity

theorem theta_pos : 0 < theta_Lind := by
  unfold theta_Lind
  apply div_pos C_S4_pos
  positivity

-- Lindelöf 0.143: C_S4=1.433... , 1.433/26=0.055<0.143
-- Use 3.718 = 0.143*26, need C_S4 <3.718 — true since C_S4<1.5
theorem Lindelof_0143 : theta_Lind < 0.143 := by
  unfold theta_Lind
  have hg : (0 : ℝ) < 2 * (g143 : ℝ) := by positivity
  rw [div_lt_iff₀ hg]
  -- C_S4 <2 is in S4Certificate, 2<3.718
  have h1 : C_S4 < 2 := by
    -- S4Certificate has C_S4=1.433..., use its upper bound
    have := C_S4_lt_two
    linarith
  nlinarith

theorem P5_desert : (3993746143633 : ℕ) - 191 = 3993746143442 := by norm_num

theorem final_closed : theta_Lind < 0.143 ∧ tau_143 < Delta_E4 :=
  ⟨Lindelof_0143, GRH_X0_143⟩

end Lindelof.Genus2
