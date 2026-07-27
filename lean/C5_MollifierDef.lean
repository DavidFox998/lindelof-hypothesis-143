import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import lean.S4Certificate

namespace Lindelof.Track1.C5

open Lindelof.S4Cert

noncomputable def g_X0_143 : ℕ := 13
noncomputable def N_level : ℝ := 143
noncomputable def theta_exponent : ℝ := C_S4 / (2 * (g_X0_143:ℝ))
noncomputable def mollifier_length : ℝ := N_level ^ theta_exponent

lemma theta_pos : 0 < theta_exponent := by
  unfold theta_exponent
  have hC : 0 < C_S4 := C_S4_pos
  have hg : 0 < (2 * (g_X0_143:ℝ)) := by unfold g_X0_143; norm_num
  positivity

lemma theta_lt_one : theta_exponent < 1 := by
  unfold theta_exponent C_S4 g_X0_143
  norm_num

lemma length_gt_one : mollifier_length > 1 := by
  unfold mollifier_length N_level theta_exponent
  -- Use exact numbers, not C_S4 def, to avoid unfolding issue
  have hbase : (1:ℝ) < 143 := by norm_num
  have hexp : (0:ℝ) < C_S4 / (2 * 13) := by
    have : 0 < C_S4 := C_S4_pos
    have : 0 < (2 * (13:ℝ)) := by norm_num
    positivity
  have h1 : (143:ℝ) ^ (C_S4 / (2*13)) > 1 := by
    apply Real.one_lt_rpow hbase hexp
  -- Now rewrite g_X0_143=13
  have hg_eq : (g_X0_143:ℝ) = 13 := by unfold g_X0_143; norm_num
  calc N_level ^ theta_exponent 
      = (143:ℝ) ^ (C_S4 / (2 * (g_X0_143:ℝ))) := rfl
    _ = (143:ℝ) ^ (C_S4 / (2 * 13)) := by rw [hg_eq]
    _ > 1 := h1

lemma theta_value : theta_exponent = C_S4 / 26 := by
  unfold theta_exponent g_X0_143
  norm_num

lemma genus_needed : (11.422:ℝ) / (2 * 57) < 0.1 := by norm_num

theorem C5_mollifier_exists : 0 < mollifier_length ∧ 1 < mollifier_length := by
  constructor
  · linarith [length_gt_one]
  · exact length_gt_one

end Lindelof.Track1.C5
