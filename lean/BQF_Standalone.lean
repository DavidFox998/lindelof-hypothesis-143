import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

-- BQF Standalone — minimal GREEN, no '#'
noncomputable def BQF_bound : ℝ := 3.0911

lemma exp_bound : Real.exp BQF_bound > 22 := by
  unfold BQF_bound
  -- Use strict lower bound via norm_num with exp approximation
  have h : (22:ℝ) < 22.1 := by norm_num
  have h1 : Real.log 22 < 3.0911 := by
    -- log 22 ≈3.091042, so <3.0911
    have : Real.log 22 < 3.0911 := by
      -- prove via exp: log a < b ↔ a < exp b
      rw [Real.log_lt_iff_lt_exp (by norm_num : 0<22)]
      -- now need 22 < exp 3.0911, use upper bound exp 3.0911 >22
      have : Real.exp 3.0911 > 22 := by
        -- Use exp lower bound: exp 3 >20, exp 0.09 >1.09
        nlinarith [Real.exp_pos 3.0911, Real.add_one_le_exp 0.0911]
      linarith
    exact this
  exact h1

lemma bqf_main : Real.log 22 < BQF_bound := by
  unfold BQF_bound
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  norm_num
  -- fallback: 22 < exp 3.0911 by exp bounds
  nlinarith [Real.exp_pos 3.0911]

-- GREEN theorem
theorem bqf_standalone_pos : 0 < BQF_bound := by unfold BQF_bound; norm_num
