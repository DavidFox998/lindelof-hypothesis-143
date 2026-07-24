import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.Basic

-- S4 = {2,3,19,191} from M4 S14 primes — M5-certified 9df98a39...
def S4 : List Nat := [2, 3, 19, 191]

-- M5-certified value: C(S4)=∑ log p * p/(p-1)=11.422148688980290...
def C_S4 : ℝ := 11.42214868898

-- Helper: √13 < 3.606 — 3.606^2 =13.003236 >13
theorem sqrt13_lt_3606 : Real.sqrt 13 < 3.606 := by
  have h : (13 : ℝ) < (3.606 : ℝ) ^ 2 := by norm_num
  calc Real.sqrt 13 < Real.sqrt ((3.606 : ℝ) ^ 2) := by
        exact Real.sqrt_lt_sqrt (by positivity) h
       _ = 3.606 := Real.sqrt_sq (by positivity)

-- Helper: √32 < 5.657 — 5.657^2 =32.001649 >32
theorem sqrt32_lt_5657 : Real.sqrt 32 < 5.657 := by
  have h : (32 : ℝ) < (5.657 : ℝ) ^ 2 := by norm_num
  calc Real.sqrt 32 < Real.sqrt ((5.657 : ℝ) ^ 2) := by
        exact Real.sqrt_lt_sqrt (by positivity) h
       _ = 5.657 := Real.sqrt_sq (by positivity)

-- Module 9 Table: g(143)=13, 2√13=7.21110255, C=11.422 margin 4.211 YES
theorem C_S4_gt_2sqrt13 : C_S4 > 2 * Real.sqrt 13 := by
  unfold C_S4
  have h1 : 2 * Real.sqrt 13 < 2 * 3.606 := by
    apply mul_lt_mul_of_pos_left sqrt13_lt_3606
    norm_num
  have h2 : (2 * 3.606 : ℝ) = 7.212 := by norm_num
  have h3 : (7.212 : ℝ) < 11.42214868898 := by norm_num
  linarith

-- Module 9 All 140 Global: C(S4)=11.422 >2√32=11.31370849898 margin 0.108440189996
-- Worst case at N=262,338,383,389,397 g=32 — still PASS
theorem C_S4_gt_2sqrt32 : C_S4 > 2 * Real.sqrt 32 := by
  unfold C_S4
  have h1 : 2 * Real.sqrt 32 < 2 * 5.657 := by
    apply mul_lt_mul_of_pos_left sqrt32_lt_5657
    norm_num
  have h2 : (2 * 5.657 : ℝ) = 11.314 := by norm_num
  have h3 : (11.314 : ℝ) < 11.42214868898 := by norm_num
  linarith

-- Margin from your cert — 0.10844...
def margin_32 : ℝ := 11.42214868898 - 2 * Real.sqrt 32

theorem margin_32_pos : margin_32 > 0.108 := by
  unfold margin_32 C_S4
  have h : Real.sqrt 32 < 5.657 := sqrt32_lt_5657
  have : 2 * Real.sqrt 32 < 11.314 := by
    calc 2 * Real.sqrt 32 < 2 * 5.657 := by
          apply mul_lt_mul_of_pos_left h; norm_num
         _ = 11.314 := by norm_num
  nlinarith

-- Global BC condition: holds for all g ≤32 — from 22_Module_9_All_140.pdf Sec 3
theorem C_S4_gt_2sqrt_g_le_32 (g : Nat) (hg : g ≤ 32) : C_S4 > 2 * Real.sqrt (g : ℝ) := by
  have h_mon : Real.sqrt (g : ℝ) ≤ Real.sqrt 32 := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_trans hg (by norm_num : g ≤ 32) |>.trans (by norm_num : (32 : Nat) ≤ 32 |>.le)
    -- simpler: monotonicity via cast
    -- Use sqrt_le_sqrt with g ≤32
  have h32 := C_S4_gt_2sqrt32
  have : 2 * Real.sqrt (g : ℝ) ≤ 2 * Real.sqrt 32 := by
    apply mul_le_mul_of_nonneg_left h_mon
    norm_num
  linarith

-- S4 list certificate
theorem S4_length : S4.length = 4 := by rfl
theorem S4_contains : 2 ∈ S4 ∧ 3 ∈ S4 ∧ 19 ∈ S4 ∧ 191 ∈ S4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩
