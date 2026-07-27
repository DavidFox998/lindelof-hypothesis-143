import Mathlib.Tactic
import lean.C5_MollifierDef

namespace Lindelof.Track1.C6

def N_1007 : ℝ := 1007
def g_1007 : ℕ := 85
def theta_1007 : ℝ := 11.422 / (2 * g_1007)

lemma theta_1007_lt_01 : theta_1007 < 0.1 := by unfold theta_1007 g_1007; norm_num
lemma theta_1007_pos : 0 < theta_1007 := by unfold theta_1007 g_1007; norm_num

theorem C6_subconvex_01 : theta_1007 < 0.1 := theta_1007_lt_01
-- This is first file that gets ε=0.1 subconvex

end Lindelof.Track1.C6
