import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The final rate deductions in Theorem 4.1

The geometry/energy bound and the transport comparison are explicit hypotheses.
In particular `W` below is a real number; identifying it with a Wasserstein
error and proving the transport comparison are not claimed in this file.
-/

namespace Lloyd

/-- Passing from the fourth-power radius estimate to the mesh diameter scale. -/
theorem radius_le_mesh_sqrt {R h c C : ℝ}
    (hR : 0 ≤ R) (hh : 0 < h) (hc : 0 < c) (hC : 0 ≤ C)
    (hbound : c / 16 * R ^ 4 ≤ C * h ^ 2) :
    R ≤ (16 * C / c) ^ (1 / 4 : ℝ) * h ^ (1 / 2 : ℝ) := by
  have hcC : 0 ≤ 16 * C / c := by positivity
  have hid : ((16 * C / c) ^ (1 / 4 : ℝ) * h ^ (1 / 2 : ℝ)) ^ 4 =
      (16 * C / c) * h ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast _ 4, ← Real.rpow_mul hcC,
      ← Real.rpow_natCast _ 4, ← Real.rpow_mul hh.le]
    norm_num
  apply (pow_le_pow_iff_left₀ hR (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [hid]
  -- Rearrange the positive geometric constant without losing its dependence.
  have : R ^ 4 ≤ (16 * C * h ^ 2) / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  convert this using 1
  ring

/-- The product of the diameter and correction budgets tends to zero. -/
theorem diameter_mul_budget_rate {h d A Cd Ca : ℝ}
    (hh : 0 < h) (hA : 0 ≤ A) (hCd : 0 ≤ Cd)
    (hd : d ≤ Cd * h ^ (1 / 2 : ℝ))
    (ha : A ≤ Ca * h ^ (-1 / 4 : ℝ)) :
    d * A ≤ (Cd * Ca) * h ^ (1 / 4 : ℝ) := by
  calc
    d * A ≤ (Cd * h ^ (1 / 2 : ℝ)) * A := mul_le_mul_of_nonneg_right hd hA
    _ ≤ (Cd * h ^ (1 / 2 : ℝ)) * (Ca * h ^ (-1 / 4 : ℝ)) := by gcongr
    _ = _ := by
      calc
        _ = (Cd * Ca) * (h ^ (1 / 2 : ℝ) * h ^ (-1 / 4 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hh]; norm_num

/-- The last step of (4.7), with all constants explicit and independent of `h`.

`hB` and `hW` are the two comparison estimates which the geometric transport
argument must provide. This lemma does not assume or assert any ODE existence.
-/
theorem transport_rate_of_comparison {h d A B W M K Cd Ca : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hK : 0 ≤ K) (hCd : 0 ≤ Cd)
    (hd : d ≤ Cd * h ^ (1 / 2 : ℝ))
    (ha : A ≤ Ca * h ^ (-1 / 4 : ℝ))
    (hB : B ≤ K * M * d * A)
    (hW : W ≤ M * (1 + K) * d + B) :
    B + W ≤ (Cd * (1 + K) + 2 * K * Cd * Ca) * M * h ^ (1 / 4 : ℝ) := by
  have hprod := diameter_mul_budget_rate hh hA hCd hd ha
  have hB' : B ≤ K * M * ((Cd * Ca) * h ^ (1 / 4 : ℝ)) := by
    calc
      B ≤ K * M * (d * A) := by nlinarith [hB]
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hK hM)
  have hd' : d ≤ Cd * h ^ (1 / 4 : ℝ) := by
    apply hd.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by norm_num)) hCd
  have hMd := mul_le_mul_of_nonneg_left hd'
    (show 0 ≤ M * (1 + K) by positivity)
  nlinarith

end Lloyd
