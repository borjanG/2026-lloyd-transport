import Lloyd.Analysis.Energy
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The noncollision estimates

These results prove the differential and Gronwall steps in the paper's
noncollision argument. Existence of a maximal Carathéodory solution, absolute
continuity of its squared separation, and global continuation remain separate
obligations; they are not consequences asserted by this file.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace Lloyd

/-- The algebraic lower bound for the squared-separation derivative.

`w` is a difference of generator lifts, `u` is the velocity difference, and `c`
is the difference of the corresponding centroid lifts. The geometric bisector
lemma supplies `hbisector`.
-/
theorem separation_drift_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w u c : E} {a L : ℝ} (ha : 0 ≤ a)
    (hvel : ‖u‖ ≤ L * ‖w‖) (hbisector : 0 ≤ ⟪w, c⟫_ℝ) :
    -(L + a) * ‖w‖ ^ 2 ≤ ⟪w, u + a • (c - w)⟫_ℝ := by
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm w u)
  have hv := mul_le_mul_of_nonneg_left hvel (norm_nonneg w)
  have hc := mul_nonneg ha hbisector
  rw [inner_add_right, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith

/-- Gronwall lower bound for an absolutely continuous squared separation. -/
theorem separation_lower_bound {s b : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hs : AbsolutelyContinuousOnInterval s 0 T)
    (hb : IntervalIntegrable b volume 0 T)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T → -2 * b t * s t ≤ deriv s t) :
    Real.exp (-2 * ∫ t in 0..T, b t) * s 0 ≤ s T := by
  let l : ℝ → ℝ := fun t => (-1 / 2 : ℝ) * ∫ u in 0..t, b u
  have hl : AbsolutelyContinuousOnInterval l 0 T :=
    (hb.absolutelyContinuousOnInterval_intervalIntegral (by simp)).const_mul (-1 / 2)
  have hi : ∀ᵐ t, t ∈ Icc 0 T →
      deriv (fun u => -s u) t + 2 * (0 : ℝ) ≤ 4 * deriv l t * (-s t) := by
    filter_upwards [hb.ae_hasDerivAt_integral, hs.ae_differentiableAt, hineq]
      with t hbt hst hit ht
    have htu : t ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using ht
    have hld : HasDerivAt l ((-1 / 2 : ℝ) * b t) t :=
      (hbt htu 0 (by simp)).const_mul (-1 / 2)
    rw [hld.deriv, (hst htu).hasDerivAt.fun_neg.deriv]
    have := hit ht
    nlinarith
  have hw := weighted_energy_inequality hT hs.fun_neg hl
    (intervalIntegrable_const (c := (0 : ℝ))) hi
  have hli : -4 * l T = 2 * ∫ t in 0..T, b t := by dsimp [l]; ring
  simp only [hli, mul_zero, intervalIntegral.integral_zero, add_zero] at hw
  have hl0 : l 0 = 0 := by simp [l]
  rw [hl0] at hw
  simp only [mul_zero, Real.exp_zero, one_mul] at hw
  have he : s 0 ≤ Real.exp (2 * ∫ t in 0..T, b t) * s T := by linarith
  have hp := mul_le_mul_of_nonneg_left he
    (Real.exp_pos (-2 * ∫ t in 0..T, b t)).le
  have hexp : Real.exp (-2 * ∫ t in 0..T, b t) *
      Real.exp (2 * ∫ t in 0..T, b t) = 1 := by
    rw [← Real.exp_add]
    have hz : -2 * (∫ t in 0..T, b t) + 2 * (∫ t in 0..T, b t) = 0 := by ring
    rw [hz, Real.exp_zero]
  calc
    _ ≤ Real.exp (-2 * ∫ t in 0..T, b t) *
        (Real.exp (2 * ∫ t in 0..T, b t) * s T) := hp
    _ = s T := by rw [← mul_assoc, hexp, one_mul]

/-- Positive initial squared separation remains positive whenever the above
absolutely continuous differential inequality holds. -/
theorem separation_pos {s b : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hs : AbsolutelyContinuousOnInterval s 0 T)
    (hb : IntervalIntegrable b volume 0 T) (h0 : 0 < s 0)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T → -2 * b t * s t ≤ deriv s t) :
    0 < s T :=
  (mul_pos (Real.exp_pos _) h0).trans_le (separation_lower_bound hT hs hb hineq)

end Lloyd
