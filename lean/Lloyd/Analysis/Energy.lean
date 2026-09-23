import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Integrating the energy inequality

This module treats absolutely continuous energies and integrable coefficients,
so that continuity in time of the velocity is not silently substituted for the
paper's L¹-in-time hypothesis. The energy differential inequality itself must
still be proved for the Voronoi particle evolution.
-/

open MeasureTheory Set
open scoped NNReal

namespace Lloyd

/-- Composition with a function Lipschitz on the image preserves absolute continuity. -/
theorem ac_comp_lipschitzOn {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {s : Set X} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g s)
    (hs : MapsTo f (uIcc a b) s) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro E hE hsum
  have hb := hsmall E hE hsum
  calc
    _ ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (f (E.2 i).1) (f (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hg.dist_le_mul _ (hs (hE.1 i hi).1) _ (hs (hE.1 i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hb.le K.coe_nonneg
    _ < ((K : ℝ) + 1) * (ε / (K + 1)) := by
      apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ = ε := by field_simp

/-- Exponentiating an absolutely continuous real function on a finite interval. -/
theorem ac_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨lo, hlo⟩ := isCompact_uIcc.bddBelow_image hf.continuousOn
  obtain ⟨hi, hhi⟩ := isCompact_uIcc.bddAbove_image hf.continuousOn
  obtain ⟨K, hK⟩ :=
    (show ContDiff ℝ 1 Real.exp from Real.contDiff_exp).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc lo hi) isCompact_Icc
  exact ac_comp_lipschitzOn hf hK (fun t ht => ⟨hlo ⟨t, ht, rfl⟩, hhi ⟨t, ht, rfl⟩⟩)

/-- Integrating factor form of the energy inequality used in Theorem 4.1.

`q` is the dissipation density `α G`, and `l` is the cumulative Lipschitz bound.
The hypotheses allow merely almost-everywhere differential inequalities.
-/
theorem weighted_energy_inequality {E l q : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hl : AbsolutelyContinuousOnInterval l 0 T)
    (hq : IntervalIntegrable q volume 0 T)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T → deriv E t + 2 * q t ≤ 4 * deriv l t * E t) :
    Real.exp (-4 * l T) * E T +
        2 * ∫ t in 0..T, Real.exp (-4 * l t) * q t ≤
      Real.exp (-4 * l 0) * E 0 := by
  let w : ℝ → ℝ := fun t => Real.exp (-4 * l t)
  have hw : AbsolutelyContinuousOnInterval w 0 T := ac_exp (hl.const_mul (-4))
  have hwE := hw.fun_mul hE
  have hwq : IntervalIntegrable (fun t => w t * q t) volume 0 T :=
    hq.continuousOn_mul hw.continuousOn
  have hd : ∀ᵐ t, t ∈ Icc 0 T → deriv (fun s => w s * E s) t ≤ -2 * (w t * q t) := by
    filter_upwards [hE.ae_differentiableAt, hl.ae_differentiableAt, hineq] with t htE htl hineqt ht
    have htu : t ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using ht
    have hdw : HasDerivAt w (w t * (-4 * deriv l t)) t := by
      exact ((htl htu).hasDerivAt.const_mul (-4)).exp
    have heq : deriv (fun s => w s * E s) t =
        (w t * (-4 * deriv l t)) * E t + w t * deriv E t :=
      (hdw.fun_mul (htE htu).hasDerivAt).deriv
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left (hineqt ht) (Real.exp_pos (-4 * l t)).le
    dsimp [w] at *
    nlinarith
  have hi := intervalIntegral.integral_mono_ae_restrict hT hwE.intervalIntegrable_deriv
    (hwq.const_mul (-2)) ((ae_restrict_iff' measurableSet_Icc).mpr hd)
  rw [hwE.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at hi
  dsimp [w] at hi
  linarith

/-- Removing the positive weight gives the two energy/dissipation estimates.

Here `m` is a lower bound for the integrating factor, eventually chosen as
`exp (-4 Λ(T))`. The weighted energy inequality is a proved input from the
preceding lemma, once it has been applied to the particle energy.
-/
theorem energy_and_dissipation_of_weighted {w q : ℝ → ℝ} {T m E E₀ : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m) (hE : 0 ≤ E)
    (hq : IntervalIntegrable q volume 0 T)
    (hwq : IntervalIntegrable (fun t => w t * q t) volume 0 T)
    (hq0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ q t)
    (hw : ∀ t ∈ Icc 0 T, m ≤ w t)
    (hweighted : w T * E + 2 * ∫ t in 0..T, w t * q t ≤ E₀) :
    E ≤ E₀ / m ∧ (∫ t in 0..T, q t) ≤ E₀ / (2 * m) := by
  have hmono : m * (∫ t in 0..T, q t) ≤ ∫ t in 0..T, w t * q t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hT (hq.const_mul m) hwq
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hq0] with t ht htmem
    exact mul_le_mul_of_nonneg_right (hw t htmem) (ht htmem)
  have hqint : 0 ≤ ∫ t in 0..T, q t := by
    have := intervalIntegral.integral_mono_ae_restrict hT (intervalIntegrable_const (c := (0 : ℝ)))
      hq ((ae_restrict_iff' measurableSet_Icc).mpr hq0)
    simpa using this
  have hwend := mul_le_mul_of_nonneg_right (hw T ⟨hT, le_rfl⟩) hE
  constructor
  · apply (le_div_iff₀ hm).mpr
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * m)).mpr
    nlinarith

/-- The energy estimates for an integrable time-dependent Lipschitz bound.

This is the full scalar Gronwall step: `L` is only interval integrable. The
geometric energy inequality for the particle scheme is its explicit input.
-/
theorem energy_dissipation_estimates {E L q : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T) (hET : 0 ≤ E T)
    (hL : IntervalIntegrable L volume 0 T) (hq : IntervalIntegrable q volume 0 T)
    (hL0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ L t)
    (hq0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ q t)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T → deriv E t + 2 * q t ≤ 4 * L t * E t) :
    E T ≤ Real.exp (4 * ∫ t in 0..T, L t) * E 0 ∧
      (∫ t in 0..T, q t) ≤ (1 / 2 : ℝ) * Real.exp (4 * ∫ t in 0..T, L t) * E 0 := by
  let l : ℝ → ℝ := fun t => ∫ s in 0..t, L s
  let w : ℝ → ℝ := fun t => Real.exp (-4 * l t)
  have hl : AbsolutelyContinuousOnInterval l 0 T :=
    hL.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hdl : ∀ᵐ t, t ∈ Icc 0 T → deriv l t = L t := by
    filter_upwards [hL.ae_hasDerivAt_integral] with t ht htmem
    exact (ht (by simpa [uIcc_of_le hT] using htmem) 0 (by simp)).deriv
  have hi : ∀ᵐ t, t ∈ Icc 0 T → deriv E t + 2 * q t ≤ 4 * deriv l t * E t := by
    filter_upwards [hdl, hineq] with t ht hi htmem
    rw [ht htmem]
    exact hi htmem
  have hweighted := weighted_energy_inequality hT hE hl hq hi
  have hweighted' : w T * E T + 2 * ∫ t in 0..T, w t * q t ≤ E 0 := by
    simpa [w, l] using hweighted
  have hw : AbsolutelyContinuousOnInterval w 0 T := ac_exp (hl.const_mul (-4))
  have hL0' : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] L := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hL0] with t ht htmem
    exact ht ⟨htmem.1.le, htmem.2⟩
  have hlmono : ∀ t ∈ Icc 0 T, l t ≤ l T := by
    intro t ht
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hL0' hL
  have hwlower : ∀ t ∈ Icc 0 T, w T ≤ w t := by
    intro t ht
    apply Real.exp_le_exp.mpr
    have := hlmono t ht
    linarith
  have hb := energy_and_dissipation_of_weighted hT (Real.exp_pos _) hET hq
    (hq.continuousOn_mul hw.continuousOn) hq0 hwlower hweighted'
  simpa [w, l, div_eq_mul_inv, neg_mul, Real.exp_neg, mul_comm, mul_left_comm, mul_assoc] using hb

end Lloyd
