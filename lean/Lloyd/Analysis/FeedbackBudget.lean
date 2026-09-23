import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The corrected feedback estimate in Theorem 4.1

These are proved analytic implications. The dissipation bound is an input here;
its derivation from the periodic Voronoi evolution is a separate obligation.
-/

open MeasureTheory
open scoped ENNReal

namespace Lloyd

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]

/-- Cauchy--Schwarz against the constant function, proved by integrating a square. -/
theorem integral_sq_le_mass_mul_integral_sq {f : S → ℝ}
    (hm : 0 < μ.real Set.univ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  let m := μ.real Set.univ
  let a := ∫ x, f x ∂μ
  have hid : (fun x => (m * f x - a) ^ 2) =
      (fun x => m ^ 2 * f x ^ 2 - (2 * m * a) * f x + a ^ 2) := by
    funext x
    ring
  have h : 0 ≤ ∫ x, (m * f x - a) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (m * f x - a))
  have hi : Integrable (fun x => m ^ 2 * f x ^ 2 - (2 * m * a) * f x) μ :=
    (hf2.const_mul (m ^ 2)).sub (hf.const_mul (2 * m * a))
  rw [hid, integral_add hi (integrable_const (a ^ 2)),
    integral_sub (hf2.const_mul (m ^ 2)) (hf.const_mul (2 * m * a)),
    integral_const_mul, integral_const_mul, integral_const] at h
  change 0 ≤ m ^ 2 * (∫ x, f x ^ 2 ∂μ) - (2 * m * a) * a + m * a ^ 2 at h
  have hprod : 0 ≤ m * (m * (∫ x, f x ^ 2 ∂μ) - a ^ 2) := by nlinarith [h]
  have := (mul_nonneg_iff_of_pos_left hm).mp hprod
  dsimp [a, m] at this
  linarith

/-- The feedback upper bound controls its square by the dissipation density. -/
theorem feedback_sq_le {a g q : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (hcap : a ≤ g / q) :
    a ^ 2 ≤ (a * g) / q := by
  have := mul_le_mul_of_nonneg_left ((le_div_iff₀ hq).mp hcap) ha
  apply (le_div_iff₀ hq).mpr
  nlinarith

omit [IsFiniteMeasure μ] in
/-- Square integrability is supplied by the feedback cap and finite dissipation. -/
theorem integrable_feedback_sq {a g : S → ℝ} {q : ℝ}
    (hq : 0 < q) (ha : AEStronglyMeasurable a μ)
    (hd : Integrable (fun x => a x * g x) μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hcap : ∀ᵐ x ∂μ, a x ≤ g x / q) :
    Integrable (fun x => a x ^ 2) μ := by
  apply (hd.div_const q).mono' (ha.pow 2)
  filter_upwards [ha0, hcap] with x hx hc
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact feedback_sq_le hq hx hc

/-- Equation (4.18), before substituting the mesh-dependent dissipation bound. -/
theorem feedback_budget_sq {a g : S → ℝ} {q : ℝ}
    (hm : 0 < μ.real Set.univ) (hq : 0 < q)
    (ha : Integrable a μ) (ha2 : Integrable (fun x => a x ^ 2) μ)
    (hd : Integrable (fun x => a x * g x) μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hcap : ∀ᵐ x ∂μ, a x ≤ g x / q) :
    (∫ x, a x ∂μ) ^ 2 ≤ μ.real Set.univ / q * ∫ x, a x * g x ∂μ := by
  have hb : (∫ x, a x ^ 2 ∂μ) ≤ (∫ x, a x * g x ∂μ) / q := by
    calc
      _ ≤ ∫ x, (a x * g x) / q ∂μ := by
        apply integral_mono_ae ha2 (hd.div_const q)
        filter_upwards [ha0, hcap] with x hx hc
        exact feedback_sq_le hq hx hc
      _ = _ := integral_div _ _
  calc
    _ ≤ μ.real Set.univ * ∫ x, a x ^ 2 ∂μ :=
      integral_sq_le_mass_mul_integral_sq hm ha ha2
    _ ≤ μ.real Set.univ * ((∫ x, a x * g x ∂μ) / q) :=
      mul_le_mul_of_nonneg_left hb hm.le
    _ = _ := by ring

/-- The corrected budget has the required mesh exponent for every admissible feedback. -/
theorem feedback_budget_mesh_sq {a g : S → ℝ} {h C : ℝ}
    (hm : 0 < μ.real Set.univ) (hh : 0 < h)
    (ha : Integrable a μ) (ha2 : Integrable (fun x => a x ^ 2) μ)
    (hd : Integrable (fun x => a x * g x) μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x)
    (hcap : ∀ᵐ x ∂μ, a x ≤ g x / h ^ (5 / 2 : ℝ))
    (henergy : (∫ x, a x * g x ∂μ) ≤ C * h ^ 2) :
    (∫ x, a x ∂μ) ^ 2 ≤ (μ.real Set.univ * C) * h ^ (-1 / 2 : ℝ) := by
  calc
    _ ≤ μ.real Set.univ / h ^ (5 / 2 : ℝ) * ∫ x, a x * g x ∂μ :=
      feedback_budget_sq hm (Real.rpow_pos_of_pos hh _) ha ha2 hd ha0 hcap
    _ ≤ μ.real Set.univ / h ^ (5 / 2 : ℝ) * (C * h ^ 2) := by
      gcongr
    _ = _ := by
      have hp : h ^ 2 / h ^ (5 / 2 : ℝ) = h ^ (-1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast h 2, ← Real.rpow_sub hh]
        norm_num
      calc
        _ = (μ.real Set.univ * C) * (h ^ 2 / h ^ (5 / 2 : ℝ)) := by ring
        _ = _ := by rw [hp]

/-- Taking a square root gives (4.5) from the dissipation estimate. -/
theorem feedback_budget_mesh {a g : S → ℝ} {h C : ℝ}
    (hm : 0 < μ.real Set.univ) (hh : 0 < h) (hC : 0 ≤ C)
    (ha : Integrable a μ) (ha2 : Integrable (fun x => a x ^ 2) μ)
    (hd : Integrable (fun x => a x * g x) μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x)
    (hcap : ∀ᵐ x ∂μ, a x ≤ g x / h ^ (5 / 2 : ℝ))
    (henergy : (∫ x, a x * g x ∂μ) ≤ C * h ^ 2) :
    (∫ x, a x ∂μ) ≤ Real.sqrt (μ.real Set.univ * C) * h ^ (-1 / 4 : ℝ) := by
  have hb := feedback_budget_mesh_sq hm hh ha ha2 hd ha0 hcap henergy
  have hs : (Real.sqrt (μ.real Set.univ * C) * h ^ (-1 / 4 : ℝ)) ^ 2 =
      (μ.real Set.univ * C) * h ^ (-1 / 2 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hm.le hC),
      ← Real.rpow_natCast _ 2, ← Real.rpow_mul hh.le]
    norm_num
  have hn : 0 ≤ Real.sqrt (μ.real Set.univ * C) * h ^ (-1 / 4 : ℝ) := by positivity
  nlinarith

omit [IsFiniteMeasure μ] in
/-- The additional centroid estimate (4.6) requires equality in the feedback law. -/
theorem full_feedback_centroid_estimate {a g : S → ℝ} {h C : ℝ}
    (hh : 0 < h)
    (hfull : ∀ᵐ x ∂μ, a x = g x / h ^ (5 / 2 : ℝ))
    (hd : Integrable (fun x => a x * g x) μ)
    (henergy : (∫ x, a x * g x ∂μ) ≤ C * h ^ 2) :
    Integrable (fun x => (g x / h ^ 2) ^ 2) μ ∧
      (∫ x, (g x / h ^ 2) ^ 2 ∂μ) ≤ C * h ^ (1 / 2 : ℝ) := by
  have hpow : h ^ (5 / 2 : ℝ) / h ^ 4 = h ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast h 4, ← Real.rpow_sub hh]
    norm_num
  have heq : (fun x => (g x / h ^ 2) ^ 2) =ᵐ[μ]
      (fun x => h ^ (-3 / 2 : ℝ) * (a x * g x)) := by
    filter_upwards [hfull] with x hx
    rw [hx, ← hpow]
    field_simp
  refine ⟨(hd.const_mul _).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_const_mul]
  calc
    _ ≤ h ^ (-3 / 2 : ℝ) * (C * h ^ 2) := by gcongr
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_natCast h 2, ← Real.rpow_add hh]
      norm_num

end Lloyd
