import Lloyd.Analysis.Energy
import Lloyd.Analysis.FeedbackBudget

/-!
# Scalar estimates of Theorem 4.1

This combines the proved Gronwall and feedback lemmas on the actual time
interval `[0,T]`. The scalar energy differential inequality is still an
assumption: proving it for the periodic particle scheme is outstanding.
This is not a declaration of the complete theorem in the paper.
-/

open MeasureTheory Set

namespace Lloyd

/-- Estimates (4.3), (4.5), and, under full feedback, (4.6), at an endpoint,
conditional on the scalar energy inequality.

The energy bound holds at every earlier time by applying the same theorem
on that subinterval. `C` is the explicit dissipation constant, independent
of `h` when `T`, `C₁`, and the integral of `L` are uniform.
-/
theorem scalar_estimates_of_energy_inequality {E L a g : ℝ → ℝ} {T h C₁ : ℝ}
    (hT : 0 < T) (hh : 0 < h) (hC₁ : 0 ≤ C₁)
    (hE : AbsolutelyContinuousOnInterval E 0 T) (hET : 0 ≤ E T)
    (hL : IntervalIntegrable L volume 0 T) (ha : IntervalIntegrable a volume 0 T)
    (hd : IntervalIntegrable (fun t => a t * g t) volume 0 T)
    (hL0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ L t)
    (ha0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ a t)
    (hg0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ g t)
    (hcap : ∀ᵐ t, t ∈ Icc 0 T → a t ≤ g t / h ^ (5 / 2 : ℝ))
    (hinit : E 0 ≤ C₁ * h ^ 2)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T → deriv E t + 2 * (a t * g t) ≤ 4 * L t * E t) :
    let C := (1 / 2 : ℝ) * Real.exp (4 * ∫ t in 0..T, L t) * C₁
    E T ≤ (2 * C) * h ^ 2 ∧
    (∫ t in 0..T, a t * g t) ≤ C * h ^ 2 ∧
    (∫ t in 0..T, a t) ≤ Real.sqrt (T * C) * h ^ (-1 / 4 : ℝ) ∧
    ((∀ᵐ t, t ∈ Icc 0 T → a t = g t / h ^ (5 / 2 : ℝ)) →
      (∫ t in 0..T, (g t / h ^ 2) ^ 2) ≤ C * h ^ (1 / 2 : ℝ)) := by
  dsimp only
  let C := (1 / 2 : ℝ) * Real.exp (4 * ∫ t in 0..T, L t) * C₁
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ a t * g t := by
    filter_upwards [ha0, hg0] with t ht hg htmem
    exact mul_nonneg (ht htmem) (hg htmem)
  obtain ⟨he, hdiss⟩ := energy_dissipation_estimates hT.le hE hET hL hd hL0 hq0 hineq
  have hinite := mul_le_mul_of_nonneg_left hinit
    (Real.exp_pos (4 * ∫ t in 0..T, L t)).le
  have hinitd := mul_le_mul_of_nonneg_left hinit
    (show 0 ≤ (1 / 2 : ℝ) * Real.exp (4 * ∫ t in 0..T, L t) by positivity)
  have henergy : E T ≤ (2 * C) * h ^ 2 := by dsimp [C]; nlinarith
  have hdiss' : (∫ t in 0..T, a t * g t) ≤ C * h ^ 2 := by dsimp [C]; nlinarith
  let μ := volume.restrict (Ioc 0 T)
  have hm : μ.real univ = T := by simp [μ, measureReal_def, Real.volume_Ioc, hT.le]
  have hμpos : 0 < μ.real univ := by rw [hm]; exact hT
  have haμ : Integrable a μ := ha.1
  have hdμ : Integrable (fun t => a t * g t) μ := hd.1
  have ha0μ : ∀ᵐ t ∂μ, 0 ≤ a t := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [ha0] with t ht htmem
    exact ht ⟨htmem.1.le, htmem.2⟩
  have hcapμ : ∀ᵐ t ∂μ, a t ≤ g t / h ^ (5 / 2 : ℝ) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hcap] with t ht htmem
    exact ht ⟨htmem.1.le, htmem.2⟩
  have ha2 := integrable_feedback_sq (Real.rpow_pos_of_pos hh _) haμ.aestronglyMeasurable
    hdμ ha0μ hcapμ
  have hdμbound : (∫ t, a t * g t ∂μ) ≤ C * h ^ 2 := by
    simpa only [intervalIntegral.integral_of_le hT.le] using hdiss'
  have hbudget := feedback_budget_mesh hμpos hh hC haμ ha2 hdμ ha0μ hcapμ hdμbound
  rw [hm] at hbudget
  refine ⟨henergy, hdiss', ?_, ?_⟩
  · simpa only [μ, C, intervalIntegral.integral_of_le hT.le] using hbudget
  · intro hfull
    have hfullμ : ∀ᵐ t ∂μ, a t = g t / h ^ (5 / 2 : ℝ) := by
      apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [hfull] with t ht htmem
      exact ht ⟨htmem.1.le, htmem.2⟩
    have hc := full_feedback_centroid_estimate hh hfullμ hdμ hdμbound
    simpa only [μ, C, intervalIntegral.integral_of_le hT.le] using hc.2

end Lloyd
