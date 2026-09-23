import Lloyd.Analysis.ParticleDynamics
import Lloyd.Transport.Coupling
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The OSL mollification calculation in Appendix B

The mollifier is a probability measure with zero first moment, supported in a
ball of radius `ε`. Thus periodic convolution is represented by an actual
Bochner integral. Existence of Filippov trajectories and the classical OSL
property of their selections are inputs; the averaging/error calculation is
proved here, not assumed.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The shifted OSL inequality, before averaging the zero-mean perturbation. -/
theorem shifted_osl_comparison {u w e z : E} {L ε V : ℝ}
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hz : ‖z‖ ≤ ε) (hu : ‖u‖ ≤ V)
    (hosl : ⟪u - w, e - z⟫_ℝ ≤ L * ‖e - z‖ ^ 2) :
    ⟪e, u - w⟫_ℝ ≤ L * (‖e‖ ^ 2 + ε ^ 2) + ε * V -
      ⟪(2 * L) • e + w, z⟫_ℝ := by
  have hz2 : ‖z‖ ^ 2 ≤ ε ^ 2 := (sq_le_sq₀ (norm_nonneg _) hε).mpr hz
  have hi := real_inner_le_norm u z
  have hprod : ‖u‖ * ‖z‖ ≤ V * ε := mul_le_mul hu hz (norm_nonneg _) hV
  rw [inner_sub_left, inner_sub_right, inner_sub_right, norm_sub_sq_real] at hosl
  rw [inner_sub_right, inner_add_left, real_inner_smul_left]
  have heu := real_inner_comm e u
  have hew := real_inner_comm e w
  nlinarith [mul_le_mul_of_nonneg_left hz2 hL]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Average the shifted comparison. The terms involving the mean displacement
vanish, including the term containing the Filippov selection `w`. -/
theorem averaged_osl_comparison (η : Measure E) [IsProbabilityMeasure η]
    {u : E → E} {w e : E} {L ε V : ℝ}
    (hu : Integrable u η) (hz : Integrable (fun z : E => z) η)
    (hmean : (∫ z, z ∂η) = 0)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hsupport : ∀ᵐ z ∂η, ‖z‖ ≤ ε) (hbound : ∀ᵐ z ∂η, ‖u z‖ ≤ V)
    (hosl : ∀ᵐ z ∂η, ⟪u z - w, e - z⟫_ℝ ≤ L * ‖e - z‖ ^ 2) :
    ⟪e, (∫ z, u z ∂η) - w⟫_ℝ ≤ L * (‖e‖ ^ 2 + ε ^ 2) + ε * V := by
  let K := L * (‖e‖ ^ 2 + ε ^ 2) + ε * V
  have hi := integral_mono_ae
    ((innerSL ℝ e).integrable_comp (hu.sub (integrable_const w)))
    ((integrable_const K).sub ((innerSL ℝ ((2 * L) • e + w)).integrable_comp hz))
    (by
      filter_upwards [hsupport, hbound, hosl] with z hz hu ho
      exact shifted_osl_comparison hL hε hV hz hu ho)
  change (∫ z, ⟪e, u z - w⟫_ℝ ∂η) ≤
    ∫ z, K - ⟪(2 * L) • e + w, z⟫_ℝ ∂η at hi
  have heq : (∫ z, ⟪e, u z - w⟫_ℝ ∂η) = ⟪e, ∫ z, u z - w ∂η⟫_ℝ :=
    (innerSL ℝ e).integral_comp_comm (hu.sub (integrable_const w))
  have heqz : (∫ z, ⟪(2 * L) • e + w, z⟫_ℝ ∂η) = ⟪(2 * L) • e + w, ∫ z, z ∂η⟫_ℝ :=
    (innerSL ℝ ((2 * L) • e + w)).integral_comp_comm hz
  have hzinner : Integrable (fun z => ⟪(2 * L) • e + w, z⟫_ℝ) η :=
    (innerSL ℝ ((2 * L) • e + w)).integrable_comp hz
  rw [heq, integral_sub hu (integrable_const w),
    integral_sub (integrable_const K) hzinner, heqz] at hi
  simpa [hmean, K] using hi

/-- Spatial convolution against the mollifier (using periodic lifts when the
velocity is periodic). -/
noncomputable def mollifiedVelocity (η : Measure E) (v : E → E) (x : E) : E :=
  ∫ z, v (x - z) ∂η

omit [BorelSpace E] in
/-- Mollification preserves the same OSL constant. -/
theorem mollifiedVelocity_osl (η : Measure E) [IsProbabilityMeasure η]
    {v : E → E} {x y : E} {L : ℝ}
    (hx : Integrable (fun z => v (x - z)) η)
    (hy : Integrable (fun z => v (y - z)) η)
    (hosl : ∀ᵐ z ∂η,
      ⟪x - y, v (x - z) - v (y - z)⟫_ℝ ≤ L * ‖x - y‖ ^ 2) :
    ⟪x - y, mollifiedVelocity η v x - mollifiedVelocity η v y⟫_ℝ ≤
      L * ‖x - y‖ ^ 2 := by
  have hi := integral_mono_ae ((innerSL ℝ (x - y)).integrable_comp (hx.sub hy))
    (integrable_const (L * ‖x - y‖ ^ 2)) hosl
  rw [(innerSL ℝ (x - y)).integral_comp_comm (hx.sub hy)] at hi
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hx hy] at hi
  change ⟪x - y, (∫ z, v (x - z) ∂η) - ∫ z, v (y - z) ∂η⟫_ℝ ≤
    ∫ _, L * ‖x - y‖ ^ 2 ∂η at hi
  simpa only [integral_const, probReal_univ, one_smul, mollifiedVelocity] using hi

omit [BorelSpace E] in
/-- Global OSL for the original velocity supplies the translated hypotheses
in the convolution lemma, with exactly the same constant. -/
theorem mollifiedVelocity_osl_of_osl (η : Measure E) [IsProbabilityMeasure η]
    {v : E → E} {x y : E} {L : ℝ}
    (hx : Integrable (fun z => v (x - z)) η)
    (hy : Integrable (fun z => v (y - z)) η)
    (hosl : ∀ p q, ⟪p - q, v p - v q⟫_ℝ ≤ L * ‖p - q‖ ^ 2) :
    ⟪x - y, mollifiedVelocity η v x - mollifiedVelocity η v y⟫_ℝ ≤ L * ‖x - y‖ ^ 2 := by
  apply mollifiedVelocity_osl η hx hy
  apply Filter.Eventually.of_forall
  intro z
  have heq : (x - z) - (y - z) = x - y := by abel
  simpa only [heq] using hosl (x - z) (y - z)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared-error derivative for two trajectories with the indicated
instantaneous velocities. No continuity of the velocity in time is assumed. -/
theorem mollified_error_derivative {x y : ℝ → E} {t : ℝ} {u w : E} {L ε V : ℝ}
    (hx : HasDerivAt x u t) (hy : HasDerivAt y w t)
    (hcomparison : ⟪x t - y t, u - w⟫_ℝ ≤
      L * (‖x t - y t‖ ^ 2 + ε ^ 2) + ε * V) :
    deriv (fun s => ‖x s - y s‖ ^ 2) t ≤
      2 * L * ‖x t - y t‖ ^ 2 + 2 * (L * ε ^ 2 + ε * V) := by
  have hd := (hx.sub hy).norm_sq.deriv
  simp only [Pi.sub_apply] at hd
  rw [hd]
  linarith

/-- Forced Gronwall, using the already checked absolutely continuous energy
lemma. This allows merely integrable time coefficients. -/
theorem forced_squared_error_bound {s L f : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hs : AbsolutelyContinuousOnInterval s 0 T)
    (h0 : s 0 = 0) (hST : 0 ≤ s T)
    (hL : IntervalIntegrable L volume 0 T) (hf : IntervalIntegrable f volume 0 T)
    (hL0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ L t)
    (hf0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ f t)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T → deriv s t ≤ 2 * L t * s t + 2 * f t) :
    s T ≤ 2 * Real.exp (2 * ∫ t in 0..T, L t) * ∫ t in 0..T, f t := by
  let I : ℝ → ℝ := fun t => ∫ u in 0..t, f u
  let E : ℝ → ℝ := fun t => s t + 2 * (I T - I t)
  have hI : AbsolutelyContinuousOnInterval I 0 T :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => I T) 0 T :=
    (LipschitzWith.const (I T)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hE : AbsolutelyContinuousOnInterval E 0 T := hs.fun_add ((hconst.fun_sub hI).const_mul 2)
  have hf0' : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] f := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hf0] with t ht htmem
    exact ht ⟨htmem.1.le, htmem.2⟩
  have htail : ∀ t ∈ Icc 0 T, 0 ≤ I T - I t := by
    intro t ht
    exact sub_nonneg.mpr (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hf0' hf)
  have hi : ∀ᵐ t, t ∈ Icc 0 T → deriv E t + 2 * (0 : ℝ) ≤ 4 * ((1/2 : ℝ) * L t) * E t := by
    filter_upwards [hf.ae_hasDerivAt_integral, hs.ae_differentiableAt, hL0, hineq]
      with t hit hst hLt het ht
    have htu : t ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using ht
    have hdI : HasDerivAt I (f t) t := hit htu 0 (by simp)
    have hdE : HasDerivAt E (deriv s t + 2 * (-f t)) t :=
      (hst htu).hasDerivAt.add ((hdI.const_sub (I T)).const_mul 2)
    rw [hdE.deriv]
    dsimp [E]
    have hpos := mul_nonneg (hLt ht) (htail t ht)
    nlinarith [het ht]
  have hresult := energy_dissipation_estimates hT hE (by simpa [E] using hST)
    (hL.const_mul (1/2)) (intervalIntegrable_const (c := (0 : ℝ)))
    (by filter_upwards [hL0] with t ht htmem; exact mul_nonneg (by norm_num) (ht htmem))
    (Filter.Eventually.of_forall (fun _ _ => le_rfl)) hi
  have h := hresult.1
  simp only [E, sub_self, mul_zero, add_zero, I, intervalIntegral.integral_same, sub_zero,
    h0, zero_add, intervalIntegral.integral_const_mul] at h
  have he : 4 * ((1/2 : ℝ) * (∫ t in 0..T, L t)) = 2 * (∫ t in 0..T, L t) := by ring
  rw [he] at h
  nlinarith

/-- The explicit Appendix B squared-error bound; no factor depends on `ε`
through a Lipschitz norm of the smoothed field. -/
theorem mollification_squared_error_bound {s L V : ℝ → ℝ} {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 ≤ ε) (hs : AbsolutelyContinuousOnInterval s 0 T)
    (h0 : s 0 = 0) (hST : 0 ≤ s T)
    (hL : IntervalIntegrable L volume 0 T) (hV : IntervalIntegrable V volume 0 T)
    (hL0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ L t)
    (hV0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ V t)
    (hineq : ∀ᵐ t, t ∈ Icc 0 T →
      deriv s t ≤ 2 * L t * s t + 2 * (L t * ε ^ 2 + ε * V t)) :
    s T ≤ 2 * Real.exp (2 * ∫ t in 0..T, L t) *
      (ε ^ 2 * (∫ t in 0..T, L t) + ε * (∫ t in 0..T, V t)) := by
  have hf := (hL.mul_const (ε ^ 2)).add (hV.const_mul ε)
  have h := forced_squared_error_bound hT hs h0 hST hL hf hL0
    (by
      filter_upwards [hL0, hV0] with t hLt hVt ht
      exact add_nonneg (mul_nonneg (hLt ht) (sq_nonneg _)) (mul_nonneg hε (hVt ht))) hineq
  rw [intervalIntegral.integral_add (hL.mul_const _) (hV.const_mul _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul] at h
  simpa only [mul_comm] using h

omit [BorelSpace E] in
/-- Connect the integral mollification calculation to actual absolutely
continuous trajectories. The unsmoothed selection's shifted OSL property is
an explicit classical Filippov input. -/
theorem mollified_trajectory_comparison (η : Measure E) [IsProbabilityMeasure η]
    {v : ℝ → E → E} {x y w : ℝ → E} {L V : ℝ → ℝ} {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hy : AbsolutelyContinuousOnInterval y 0 T) (hinit : x 0 = y 0)
    (hz : Integrable (fun z : E => z) η) (hmean : (∫ z, z ∂η) = 0)
    (hsupport : ∀ᵐ z ∂η, ‖z‖ ≤ ε)
    (hL : IntervalIntegrable L volume 0 T) (hV : IntervalIntegrable V volume 0 T)
    (hL0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ L t)
    (hV0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ V t)
    (hvel : ∀ᵐ t, t ∈ Icc 0 T → Integrable (fun z => v t (x t - z)) η)
    (hbound : ∀ᵐ t, t ∈ Icc 0 T → ∀ᵐ z ∂η, ‖v t (x t - z)‖ ≤ V t)
    (hosl : ∀ᵐ t, t ∈ Icc 0 T → ∀ᵐ z ∂η,
      ⟪v t (x t - z) - w t, (x t - y t) - z⟫_ℝ ≤ L t * ‖(x t - y t) - z‖ ^ 2)
    (hxode : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt x (mollifiedVelocity η (v t) (x t)) t)
    (hyode : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt y (w t) t) :
    ‖x T - y T‖ ^ 2 ≤ 2 * Real.exp (2 * ∫ t in 0..T, L t) *
      (ε ^ 2 * (∫ t in 0..T, L t) + ε * (∫ t in 0..T, V t)) := by
  apply mollification_squared_error_bound hT hε (ac_norm_sq (hx.fun_sub hy))
    (by simp [hinit]) (sq_nonneg _) hL hV hL0 hV0
  filter_upwards [hL0, hV0, hvel, hbound, hosl, hxode, hyode]
    with t hLt hVt hvt hbt hot hxt hyt ht
  apply mollified_error_derivative (hxt ht) (hyt ht)
  exact averaged_osl_comparison η (hvt ht) hz hmean (hLt ht) hε (hVt ht)
    hsupport (hbt ht) (hot ht)

/-- Passing from time-dependent integral bounds to their terminal values gives
the uniform-in-time bound stated in Appendix B. -/
theorem mollification_uniform_bound {s L V : ℝ → ℝ} {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hL : IntervalIntegrable L volume 0 T) (hV : IntervalIntegrable V volume 0 T)
    (hL0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ L t)
    (hV0 : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ V t)
    (hpoint : ∀ t ∈ Icc 0 T,
      s t ≤ 2 * Real.exp (2 * ∫ u in 0..t, L u) *
        (ε ^ 2 * (∫ u in 0..t, L u) + ε * (∫ u in 0..t, V u))) :
    ∀ t ∈ Icc 0 T, s t ≤ 2 * Real.exp (2 * ∫ u in 0..T, L u) *
      (ε ^ 2 * (∫ u in 0..T, L u) + ε * (∫ u in 0..T, V u)) := by
  have hmono : ∀ (f : ℝ → ℝ), IntervalIntegrable f volume 0 T →
      (∀ᵐ t, t ∈ Icc 0 T → 0 ≤ f t) →
      ∀ t ∈ Icc 0 T, 0 ≤ (∫ u in 0..t, f u) ∧ (∫ u in 0..t, f u) ≤ ∫ u in 0..T, f u := by
    intro f hf hf0 t ht
    have hf0' : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] f := by
      apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [hf0] with u hu humem
      exact hu ⟨humem.1.le, humem.2⟩
    constructor
    · have htint : IntervalIntegrable f volume 0 t := hf.mono_set (by
        simp only [uIcc_of_le hT, uIcc_of_le ht.1]
        exact Icc_subset_Icc le_rfl ht.2)
      have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 t)] f := by
        apply (ae_restrict_iff' measurableSet_Ioc).mpr
        filter_upwards [hf0] with u hu humem
        exact hu ⟨humem.1.le, humem.2.trans ht.2⟩
      have hh := intervalIntegral.integral_mono_interval (f := f) le_rfl le_rfl ht.1 hnonneg htint
      simpa using hh
    · exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hf0' hf
  intro t ht
  obtain ⟨hLt, hLT⟩ := hmono L hL hL0 t ht
  obtain ⟨hVt, hVT⟩ := hmono V hV hV0 t ht
  have he : Real.exp (2 * ∫ u in 0..t, L u) ≤ Real.exp (2 * ∫ u in 0..T, L u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hf : ε ^ 2 * (∫ u in 0..t, L u) + ε * (∫ u in 0..t, V u) ≤
      ε ^ 2 * (∫ u in 0..T, L u) + ε * (∫ u in 0..T, V u) :=
    add_le_add (mul_le_mul_of_nonneg_left hLT (sq_nonneg ε)) (mul_le_mul_of_nonneg_left hVT hε)
  exact (hpoint t ht).trans (mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hf
    (by positivity) (by positivity))

/-- Take a square root and extract the `sqrt ε` rate for `0 ≤ ε ≤ 1`. -/
theorem mollification_sqrt_rate {d ε Λ V : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hd : 0 ≤ d) (hΛ : 0 ≤ Λ) (hV : 0 ≤ V)
    (hbound : d ^ 2 ≤ 2 * Real.exp (2 * Λ) * (ε ^ 2 * Λ + ε * V)) :
    d ≤ Real.sqrt (2 * Real.exp (2 * Λ) * (Λ + V)) * Real.sqrt ε := by
  have hεsq : ε ^ 2 ≤ ε := by nlinarith
  have hp : 0 ≤ 2 * Real.exp (2 * Λ) := by positivity
  have hb : d ^ 2 ≤ (2 * Real.exp (2 * Λ) * (Λ + V)) * ε := by
    have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεsq hΛ) hp
    nlinarith
  have h := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq hd, Real.sqrt_mul (by positivity)] at h
  exact h

/-- The final common-source transport bound, valid for arbitrary total mass. -/
theorem mollification_transport_bound {S X : Type*} [MeasurableSpace S]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (σ : Measure S) {f g : S → X} {ε Λ V : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hΛ : 0 ≤ Λ) (hV : 0 ≤ V)
    (hbound : ∀ᵐ z ∂σ, dist (f z) (g z) ^ 2 ≤
      2 * Real.exp (2 * Λ) * (ε ^ 2 * Λ + ε * V)) :
    wassersteinOne (σ.map f) (σ.map g) ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.exp (2 * Λ) * (Λ + V)) * Real.sqrt ε) * σ univ := by
  apply wassersteinOne_maps_le_mass_mul σ hf hg
  filter_upwards [hbound] with z hz
  exact mollification_sqrt_rate hε hε1 dist_nonneg hΛ hV hz

omit [CompleteSpace E] in
/-- Apply the mollification transport estimate to the actual flat torus by
projecting the compared lifts. Quotient distance can only decrease. -/
theorem mollification_torus_transport_bound [FiniteDimensional ℝ E]
    {κ : Type*} [Fintype κ] (b : Module.Basis κ ℝ E)
    {S : Type*} [MeasurableSpace S] (σ : Measure S) {f g : S → E} {ε Λ V : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hΛ : 0 ≤ Λ) (hV : 0 ≤ V)
    (hbound : ∀ᵐ z ∂σ, ‖f z - g z‖ ^ 2 ≤
      2 * Real.exp (2 * Λ) * (ε ^ 2 * Λ + ε * V)) :
    wassersteinOne (σ.map (fun z => torusProjection b (f z)))
      (σ.map (fun z => torusProjection b (g z))) ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.exp (2 * Λ) * (Λ + V)) * Real.sqrt ε) * σ univ := by
  apply mollification_transport_bound σ ((torusProjection b).continuous.measurable.comp hf)
    ((torusProjection b).continuous.measurable.comp hg) hε hε1 hΛ hV
  filter_upwards [hbound] with z hz
  have h := torusProjection_dist_le b (f z) (g z)
  rw [dist_eq_norm (f z) (g z)] at h
  exact ((sq_le_sq₀ dist_nonneg (norm_nonneg _)).mpr h).trans hz

end Lloyd
