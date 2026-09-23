import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic

/-!
# Couplings and an elementary Wasserstein bound

We use the infimum of transport cost over measures with the prescribed
marginals, with values in `ℝ≥0∞`. This applies to finite equal-mass measures,
without normalizing their mass to one. Empty coupling sets give infinity.

The actual histogram/flow measures and their time-dependent comparison from
Theorem 2.1 have not yet been constructed. The proved common-source coupling
is one prerequisite for that construction.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Lloyd

variable {X : Type*} [MeasurableSpace X]

/-- A positive transport measure with two specified marginals. -/
structure TransportCoupling (μ ν : Measure X) where
  plan : Measure (X × X)
  first_marginal : plan.map Prod.fst = μ
  second_marginal : plan.map Prod.snd = ν

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- First Wasserstein transport cost for positive measures of arbitrary mass. -/
noncomputable def wassersteinOne (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ γ : TransportCoupling μ ν, ∫⁻ z, edist z.1 z.2 ∂γ.plan

omit [BorelSpace X] [SecondCountableTopology X] in
theorem wassersteinOne_le_cost {μ ν : Measure X} (γ : TransportCoupling μ ν) :
    wassersteinOne μ ν ≤ ∫⁻ z, edist z.1 z.2 ∂γ.plan :=
  iInf_le _ γ

/-- Couple two images of one measure by using the same source point. -/
noncomputable def couplingOfMaps {S : Type*} [MeasurableSpace S]
    (σ : Measure S) {f g : S → X} (hf : Measurable f) (hg : Measurable g) :
    TransportCoupling (σ.map f) (σ.map g) where
  plan := σ.map (fun x => (f x, g x))
  first_marginal := by rw [Measure.map_map measurable_fst (hf.prodMk hg)]; rfl
  second_marginal := by rw [Measure.map_map measurable_snd (hf.prodMk hg)]; rfl

/-- The common-source coupling bounds Wasserstein distance by the average displacement. -/
theorem wassersteinOne_maps_le {S : Type*} [MeasurableSpace S]
    (σ : Measure S) {f g : S → X} (hf : Measurable f) (hg : Measurable g) :
    wassersteinOne (σ.map f) (σ.map g) ≤ ∫⁻ x, edist (f x) (g x) ∂σ := by
  have hc := wassersteinOne_le_cost (couplingOfMaps σ hf hg)
  simpa only [couplingOfMaps, lintegral_map (measurable_fst.edist measurable_snd) (hf.prodMk hg)]
    using hc

/-- A uniform displacement `d` gives cost at most `d` times total mass. -/
theorem wassersteinOne_maps_le_mass_mul {S : Type*} [MeasurableSpace S]
    (σ : Measure S) {f g : S → X} {d : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hbound : ∀ᵐ x ∂σ, dist (f x) (g x) ≤ d) :
    wassersteinOne (σ.map f) (σ.map g) ≤ ENNReal.ofReal d * σ univ := by
  apply (wassersteinOne_maps_le σ hf hg).trans
  calc
    _ ≤ ∫⁻ _ : S, ENNReal.ofReal d ∂σ := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hx
    _ = _ := by simp

/-- The elementary histogram-to-generators bound, for a measurable cell selector. -/
theorem wassersteinOne_quantize_le (μ : Measure X) {q : X → X} {d : ℝ}
    (hq : Measurable q) (hbound : ∀ᵐ x ∂μ, dist x (q x) ≤ d) :
    wassersteinOne μ (μ.map q) ≤ ENNReal.ofReal d * μ univ := by
  simpa using wassersteinOne_maps_le_mass_mul μ measurable_id hq hbound

end Lloyd
