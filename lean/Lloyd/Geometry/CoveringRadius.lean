import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Quantization energy and covering radius

The metric argument in (4.16): a ball about a point far from all generators
contributes a definite amount to the quantization energy. This works on any
finite metric measure space with the stated two-dimensional ball-volume bound.
The flat-torus ball-volume bound remains to be supplied separately.
-/

open MeasureTheory Metric Set

namespace Lloyd

variable {X : Type*} [MetricSpace X]

/-- Closed Voronoi cell, allowing shared cell boundaries. -/
def voronoiCell (sites : Set X) (p : X) : Set X :=
  {y | ∀ q ∈ sites, dist y p ≤ dist y q}

theorem dist_eq_infDist_of_mem_voronoiCell {sites : Set X} {p y : X}
    (hp : p ∈ sites) (hy : y ∈ voronoiCell sites p) :
    dist y p = infDist y sites := by
  exact le_antisymm ((le_infDist ⟨p, hp⟩).mpr hy) (infDist_le_dist_of_mem hp)

/-- Each cell has diameter at most twice any global covering-radius bound. -/
theorem voronoiCell_diam_le {sites : Set X} {p : X} {R : ℝ}
    (hp : p ∈ sites) (hR : 0 ≤ R) (hcover : ∀ y, infDist y sites ≤ R) :
    Metric.diam (voronoiCell sites p) ≤ 2 * R := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  calc
    dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
    _ = infDist x sites + infDist y sites := by
      rw [dist_comm p y, dist_eq_infDist_of_mem_voronoiCell hp hx,
        dist_eq_infDist_of_mem_voronoiCell hp hy]
    _ ≤ 2 * R := by linarith [hcover x, hcover y]

/-- The nearest-site distance is at least half its value at the center of this ball. -/
theorem half_radius_le_infDist {sites : Set X} {z y : X} {R : ℝ}
    (hz : infDist z sites = R) (hy : y ∈ ball z (R / 2)) :
    R / 2 ≤ infDist y sites := by
  have hd := infDist_le_infDist_add_dist (x := z) (y := y) (s := sites)
  rw [hz, dist_comm z y] at hd
  have hball : dist y z < R / 2 := hy
  linarith

variable [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The integral definition of the quadratic quantization energy. -/
noncomputable def quantizationEnergy (μ : Measure X) (sites : Set X) : ℝ :=
  ∫ y, (infDist y sites) ^ 2 ∂μ

/-- The ball at half the covering radius gives the energy lower bound (4.16). -/
theorem quantizationEnergy_ge_ball {sites : Set X} {z : X} {R : ℝ}
    (hz : infDist z sites = R)
    (hi : Integrable (fun y => (infDist y sites) ^ 2) μ) :
    R ^ 2 / 4 * μ.real (ball z (R / 2)) ≤ quantizationEnergy μ sites := by
  have hR : 0 ≤ R := hz ▸ infDist_nonneg
  calc
    _ = ∫ _ in ball z (R / 2), R ^ 2 / 4 ∂μ := by
      simp [mul_comm]
    _ ≤ ∫ y in ball z (R / 2), (infDist y sites) ^ 2 ∂μ := by
      apply integral_mono_ae (integrable_const _) (hi.mono_measure Measure.restrict_le_self)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have h := half_radius_le_infDist hz hy
      nlinarith [infDist_nonneg (x := y) (s := sites)]
    _ ≤ quantizationEnergy μ sites := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun y => sq_nonneg (infDist y sites))) hi

/-- Two-dimensional volume growth gives the fourth-power radius bound. -/
theorem quantizationEnergy_ge_radius_fourth {sites : Set X} {z : X} {R c : ℝ}
    (hz : infDist z sites = R)
    (hi : Integrable (fun y => (infDist y sites) ^ 2) μ)
    (hball : c * (R / 2) ^ 2 ≤ μ.real (ball z (R / 2))) :
    c / 16 * R ^ 4 ≤ quantizationEnergy μ sites := by
  have hb := quantizationEnergy_ge_ball hz hi
  have hm := mul_le_mul_of_nonneg_left hball (show 0 ≤ R ^ 2 / 4 by positivity)
  nlinarith

end Lloyd
