import Lloyd.Geometry.PeriodicCell
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Positive finite cell volumes from separation and covering

A separated generator has a ball inside its cell. A covering bound confines
the cell to a compact ball. These facts supply the measure hypotheses of the
centroid lemmas. `LatticeGeometry.lean` supplies the separation
and covering bounds for finite periodic configurations of a basis lattice.
-/

open MeasureTheory Metric Set

namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E]

/-- Half the generator separation is an inscribed cell radius. -/
theorem ball_subset_voronoiCell_of_separated {sites : Set E} {p : E} {r : ℝ}
    (hsep : ∀ q ∈ sites, q ≠ p → 2 * r ≤ dist p q) :
    ball p r ⊆ voronoiCell sites p := by
  intro y hy q hq
  by_cases heq : q = p
  · simp [heq]
  · have hs := hsep q hq heq
    have ht := dist_triangle p y q
    rw [dist_comm p y] at ht
    have hy' : dist y p < r := hy
    linarith

/-- A global covering bound confines each cell to the corresponding closed ball. -/
theorem voronoiCell_subset_closedBall {sites : Set E} {p : E} {R : ℝ}
    (hp : p ∈ sites) (hcover : ∀ y, infDist y sites ≤ R) :
    voronoiCell sites p ⊆ closedBall p R := by
  intro y hy
  change dist y p ≤ R
  rw [dist_eq_infDist_of_mem_voronoiCell hp hy]
  exact hcover y

variable [ProperSpace E]

/-- Lifted cells are compact once their nearest-site distance is uniformly bounded. -/
theorem isCompact_voronoiCell {sites : Set E} {p : E} {R : ℝ}
    (hp : p ∈ sites) (hcover : ∀ y, infDist y sites ≤ R) :
    IsCompact (voronoiCell sites p) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_voronoiCell sites p)
    (isBounded_closedBall.subset (voronoiCell_subset_closedBall hp hcover))

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsLocallyFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]

/-- The positive-finite-volume and integrability conditions required by the
centroid construction, deduced from explicit separation and covering. -/
theorem voronoiCell_measure_properties {sites : Set E} {p : E} {r R : ℝ}
    (hp : p ∈ sites) (hr : 0 < r)
    (hsep : ∀ q ∈ sites, q ≠ p → 2 * r ≤ dist p q)
    (hcover : ∀ y, infDist y sites ≤ R) :
    μ (voronoiCell sites p) ≠ 0 ∧ μ (voronoiCell sites p) ≠ ⊤ ∧
      IntegrableOn (fun y : E => y) (voronoiCell sites p) μ := by
  have hc := isCompact_voronoiCell hp hcover
  have hpos := (measure_ball_pos μ p hr).trans_le
    (measure_mono (ball_subset_voronoiCell_of_separated hsep))
  exact ⟨ne_of_gt hpos, hc.measure_ne_top, continuousOn_id.integrableOn_compact hc⟩

end Lloyd
