import Lloyd.Geometry.CoveringRadius
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Lifted periodic Voronoi cells and the bisector argument

The additive subgroup is left arbitrary here. Finiteness and positive volume of each cell
are explicit hypotheses of the centroid lemmas in this file.
`LatticeGeometry.lean` derives them for a full-rank basis lattice, and
`Quantization.lean` applies the centroid results to the actual cells.
-/

open MeasureTheory Metric Set
open scoped InnerProductSpace

namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Euclidean Voronoi comparison is an affine half-space inequality. -/
theorem dist_le_dist_iff_inner (x p q : E) :
    dist x p ≤ dist x q ↔ (‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 ≤ ⟪x, p - q⟫_ℝ := by
  rw [dist_eq_norm, dist_eq_norm,
    ← sq_le_sq₀ (norm_nonneg (x - p)) (norm_nonneg (x - q)),
    norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
  constructor <;> intro h <;> nlinarith

/-- Voronoi cells in a real inner product space are convex. -/
theorem convex_voronoiCell (sites : Set E) (p : E) : Convex ℝ (voronoiCell sites p) := by
  intro x hx y hy a b ha hb hab q hq
  rw [dist_le_dist_iff_inner]
  have hx' := (dist_le_dist_iff_inner x p q).mp (hx q hq)
  have hy' := (dist_le_dist_iff_inner y p q).mp (hy q hq)
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

omit [InnerProductSpace ℝ E] in
theorem isClosed_voronoiCell (sites : Set E) (p : E) : IsClosed (voronoiCell sites p) := by
  have heq : voronoiCell sites p = ⋂ q ∈ sites, {y | dist y p ≤ dist y q} := by
    ext y
    simp [voronoiCell]
  rw [heq]
  exact isClosed_iInter (fun q => isClosed_iInter (fun _ =>
    isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)))

/-- Two points in opposite Voronoi half-spaces satisfy the bisector inequality. -/
theorem bisector_inner_nonneg {p q u v : E}
    (hu : dist u p ≤ dist u q) (hv : dist v q ≤ dist v p) :
    0 ≤ ⟪p - q, u - v⟫_ℝ := by
  have hu' := (dist_le_dist_iff_inner u p q).mp hu
  have hv' := (dist_le_dist_iff_inner v q p).mp hv
  rw [real_inner_comm, inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [inner_sub_right] at hu' hv'
  linarith

/-- All lattice translates of all generators. -/
def periodicSites {ι : Type*} (Λ : AddSubgroup E) (x : ι → E) : Set E :=
  Set.range (fun z : ι × Λ => x z.1 + (z.2 : E))

/-- The convex lifted cell of a representative of generator `i`. -/
def periodicCell {ι : Type*} (Λ : AddSubgroup E) (x : ι → E) (i : ι) : Set E :=
  voronoiCell (periodicSites Λ x) (x i)

omit [InnerProductSpace ℝ E] in
theorem mem_periodicCell_iff {ι : Type*} {Λ : AddSubgroup E} {x : ι → E} {i : ι} {y : E} :
    y ∈ periodicCell Λ x i ↔ ∀ j (k : Λ), dist y (x i) ≤ dist y (x j + (k : E)) := by
  constructor
  · intro hy j k
    exact hy _ ⟨(j, k), rfl⟩
  · intro hy q hq
    rcases hq with ⟨⟨j, k⟩, rfl⟩
    exact hy j k

omit [InnerProductSpace ℝ E] in
theorem generator_mem_periodicCell {ι : Type*} (Λ : AddSubgroup E) (x : ι → E) (i : ι) :
    x i ∈ periodicCell Λ x i := by
  rw [mem_periodicCell_iff]
  intro j k
  simp

/-- The periodic version of the geometric inequality used to prevent collisions. -/
theorem periodic_bisector_inner_nonneg {ι : Type*} {Λ : AddSubgroup E} {x : ι → E}
    {i j : ι} {ci cj : E} (hi : ci ∈ periodicCell Λ x i) (hj : cj ∈ periodicCell Λ x j)
    (k : Λ) : 0 ≤ ⟪x i - x j - (k : E), ci - cj - (k : E)⟫_ℝ := by
  have hci := (mem_periodicCell_iff.mp hi) j k
  have hcj := (mem_periodicCell_iff.mp hj) i (-k)
  have hcj' : dist (cj + (k : E)) (x j + (k : E)) ≤ dist (cj + (k : E)) (x i) := by
    convert hcj using 1 <;> simp only [dist_eq_norm, AddSubgroup.coe_neg] <;>
      congr 1 <;> abel
  have h := bisector_inner_nonneg hci hcj'
  convert h using 1
  congr 1 <;> abel

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The actual integral centroid of a cell, not a freely chosen point in it. -/
noncomputable def cellCentroid (μ : Measure E) (P : Set E) : E := ⨍ y in P, y ∂μ

/-- A finite positive-volume Voronoi cell contains its integral centroid. -/
theorem cellCentroid_mem_voronoiCell (μ : Measure E) (sites : Set E) (p : E)
    (h0 : μ (voronoiCell sites p) ≠ 0) (hfin : μ (voronoiCell sites p) ≠ ⊤)
    (hi : IntegrableOn (fun y : E => y) (voronoiCell sites p) μ) :
    cellCentroid μ (voronoiCell sites p) ∈ voronoiCell sites p := by
  exact (convex_voronoiCell sites p).set_average_mem (isClosed_voronoiCell sites p) h0 hfin
    (ae_restrict_mem (isClosed_voronoiCell sites p).measurableSet) hi

/-- In particular the centroid displacement is bounded by a global covering radius. -/
theorem cellCentroid_displacement_le (μ : Measure E) {sites : Set E} {p : E} {R : ℝ}
    (hp : p ∈ sites) (hcover : ∀ y, infDist y sites ≤ R)
    (h0 : μ (voronoiCell sites p) ≠ 0) (hfin : μ (voronoiCell sites p) ≠ ⊤)
    (hi : IntegrableOn (fun y : E => y) (voronoiCell sites p) μ) :
    ‖cellCentroid μ (voronoiCell sites p) - p‖ ≤ R := by
  rw [← dist_eq_norm, dist_eq_infDist_of_mem_voronoiCell hp
    (cellCentroid_mem_voronoiCell μ sites p h0 hfin hi)]
  exact hcover _

end Lloyd
