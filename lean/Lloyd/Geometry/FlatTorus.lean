import Lloyd.Geometry.LatticeGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The actual flat torus, its metric, and its finite volume measure

A basis of Euclidean space generates a full-rank lattice. We use Mathlib's
quotient metric and push Lebesgue measure on a fundamental parallelepiped to
the quotient. Lifted nearest-site distances agree with nearest-site distances
on this torus; this is a geometric identity, not an assumed estimate.
-/

open MeasureTheory Metric Set Topology

noncomputable section
namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type*}

/-- The quotient by the integer span of a real basis. -/
abbrev FlatTorus (b : Module.Basis κ ℝ E) := E ⧸ basisLattice b

/-- Projection from lifted coordinates to the torus. -/
def torusProjection (b : Module.Basis κ ℝ E) : NormedAddGroupHom E (FlatTorus b) :=
  (basisLattice b).normedMk

theorem torusProjection_surjective (b : Module.Basis κ ℝ E) :
    Function.Surjective (torusProjection b) := (basisLattice b).surjective_normedMk

theorem torusProjection_eq_iff (b : Module.Basis κ ℝ E) (x y : E) :
    torusProjection b x = torusProjection b y ↔ x - y ∈ basisLattice b :=
  QuotientAddGroup.eq_iff_sub_mem

theorem torusProjection_add_lattice (b : Module.Basis κ ℝ E) (x : E) (k : basisLattice b) :
    torusProjection b (x + (k : E)) = torusProjection b x := by
  apply (torusProjection_eq_iff b _ _).mpr
  simp [k.property]

theorem torus_dist_eq_infDist_lattice (b : Module.Basis κ ℝ E) (x y : E) :
    dist (torusProjection b x) (torusProjection b y) = infDist (x - y) (basisLattice b) := by
  rw [dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk (x - y)

theorem torusProjection_dist_le (b : Module.Basis κ ℝ E) (x y : E) :
    dist (torusProjection b x) (torusProjection b y) ≤ dist x y := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact QuotientAddGroup.norm_mk_le_norm

variable [Fintype κ] [FiniteDimensional ℝ E]

/-- A full-rank lattice makes the quotient compact. -/
instance flatTorus_compact (b : Module.Basis κ ℝ E) : CompactSpace (FlatTorus b) := by
  have hc := IsZLattice.isCompact_range_of_periodic
    (Submodule.span ℤ (Set.range b)) (torusProjection b) (torusProjection b).continuous
    (fun z w hw => torusProjection_add_lattice b z ⟨w, hw⟩)
  rw [Set.range_eq_univ.mpr (torusProjection_surjective b)] at hc
  exact ⟨hc⟩

/-- On the torus, a shortest distance is realized by some lattice translate. -/
theorem torus_dist_realized (b : Module.Basis κ ℝ E) (x y : E) :
    ∃ k : basisLattice b,
      dist (torusProjection b x) (torusProjection b y) = dist x (y + (k : E)) := by
  have hc : IsClosed (basisLattice b : Set E) := inferInstance
  obtain ⟨k, hk, heq⟩ := hc.exists_infDist_eq_dist ⟨0, (basisLattice b).zero_mem⟩ (x - y)
  refine ⟨⟨k, hk⟩, ?_⟩
  rw [torus_dist_eq_infDist_lattice, heq, dist_eq_norm, dist_eq_norm]
  congr 1
  abel

/-- Quotient nearest-site distance equals distance to the complete periodic set. -/
theorem torus_infDist_eq_periodic {ι : Type*} [Nonempty ι]
    (b : Module.Basis κ ℝ E) (x : ι → E) (y : E) :
    infDist (torusProjection b y) (Set.range (fun i => torusProjection b (x i))) =
      infDist y (periodicSites (basisLattice b) x) := by
  apply le_antisymm
  · apply (le_infDist ?_).mpr
    · rintro z ⟨⟨i, k⟩, rfl⟩
      calc
        _ ≤ dist (torusProjection b y) (torusProjection b (x i)) :=
          infDist_le_dist_of_mem (s := Set.range (fun j => torusProjection b (x j))) ⟨i, rfl⟩
        _ = dist (torusProjection b y) (torusProjection b (x i + (k : E))) := by
          rw [torusProjection_add_lattice]
        _ ≤ _ := torusProjection_dist_le b _ _
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨x i, (i, 0), by simp⟩
  · apply (le_infDist (Set.range_nonempty _)).mpr
    rintro z ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := torus_dist_realized b y (x i)
    rw [hk]
    exact infDist_le_dist_of_mem ⟨(i, k), rfl⟩

/-- Distinct generators means distinct points of the quotient, not merely
unequal representatives in Euclidean space. -/
def DistinctOnTorus {ι : Type*} (b : Module.Basis κ ℝ E) (x : ι → E) : Prop :=
  Function.Injective (fun i => torusProjection b (x i))

instance flatTorus_measurableSpace (b : Module.Basis κ ℝ E) : MeasurableSpace (FlatTorus b) :=
  borel (FlatTorus b)

instance flatTorus_borelSpace (b : Module.Basis κ ℝ E) : BorelSpace (FlatTorus b) := ⟨rfl⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- Volume on the quotient obtained from one fundamental domain. -/
def torusMeasure (b : Module.Basis κ ℝ E) (μ : Measure E) : Measure (FlatTorus b) :=
  (μ.restrict (ZSpan.fundamentalDomain b)).map (torusProjection b)

omit [Fintype κ] [FiniteDimensional ℝ E] in
theorem torusMeasure_univ (b : Module.Basis κ ℝ E) (μ : Measure E) :
    torusMeasure b μ Set.univ = μ (ZSpan.fundamentalDomain b) := by
  simp [torusMeasure, Measure.map_apply (torusProjection b).continuous.measurable]

instance torusMeasure_finite (b : Module.Basis κ ℝ E) (μ : Measure E)
    [IsLocallyFiniteMeasure μ] : IsFiniteMeasure (torusMeasure b μ) where
  measure_univ_lt_top := by
    rw [torusMeasure_univ]
    exact (measure_mono (ZSpan.fundamentalDomain_subset_parallelepiped b)).trans_lt
      b.parallelepiped.isCompact.measure_lt_top

omit [FiniteDimensional ℝ E] in
theorem torusMeasure_univ_ne_zero (b : Module.Basis κ ℝ E) (μ : Measure E)
    [Measure.IsAddHaarMeasure μ] : torusMeasure b μ Set.univ ≠ 0 := by
  rw [torusMeasure_univ]
  exact ZSpan.measure_fundamentalDomain_ne_zero b

/-- The plane and a general planar lattice basis used in the paper. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev PlanarLatticeBasis := Module.Basis (Fin 2) ℝ Plane

/-- The unnormalized area measure on the paper's two-dimensional flat torus. -/
def torusVolume (b : PlanarLatticeBasis) : Measure (FlatTorus b) := torusMeasure b volume

end Lloyd
