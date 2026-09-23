import Lloyd.Geometry.Quantization
import Lloyd.Analysis.ConvergenceRate
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Area growth of balls on an arbitrary planar flat torus

Lattice separation supplies a small embedded Euclidean ball. A one-generator
Voronoi fundamental domain transfers its area to the quotient. Shrinking
larger radii by a fixed factor gives a quadratic lower bound on any fixed
bounded range of radii. No ball-volume estimate is assumed.
-/

open MeasureTheory Metric Set

noncomputable section
namespace Lloyd

/-- A Euclidean ball inside the one-generator cell contributes its full area
to a torus ball with at least that radius. -/
theorem euclidean_ball_volume_le_torus_ball (b : PlanarLatticeBasis) {ε : ℝ}
    (hsep : ∀ k ∈ basisLattice b, k ≠ 0 → 2 * ε ≤ dist (0 : Plane) k)
    (y : Plane) {s r : ℝ} (hs : s ≤ ε) (hsr : s ≤ r) :
    volume (ball y s) ≤ torusVolume b (ball (torusProjection b y) r) := by
  haveI : Countable (basisLattice b) :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  let x : Unit → Plane := fun _ => y
  have hx : DistinctOnTorus b x := fun _ _ _ => Subsingleton.elim _ _
  let A := (torusProjection b) ⁻¹' ball (torusProjection b y) r
  have hA : MeasurableSet A := (torusProjection b).continuous.measurable measurableSet_ball
  have hp : ∀ k : basisLattice b, (fun z => k +ᵥ z) ⁻¹' A = A := by
    intro k
    ext z
    change (torusProjection b) ((k : Plane) + z) ∈ ball (torusProjection b y) r ↔
      (torusProjection b) z ∈ ball (torusProjection b y) r
    rw [add_comm, torusProjection_add_lattice]
  have heq := (cellUnion_isFundamentalDomain (μ := volume) b x hx).measure_set_eq
    (ZSpan.isAddFundamentalDomain' b volume) hA hp
  have hsub : ball y s ⊆ A ∩ cellUnion (basisLattice b) x := by
    intro z hz
    refine ⟨?_, mem_iUnion.mpr ⟨(), ?_⟩⟩
    · exact (torusProjection_dist_le b z y).trans_lt (hz.trans_le hsr)
    · apply ball_subset_voronoiCell_of_separated (r := ε) ?_ (hz.trans_le hs)
      rintro q ⟨⟨i, k⟩, rfl⟩ hne
      have hk : (k : Plane) ≠ 0 := by
        intro hk
        apply hne
        simp [x, hk]
      simpa [x, dist_eq_norm] using hsep k k.property hk
  calc
    _ ≤ volume (A ∩ cellUnion (basisLattice b) x) := measure_mono hsub
    _ = volume (A ∩ ZSpan.fundamentalDomain b) := heq
    _ = torusVolume b (ball (torusProjection b y) r) := by
      rw [torusVolume, torusMeasure,
        Measure.map_apply (torusProjection b).continuous.measurable measurableSet_ball,
        Measure.restrict_apply hA]

/-- A positive quadratic area bound, uniformly in the centre and all radii
in any prescribed bounded interval. The constant depends only on the torus
and the upper radius, never on the particle configuration. -/
theorem exists_torus_ball_volume_lower_bound (b : PlanarLatticeBasis) {R : ℝ} (hR : 0 < R) :
    ∃ c > 0, ∀ (z : FlatTorus b) (r : ℝ), 0 ≤ r → r ≤ R →
      c * r ^ 2 ≤ (torusVolume b).real (ball z r) := by
  have hc : IsClosed (basisLattice b : Set Plane) := inferInstance
  haveI : DiscreteTopology (basisLattice b) := basisLattice_discrete b
  haveI : IsFiniteMeasure (torusVolume b) :=
    inferInstanceAs (IsFiniteMeasure (torusMeasure b volume))
  have hd : IsDiscrete (basisLattice b : Set Plane) := DiscreteTopology.isDiscrete
  obtain ⟨ε, hε, hsep⟩ := exists_separation_of_closed_discrete hc hd (0 : Plane)
  let t : ℝ := min 1 (ε / R)
  have ht : 0 < t := lt_min zero_lt_one (div_pos hε hR)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R ≤ ε := (le_div_iff₀ hR).mp (min_le_right _ _)
  refine ⟨Real.pi * t ^ 2, mul_pos Real.pi_pos (sq_pos_of_pos ht), ?_⟩
  intro z r hr hrR
  obtain ⟨y, rfl⟩ := torusProjection_surjective b z
  have htr : t * r ≤ r := by nlinarith
  have hte : t * r ≤ ε := (mul_le_mul_of_nonneg_left hrR ht.le).trans htR
  have hvol := euclidean_ball_volume_le_torus_ball b hsep y hte htr
  have hreal := ENNReal.toReal_mono (measure_ne_top (torusVolume b) _) hvol
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg ht.le hr), ENNReal.toReal_ofReal Real.pi_pos.le] at hreal
  convert hreal using 1
  ring

/-- The actual torus energy controls the fourth power of nearest-site distance,
with a constant independent of the number and configuration of generators. -/
theorem exists_cellEnergy_radius_fourth_bound (b : PlanarLatticeBasis) :
    ∃ c > 0, ∀ {ι : Type} [Fintype ι] [Nonempty ι] (x : ι → Plane),
      DistinctOnTorus b x → ∀ z : FlatTorus b,
        c / 16 * (infDist z (Set.range (fun i => torusProjection b (x i)))) ^ 4 ≤
          cellEnergy b volume x := by
  let R : ℝ := (∑ k, ‖b k‖) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨c, hc, hball⟩ := exists_torus_ball_volume_lower_bound b hR
  refine ⟨c, hc, ?_⟩
  intro ι _ _ x hx z
  rw [cellEnergy_eq_torus_quantization b x hx]
  apply quantizationEnergy_ge_radius_fourth rfl (torus_quantization_integrable b x)
  apply hball _ _ (div_nonneg infDist_nonneg (by norm_num))
  obtain ⟨y, rfl⟩ := torusProjection_surjective b z
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [torus_infDist_eq_periodic]
  have hcover := periodicSites_covering_bound b x i y
  have hsum : 0 ≤ ∑ k, ‖b k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  dsimp [R]
  linarith

/-- Small actual quantization energy implies the paper's cell-diameter scale.
The constant is uniform over the number of particles and their positions. -/
theorem exists_periodicCell_diameter_mesh_bound (b : PlanarLatticeBasis)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ Cd ≥ 0, ∀ {ι : Type} [Fintype ι] [Nonempty ι] (x : ι → Plane),
      DistinctOnTorus b x → ∀ {h : ℝ}, 0 < h → cellEnergy b volume x ≤ C * h ^ 2 →
        ∀ i, Metric.diam (periodicCell (basisLattice b) x i) ≤ Cd * h ^ (1 / 2 : ℝ) := by
  obtain ⟨c, hc, hrad⟩ := exists_cellEnergy_radius_fourth_bound b
  refine ⟨2 * (16 * C / c) ^ (1 / 4 : ℝ), by positivity, ?_⟩
  intro ι _ _ x hx h hh henergy i
  have hcover : ∀ y, infDist y (periodicSites (basisLattice b) x) ≤
      (16 * C / c) ^ (1 / 4 : ℝ) * h ^ (1 / 2 : ℝ) := by
    intro y
    have hb := hrad x hx (torusProjection b y)
    rw [torus_infDist_eq_periodic] at hb
    exact radius_le_mesh_sqrt infDist_nonneg hh hc hC (hb.trans henergy)
  have hd := voronoiCell_diam_le
    (show x i ∈ periodicSites (basisLattice b) x from ⟨(i, 0), by simp⟩)
    (show 0 ≤ (16 * C / c) ^ (1 / 4 : ℝ) * h ^ (1 / 2 : ℝ) by positivity) hcover
  convert hd using 1
  ring

end Lloyd
