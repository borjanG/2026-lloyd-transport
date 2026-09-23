import Lloyd.Geometry.CellFundamentalDomain

/-!
# The energy and centroid dissipation of the actual periodic configuration

The sum of lifted cell energies is identified with the nearest-site energy on
the flat torus. Cell centroids are derived from their integral definition, and
the dissipation has a configuration-independent upper bound. These are static
geometric results; differentiating the energy along the particle ODE is a
separate, still outstanding step.
-/

open MeasureTheory Metric Set

noncomputable section
namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- The energy `F` as a sum of integrals over lifted periodic cells. -/
def cellEnergy (b : Module.Basis κ ℝ E) (μ : Measure E) (x : ι → E) : ℝ :=
  ∑ i, ∫ y in periodicCell (basisLattice b) x i, ‖y - x i‖ ^ 2 ∂μ

/-- The centroid dissipation `G` of the actual cells. -/
def centroidDissipation (b : Module.Basis κ ℝ E) (μ : Measure E) (x : ι → E) : ℝ :=
  ∑ i, μ.real (periodicCell (basisLattice b) x i) *
    ‖cellCentroid μ (periodicCell (basisLattice b) x i) - x i‖ ^ 2

omit [MeasurableSpace E] [BorelSpace E] [Nonempty ι] in
/-- The union of finitely many chosen lifted cells is compact. -/
theorem cellUnion_isCompact (b : Module.Basis κ ℝ E) (x : ι → E) :
    IsCompact (cellUnion (basisLattice b) x) :=
  isCompact_iUnion (fun i => periodicCell_isCompact b x i)

omit [Nonempty ι] in
/-- The actual periodic centroid belongs to its cell, with no additional
cell-volume or integrability hypotheses. -/
theorem periodicCell_centroid_mem (b : Module.Basis κ ℝ E) (x : ι → E) (i : ι) :
    cellCentroid μ (periodicCell (basisLattice b) x i) ∈ periodicCell (basisLattice b) x i := by
  obtain ⟨h0, hf, hi⟩ := periodicCell_measure_properties (μ := μ) b x i
  exact cellCentroid_mem_voronoiCell μ _ _ h0 hf hi

omit [Nonempty ι] in
/-- A lattice-dependent bound for every centroid displacement. -/
theorem periodicCell_centroid_displacement_le (b : Module.Basis κ ℝ E) (x : ι → E) (i : ι) :
    ‖cellCentroid μ (periodicCell (basisLattice b) x i) - x i‖ ≤ ∑ k, ‖b k‖ := by
  obtain ⟨h0, hf, hi⟩ := periodicCell_measure_properties (μ := μ) b x i
  exact cellCentroid_displacement_le μ ⟨(i, 0), by simp⟩
    (periodicSites_covering_bound b x i) h0 hf hi

omit [Fintype ι] [Nonempty ι] in
/-- Squared distance to the nearest generator is integrable on the torus. -/
theorem torus_quantization_integrable (b : Module.Basis κ ℝ E) (x : ι → E) :
    Integrable (fun y => (infDist y (Set.range (fun i => torusProjection b (x i)))) ^ 2)
      (torusMeasure b μ) :=
  by
    have hc := (continuous_infDist_pt (Set.range (fun i => torusProjection b (x i)))).pow 2
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

/-- The two definitions of the paper's quantization energy agree. -/
theorem cellEnergy_eq_torus_quantization (b : Module.Basis κ ℝ E) (x : ι → E)
    (hx : DistinctOnTorus b x) :
    cellEnergy b μ x =
      quantizationEnergy (torusMeasure b μ) (Set.range (fun i => torusProjection b (x i))) := by
  let f : E → ℝ := fun y => (infDist y (periodicSites (basisLattice b) x)) ^ 2
  have hfc : Continuous f := (continuous_infDist_pt _).pow 2
  have hfi : IntegrableOn f (cellUnion (basisLattice b) x) μ :=
    hfc.continuousOn.integrableOn_compact (cellUnion_isCompact b x)
  have hp : ∀ (k : basisLattice b) y, f (y + (k : E)) = f y := by
    intro k y
    dsimp [f]
    rw [← torus_infDist_eq_periodic b x (y + (k : E)),
      ← torus_infDist_eq_periodic b x y, torusProjection_add_lattice]
  have hsum := integral_iUnion_ae
    (fun i => (isClosed_voronoiCell (periodicSites (basisLattice b) x) (x i)).measurableSet.nullMeasurableSet)
    (periodicCells_aedisjoint (μ := μ) b x hx) hfi
  rw [tsum_fintype] at hsum
  calc
    cellEnergy b μ x = ∑ i, ∫ y in periodicCell (basisLattice b) x i, f y ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply setIntegral_congr_fun (isClosed_voronoiCell _ (x i)).measurableSet
      intro y hy
      dsimp only [f]
      rw [← dist_eq_norm, dist_eq_infDist_of_mem_voronoiCell
        (show x i ∈ periodicSites (basisLattice b) x from ⟨(i, 0), by simp⟩) hy]
    _ = ∫ y in cellUnion (basisLattice b) x, f y ∂μ := hsum.symm
    _ = ∫ y in ZSpan.fundamentalDomain b, f y ∂μ :=
      cellUnion_integral_eq_fundamentalDomain b x hx hp
    _ = quantizationEnergy (torusMeasure b μ)
        (Set.range (fun i => torusProjection b (x i))) := by
      unfold quantizationEnergy torusMeasure
      rw [integral_map_of_stronglyMeasurable (torusProjection b).continuous.measurable
        ((continuous_infDist_pt _).pow 2).stronglyMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by dsimp only [f]; rw [torus_infDist_eq_periodic])

/-- Cell volumes sum to the torus area also as real numbers. -/
theorem sum_periodicCell_real_volume (b : Module.Basis κ ℝ E) (x : ι → E)
    (hx : DistinctOnTorus b x) :
    ∑ i, μ.real (periodicCell (basisLattice b) x i) = (torusMeasure b μ).real Set.univ := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun i _ => (periodicCell_measure_properties (μ := μ) b x i).2.1),
    sum_periodicCell_volume b x hx]

omit [FiniteDimensional ℝ E] [BorelSpace E] [Fintype κ] [Nonempty ι]
  [Measure.IsAddHaarMeasure μ] in
theorem centroidDissipation_nonneg (b : Module.Basis κ ℝ E) (x : ι → E) :
    0 ≤ centroidDissipation b μ x := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (measureReal_nonneg) (sq_nonneg _))

/-- A uniform bound for `G`, depending only on the torus and chosen basis. -/
theorem centroidDissipation_le (b : Module.Basis κ ℝ E) (x : ι → E)
    (hx : DistinctOnTorus b x) :
    centroidDissipation b μ x ≤ (torusMeasure b μ).real Set.univ * (∑ k, ‖b k‖) ^ 2 := by
  calc
    _ ≤ ∑ i, μ.real (periodicCell (basisLattice b) x i) * (∑ k, ‖b k‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      exact sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun k _ => norm_nonneg _)) |>.mpr
        (periodicCell_centroid_displacement_le b x i)
    _ = _ := by rw [← Finset.sum_mul, sum_periodicCell_real_volume b x hx]


omit [Nonempty ι] in
/-- The actual integral centroids satisfy the periodic bisector inequality. -/
theorem periodic_centroid_bisector (b : Module.Basis κ ℝ E) (x : ι → E)
    (i j : ι) (k : basisLattice b) :
    0 ≤ inner (𝕜 := ℝ) (x i - x j - (k : E))
      (cellCentroid μ (periodicCell (basisLattice b) x i) -
        cellCentroid μ (periodicCell (basisLattice b) x j) - (k : E)) :=
  periodic_bisector_inner_nonneg (periodicCell_centroid_mem b x i)
    (periodicCell_centroid_mem b x j) k

/-- The feedback cap gives a bound depending on the fixed mesh and torus. -/
theorem capped_feedback_le (b : Module.Basis κ ℝ E) (x : ι → E)
    (hx : DistinctOnTorus b x) {α h : ℝ} (hh : 0 < h)
    (hα : α ≤ centroidDissipation b μ x / h ^ (5 / 2 : ℝ)) :
    α ≤ (torusMeasure b μ).real Set.univ * (∑ k, ‖b k‖) ^ 2 / h ^ (5 / 2 : ℝ) := by
  exact hα.trans (div_le_div_of_nonneg_right (centroidDissipation_le b x hx)
    (Real.rpow_nonneg hh.le _))

end Lloyd
