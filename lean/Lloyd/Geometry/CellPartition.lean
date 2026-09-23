import Lloyd.Geometry.FlatTorus

/-!
# Voronoi cells partition the periodic covering up to a null set

Distinct sites have a null bisector. With countably many lattice translates,
almost every point therefore has a unique nearest lifted generator.
-/

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

noncomputable section
namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equality of distances is the equation of an affine hyperplane. -/
theorem dist_eq_dist_iff_inner (y p q : E) :
    dist y p = dist y q ↔ ⟪y, p - q⟫_ℝ = (‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 := by
  rw [le_antisymm_iff, dist_le_dist_iff_inner, dist_le_dist_iff_inner]
  simp only [inner_sub_right]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · intro h
    constructor <;> linarith

/-- The perpendicular bisector as an affine subspace. -/
def bisectorAffine (p q : E) : AffineSubspace ℝ E where
  carrier := {y | ⟪y, p - q⟫_ℝ = (‖p‖ ^ 2 - ‖q‖ ^ 2) / 2}
  smul_vsub_vadd_mem c y₁ y₂ y₃ h₁ h₂ h₃ := by
    change ⟪c • (y₁ - y₂) + y₃, p - q⟫_ℝ = _
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
    change ⟪y₁, p - q⟫_ℝ = _ at h₁
    change ⟪y₂, p - q⟫_ℝ = _ at h₂
    change ⟪y₃, p - q⟫_ℝ = _ at h₃
    rw [h₁, h₂, h₃]
    ring

theorem bisectorAffine_ne_top {p q : E} (hne : p ≠ q) : bisectorAffine p q ≠ ⊤ := by
  intro h
  have hp : p ∈ bisectorAffine p q := by rw [h]; trivial
  have hd := (dist_eq_dist_iff_inner p p q).mpr hp
  exact hne (dist_eq_zero.mp (by simpa using hd.symm))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Cell boundaries coming from distinct sites have zero volume. -/
theorem measure_bisector_zero {p q : E} (hne : p ≠ q) :
    μ {y | dist y p = dist y q} = 0 := by
  have heq : {y | dist y p = dist y q} = (bisectorAffine p q : Set E) := by
    ext y
    exact dist_eq_dist_iff_inner y p q
  rw [heq]
  exact Measure.addHaar_affineSubspace μ _ (bisectorAffine_ne_top hne)

/-- Outside a null set, no two distinct members of a countable site family tie. -/
theorem ae_no_distance_ties {ι : Type*} [Countable ι] (p : ι → E)
    (hp : Function.Injective p) :
    ∀ᵐ y ∂μ, ∀ i j, i ≠ j → dist y (p i) ≠ dist y (p j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact ae_of_all _ (by simp [hij])
  · have hz := measure_bisector_zero (μ := μ) (hp.ne hij)
    have ha := measure_eq_zero_iff_ae_notMem.mp hz
    exact ha.mono (fun y hy _ => hy)

variable {κ : Type*} [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype κ] in
/-- Distinct quotient generators make all indexed lattice translates distinct. -/
theorem periodic_index_injective {ι : Type*} (b : Module.Basis κ ℝ E) {x : ι → E}
    (hx : DistinctOnTorus b x) :
    Function.Injective (fun z : ι × basisLattice b => x z.1 + (z.2 : E)) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ hij
  have heq := congrArg (torusProjection b) hij
  simp only [torusProjection_add_lattice] at heq
  have hidx : i = j := hx heq
  subst j
  have hkl : k = l := Subtype.ext (add_left_cancel hij)
  subst l
  rfl

/-- Almost every Euclidean point belongs to exactly one indexed lifted cell. -/
theorem ae_unique_periodic_cell {ι : Type*} [Finite ι] [Nonempty ι]
    (b : Module.Basis κ ℝ E) (x : ι → E) (hx : DistinctOnTorus b x) :
    ∀ᵐ y ∂μ, ∃! z : ι × basisLattice b,
      y ∈ voronoiCell (periodicSites (basisLattice b) x) (x z.1 + (z.2 : E)) := by
  haveI : Countable (basisLattice b) :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hno := ae_no_distance_ties (μ := μ)
    (fun z : ι × basisLattice b => x z.1 + (z.2 : E)) (periodic_index_injective b hx)
  filter_upwards [hno] with y hy
  have hc := (periodicSites_closed_discrete (basisLattice b) x).1
  have hn : (periodicSites (basisLattice b) x).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨x i, (i, 0), by simp⟩
  obtain ⟨p, ⟨z, rfl⟩, hp⟩ := hc.exists_infDist_eq_dist hn y
  have hz : y ∈ voronoiCell (periodicSites (basisLattice b) x) (x z.1 + (z.2 : E)) := by
    intro q hq
    rw [← hp]
    exact infDist_le_dist_of_mem hq
  refine ⟨z, hz, ?_⟩
  intro w hw
  by_contra hne
  apply hy w z hne
  exact le_antisymm (hw _ ⟨z, rfl⟩) (hz _ ⟨w, rfl⟩)

end Lloyd
