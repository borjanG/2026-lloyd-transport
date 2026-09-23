import Lloyd.Geometry.CellPartition

/-!
# The union of the chosen lifted cells is a fundamental domain

This identifies the total cell volume with the torus area, and permits
integration of periodic quantities using the cells instead of a parallelepiped.
-/

open MeasureTheory Set Metric Filter
open scoped Pointwise

noncomputable section
namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E]

/-- Moving a site by a lattice vector moves its cell by the same vector. -/
theorem translated_cell_iff {ι : Type*} (Λ : AddSubgroup E) (x : ι → E)
    (i : ι) (k : Λ) (y : E) :
    y ∈ voronoiCell (periodicSites Λ x) (x i + (k : E)) ↔
      y - (k : E) ∈ periodicCell Λ x i := by
  constructor
  · intro hy
    rw [mem_periodicCell_iff]
    intro j l
    have h := hy _ ⟨(j, l + k), rfl⟩
    convert h using 1 <;> simp only [dist_eq_norm, AddSubgroup.coe_add] <;> congr 1 <;> abel
  · intro hy q hq
    obtain ⟨⟨j, l⟩, rfl⟩ := hq
    have h := (mem_periodicCell_iff.mp hy) j (l - k)
    convert h using 1 <;> simp only [dist_eq_norm, AddSubgroup.coe_sub] <;> congr 1 <;> abel

/-- One chosen lift of the cell of each generator. -/
def cellUnion {ι : Type*} (Λ : AddSubgroup E) (x : ι → E) : Set E :=
  ⋃ i, periodicCell Λ x i

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {κ : Type*} [Fintype κ]

/-- The chosen lifted cells form a fundamental domain for the lattice action. -/
theorem cellUnion_isFundamentalDomain {ι : Type*} [Finite ι] [Nonempty ι]
    (b : Module.Basis κ ℝ E) (x : ι → E) (hx : DistinctOnTorus b x) :
    IsAddFundamentalDomain (basisLattice b) (cellUnion (basisLattice b) x) μ where
  nullMeasurableSet := (MeasurableSet.iUnion (fun i =>
    (isClosed_voronoiCell (periodicSites (basisLattice b) x) (x i)).measurableSet)).nullMeasurableSet
  ae_covers := by
    filter_upwards [ae_unique_periodic_cell (μ := μ) b x hx] with y hy
    obtain ⟨⟨i, k⟩, hi, _⟩ := hy
    refine ⟨-k, ?_⟩
    have hm := (translated_cell_iff (basisLattice b) x i k y).mp hi
    have hU : y - (k : E) ∈ cellUnion (basisLattice b) x := mem_iUnion.mpr ⟨i, hm⟩
    simpa only [AddSubgroup.vadd_def, AddSubgroup.coe_neg, vadd_eq_add, sub_eq_add_neg, add_comm] using hU
  aedisjoint := by
    intro k l hkl
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_unique_periodic_cell (μ := μ) b x hx] with y hy
    rintro ⟨hk, hl⟩
    rw [mem_vadd_set_iff_neg_vadd_mem] at hk hl
    change -(k : E) + y ∈ cellUnion (basisLattice b) x at hk
    change -(l : E) + y ∈ cellUnion (basisLattice b) x at hl
    obtain ⟨i, hi⟩ := mem_iUnion.mp hk
    obtain ⟨j, hj⟩ := mem_iUnion.mp hl
    have hi' := (translated_cell_iff (basisLattice b) x i k y).mpr
      (by simpa [sub_eq_add_neg, add_comm] using hi)
    have hj' := (translated_cell_iff (basisLattice b) x j l y).mpr
      (by simpa [sub_eq_add_neg, add_comm] using hj)
    have heq : (i, k) = (j, l) := hy.unique hi' hj'
    exact hkl (congrArg Prod.snd heq)

/-- Distinct chosen cells only overlap on a null set. -/
theorem periodicCells_aedisjoint {ι : Type*} [Finite ι] [Nonempty ι]
    (b : Module.Basis κ ℝ E) (x : ι → E) (hx : DistinctOnTorus b x) :
    Pairwise (fun i j => AEDisjoint μ (periodicCell (basisLattice b) x i)
      (periodicCell (basisLattice b) x j)) := by
  intro i j hij
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_unique_periodic_cell (μ := μ) b x hx] with y hy
  rintro ⟨hi, hj⟩
  have hi' : y ∈ voronoiCell (periodicSites (basisLattice b) x) (x i + (0 : E)) := by
    simpa [periodicCell] using hi
  have hj' : y ∈ voronoiCell (periodicSites (basisLattice b) x) (x j + (0 : E)) := by
    simpa [periodicCell] using hj
  have heq : (i, (0 : basisLattice b)) = (j, 0) := hy.unique hi' hj'
  exact hij (congrArg Prod.fst heq)

/-- The sum of the volumes of the chosen cells is exactly the torus area. -/
theorem sum_periodicCell_volume {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Module.Basis κ ℝ E) (x : ι → E) (hx : DistinctOnTorus b x) :
    ∑ i, μ (periodicCell (basisLattice b) x i) = torusMeasure b μ Set.univ := by
  haveI : Countable (basisLattice b) :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hm := measure_iUnion₀ (periodicCells_aedisjoint (μ := μ) b x hx)
    (fun i => (isClosed_voronoiCell _ (x i)).measurableSet.nullMeasurableSet)
  rw [tsum_fintype] at hm
  rw [torusMeasure_univ, ← hm]
  exact (cellUnion_isFundamentalDomain b x hx).measure_eq (ZSpan.isAddFundamentalDomain' b μ)

/-- Periodic integrals may be computed on the lifted cells' union. -/
theorem cellUnion_integral_eq_fundamentalDomain {ι : Type*} [Finite ι] [Nonempty ι]
    (b : Module.Basis κ ℝ E) (x : ι → E) (hx : DistinctOnTorus b x)
    {f : E → ℝ} (hf : ∀ (k : basisLattice b) y, f (y + (k : E)) = f y) :
    (∫ y in cellUnion (basisLattice b) x, f y ∂μ) =
      ∫ y in ZSpan.fundamentalDomain b, f y ∂μ := by
  haveI : Countable (basisLattice b) :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  apply (cellUnion_isFundamentalDomain b x hx).setIntegral_eq (ZSpan.isAddFundamentalDomain' b μ)
  intro k y
  simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_comm] using hf k y

end Lloyd
