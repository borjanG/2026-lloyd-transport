import Lloyd.Geometry.CoveringRadius
import Mathlib.MeasureTheory.Measure.Real

/-!
# Removal, insertion, and separation (Section 3)

The estimates compare actual nearest-site energy integrals. Cell radius and
ball-volume estimates and the variational minimality property are explicit
inputs. In particular the removal/insertion energy bounds are not assumed.
The metric formulation applies to both the flat torus and a bounded domain
with its restricted volume measure.
-/

open MeasureTheory Metric Set

namespace Lloyd
variable {X : Type*} [MetricSpace X]

/-- Inserting a site takes the minimum of the old distance and the new one. -/
theorem infDist_insert_site {s : Set X} (hs : s.Nonempty) (p y : X) :
    infDist y (insert p s) = min (dist y p) (infDist y s) := by
  apply le_antisymm
  · exact le_min (infDist_le_dist_of_mem (mem_insert p s))
      (infDist_le_infDist_of_subset (subset_insert p s) hs)
  · apply (le_infDist (insert_nonempty p s)).mpr
    intro q hq
    rcases hq with rfl | hq
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (infDist_le_dist_of_mem hq)

/-- The cell used in the deletion integral is exactly the Voronoi cell of
`p` in the full configuration. -/
theorem removal_cell_eq_voronoiCell {s : Set X} (hs : s.Nonempty) (p : X) :
    {y | dist y p ≤ infDist y s} = voronoiCell (insert p s) p := by
  ext y
  change (dist y p ≤ infDist y s) ↔ ∀ q ∈ insert p s, dist y p ≤ dist y q
  constructor
  · intro hy q hq
    rcases hq with rfl | hq
    · exact le_rfl
    · exact hy.trans (infDist_le_dist_of_mem hq)
  · intro hy
    exact (le_infDist hs).mpr (fun q hq => hy q (mem_insert_of_mem p hq))

/-- The pointwise cost of deleting `p`, assigning its cell to a surviving `q`. -/
theorem removal_cost_pointwise {s : Set X} {p q y : X} {r : ℝ}
    (hq : q ∈ s) (hr : 0 ≤ r)
    (hcell : dist y p ≤ infDist y s → dist y p ≤ r) :
    (infDist y s) ^ 2 ≤ (infDist y (insert p s)) ^ 2 +
      if dist y p ≤ infDist y s then dist p q * (2 * r + dist p q) else 0 := by
  rw [infDist_insert_site ⟨q, hq⟩]
  split_ifs with hc
  · rw [min_eq_left hc]
    have hn := infDist_nonneg (x := y) (s := s)
    have hnear := (infDist_le_dist_of_mem (x := y) hq).trans (dist_triangle y p q)
    have hradius := hcell hc
    have hd := dist_nonneg (x := p) (y := q)
    have hy := dist_nonneg (x := y) (y := p)
    nlinarith
  · rw [min_eq_right (le_of_not_ge hc)]
    simp

/-- A new point in a hole of radius `R` lowers squared distance by `R²/2`
throughout the ball of radius `R/4`. -/
theorem insertion_gain_pointwise {s : Set X} (hs : s.Nonempty) {z y : X} {R : ℝ}
    (hR : 0 ≤ R) (hz : R ≤ infDist z s) (hy : y ∈ ball z (R / 4)) :
    R ^ 2 / 2 ≤ (infDist y s) ^ 2 - (infDist y (insert z s)) ^ 2 := by
  have htri := infDist_le_infDist_add_dist (x := z) (y := y) (s := s)
  rw [dist_comm z y] at htri
  have hdy : dist y z < R / 4 := hy
  have hnear : dist y z ≤ infDist y s := by linarith
  rw [infDist_insert_site hs, min_eq_left hnear]
  have hn := infDist_nonneg (x := y) (s := s)
  have hd := dist_nonneg (x := y) (y := z)
  nlinarith

variable [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Integrate the deletion estimate over exactly the removed cell (ties allowed). -/
theorem quantization_removal_bound {s : Set X} {p q : X} {r : ℝ}
    (hq : q ∈ s) (hr : 0 ≤ r)
    (hfull : Integrable (fun y => (infDist y (insert p s)) ^ 2) μ)
    (hremoved : Integrable (fun y => (infDist y s) ^ 2) μ)
    (hcell : ∀ᵐ y ∂μ, dist y p ≤ infDist y s → dist y p ≤ r) :
    quantizationEnergy μ s ≤ quantizationEnergy μ (insert p s) +
      μ.real {y | dist y p ≤ infDist y s} * dist p q * (2 * r + dist p q) := by
  classical
  let C := {y | dist y p ≤ infDist y s}
  let K := dist p q * (2 * r + dist p q)
  have hC : MeasurableSet C := (isClosed_le (continuous_id.dist continuous_const)
    (continuous_infDist_pt s)).measurableSet
  have hK : Integrable (C.indicator (fun _ : X => K)) μ := (integrable_const K).indicator hC
  have hi := integral_mono_ae hremoved (hfull.add hK) (by
    filter_upwards [hcell] with y hy
    simpa only [Pi.add_apply, Set.indicator, C, mem_setOf_eq, K] using
      removal_cost_pointwise hq hr hy)
  simp only [Pi.add_apply] at hi
  rw [integral_add hfull hK, integral_indicator hC] at hi
  simpa [quantizationEnergy, C, K, mul_assoc] using hi

/-- Integrate the insertion gain; the old/new energies are actual integrals. -/
theorem quantization_insertion_bound {s : Set X} (hs : s.Nonempty) {z : X} {R : ℝ}
    (hR : 0 ≤ R) (hz : R ≤ infDist z s)
    (hold : Integrable (fun y => (infDist y s) ^ 2) μ)
    (hnew : Integrable (fun y => (infDist y (insert z s)) ^ 2) μ) :
    quantizationEnergy μ (insert z s) ≤ quantizationEnergy μ s -
      R ^ 2 / 2 * μ.real (ball z (R / 4)) := by
  have hnonneg : ∀ y, 0 ≤ (infDist y s) ^ 2 - (infDist y (insert z s)) ^ 2 := by
    intro y
    have h := infDist_le_infDist_of_subset (x := y) (subset_insert z s) hs
    have hn := infDist_nonneg (x := y) (s := insert z s)
    nlinarith
  have hgain : R ^ 2 / 2 * μ.real (ball z (R / 4)) ≤
      ∫ y, (infDist y s) ^ 2 - (infDist y (insert z s)) ^ 2 ∂μ := by
    calc
      _ = ∫ _ in ball z (R / 4), R ^ 2 / 2 ∂μ := by simp [mul_comm]
      _ ≤ ∫ y in ball z (R / 4),
          (infDist y s) ^ 2 - (infDist y (insert z s)) ^ 2 ∂μ := by
        apply integral_mono_ae (integrable_const _) ((hold.sub hnew).mono_measure Measure.restrict_le_self)
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        exact insertion_gain_pointwise hs hR hz hy
      _ ≤ _ := integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall hnonneg) (hold.sub hnew)
  rw [integral_sub hold hnew] at hgain
  unfold quantizationEnergy
  linarith

/-- Minimality forces insertion gain to be no larger than removal cost. -/
theorem minimizer_swap_inequality {s : Set X} {p q z : X} {r R c : ℝ}
    (hq : q ∈ s) (hr : 0 ≤ r) (hR : 0 ≤ R) (hz : R ≤ infDist z s)
    (hfull : Integrable (fun y => (infDist y (insert p s)) ^ 2) μ)
    (hremoved : Integrable (fun y => (infDist y s) ^ 2) μ)
    (hnew : Integrable (fun y => (infDist y (insert z s)) ^ 2) μ)
    (hcell : ∀ᵐ y ∂μ, dist y p ≤ infDist y s → dist y p ≤ r)
    (hball : c * (R / 4) ^ 2 ≤ μ.real (ball z (R / 4)))
    (hmin : quantizationEnergy μ (insert p s) ≤ quantizationEnergy μ (insert z s)) :
    c * R ^ 4 / 32 ≤ μ.real {y | dist y p ≤ infDist y s} *
      dist p q * (2 * r + dist p q) := by
  have hdel := quantization_removal_bound hq hr hfull hremoved hcell
  have hadd := quantization_insertion_bound ⟨q, hq⟩ hR hz hremoved hnew
  have hm := mul_le_mul_of_nonneg_left hball (show 0 ≤ R ^ 2 / 2 by positivity)
  nlinarith

/-- The scale-free separation deduction. Its constant depends on `A,B,C`,
not on the number of generators or on the mesh `h`. -/
theorem separation_from_swap {A B C h δ : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hh : 0 < h) (hδ : 0 ≤ δ)
    (hswap : A * h ^ 4 ≤ B * h ^ 2 * δ * (2 * C * h + δ)) :
    min 1 (A / (B * (2 * C + 1))) * h ≤ δ := by
  by_cases hd : h ≤ δ
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le).trans (by simpa using hd)
  · have hd' : δ ≤ h := (le_of_not_ge hd)
    have hc : 0 < B * (2 * C + 1) := by positivity
    have hs : A * h ≤ B * (2 * C + 1) * δ := by
      have hm := mul_le_mul_of_nonneg_left hd' (show 0 ≤ B * h ^ 2 * δ by positivity)
      have hpoly : (A * h - B * (2 * C + 1) * δ) * h ^ 3 ≤ 0 := by nlinarith
      have hp : 0 < h ^ 3 := by positivity
      nlinarith
    have hb : A / (B * (2 * C + 1)) * h ≤ δ := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hc).mpr (by nlinarith [hs])
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le).trans hb

/-- Assemble the integral swap argument and its scale-independent separation
constant. `R⁴ = K h⁴` records the hole radius chosen from the area argument. -/
theorem minimizer_mesh_separation {s : Set X} {p q z : X} {B C c K h R : ℝ}
    (hq : q ∈ s) (hB : 0 < B) (hC : 0 ≤ C) (hh : 0 < h)
    (hR : 0 ≤ R) (hscale : R ^ 4 = K * h ^ 4) (hz : R ≤ infDist z s)
    (hfull : Integrable (fun y => (infDist y (insert p s)) ^ 2) μ)
    (hremoved : Integrable (fun y => (infDist y s) ^ 2) μ)
    (hnew : Integrable (fun y => (infDist y (insert z s)) ^ 2) μ)
    (hcell : ∀ᵐ y ∂μ, dist y p ≤ infDist y s → dist y p ≤ C * h)
    (hvolume : μ.real {y | dist y p ≤ infDist y s} ≤ B * h ^ 2)
    (hball : c * (R / 4) ^ 2 ≤ μ.real (ball z (R / 4)))
    (hmin : quantizationEnergy μ (insert p s) ≤ quantizationEnergy μ (insert z s)) :
    min 1 ((c * K / 32) / (B * (2 * C + 1))) * h ≤ dist p q := by
  have hswap := minimizer_swap_inequality hq (mul_nonneg hC hh.le) hR hz
    hfull hremoved hnew hcell hball hmin
  have hcost := mul_le_mul_of_nonneg_right hvolume
    (show 0 ≤ dist p q * (2 * (C * h) + dist p q) by positivity)
  apply separation_from_swap hB hC hh dist_nonneg
  rw [hscale] at hswap
  nlinarith [hcost]

/-- The numerical separation constant printed in Section 3. -/
theorem paper_minimizer_separation_constant {C c h δ : ℝ}
    (hC : 0 < C) (hh : 0 < h) (hδ : 0 ≤ δ)
    (hswap : c * h ^ 4 / (128 * Real.pi ^ 2) ≤
      Real.pi * C ^ 2 * h ^ 2 * δ * (2 * C * h + δ)) :
    4 * ((1/4 : ℝ) * min 1 (c / (128 * Real.pi ^ 3 * C ^ 2 * (2 * C + 1)))) * h ≤ δ := by
  have h := separation_from_swap (A := c / (128 * Real.pi ^ 2))
    (B := Real.pi * C ^ 2) (C := C) (by positivity) hC.le hh hδ (by convert hswap using 1; ring)
  have heq : (c / (128 * Real.pi ^ 2)) / (Real.pi * C ^ 2 * (2 * C + 1)) =
      c / (128 * Real.pi ^ 3 * C ^ 2 * (2 * C + 1)) := by
    rw [div_div]; congr 1; ring
  rw [heq] at h
  convert h using 1; ring

omit [MeasurableSpace X] [BorelSpace X] in
/-- A configuration within `r` of a separated configuration loses at most `2r`
of pairwise separation. -/
theorem separation_under_perturbation {ι : Type*} {x y : ι → X} {i j : ι} {d r : ℝ}
    (hsep : d ≤ dist (y i) (y j)) (hi : dist (x i) (y i) ≤ r)
    (hj : dist (x j) (y j) ≤ r) :
    d - 2 * r ≤ dist (x i) (x j) := by
  have ht := dist_triangle (y i) (x i) (y j)
  have ht' := dist_triangle (x i) (x j) (y j)
  rw [dist_comm (y i) (x i)] at ht
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- Separation puts a ball inside the corresponding closed Voronoi cell. -/
theorem separated_ball_subset_cell {sites : Set X} {p : X} {r : ℝ}
    (hsep : ∀ q ∈ sites, q ≠ p → 2 * r ≤ dist p q) :
    ball p r ⊆ voronoiCell sites p := by
  intro y hy q hq
  by_cases heq : q = p
  · simp [heq]
  · have hs := hsep q hq heq
    have ht := dist_triangle p y q
    rw [dist_comm p y] at ht
    have hd : dist y p < r := hy
    linarith

omit [BorelSpace X] in
/-- The ball-area input and separation give the required cell-volume lower bound. -/
theorem separated_cell_volume {sites : Set X} {p : X} {r c : ℝ}
    (hsep : ∀ q ∈ sites, q ≠ p → 2 * r ≤ dist p q)
    (hball : c * r ^ 2 ≤ μ.real (ball p r)) :
    c * r ^ 2 ≤ μ.real (voronoiCell sites p) :=
  hball.trans (measureReal_mono (separated_ball_subset_cell hsep))

omit [BorelSpace X] in
/-- The relative volume bound used to compare later cell volumes to the
initial ones in Section 3. -/
theorem separated_cell_volume_ratio {sites initialSites : Set X} {p p₀ : X} {r h c B : ℝ}
    (hc : 0 ≤ c) (hB : 0 < B)
    (hsep : ∀ q ∈ sites, q ≠ p → 2 * (r * h) ≤ dist p q)
    (hball : c * (r * h) ^ 2 ≤ μ.real (ball p (r * h)))
    (hinitial : μ.real (voronoiCell initialSites p₀) ≤ B * h ^ 2) :
    (c * r ^ 2 / B) * μ.real (voronoiCell initialSites p₀) ≤ μ.real (voronoiCell sites p) := by
  calc
    _ ≤ (c * r ^ 2 / B) * (B * h ^ 2) :=
      mul_le_mul_of_nonneg_left hinitial (by positivity)
    _ = c * (r * h) ^ 2 := by field_simp
    _ ≤ _ := separated_cell_volume hsep hball

omit [BorelSpace X] in
/-- The finite union-of-balls argument that supplies an insertion point.
The area bound is a standard geometric input; the noncoverage is proved. -/
theorem exists_hole_of_ball_volume {ι : Type*} [Fintype ι] (x : ι → X)
    {Ω : Set X} {R a : ℝ}
    (hball : ∀ i, μ.real (ball (x i) R) ≤ a)
    (harea : (Fintype.card ι : ℝ) * a < μ.real Ω) :
    ∃ z ∈ Ω, ∀ i, R ≤ dist z (x i) := by
  classical
  by_contra! h
  have hcover : Ω ⊆ ⋃ i, ball (x i) R := by
    intro z hz
    obtain ⟨i, hi⟩ := h z hz
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hm := measureReal_mono (μ := μ) hcover
  have hu := measureReal_iUnion_fintype_le (μ := μ) (fun i => ball (x i) R)
  have hs : (∑ i, μ.real (ball (x i) R)) ≤ (Fintype.card ι : ℝ) * a := by
    calc
      _ ≤ ∑ _i : ι, a := Finset.sum_le_sum (fun i _ => hball i)
      _ = _ := by simp
  linarith

end Lloyd
