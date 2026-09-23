import Lloyd.Analysis.Noncollision
import Lloyd.Geometry.PeriodicFaces
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The paper's particle drift and its estimates

The drift uses the actual integral centroids of the periodic cells.
Noncollision is proved for any absolutely continuous solution satisfying the
ODE almost everywhere. Existence/continuation of that ODE is a classical input,
not constructed here. The energy conclusion takes the classical gradient-chain
formula and per-cell divergence formulas as inputs, and uses the checked face
calculation rather than assuming the desired energy differential inequality.
-/

open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Squared norm of an absolutely continuous curve is absolutely continuous. -/
theorem ac_norm_sq {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖ ^ 2) a b := by
  have hn : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
    ac_comp_lipschitzOn hf lipschitzWith_one_norm.lipschitzOnWith (fun _ _ => mem_univ _)
  simpa only [pow_two] using hn.fun_mul hn

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- The sampled velocity plus the actual periodic Lloyd correction. -/
def lloydDrift (b : Module.Basis κ ℝ E) (μ : Measure E)
    (x v : ι → E) (a : ℝ) (i : ι) : E :=
  v i + a • (cellCentroid μ (periodicCell (basisLattice b) x i) - x i)

/-- Connect the actual centroid geometry to the separation drift estimate. -/
theorem lloydDrift_separation (b : Module.Basis κ ℝ E) (x v : ι → E)
    (i j : ι) (k : basisLattice b) {a L : ℝ} (ha : 0 ≤ a)
    (hvel : ‖v i - v j‖ ≤ L * ‖x i - x j - (k : E)‖) :
    -(L + a) * ‖x i - x j - (k : E)‖ ^ 2 ≤
      ⟪x i - x j - (k : E), lloydDrift b μ x v a i - lloydDrift b μ x v a j⟫_ℝ := by
  have h := separation_drift_lower ha hvel (periodic_centroid_bisector (μ := μ) b x i j k)
  convert h using 1
  unfold lloydDrift
  congr 1
  simp only [smul_sub]
  abel

/-- Differentiation of the squared separation, including every lattice translate. -/
theorem lloyd_squared_separation_derivative (b : Module.Basis κ ℝ E)
    {x : ℝ → ι → E} {v : ι → E} {a L t : ℝ} (i j : ι) (k : basisLattice b)
    (ha : 0 ≤ a) (hvel : ‖v i - v j‖ ≤ L * ‖x t i - x t j - (k : E)‖)
    (hi : HasDerivAt (fun s => x s i) (lloydDrift b μ (x t) v a i) t)
    (hj : HasDerivAt (fun s => x s j) (lloydDrift b μ (x t) v a j) t) :
    -2 * (L + a) * ‖x t i - x t j - (k : E)‖ ^ 2 ≤
      deriv (fun s => ‖x s i - x s j - (k : E)‖ ^ 2) t := by
  have hd := ((hi.sub hj).sub_const (k : E)).norm_sq.deriv
  simp only [Pi.sub_apply] at hd
  rw [hd]
  have h := lloydDrift_separation (μ := μ) b (x t) v i j k ha hvel
  linarith

/-- A quantitative noncollision bound for actual absolutely continuous solutions.
The velocity hypothesis is the lifted periodic Lipschitz bound. -/
theorem lloyd_torus_separation (b : Module.Basis κ ℝ E)
    {x v : ℝ → ι → E} {a L : ℝ → ℝ} {T : ℝ} (i j : ι)
    (hT : 0 ≤ T) (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) 0 T)
    (hb : IntervalIntegrable (fun t => L t + a t) volume 0 T)
    (ha : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ a t)
    (hvel : ∀ᵐ t, t ∈ Icc 0 T → ∀ k : basisLattice b,
      ‖v t i - v t j‖ ≤ L t * ‖x t i - x t j - (k : E)‖)
    (hode : ∀ᵐ t, t ∈ Icc 0 T → ∀ i,
      HasDerivAt (fun s => x s i) (lloydDrift b μ (x t) (v t) (a t) i) t) :
    Real.exp (-2 * ∫ t in 0..T, L t + a t) *
        dist (torusProjection b (x 0 i)) (torusProjection b (x 0 j)) ^ 2 ≤
      dist (torusProjection b (x T i)) (torusProjection b (x T j)) ^ 2 := by
  obtain ⟨k, hk⟩ := torus_dist_realized b (x T i) (x T j)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (k : E)) 0 T :=
    (LipschitzWith.const (k : E)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hs := ac_norm_sq (((hx i).fun_sub (hx j)).fun_sub hconst)
  have hineq : ∀ᵐ t, t ∈ Icc 0 T →
      -2 * (L t + a t) * ‖x t i - x t j - (k : E)‖ ^ 2 ≤
        deriv (fun s => ‖x s i - x s j - (k : E)‖ ^ 2) t := by
    filter_upwards [ha, hvel, hode] with t hat hvt hot ht
    exact lloyd_squared_separation_derivative b i j k (hat ht) (hvt ht k) (hot ht i) (hot ht j)
  have hsep := separation_lower_bound hT hs hb hineq
  have hinit := torusProjection_dist_le b (x 0 i) (x 0 j + (k : E))
  rw [torusProjection_add_lattice] at hinit
  rw [dist_eq_norm (x 0 i) (x 0 j + (k : E))] at hinit
  have hvec : ∀ t, x t i - (x t j + (k : E)) = x t i - x t j - (k : E) := by
    intro t; abel
  rw [hvec] at hinit
  have hsquared := (sq_le_sq₀ dist_nonneg (norm_nonneg _)).mpr hinit
  have hm := mul_le_mul_of_nonneg_left hsquared
    (Real.exp_pos (-2 * ∫ t in 0..T, L t + a t)).le
  rw [hk, dist_eq_norm (x T i) (x T j + (k : E)), hvec]
  exact hm.trans hsep

/-- Distinct initial generators remain distinct along any such solution. -/
theorem lloyd_no_collision (b : Module.Basis κ ℝ E)
    {x v : ℝ → ι → E} {a L : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) 0 T)
    (hinit : DistinctOnTorus b (x 0))
    (hb : IntervalIntegrable (fun t => L t + a t) volume 0 T)
    (ha : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ a t)
    (hvel : ∀ᵐ t, t ∈ Icc 0 T → ∀ i j (k : basisLattice b),
      ‖v t i - v t j‖ ≤ L t * ‖x t i - x t j - (k : E)‖)
    (hode : ∀ᵐ t, t ∈ Icc 0 T → ∀ i,
      HasDerivAt (fun s => x s i) (lloydDrift b μ (x t) (v t) (a t) i) t) :
    DistinctOnTorus b (x T) := by
  intro i j heq
  change torusProjection b (x T i) = torusProjection b (x T j) at heq
  by_contra hij
  have h0 : 0 < dist (torusProjection b (x 0 i)) (torusProjection b (x 0 j)) :=
    dist_pos.mpr (fun h => hij (hinit h))
  have h := lloyd_torus_separation b i j hT hx hb ha
    (by filter_upwards [hvel] with t ht htmem; exact ht htmem i j) hode
  rw [heq, dist_self, zero_pow (by decide : 2 ≠ 0)] at h
  exact (not_le_of_gt (mul_pos (Real.exp_pos _) (sq_pos_of_pos h0))) h

/-- The energy directional derivative given by the classical centroid gradient. -/
def cellEnergyDirectional (b : Module.Basis κ ℝ E) (μ : Measure E)
    (x u : ι → E) : ℝ :=
  ∑ i, 2 * μ.real (periodicCell (basisLattice b) x i) *
    ⟪x i - cellCentroid μ (periodicCell (basisLattice b) x i), u i⟫_ℝ

omit [FiniteDimensional ℝ E] [BorelSpace E] [Fintype κ] [Measure.IsAddHaarMeasure μ] in
/-- Substitution of the Lloyd drift produces exactly `-2 a G`. -/
theorem lloyd_energy_substitution (b : Module.Basis κ ℝ E) (x v : ι → E) (a : ℝ) :
    cellEnergyDirectional b μ x (lloydDrift b μ x v a) =
      cellEnergyDirectional b μ x v - 2 * a * centroidDissipation b μ x := by
  unfold cellEnergyDirectional centroidDissipation
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let c := cellCentroid μ (periodicCell (basisLattice b) x i)
  change 2 * _ * ⟪x i - c, v i + a • (c - x i)⟫_ℝ = _
  rw [inner_add_right, inner_smul_right]
  have heq : x i - c = -(c - x i) := by abel
  have hinner : ⟪x i - c, c - x i⟫_ℝ = -‖c - x i‖ ^ 2 := by
    rw [heq, inner_neg_left, real_inner_self_eq_norm_sq]
  rw [hinner]
  dsimp [c]
  ring

omit [FiniteDimensional ℝ E] [BorelSpace E] [Fintype κ] [Measure.IsAddHaarMeasure μ] in
/-- The actual energy differential inequality, conditional on the classical
chain rule and per-cell divergence formulas for a finite face representation. -/
theorem lloyd_energy_from_faces [DecidableEq ι] {F : Type*} [Fintype F]
    (b : Module.Basis κ ℝ E) {x : ℝ → ι → E} {v : ι → E} {a L t : ℝ}
    (D : PeriodicFaceData (F := F) (basisLattice b) (x t))
    (hchain : deriv (fun s => cellEnergy b μ (x s)) t =
      cellEnergyDirectional b μ (x t) (lloydDrift b μ (x t) v a))
    (hdiv : ∀ i, 4 * (∫ y in periodicCell (basisLattice b) (x t) i, ‖y - x t i‖ ^ 2 ∂μ) =
      ∑ s, if faceOwner D s = i then faceRadialFlux D s else 0)
    (htransport : ∀ i, 2 * μ.real (periodicCell (basisLattice b) (x t) i) *
        ⟪x t i - cellCentroid μ (periodicCell (basisLattice b) (x t) i), v i⟫_ℝ =
      ∑ s, if faceOwner D s = i then faceVelocityFlux D v s else 0)
    (hosl : ∀ f, ⟪v (D.left f) - v (D.right f),
      x t (D.left f) - x t (D.right f) - (D.shift f : E)⟫_ℝ ≤ L * (faceSpacing D f) ^ 2) :
    deriv (fun s => cellEnergy b μ (x s)) t + 2 * a * centroidDissipation b μ (x t) ≤
      4 * L * cellEnergy b μ (x t) := by
  rw [hchain, lloyd_energy_substitution, sub_add_cancel]
  exact periodic_face_osl_bound D _ _ v hdiv htransport hosl

end Lloyd
