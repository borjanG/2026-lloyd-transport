import Lloyd.Geometry.Quantization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Periodic face cancellation and the one-sided energy estimate

An unoriented face has two incidences, even when both belong to the same
generator through a lattice translate. The finite incidence representation and
the per-cell divergence formulas are explicit geometric/classical inputs.
The global weighted-face identity, orientation signs, self-face cancellation,
and the OSL bound are proved, not included among these inputs.

Constructing this finite face representation from the previously defined
periodic cells is a separate remaining obligation.
-/

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section
namespace Lloyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial component on a perpendicular bisector is half the site spacing. -/
theorem bisector_radial_component {p q y : E} (hne : p ≠ q)
    (hy : dist y p = dist y q) :
    ⟪y - p, ‖q - p‖⁻¹ • (q - p)⟫_ℝ = ‖q - p‖ / 2 := by
  have hd : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
  have h := congrArg (fun r : ℝ => r ^ 2) hy
  simp only [dist_eq_norm] at h
  have heq : y - q = (y - p) - (q - p) := by abel
  rw [heq, norm_sub_sq_real (y - p) (q - p)] at h
  have hi : ⟪y - p, q - p⟫_ℝ = ‖q - p‖ ^ 2 / 2 := by linarith
  rw [inner_smul_right, hi]
  field_simp

/-- Reversing the two sites reverses the unit normal. -/
theorem reversed_face_normal (p q : E) :
    ‖p - q‖⁻¹ • (p - q) = -(‖q - p‖⁻¹ • (q - p)) := by
  rw [← neg_sub q p, norm_neg, smul_neg]

variable [MeasurableSpace E] {ι F : Type*} [Fintype ι] [Fintype F]

/-- Surface measures on one representative of each unoriented periodic face.
The endpoints may have equal labels; their lifted sites must be different. -/
structure PeriodicFaceData (Λ : AddSubgroup E) (x : ι → E) where
  left : F → ι
  right : F → ι
  shift : F → Λ
  surface : F → Measure E
  different : ∀ f, x (left f) ≠ x (right f) + (shift f : E)
  bisector : ∀ f, ∀ᵐ y ∂surface f,
    dist y (x (left f)) = dist y (x (right f) + (shift f : E))
  integrable : ∀ f, Integrable (fun y => ‖y - x (left f)‖ ^ 2) (surface f)

variable {Λ : AddSubgroup E} {x : ι → E} (D : PeriodicFaceData (F := F) Λ x)

def faceSpacing (f : F) : ℝ := ‖x (D.right f) + (D.shift f : E) - x (D.left f)‖
def faceNormal (f : F) : E :=
  (faceSpacing D f)⁻¹ • (x (D.right f) + (D.shift f : E) - x (D.left f))
def faceWeight (f : F) : ℝ := ∫ y, ‖y - x (D.left f)‖ ^ 2 ∂D.surface f
def faceOwner (s : F × Bool) : ι := if s.2 then D.right s.1 else D.left s.1
def faceSideCenter (s : F × Bool) : E :=
  if s.2 then x (D.right s.1) + (D.shift s.1 : E) else x (D.left s.1)
def faceSideNormal (s : F × Bool) : E :=
  if s.2 then -faceNormal D s.1 else faceNormal D s.1
def faceRadialFlux (s : F × Bool) : ℝ :=
  ∫ y, ‖y - faceSideCenter D s‖ ^ 2 *
    ⟪y - faceSideCenter D s, faceSideNormal D s⟫_ℝ ∂D.surface s.1
def faceVelocityFlux (v : ι → E) (s : F × Bool) : ℝ :=
  -faceWeight D s.1 * ⟪faceSideNormal D s, v (faceOwner D s)⟫_ℝ

omit [InnerProductSpace ℝ E] [Fintype ι] [Fintype F] in
theorem faceSpacing_pos (f : F) : 0 < faceSpacing D f :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (D.different f).symm)

omit [InnerProductSpace ℝ E] [Fintype ι] [Fintype F] in
theorem faceWeight_nonneg (f : F) : 0 ≤ faceWeight D f :=
  integral_nonneg (fun _ => sq_nonneg _)

omit [Fintype ι] [Fintype F] in
/-- Each of the two incidences contributes exactly half of `dΓ ∫Γ f`. -/
theorem faceRadialFlux_eq (s : F × Bool) :
    faceRadialFlux D s = faceWeight D s.1 * (faceSpacing D s.1 / 2) := by
  rcases s with ⟨f, b⟩
  have hquad : (fun y => ‖y - (x (D.right f) + (D.shift f : E))‖ ^ 2) =ᵐ[D.surface f]
      (fun y => ‖y - x (D.left f)‖ ^ 2) := by
    filter_upwards [D.bisector f] with y hy
    simpa only [dist_eq_norm] using (congrArg (fun r : ℝ => r ^ 2) hy).symm
  cases b
  · unfold faceRadialFlux
    have heq : (fun y => ‖y - faceSideCenter D (f, false)‖ ^ 2 *
        ⟪y - faceSideCenter D (f, false), faceSideNormal D (f, false)⟫_ℝ) =ᵐ[D.surface f]
        (fun y => ‖y - x (D.left f)‖ ^ 2 * (faceSpacing D f / 2)) := by
      filter_upwards [D.bisector f] with y hy
      simp only [faceSideCenter, faceSideNormal, Bool.false_eq_true, ↓reduceIte]
      change _ * ⟪y - x (D.left f), ‖x (D.right f) + (D.shift f : E) - x (D.left f)‖⁻¹ •
        (x (D.right f) + (D.shift f : E) - x (D.left f))⟫_ℝ = _
      rw [bisector_radial_component (D.different f) hy]
      rfl
    rw [integral_congr_ae heq, integral_mul_const]
    rfl
  · unfold faceRadialFlux
    have heq : (fun y => ‖y - faceSideCenter D (f, true)‖ ^ 2 *
        ⟪y - faceSideCenter D (f, true), faceSideNormal D (f, true)⟫_ℝ) =ᵐ[D.surface f]
        (fun y => ‖y - x (D.left f)‖ ^ 2 * (faceSpacing D f / 2)) := by
      filter_upwards [D.bisector f, hquad] with y hy hq
      simp only [faceSideCenter, faceSideNormal, ↓reduceIte]
      have hn := reversed_face_normal (x (D.left f)) (x (D.right f) + (D.shift f : E))
      change _ = -faceNormal D f at hn
      have hdrev : ‖x (D.left f) - (x (D.right f) + (D.shift f : E))‖ = faceSpacing D f :=
        norm_sub_rev _ _
      rw [← hn, bisector_radial_component (D.different f).symm hy.symm, hq, hdrev]
    rw [integral_congr_ae heq, integral_mul_const]
    rfl

variable [DecidableEq ι]

omit [InnerProductSpace ℝ E] in
/-- Regrouping incidences by their owning cell loses none, including loop faces. -/
theorem sum_face_incidents_by_owner (g : F × Bool → ℝ) :
    (∑ i, ∑ s, if faceOwner D s = i then g s else 0) = ∑ s, g s := by
  classical
  rw [Finset.sum_comm]
  simp

omit [Fintype ι] [Fintype F] [DecidableEq ι] in
/-- The two oriented velocity fluxes give the difference of endpoint velocities. -/
theorem faceVelocityFlux_pair (v : ι → E) (f : F) :
    faceVelocityFlux D v (f, false) + faceVelocityFlux D v (f, true) =
      (⟪v (D.left f) - v (D.right f),
        x (D.left f) - x (D.right f) - (D.shift f : E)⟫_ℝ / faceSpacing D f) *
        faceWeight D f := by
  simp only [faceVelocityFlux, faceSideNormal, faceOwner, Bool.false_eq_true, ↓reduceIte,
    inner_neg_left, faceNormal, real_inner_smul_left]
  have heq : x (D.left f) - x (D.right f) - (D.shift f : E) =
      -(x (D.right f) + (D.shift f : E) - x (D.left f)) := by abel
  rw [heq, inner_neg_right, inner_sub_left (v (D.left f)) (v (D.right f))]
  have hl : ⟪x (D.right f) + (D.shift f : E) - x (D.left f), v (D.left f)⟫_ℝ =
      ⟪v (D.left f), x (D.right f) + (D.shift f : E) - x (D.left f)⟫_ℝ := real_inner_comm _ _
  have hr : ⟪x (D.right f) + (D.shift f : E) - x (D.left f), v (D.right f)⟫_ℝ =
      ⟪v (D.right f), x (D.right f) + (D.shift f : E) - x (D.left f)⟫_ℝ := real_inner_comm _ _
  rw [hl, hr]
  ring

omit [Fintype ι] [Fintype F] [DecidableEq ι] in
/-- A periodic OSL velocity supplies the inequality on every lifted face,
including those that cross a chosen fundamental-domain boundary. -/
theorem periodic_face_osl_from_velocity (v : E → E) {L : ℝ}
    (hperiodic : ∀ y (k : Λ), v (y + (k : E)) = v y)
    (hosl : ∀ p q, ⟪v p - v q, p - q⟫_ℝ ≤ L * ‖p - q‖ ^ 2) (f : F) :
    ⟪v (x (D.left f)) - v (x (D.right f)),
      x (D.left f) - x (D.right f) - (D.shift f : E)⟫_ℝ ≤ L * (faceSpacing D f) ^ 2 := by
  have h := hosl (x (D.left f)) (x (D.right f) + (D.shift f : E))
  rw [hperiodic] at h
  have heq : x (D.left f) - (x (D.right f) + (D.shift f : E)) =
      x (D.left f) - x (D.right f) - (D.shift f : E) := by abel
  have hn : ‖x (D.left f) - (x (D.right f) + (D.shift f : E))‖ = faceSpacing D f :=
    norm_sub_rev _ _
  rw [hn, heq] at h
  exact h

omit [Fintype ι] [Fintype F] [DecidableEq ι] in
/-- A face shared with a lattice translate of the same generator contributes
zero to the transport term, without removing its energy contribution. -/
theorem self_face_transport_zero (v : ι → E) (f : F) (h : D.left f = D.right f) :
    faceVelocityFlux D v (f, false) + faceVelocityFlux D v (f, true) = 0 := by
  rw [faceVelocityFlux_pair, h]
  simp

/-- Sum the per-cell divergence identities and derive the global weighted-face
identity. The global identity is a conclusion, not an assumption. -/
theorem periodic_weighted_face_identity (energy : ι → ℝ)
    (hdiv : ∀ i, 4 * energy i =
      ∑ s, if faceOwner D s = i then faceRadialFlux D s else 0) :
    (∑ f, faceSpacing D f * faceWeight D f) = 4 * ∑ i, energy i := by
  classical
  rw [Finset.mul_sum]
  simp_rw [hdiv]
  rw [sum_face_incidents_by_owner]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f _
  simp [faceRadialFlux_eq]
  ring

/-- The OSL face estimate, conditional only on the per-cell divergence
identities and finite periodic incidence representation described above. -/
theorem periodic_face_osl_bound (energy transport : ι → ℝ) (v : ι → E) {L : ℝ}
    (hdiv : ∀ i, 4 * energy i =
      ∑ s, if faceOwner D s = i then faceRadialFlux D s else 0)
    (htransport : ∀ i, transport i =
      ∑ s, if faceOwner D s = i then faceVelocityFlux D v s else 0)
    (hosl : ∀ f, ⟪v (D.left f) - v (D.right f),
      x (D.left f) - x (D.right f) - (D.shift f : E)⟫_ℝ ≤
        L * (faceSpacing D f) ^ 2) :
    (∑ i, transport i) ≤ 4 * L * ∑ i, energy i := by
  classical
  simp_rw [htransport]
  rw [sum_face_incidents_by_owner, Fintype.sum_prod_type]
  have hpair : ∀ f, (∑ b : Bool, faceVelocityFlux D v (f, b)) ≤
      L * (faceSpacing D f * faceWeight D f) := by
    intro f
    have hp := faceSpacing_pos D f
    have hq : ⟪v (D.left f) - v (D.right f),
        x (D.left f) - x (D.right f) - (D.shift f : E)⟫_ℝ / faceSpacing D f ≤
        L * faceSpacing D f := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [hosl f]
    have hm := mul_le_mul_of_nonneg_right hq (faceWeight_nonneg D f)
    rw [show (∑ b : Bool, faceVelocityFlux D v (f, b)) =
        faceVelocityFlux D v (f, false) + faceVelocityFlux D v (f, true) by simp [add_comm],
      faceVelocityFlux_pair]
    simpa only [mul_assoc] using hm
  calc
    _ ≤ ∑ f, L * (faceSpacing D f * faceWeight D f) := Finset.sum_le_sum (fun f _ => hpair f)
    _ = _ := by rw [← Finset.mul_sum, periodic_weighted_face_identity D energy hdiv]; ring

end Lloyd
