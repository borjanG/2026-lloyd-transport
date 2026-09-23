# The four targeted arguments

These are checked implications about the quantities below. They deliberately
leave named classical results as explicit hypotheses. There are also some
unformalized connections to the paper's geometric/flow constructions, stated
below. Neither Theorem 4.1 nor the full OSL extension is certified end to end.

The new source files contain no `sorry`, admitted theorem, or added axiom.
`make check` audits every theorem, including the earlier library.

## 1. Periodic weighted faces and the OSL estimate

File: [PeriodicFaces.lean](Lloyd/Geometry/PeriodicFaces.lean).

A face has a left generator, a right generator, a lattice shift, and an actual
surface measure. Its two incidences are indexed separately by `Bool`. This
allows the same generator label on both sides of a self-translated face.

The checked chain is:

- `bisector_radial_component`: the normalized radial flux is half the spacing.
- `faceRadialFlux_eq`: the integral on each incidence equals `dΓ JΓ / 2`.
- `sum_face_incidents_by_owner`: summing by cell counts every incidence once.
- `periodic_weighted_face_identity`: the **conclusion** is `∑Γ dΓ JΓ = 4 F`.
- `faceVelocityFlux_pair`: paired flux equals the velocity difference divided
  by spacing, times the weight, with the correct sign.
- `self_face_transport_zero`: self-translated faces contribute zero transport
  while remaining in the energy identity.
- `periodic_face_osl_from_velocity`: a periodic OSL field supplies the lifted
  face inequalities, including faces crossing a fundamental domain boundary.
- `periodic_face_osl_bound`: the **conclusion** is `T_v ≤ 4 L F`.

**Inputs:** a finite periodic face representation, distinct lifted endpoints,
its bisector/surface-integrability properties, and the two local divergence
formulas (radial energy and constant-velocity flux). The global weighted
identity and the transport bound are not hypotheses.

**Remaining connection:** this pass does not construct `PeriodicFaceData` from
all the actual periodic Voronoi cells or establish those local formulas for
that construction. This is an unformalized geometric connection, beyond merely
citing an abstract divergence theorem. The summation and self-face calculations
are checked for any representation satisfying the precise inputs.

## 2. Removal, insertion, separation, and volumes

File: [RemovalInsertion.lean](Lloyd/Geometry/RemovalInsertion.lean).

The energy is the existing `quantizationEnergy μ sites`, an actual integral of
squared distance to the nearest site. A surviving nonempty set `s`, deleted
site `p`, surviving neighbor `q`, and inserted point `z` represent the swap.

- `infDist_insert_site` proves the new nearest distance is the minimum of
  the old one and the distance to the inserted site.
- `removal_cell_eq_voronoiCell` identifies the region of the deletion integral
  with the actual closed Voronoi cell (including harmless ties).
- `quantization_removal_bound` proves
  `F(s) ≤ F(insert p s) + volume(cell p) δ (2r+δ)`.
- `quantization_insertion_bound` proves
  `F(insert z s) ≤ F(s) − R² volume(B(z,R/4))/2`.
- `exists_hole_of_ball_volume` proves that a finite union of balls whose summed
  area is smaller than the domain cannot cover it, supplying a far point.
- `minimizer_swap_inequality` combines the integral bounds and minimality.
- `minimizer_mesh_separation` derives the mesh-independent coefficient from
  radius `C h`, cell volume `B h²`, ball lower bound `c r²`, and `R⁴ = K h⁴`.
- `paper_minimizer_separation_constant` checks exactly the printed coefficient
  `C₃ = (1/4) min(1, c/(128 π³ C₁²(2C₁+1)))`.
- `separation_under_perturbation`, `separated_cell_volume`, and
  `separated_cell_volume_ratio` check the nearby-configuration and relative
  cell-volume deductions.

**Inputs:** ordinary integrability, cell-radius and cell-area upper bounds,
ball-area estimates, and the variational comparison that the original
configuration has no larger energy than its replacement. The removal and
insertion energy bounds themselves are proved, not assumed.

**Scope:** the metric formulation applies to the torus or to the domain with
restricted volume. It does not construct minimizers, establish the assumed
quasi-uniformity, or package the finite `N` configuration/cardinality argument
into a single theorem quantified over all minimizers. The hole argument and
swap comparison are provided as separate proved steps. No convergence claim
for the trapping feedback is added.

## 3. Actual centroid drift, noncollision, and energy

File: [ParticleDynamics.lean](Lloyd/Analysis/ParticleDynamics.lean).

`lloydDrift` uses the already defined integral centroids of actual lifted
periodic cells. `cellEnergy` and `centroidDissipation` retain their existing
integral definitions.

- `lloydDrift_separation` applies the actual centroid bisector theorem.
- `lloyd_squared_separation_derivative` differentiates every translated
  squared separation along a given solution; `ac_norm_sq` also proves the
  required absolute continuity.
- `lloyd_torus_separation` chooses a closest translate at the terminal time
  and proves
  `dist_T² ≥ exp(-2 ∫(L+α)) dist_0²` for the actual quotient metric.
- `lloyd_no_collision` proves distinctness is preserved.
- `lloyd_energy_substitution` proves exactly `F′ = T_v − 2 α G` after
  substituting the drift in the centroid gradient expression.
- `lloyd_energy_from_faces` derives `F′ + 2 α G ≤ 4 L F` using target 1.

**Inputs:** an absolutely continuous solution satisfying the ODE almost
everywhere, integrability of `L+α`, and the lifted Lipschitz velocity bound.
For energy, the classical gradient-chain formula and the explicit per-cell
face formulas are supplied. No energy differential inequality is assumed in
`lloyd_energy_from_faces`.

**Scope:** local existence, uniqueness, continuous lifts, and global
continuation are not constructed here. The noncollision theorem concerns any
solution on the interval specified in its hypotheses. Energy differentiability
of moving cells remains an explicit classical input for this targeted check.

## 4. Mollification, trajectory error, and transport

File: [Mollification.lean](Lloyd/Analysis/Mollification.lean).

`mollifiedVelocity` is an actual Bochner integral. The mollifier is represented
by a probability measure with integrable identity, zero first moment, and
support within radius `ε`; symmetry is used only through its zero mean.

- `shifted_osl_comparison` proves the displaced pointwise inequality.
- `averaged_osl_comparison` integrates it and cancels all first-moment terms,
  including the one containing the unsmoothed selection.
- `mollifiedVelocity_osl_of_osl` preserves the same OSL coefficient.
- `mollified_trajectory_comparison` joins the integral comparison to actual
  absolutely continuous trajectories and the checked Gronwall calculation.
- `mollification_uniform_bound` replaces partial time integrals by terminal
  ones and proves the bound for every `t ∈ [0,T]`.
- `mollification_sqrt_rate` extracts `sqrt(ε)` for `0 ≤ ε ≤ 1`.
- `mollification_transport_bound` uses a common-source coupling;
  `mollification_torus_transport_bound` applies it to the actual torus by
  projecting lifts.

The checked squared-error constant is
`2 exp(2 Λ(T)) (ε² Λ(T) + ε V_T)`. The resulting transport coefficient is
`sqrt(2 exp(2 Λ(T)) (Λ(T)+V_T))` times total mass and `sqrt(ε)`.
It contains no Lipschitz norm of the mollified velocity.

**Inputs:** integrable nonnegative time bounds `L,V`, integrability of the
convolution, the indicated AC trajectories and their ODEs, and the shifted OSL
inequality involving the selected unsmoothed velocity. Measurability of the
flow maps is an input to the transport result.

**Scope:** the Filippov set and its flow-existence theorem are not constructed,
and inheritance of OSL by Filippov selections is supplied as a classical input.
The norm estimate is connected to trajectories, and the common-source
transport implication is checked separately. The final histogram comparison
and triangle-inequality assembly with the mesh error remain outside this pass.

## Reproducibility

Run `make check`. `verification.json` records all theorem names, their allowed
axioms, and source hashes. `TARGETS-SOURCE.json` records the manuscript source
snapshot consulted for these four targets, separately from the original
`SOURCE.json`. The theorem count is an inventory, not a percentage of the paper
or a claim of end-to-end completion.
