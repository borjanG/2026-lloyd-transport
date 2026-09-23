# Proof status: four targeted arguments and Theorem 4.1

The complete theorem is **unfinished**. No Lean declaration of the full theorem
has been proved. The current library has no placeholder proofs and no added
axioms. Building the library certifies the intermediate statements below,
including their explicit assumptions; it does not certify the full paper.

## Current targeted verification

The four requested arguments are mapped in [TARGETS.md](TARGETS.md). New modules
are `Geometry/PeriodicFaces.lean`, `Geometry/RemovalInsertion.lean`,
`Analysis/ParticleDynamics.lean`, and `Analysis/Mollification.lean`.

They prove the weighted face identity and OSL face estimate, integral
removal/insertion bounds and their separation/volume consequences, actual
centroid-drift noncollision and conditional energy inequality, and the
mollification/trajectory/transport error calculation. The face representation,
local divergence and gradient-chain formulas, standard geometric bounds, and
classical ODE/Filippov inputs are explicitly distinguished from their conclusions.

For this targeted task, classical existence theorems are intentionally accepted
as explicit hypotheses. Their full formalization is not a prerequisite for
using the new conditional results.

## Checked components

| Part of the paper | Lean file | What is proved / what remains an input |
| --- | --- | --- |
| Integrating factor and energy bounds | `Lloyd/Analysis/Energy.lean` | The complete scalar integration step for absolutely continuous functions, including composition with the exponential. The energy differential inequality is an input here; `ParticleDynamics.lean` now derives it from explicit local divergence and gradient-chain inputs. |
| Corrected (4.18) and (4.5) | `Lloyd/Analysis/FeedbackBudget.lean` | Cauchy--Schwarz, square integrability from the feedback cap, the total correction bound, and the exact mesh exponent. Dissipation is an input. |
| (4.6) | `Lloyd/Analysis/FeedbackBudget.lean` | The centroid estimate under equality feedback. Equality is explicitly required. |
| Scalar estimates combined | `Lloyd/Analysis/ScalarEstimates.lean` | Energy, dissipation, correction budget, and conditional centroid estimate on `[0,T]`, for `T>0`. Initial energy, nonnegativity, integrability, and the scalar energy inequality are explicit hypotheses. |
| Covering-radius argument | `Lloyd/Geometry/CoveringRadius.lean` | The ball lower bound for quantization energy, its fourth-power consequence, and cell diameter at most twice the covering radius. The generic result has ball-volume and integrability hypotheses; `TorusBalls.lean` now supplies them for the actual planar torus. |
| Convex cells and centroids | `Lloyd/Geometry/PeriodicCell.lean` | Euclidean cells are closed and convex; their integral centroids belong to them when their measure is finite and nonzero and the identity is integrable. Definitions include every lattice translate. |
| Lattice and cell volume | `Lloyd/Geometry/LatticeGeometry.lean` | An arbitrary real basis generates the full-rank lattice. Separation, covering, compactness, positive finite cell volumes, and integrable centroids are proved from this construction. |
| Actual flat torus | `Lloyd/Geometry/FlatTorus.lean` | The quotient metric, compactness, finite positive area, and equality of quotient and lifted nearest-site distances. |
| Cell partition | `Lloyd/Geometry/CellPartition.lean`, `CellFundamentalDomain.lean` | Bisectors have zero volume; almost every lifted point has a unique nearest indexed site. The union of the chosen cells is a lattice fundamental domain; cell volumes sum to torus area. |
| Actual energy and dissipation | `Lloyd/Geometry/Quantization.lean` | Defines `F` and `G` using the actual cells and integral centroids. Proves the equality with the torus nearest-distance energy, centroid membership, the centroid bisector inequality, a configuration-independent bound on `G`, and the fixed-mesh bound on capped feedback. |
| Torus area and diameter estimates | `Lloyd/Geometry/TorusBalls.lean` | Derives a quadratic ball-area lower bound from lattice separation, then a fourth-power energy bound. Small actual cell energy implies cell diameter of order `sqrt(h)`, with a constant independent of the configuration and number of generators. |
| Bisector inequality | `Lloyd/Geometry/PeriodicCell.lean` | The periodic inequality for points in the two lifted cells. The unconditional application to integral centroids of the basis-lattice cells is now proved in `Quantization.lean`. |
| Separation estimates | `Lloyd/Analysis/Noncollision.lean` | The vector drift estimate and lower Gronwall bound. `ParticleDynamics.lean` now connects them to the actual centroids, differentiates squared separation, and proves torus noncollision for given AC solutions. Trajectory existence and continuation are not constructed. |
| Basic transport cost | `Lloyd/Transport/Coupling.lean` | An explicit definition as infimum over couplings, and the common-source coupling bound for measures of arbitrary mass. This does not construct the paper's histogram or PDE solution. |
| Diameter scale and final rate | `Lloyd/Analysis/ConvergenceRate.lean` | Fourth-root radius deduction, diameter-times-budget rate, and the final `h^(1/4)` calculation. The quantities in the last result are scalars with explicit comparison assumptions; they are not yet connected to the paper's Wasserstein error. |

## Missing links required to prove the theorem

1. **Regularity of the geometric quantities.** Prove the Appendix A gradient
   formula for `F`, and local Lipschitz regularity of volumes, centroid
   displacements, and `G` away from collisions. This includes configurations
   where Voronoi neighbours change. Prove the representative-independence and
   translation identities needed to formulate the centroid drift on the
   quotient. Static geometry, energy identification, the ball-area bound, and
   the fixed-mesh feedback bound are now checked; differentiating moving cells
   is not.

2. **Existence and uniqueness of particle trajectories.** Establish local
   Carathéodory existence for time-measurable, locally integrably bounded,
   spatially locally Lipschitz vector fields. Apply it to the actual feedback
   equation, justify continuous lifts (the squared-separation derivative is now checked),
   then use the now-checked quantitative torus separation result and compactness
   to continue the solution globally. A theorem for velocities continuous in time alone would
   not cover the hypothesis of Theorem 4.1.

3. **The energy differential inequality for those trajectories.** Use the
   gradient identity and justify periodic integration by parts for the stated
   spatial Lipschitz velocity to prove `F' + 2 α G ≤ 4 L F` almost everywhere.
   The new face and dynamics modules check the face algebra and the drift
   substitution; constructing actual finite face data and proving their local
   divergence identities and the gradient-chain input are still needed for an
   unconditional statement.

4. **The transport comparison from Theorem 2.1.** Construct the Lipschitz flow
   and transported measure, constant cell masses from nonnegative `ρ₀`, the
   Voronoi histogram, and measurable cell selectors. Prove the common-source
   comparison, the evolution estimate for displacement, and the bound for
   `B_h`. Connect the extended-valued transport cost to the finite real-valued
   bound in the paper. The checked coupling is a prerequisite, not this whole
   argument.

5. **Assemble the exact theorem.** Insert the actual geometric objects and
   trajectories into the existing estimates. Quantify over `N ≥ 2` with
   `h = sqrt(area/N)`, prove uniform constants depending only on the allowed
   data, take the time suprema, and handle degenerate cases such as `T=0` and
   zero total mass. State and prove every clause of Theorem 4.1. Only then mark
   the theorem complete.

For an eventual end-to-end proof, one remaining milestone is Appendix A: the differentiability of the actual
energy and local Lipschitz dependence of the cell integrals. A useful route to
the gradient is to differentiate the nearest-distance minimum at points with a
unique nearest site, and then justify differentiation under the integral. The
null-set and energy-identification results required for that route are now in
place. This is a proposed route, not an already checked differentiability proof.

The pinned Mathlib's `Analysis/ODE/PicardLindelof.lean` explicitly assumes
continuity in time (`IsPicardLindelof.continuousOn`). The paper permits merely
integrable time dependence, so its local-existence invocation cannot currently
be replaced by a direct application of that result.

## Scope

The current scope includes the four targeted arguments in Sections 3, 4, 5
and Appendix B. The one-sided Lipschitz face and mollification calculations
are now checked conditionally, as described in TARGETS.md. The full extension,
including flow construction and the final histogram theorem, remains unfinished.
The manuscript and archive remain separate from this Lean project.
