# Lean formalization of the Lloyd paper

**Status: four targeted arguments now have Lean proofs with explicit inputs;
Theorem 4.1 and the full Section 5 extension are not proved end to end.**
The current scope is to check the paper-specific arguments while leaving
classical existence, differentiation, and divergence results as stated inputs.
See [TARGETS.md](TARGETS.md) for the precise boundary of each of the four proofs,
and [STATUS.md](STATUS.md) for the larger theorem's status.

The source paper is [TOUT/v7.pdf](../TOUT/v7.pdf), with editable source at
[TOUT/v7.tex](../TOUT/v7.tex). This targets the corrected version: the general
feedback satisfies `0 ≤ α ≤ G/h^(5/2)`, whereas estimate (4.6) additionally
requires `α = G/h^(5/2)`.

## The four current targets

- **Periodic faces:** the bisector flux, both orientations of each face,
  self-translated face cancellation, the weighted face identity, and `T_v ≤ 4 L F`.
  The finite face representation and local divergence formulas are inputs;
  the global identity is proved.
- **Removal/insertion:** actual energy integral comparisons, the hole obtained
  from the union-of-balls argument, minimizer separation, perturbation of
  separated sites, and cell-volume bounds. Geometric radius/area estimates,
  integrability, and variational minimality are explicit inputs.
- **Particle dynamics:** the actual centroid drift, squared-separation
  differentiation, quantitative torus separation and noncollision, and the
  exact `-2 α G` dissipation term. The energy inequality follows from the
  classical chain formula and the checked face estimate.
- **Mollification:** actual Bochner integral averaging, zero-mean cancellation,
  preservation of OSL, comparison of absolutely continuous trajectories,
  the error bound uniform in time, and the `sqrt(ε)` common-source transport bound.
  Existence/measurability of flows and the Filippov selection's OSL property are inputs.

## Earlier checked components

- The energy integration argument, allowing an integrable time coefficient and
  an absolutely continuous energy.
- The corrected feedback budget `A ≤ C h^(-1/4)` from the dissipation bound.
- The stronger centroid estimate for full feedback.
- A genuine flat torus for any planar lattice basis, with its quotient distance
  and finite positive area measure.
- Compact lifted Voronoi cells with positive finite volume; their integral
  centroids belong to them and satisfy the periodic bisector inequality.
- The cell partition up to null sets, total cell area, and equality of the
  cell-integral energy with the nearest-distance energy on the torus.
- The torus ball-area lower bound and `F ≥ c R^4/16`, with `c` independent
  of the particle number and configuration.
- The actual implication `F ≤ C h² → diam(Pᵢ) ≤ Cd sqrt(h)`, uniformly
  over all cells and configurations.
- A uniform geometric bound on actual centroid dissipation `G` and therefore
  a bound on capped feedback for each fixed positive mesh size.
- The differential and Gronwall estimates used to prevent collisions.
- A transport coupling between two images of the same measure, and its
  displacement-cost bound.
- The final calculation giving the `h^(1/4)` convergence rate, assuming the
  geometric and transport comparisons.

Each result displays its assumptions explicitly. In particular, proving an
implication from the energy inequality is different from establishing that
inequality without additional hypotheses for the actual particle system. The
new face and dynamics modules reduce this to the explicitly stated local
divergence, face-representation, and gradient-chain inputs.

## Check the project

In a terminal in this folder:

```sh
make check
```

This compiles every proof and audits the axioms of every project theorem. It
rejects unfinished proofs and extra axioms. It allows the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. The machine-readable result is
[verification.json](verification.json), including hashes of the checked files.

For a freshly copied project without its `.lake` cache, first run:

```sh
make cache
make check
```

Lean is pinned to **4.29.0**; Mathlib is pinned to **v4.29.0**, commit
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. Dependency revisions are recorded in
`lake-manifest.json`. The generated `.lake` directory is not source code and
is ignored by Git. This project has its own dependencies, with no path
connection to another paper's Lean project.

## Where to start reading

[GUIDE.md](GUIDE.md) explains what it means to finish this formalization, what
has actually been connected to the paper, and which classical inputs are deliberately left outside the current scope.

[Quantization.lean](Lloyd/Geometry/Quantization.lean) defines the actual `F` and
`G`. [TorusBalls.lean](Lloyd/Geometry/TorusBalls.lean) proves the geometric
implication from small `F` to small cell diameters without assumed ball-area
or cell-volume estimates.

[ScalarEstimates.lean](Lloyd/Analysis/ScalarEstimates.lean) connects the energy
and feedback calculations on the time interval. Its assumptions include the
energy differential inequality: it is a proved intermediate result, not the
complete Theorem 4.1.

[STATUS.md](STATUS.md) maps the other files to the paper and identifies the
remaining links. [SOURCE.json](SOURCE.json) records the original manuscript
snapshot; [TARGETS-SOURCE.json](TARGETS-SOURCE.json) records the source used for
this four-target pass. This pass changed the Lean project, not the manuscript.
