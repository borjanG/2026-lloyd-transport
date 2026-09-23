# How to read the four-target formalization

The current task is targeted verification of four arguments, not rebuilding
all classical analysis or claiming a complete Lean proof of the paper.

A Lean theorem lists assumptions followed by a conclusion. Lean checks that
the conclusion follows from those assumptions. Here, standard analytical
inputs can remain assumptions, but the paper-specific estimate being checked
must be a conclusion. None of the new proofs use `sorry` or introduce axioms.

## What each target now does

1. **Faces.** Give Lean a finite list of periodic faces, their two endpoints,
   lattice shifts, and surface measures. Give the local divergence formulas.
   Lean proves the radial flux on each side, counts each face twice, derives
   the weighted identity, cancels self-translated faces in transport, and
   deduces the OSL energy estimate. Constructing that finite list and proving
   its local formulas from the actual periodic cells is still unformalized.

2. **Removal and insertion.** Energy is an integral of squared nearest-site
   distance, not an arbitrary scalar. Lean proves what happens to that
   integral on deleting and inserting a site. Minimality then forces a
   separation bound, whose constant is independent of the mesh and number of
   sites. It also checks the nearby-configuration and volume deductions.
   The standard radius/area bounds and minimality are supplied explicitly.
   This does not prove quasi-uniformity of minimizers or convergence of the
   trapping feedback, neither of which this argument establishes in the paper.

3. **Dynamics.** The drift uses the integral centroids already constructed
   from actual periodic cells. For any absolutely continuous curve satisfying
   the ODE almost everywhere, Lean proves quantitative separation on the
   torus and thus noncollision. Substituting this drift in the classical
   energy-gradient formula gives exactly `-2 α G`; combining it with the
   checked face argument gives the energy differential inequality.
   ODE existence/continuation and the gradient-chain formula are inputs.

4. **Mollification.** Convolution is an actual integral against a probability
   measure. Lean checks the zero-mean cancellation, OSL preservation, the
   comparison of trajectories, Gronwall, the uniform-in-time error bound, and
   the square-root rate and transport coupling. Existence of Filippov flows
   and inheritance of OSL by the selected Filippov velocity are inputs.

[TARGETS.md](TARGETS.md) names the exact declarations and assumptions.

## What a passing check means

Run `make check`. It builds all modules and prints the axioms of every project
theorem. The audit permits only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`; its file hashes are in `verification.json`.

It certifies these conditional mathematical statements. It does not certify
all of Theorem 4.1, a constructed Filippov flow, the actual finite face
representation, or the final histogram convergence theorem. Those are separate
claims. The current approach lets us examine the four arguments without first
formalizing all the classical prerequisites.
