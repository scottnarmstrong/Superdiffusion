# `Algsuperdiff/StochasticProcess`

Analytic theory of the divergence-form operator `-∇ · (a ∇ ·)` with a bounded
measurable, uniformly elliptic coefficient field `a = ν I + k` whose
antisymmetric part `k` is only in `W^{1,∞}`, developed to the point where the
associated diffusion process can be built.  Everything here is stated for a
general such coefficient field: nothing in this directory refers to the
paper's random model.

All modules live under `Common/`.

- **`Common/DivergenceForm/`** — weak solutions of the Dirichlet problem on a
  cube and on the whole space; the resolvent and the semigroup, on `L²`, on
  the bounded measurable functions and on `C₀`; the maximum principle; the
  exhaustion of the whole space by cubes and the resulting minimal resolvent;
  and the exponential decay estimates (`Decay/`) that make the whole-space
  resolvent map `C₀` to `C₀`.

- **`Common/Regularity/`** — interior regularity for the same operator: the
  Campanato characterization of Hölder continuity (`Campanato/`), the
  coefficient-freezing comparison argument (`Freezing/`), and the resulting
  interior Schauder and gradient estimates on cubes.

  `Common/Regularity/Ported/` is the small-contrast Schauder chain.

- **`Common/Semigroup/`** — the Laplace transform relating the semigroup to
  the resolvent, and the dense range of the resolvent.

- **`Common/FunctionalAnalysis/`** — density of compactly supported functions
  and zero-extension, used to compare the cube and whole-space problems.

These results are the analytic input to `Algsuperdiff/Section5/`, where the
diffusion process of the operator is obtained over the `MarkovProcess`
library; `Algsuperdiff/Process/` holds the paper-shaped process estimates
built on top of it.

`import Algsuperdiff.StochasticProcess` pulls in the whole directory.
