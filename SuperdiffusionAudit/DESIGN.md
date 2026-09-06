# Design of the comparator surface

Each of the three main theorems has a directory here with the same four files.

- `Challenge.lean` imports `Mathlib` and nothing else. It rebuilds from mathlib
  primitives every object the theorem mentions: the antisymmetric `C²` shell
  fields and their Borel structure, the exact shell transformations, the
  regular coefficient fields, the weighted cube observable of the model's
  assumptions, the corrector machinery behind the disorder constant `cstar`,
  the model itself, the sample carrier, the full stream field
  `k(x) = ∑_n (j_n(x) − j_n(0))`, the Dirichlet problems on triadic cubes, and,
  for Theorem A, the diffusion process through a resolvent identity for its
  generator. It states the theorem and ends in a single `sorry`. This file is
  the object of trust: a reader checks what it says, not how it is proved.
- `Solution.lean` imports the library and proves the challenge's theorem by
  applying the library's verified statement.
- `SolutionBasic.lean` holds the mathlib-only lemmas about the challenge's own
  definitions that the solution needs.
- `comparator.json` names the challenge, the solution, the theorem and the
  permitted axioms (`propext`, `Classical.choice`, `Quot.sound`).

The files under `Support/` are part of the solutions. Each `*Bridge.lean`
identifies the challenge's definitions with the library's, mostly by `rfl`;
the `*CarrierMeasurability.lean` files supply the two measurability facts the
identification needs; the Theorem A solution also uses `LaplaceUniqueness.lean`
and the `Superdiffusivity{Resolvent,LiveLaw,Marginal}.lean` files to pass from
the challenge's resolvent characterization of the process to the library's
construction.

The public workflow feeds each pair to
[leanprover/comparator](https://github.com/leanprover/comparator), which
elaborates both statements and requires them to coincide, replays the
solution's proof through an independent implementation of the Lean kernel,
and rejects any axiom outside the permitted three. Nothing a solution imports
can change the statement the reader saw in the challenge; it can only supply
a kernel-checked proof of it.

`check_standalone.sh` elaborates a challenge on its own, with the library's
build options, to confirm that it depends on mathlib alone.
