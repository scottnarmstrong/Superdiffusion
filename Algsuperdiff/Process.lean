/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Algsuperdiff.Process.Kernel.OnePointExhaustionTail
import Algsuperdiff.Process.Kernel.ResolventTail
import Algsuperdiff.Process.Kernel.ResolventTailMoments
import Algsuperdiff.Process.Kernel.ResolventTailVariable
import Algsuperdiff.Process.Trajectory.ExitTimeChaining
import Algsuperdiff.Process.Trajectory.ExitTimeSurvival
import Algsuperdiff.Process.Trajectory.HitExitChaining
import Algsuperdiff.Process.Trajectory.HitExitTail

/-!
# Paper-shaped process theory

The process-theoretic modules of this paper that are shaped by the estimates
Sections 4 and 5 actually produce, rather than by the general theory of the
`MarkovProcess` library.  Everything here is stated on top of that library and
declared in the `Algsuperdiff.Process` namespace.

* `Algsuperdiff/Process/Kernel/ResolventTail.lean` — the displacement tail of
  the transition law from decay of the resolvent, by excessive-function
  comparison.
* `Algsuperdiff/Process/Kernel/ResolventTailMoments.lean` — the layer-cake
  passage from that displacement tail to the Kolmogorov fourth-moment
  criterion, and the regularity data of the compactified semigroup.
* `Algsuperdiff/Process/Kernel/ResolventTailVariable.lean` — the same passage
  when the profile and the cutting radius degrade with the shift.
* `Algsuperdiff/Process/Kernel/OnePointExhaustionTail.lean` — transport of a
  tail estimate in the metric of the live space to the exhaustion metric of the
  one-point compactification.
* `Algsuperdiff/Process/Trajectory/ExitTimeChaining.lean` — the geometric decay
  of a discounted exit weight under strong-Markov restarts.
* `Algsuperdiff/Process/Trajectory/HitExitChaining.lean` — the same chaining
  for the composite rule "hit a closed cell, then leave its enlargement".
* `Algsuperdiff/Process/Trajectory/HitExitTail.lean` — the Chernoff bound
  turning that chaining into an early-exit probability.
* `Algsuperdiff/Process/Trajectory/ExitTimeSurvival.lean` — Paley--Zygmund
  survival of the exit time above a fraction of its mean.
-/
