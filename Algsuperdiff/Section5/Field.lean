/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Algsuperdiff.Section5.Field.TailGauge
import Algsuperdiff.Section5.Field.TailMoments
import Algsuperdiff.Section5.Field.TailProbability
import Algsuperdiff.Section5.Field.SharpTailProbability
import Algsuperdiff.Section5.Field.SharpTailGrowth
import Algsuperdiff.Section5.Field.Carrier
import Algsuperdiff.Section5.Field.StreamField
import Algsuperdiff.Section5.Field.Continuity
import Algsuperdiff.Section5.Field.Growth
import Algsuperdiff.Section5.Field.CutoffLimit
import Algsuperdiff.Section5.Field.Exhaustion
import Algsuperdiff.Section5.Field.Holder
import Algsuperdiff.Section5.Field.HolderEstimate
import Algsuperdiff.Section5.Field.ScaleDecompositionBounds
import Algsuperdiff.Section5.Field.FreezingRadius
import Algsuperdiff.Section5.Field.LocalSplitBounds
import Algsuperdiff.Section5.Field.LocalizedTailData
import Algsuperdiff.Section5.Field.BoundaryGrowth
import Algsuperdiff.Section5.Field.BoundaryConservativity
import Algsuperdiff.Section5.Field.SubexponentialProfile
import Algsuperdiff.Section5.Field.LocalizedTailProfile
import Algsuperdiff.Section5.Field.LocalizedTailEnvelope
import Algsuperdiff.Section5.Field.UniformExhaustionProfile
import Algsuperdiff.Section5.Field.UniformExhaustionBudget
import Algsuperdiff.Section5.Field.ExhaustionTailInput
import Algsuperdiff.Section5.Field.WholeSpaceC0
import Algsuperdiff.Section5.Field.ShiftAsymptotics
import Algsuperdiff.Section5.Field.WholeSpaceDenseRange
import Algsuperdiff.Section5.Field.WholeSpaceKernelConservativity
import Algsuperdiff.Section5.Field.StreamProcess

/-!
# The full stream matrix

This facade exports the whole construction of the normalized stream matrix
`k(x) = Σ_{n ∈ ℤ} (j_n(x) - j_n(0))`: the deterministic tail gauges, their
first moments, the almost-sure tail event, the sample carrier and its law, the
field itself, its continuity, its measurability in the sample, its linear
growth, its localized log-subexponential resolvent-tail profile, and the
identification of the ascending condition with the Section 5.1 large-scale
event.

It also exports the quenched law of the field as a measurable family: the
whole-space processes of the samples form one kernel from the sample and the
starting point to path space, so quenched expectations may be integrated
against the sample law.  That family is unconditional: the coefficient field on
each exhaustion cube is a measurable parameter, the cube resolvent is continuous
in that parameter, and the two combine into measurability in the sample of the
value of the cube resolvent at each point.

Section 5 is not part of the default build root yet, so this module is built as
the explicit target `Algsuperdiff.Section5.Field`.  The tree has several
maximal modules (`Growth`, `LargeScaleBridge`, `Measurability`,
`ParameterizedProcess`), so no single one of them covers it.
-/
