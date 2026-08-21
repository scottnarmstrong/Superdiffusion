import Algsuperdiff.Frozen.Section24.CoarseMatrixDerivativeCharacterization
import Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
import Algsuperdiff.Frozen.Section24.PerturbCoeffOn
import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.BigLambda.UnitCubeBigLambdaCharacterization
import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationErrorCharacterization
import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambdaCharacterization
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.GradientW1Infinity
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.ValueL2
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.W1Infinity
import Algsuperdiff.Section24.CoarseMatrixDerivative.BoundedField
import Algsuperdiff.Section24.CoarseMatrixDerivative.Existence
import Algsuperdiff.Section24.CoarseMatrixDerivative.Polarization
import Algsuperdiff.Section24.CoarseMatrixDerivative.ResponsePairing
import Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.Characterization
import Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
import Algsuperdiff.Section24.UnitCubeMultiscale.EllipticityLocality
import Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.Characterization
import Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationErrorLocality
import Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.Characterization
import Homogenization.Ambient.ScalarMatrix

/-!
# Section 2.4 sensitivity: semantic import hub for provider modules

Import hub collecting the proved semantic units (frozen definition and
characterization files together with the public Section 2.4 A modules) needed
by the Section 2.4 sensitivity provider modules.

## Cycle-safety rule

Provider modules import this file, never
`Algsuperdiff.Section24.Sensitivity.Vocabulary`.  `Vocabulary` is imported by
the frozen sensitivity anchors, so a provider importing it (directly or
transitively) would create an import cycle when the anchors are onto their
providers.  Accordingly, this file must never import `Vocabulary` or any frozen
sensitivity anchor (`ResponseJDerivative`, `CoarseMatrixDerivativeBound`,
`LambdaSensitivity`, `ResponseJSensitivity`, `BigLambdaSensitivity`,
`BigLambdaSensitivityAtDelta`, `LambdaSensitivityUnconditional`,
`ResponseJSensitivityUnconditional`).
-/
