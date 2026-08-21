import Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.Closure
import Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.BoundProvider
import Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Closure
import Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.Closure
import Algsuperdiff.Section24.Sensitivity.Provider.Path.Closure
import Algsuperdiff.Section24.Sensitivity.Provider.Response.Closure
import Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.Provider

/-!
# sensitivity provider exports

It is imported by `Algsuperdiff.Section24.Sensitivity.Vocabulary`, which the
frozen theorems import, so a anchor closes by exact application of its
provider.

- `Provider.Path.Closure`: `responseJ_derivative` (`S24-S).
- `Provider.DhBound.Discharge.BoundProvider`: `coarseMatrixDerivative_bound`
  (`S24-S).
- `Provider.Lambda.Closure`: `lambda_sensitivity` (`S24-S).
- `Provider.Response.Closure`: `responseJ_sensitivity` (`S24-S).
- `Provider.BigLambda.Closure`: `bigLambda_sensitivity` and
  `bigLambda_sensitivity_at_delta` (`S24-S, `S24-S).
- `Provider.LambdaUnconditional.Closure`: `lambda_sensitivity_unconditional`
  (`S24-S).
- `Provider.ResponseUnconditional.Provider`:
  `responseJ_sensitivity_unconditional` (`S24-S).
-/
