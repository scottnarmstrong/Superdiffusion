import Algsuperdiff.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the three main
theorems.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

This file is intentionally not imported by the library root: a `#print axioms`
command re-runs on every rebuild of the module that carries it, so the report
is kept off the default target and produced only when the module is built
explicitly (`lake build Algsuperdiff.Meta.AxiomsAudit`), as continuous
integration does on every push.
-/

#print axioms Algsuperdiff.superdiffusivity
#print axioms Algsuperdiff.generator_renormalization
#print axioms Algsuperdiff.anomalous_regularity
