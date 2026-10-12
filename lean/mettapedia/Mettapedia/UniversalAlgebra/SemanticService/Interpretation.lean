import Mettapedia.Logic.TheorySimulation
import Mettapedia.UniversalAlgebra.EquationSystemInterpretation
import Mettapedia.UniversalAlgebra.SemanticService.Simulation

/-!
# Algebraic interpretations as SemanticService semantic translations

An equation-system interpretation induces a semantic translation between the
corresponding SemanticService theories: generated scope is preserved by proof transport,
and model-theoretic meaning is preserved by model reduct.  This does not claim
an exact translation of the concrete replay-certificate representation.

Formerly `Mettapedia.UniversalAlgebra.NIK.Interpretation`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
The namespace was `Mettapedia.UniversalAlgebra.NIK`; it is now `Mettapedia.UniversalAlgebra.SemanticService`.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.SemanticService

open Mettapedia.GSLT.LanguageDef.HeterogeneousTheory
open Mettapedia.Logic.TheorySimulation

universe u

variable {S T : Signature.{u}}
  [DecidableEq S.Operation] [DecidableEq T.Operation]

/-- Every algebraic equation-system interpretation induces a semantic
theory translation. -/
def theoryTranslation {source : EquationSystem S}
    {target : EquationSystem T}
    (interpretation : EquationSystem.Interpretation source target) :
    TheoryTranslation (theory source) (theory target) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind equation =>
    equation.translate interpretation.symbols
  scope_preserved := by
    intro _kind _equation inScope
    exact interpretation.mapConsequence inScope
  meaning_preserved := by
    intro _kind _equation meaningful
    exact interpretation.mapEntailsAt meaningful

/-- The target SemanticService theory semantically simulates the source whenever the
source equation system has an algebraic interpretation in the target. -/
theorem semanticallySimulates {source : EquationSystem S}
    {target : EquationSystem T}
    (interpretation : EquationSystem.Interpretation source target) :
    SemanticallySimulates (theoryObject target) (theoryObject source) :=
  ⟨theoryTranslation interpretation, trivial⟩

end Mettapedia.UniversalAlgebra.SemanticService
