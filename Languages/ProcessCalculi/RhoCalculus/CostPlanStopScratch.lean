import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- Rho authored equation equivalence preserves its canonical representative. -/
theorem rhoEquationEquiv_canonicalize_eq
    {left right : Pattern}
    (equivalent : ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoReflectionProfile defaultBasePremises rhoCalc left right) :
    canonicalize rhoReflectivePresentation left =
      canonicalize rhoReflectivePresentation right := by
  induction equivalent with
  | rel left right step =>
      simpa only [CanonicalMatch.derivedCanonicalize_eq] using
        LanguageDefSemanticAgreement.rhoEquationContextStep_canonicalize_eq
          step
  | refl pattern => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
