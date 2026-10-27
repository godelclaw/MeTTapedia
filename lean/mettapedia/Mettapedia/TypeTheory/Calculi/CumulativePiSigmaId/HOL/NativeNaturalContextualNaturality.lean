import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualReindexing
import Mettapedia.Logic.HOL.PredicateProductsNaturality

/-!
# Naturality of contextual natural-number conversion elaboration

The contextual source substitution and the retained HOL substitution commute.
The comparison retains proof constructors and hypothesis occurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.Contextual.Proof

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} [DecidableEq Base]
    {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}

theorem hol_substitute_heq {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code)
    {Ξ : HOL.Ctx Base} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile index.targetContext Ξ index.sourceContext targetContext) :
    HEq (proof.substitute substitution).hol (HOL.ProofSyntax.subst substitution.target proof.hol) := by
  induction proof generalizing Ξ with
  | base path =>
      simp only [substitute, hol_castCode, hol]
      exact (heq_of_eq (substitution.elaborate_mapConv path)).trans
        (HOL.ProofSyntax.castIndices_heq _ _ _)
  | refl source =>
      simp only [substitute, hol_castCode, hol, HOL.ProofSyntax.subst]
      congr 1
      exact (assumptions_substitute operations substitution.target).symm
  | symm proof ih =>
      simp only [substitute, hol, HOL.ProofSyntax.subst]
      congr 1
      · exact (assumptions_substitute operations substitution.target).symm
      · exact ih substitution
  | trans first second ihFirst ihSecond =>
      simp only [substitute, hol, HOL.ProofSyntax.subst]
      congr 1
      · exact (assumptions_substitute operations substitution.target).symm
      · exact ihFirst substitution
      · exact ihSecond substitution
  | application _ _ first second ihFirst ihSecond =>
      simp only [substitute, hol_castCode, hol_castType, hol, align]
      refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
      refine HEq.trans ?_ (HOL.ProofSyntax.subst_castIndices_heq _ _ _ _).symm
      simp only [HOL.ProofSyntax.appCongr, HOL.ProofSyntax.subst]
      congr 1
      all_goals first
        | exact (assumptions_substitute operations substitution.target).symm
        | (congr 1
           all_goals first
             | exact (assumptions_substitute operations substitution.target).symm
             | exact ihFirst substitution
             | exact ihSecond substitution)
  | abstraction _ _ _ _ _ _ body _ ihBody =>
      simp only [substitute, hol_castCode, hol, align]
      refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
      refine HEq.trans ?_ (HOL.ProofSyntax.subst_castIndices_heq _ _ _ _).symm
      simp only [HOL.ProofSyntax.subst]
      congr 1
      · exact (assumptions_substitute operations substitution.target).symm
      · refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
        refine HEq.trans ?_ (HOL.ProofSyntax.id_mp_heq _ _).symm
        refine HEq.trans ?_ (HOL.ProofSyntax.subst_castIndices_heq _ _ _ _).symm
        exact ihBody _
  | product _ _ _ _ _ domain family ihDomain ihFamily =>
      simp only [substitute, hol_castCode, hol, align]
      refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
      refine HEq.trans ?_ (HOL.ProofSyntax.subst_castIndices_heq _ _ _ _).symm
      refine HEq.trans ?_ (HOL.PredicateProducts.subst_congruence_heq _ _ _).symm
      congr 1
      · exact (assumptions_substitute operations substitution.target).symm
      · exact ihDomain substitution
      · refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
        refine HEq.trans ?_ (HOL.ProofSyntax.castIndices_heq _ _ _).symm
        refine HEq.trans ?_ (HOL.ProofSyntax.subst_castIndices_heq _ _ _ _).symm
        exact ihFamily _

/-- Literal equality after the fixed root assumptions are transported. -/
theorem hol_substitute {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code)
    {Ξ : HOL.Ctx Base} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile index.targetContext Ξ index.sourceContext targetContext) :
    (proof.substitute substitution).hol = substitution.proof proof.hol := by
  apply eq_of_heq
  exact (hol_substitute_heq proof substitution).trans (HOL.ProofSyntax.castIndices_heq _ _ _).symm

/-- Moving the context and widening row permissions commute on the full
retained HOL proof. -/
theorem hol_widen_substitute {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code)
    {Ξ : HOL.Ctx Base} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile index.targetContext Ξ index.sourceContext targetContext) :
    ((proof.widen included).substitute substitution).hol =
      ((proof.substitute substitution).widen included).hol := by
  rw [hol_substitute, hol_widen, hol_widen, hol_substitute]

#print axioms hol_substitute_heq
#print axioms hol_substitute
#print axioms hol_widen_substitute

end AnnotatedConversion.Contextual.Proof
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
