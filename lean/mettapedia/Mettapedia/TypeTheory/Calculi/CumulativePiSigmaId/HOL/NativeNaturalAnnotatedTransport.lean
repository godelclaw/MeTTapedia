import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedElaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateComputation

/-!
# Instantiation and composition through coherent annotated readings

Opening an annotated lambda commutes with the existing HOL substitution.
An actual source beta step therefore receives the primitive retained beta
proof at its computed endpoints. Two translated proofs whose middle is the
same annotated source term compose without a supplied target-equality premise:
the reader's coherence theorem establishes that their middle codes agree.

These operations join represented steps. A complete interpreter for the
source's typed conversion certificates remains a separate consumer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}

theorem AnnotatedReads.instantiate
    {body : CTm Tower.Head (domain :: Γ).length} {argument : CTm Tower.Head Γ.length}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain}
    {argumentCode : HOL.Term Const Γ domain}
    (bodyRead : AnnotatedReads operations body bodyCode)
    (argumentRead : AnnotatedReads operations argument argumentCode) :
    AnnotatedReads operations (CTm.inst0 argument body) (HOL.instantiate argumentCode bodyCode) := by
  apply bodyRead.substitute (HOL.Subst.single argumentCode) (CTm.subst0 argument)
  intro type index
  cases index with
  | vz => exact argumentRead
  | vs prior => exact .var prior

namespace AnnotatedReading

def beta {Δ : List (HOL.Formula Const Γ)}
    {sourceDomain : CTm Tower.Head Γ.length}
    {body : CTm Tower.Head (domain :: Γ).length} {argument : CTm Tower.Head Γ.length}
    {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain}
    {argumentCode : HOL.Term Const Γ domain}
    (_domainRead : AnnotatedReads operations sourceDomain domainCode)
    (_bodyRead : AnnotatedReads operations body bodyCode)
    (_argumentRead : AnnotatedReads operations argument argumentCode) :
    HOL.ProofSyntax Const Δ (.eq (.app (.lam bodyCode) argumentCode) (HOL.instantiate argumentCode bodyCode)) :=
  .beta argumentCode bodyCode

theorem beta_endpoints
    {sourceDomain : CTm Tower.Head Γ.length}
    {body : CTm Tower.Head (domain :: Γ).length} {argument : CTm Tower.Head Γ.length}
    {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain}
    {argumentCode : HOL.Term Const Γ domain}
    (domainRead : AnnotatedReads operations sourceDomain domainCode)
    (bodyRead : AnnotatedReads operations body bodyCode)
    (argumentRead : AnnotatedReads operations argument argumentCode) :
    AnnotatedReads operations (.app (.lam sourceDomain body) argument) (.app (.lam bodyCode) argumentCode) ∧
      AnnotatedReads operations (CTm.inst0 argument body) (HOL.instantiate argumentCode bodyCode) :=
  ⟨.application (.abstraction domainRead bodyRead) argumentRead, bodyRead.instantiate argumentRead⟩

variable [DecidableEq Base]

/-- Composition derives literal agreement at the shared annotated source;
the caller supplies the two actual proofs, not a coherence assumption. -/
def compose {type : HOL.Ty Base} {Δ : List (HOL.Formula Const Γ)}
    {middle : CTm Tower.Head Γ.length}
    {left firstMiddle secondMiddle right : HOL.Term Const Γ type}
    (firstRead : AnnotatedReads operations middle firstMiddle)
    (secondRead : AnnotatedReads operations middle secondMiddle)
    (first : HOL.ProofSyntax Const Δ (.eq left firstMiddle))
    (second : HOL.ProofSyntax Const Δ (.eq secondMiddle right)) :
    HOL.ProofSyntax Const Δ (.eq left right) :=
  .eqTrans first (HOL.ProofSyntax.castIndices rfl
    (congrArg (fun term => HOL.Term.eq term right) (term_unique secondRead firstRead)) second)

theorem compose_free {type : HOL.Ty Base} {Δ : List (HOL.Formula Const Γ)}
    {middle : CTm Tower.Head Γ.length}
    {left firstMiddle secondMiddle right : HOL.Term Const Γ type}
    (firstRead : AnnotatedReads operations middle firstMiddle)
    (secondRead : AnnotatedReads operations middle secondMiddle)
    (first : HOL.ProofSyntax Const Δ (.eq left firstMiddle))
    (second : HOL.ProofSyntax Const Δ (.eq secondMiddle right))
    (firstFree : first.FunctionExtensionalityFree) (secondFree : second.FunctionExtensionalityFree) :
    (compose firstRead secondRead first second).FunctionExtensionalityFree := by
  simp [compose, HOL.ProofSyntax.FunctionExtensionalityFree, firstFree, secondFree]

#print axioms beta_endpoints
#print axioms compose
#print axioms compose_free

end AnnotatedReading
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
