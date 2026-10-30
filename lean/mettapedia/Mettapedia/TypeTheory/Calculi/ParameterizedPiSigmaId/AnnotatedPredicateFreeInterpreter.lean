import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateInterpreter
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRoots

/-!
# Retaining the native proof fragment during contextual interpretation

The shared traversal carries evidence that its actual HOL proof uses neither
eta nor function extensionality. Root providers supply this property for their
selected templates; every surrounding operation preserves it. The underlying
reading and source checkers are unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {lex : LexicalReading Head Base Const} {closed : List (HOL.ClosedFormula Const)}
  {Γ : HOL.Ctx Base}

namespace EqualityReading
variable [DecidableEq Base]

theorem trans_free {source middle target : CTm Head Γ.length}
    (first : EqualityReading lex closed Γ source middle) (second : EqualityReading lex closed Γ middle target)
    (firstFree : first.2.proof.FunctionExtensionalityFree)
    (secondFree : second.2.proof.FunctionExtensionalityFree) :
    (trans first second).2.proof.FunctionExtensionalityFree := by
  obtain ⟨carrier, first⟩ := first
  obtain ⟨other, second⟩ := second
  have same : carrier = other := congrArg Sigma.fst (Reader.coherent first.rightRead second.leftRead)
  cases same
  simpa only [trans, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_castIndices] using And.intro firstFree secondFree
end EqualityReading

namespace FreeInterpreter

abbrev Evidence (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const))
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) (carrier : HOL.Ty Base) :=
  { reading : EqualityAt lex closed Γ source target carrier // reading.proof.FunctionExtensionalityFree }

def operations [DecidableEq Base] : Interpreter.EvidenceOps lex closed where
  Evidence := Evidence lex closed
  view := Subtype.val
  refl := fun reading => ⟨EqualityAt.refl reading, True.intro⟩
  symm := fun reading => ⟨reading.val.symm, reading.property⟩
  trans := fun first second =>
    let combined := EqualityReading.trans ⟨first.1, first.2.val⟩ ⟨second.1, second.2.val⟩
    ⟨combined.1, combined.2, EqualityReading.trans_free _ _ first.2.property second.2.property⟩
  app := fun function argument => ⟨EqualityAt.app function.val argument.val, ⟨function.property, argument.property⟩⟩
  lam := fun domains bodies => ⟨EqualityAt.lam domains.val bodies.val, by
    simpa only [EqualityAt.lam, HOL.ProofSyntax.FunctionExtensionalityFree,
      HOL.ProofSyntax.functionExtensionalityFree_castIndices] using bodies.property⟩
  pi := fun domains families => ⟨EqualityAt.pi domains.val families.val, by
    apply HOL.PredicateProducts.congruence_free
    · exact domains.property
    · simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices] using families.property⟩
  beta := fun domain body argument => ⟨EqualityAt.beta domain body argument, True.intro⟩

variable [DecidableEq Base] [DecidableEq Head]

def roots {decls : DeclName → Option (CTm Head 0)} {table : AlgebraicSchema.SchemaTable Head}
    (entries : Roots.Table lex closed decls table) (enabled : Fin table.length → Bool)
    (free : ∀ address entry, entries address = some entry → entry.template.proof.FunctionExtensionalityFree)
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) (code : SchemaJudgmentCode.Code Head Γ.length) :
    Option ((carrier : HOL.Ty Base) × Evidence lex closed Γ source target carrier) :=
  (Roots.read? entries enabled Γ source target code).map fun result =>
    ⟨result.equality.1, result.equality.2, result.equality_free free⟩

end FreeInterpreter
#print axioms EqualityReading.trans_free
#print axioms FreeInterpreter.operations
#print axioms FreeInterpreter.roots
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
