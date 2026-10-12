import Mettapedia.OSLF.NativeTypes.Generation.NativeGraphFormation

/-!
# Parameterized structural types in the common native grammar

The inhabitants are constrained by native logical equality to the authored
constructor applied to its ordered parameters. Binding parameters retain their
actual function carriers. Formation emits a complete ordinary certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Installation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable {language : LanguageDef} (installed : Installation language)

def structuralType (constructor : installed.Constructor) :
    TypeExpr installed.symbols (installed.parameters constructor).length :=
  .comprehension (installed.result constructor).native
    (installed.graph constructor (fun position => .var position.succ) (.var 0))

def structuralFormation (constructor : installed.Constructor) :
    Derivation installed.signature
      (.type (installed.signature.termParameters constructor) (installed.structuralType constructor)) := by
  let context := installed.signature.termParameters constructor
  let result : TypeExpr installed.symbols (installed.parameters constructor).length :=
    (installed.result constructor).native
  let contextTree := installed.formation.termHeader constructor
  let resultTree := installed.formation.termResult constructor
  let extended := deriveList (.contextExtend context result)
    (.cons contextTree (.cons resultTree .nil))
  let arguments := deriveList (.substitutionWeaken context result) (.cons resultTree .nil)
  have target : Derivation installed.signature
      (.term (.snoc context result) (.var 0) (installed.result constructor).native) := by
    have tree := deriveList (.variable (.snoc context result) 0) (.cons extended .nil)
    have same : (ContextExpr.snoc context result).lookup 0 = (installed.result constructor).native := by
      change result.rename Fin.succ = _
      exact Carrier.native_rename _ _
    exact (congrArg (Judgment.term (.snoc context result) (.var 0)) same) ▸ tree
  let graphTree := installed.graphFormation constructor (.snoc context result)
    (fun position => .var position.succ) (.var 0) extended arguments target
  exact deriveList (.comprehensionFormation context result
    (installed.graph constructor (fun position => .var position.succ) (.var 0)))
    (.cons contextTree (.cons resultTree (.cons graphTree .nil)))

def structuralCertificate (constructor : installed.Constructor) :=
  Certificates.Refinement.erase (installed.structuralFormation constructor)

theorem structuralCertificate_checked (constructor : installed.Constructor) :
    Certificates.Refinement.check (installed.structuralCertificate constructor)
      (.type (installed.signature.termParameters constructor) (installed.structuralType constructor)) = true :=
  Certificates.Refinement.check_erase (installed.structuralFormation constructor)

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Installation
