import Mettapedia.OSLF.NativeTypes.Generation.NativeModalFormation

/-!
# Native event and parameter projection certificates

Each projection consumes the original input and its dependent event value.
Its result is the authored carrier computed from the schema's program, focus
or scoped parameter slot. All formation trees use the common native rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open NativeSignature

variable (plan : Plan) (installed : Installation plan.snapshot.language)
    (modal : List (NativeModalHeaders.Header plan))

def projection (symbol : Projection plan modal) : TermExpr (symbols plan installed modal) 2 :=
  .primitive (.inr symbol) TermExpr.var

def projectionFormation (symbol : Projection plan modal) :
    Derivation (signature plan installed modal)
      (.term (eventContext plan installed modal symbol.index)
        (projection plan installed modal symbol)
        (authoredType plan installed modal (projectionCarrier plan modal symbol) 2)) := by
  let formed := (headers plan installed modal).termHeader (.inr symbol)
  have tree := deriveList (.primitive (eventContext plan installed modal symbol.index)
      (.inr symbol) TermExpr.var)
    (.cons formed (.cons formed
      (.cons ((headers plan installed modal).termResult (.inr symbol))
        (.cons (deriveList (.substitutionIdentity (eventContext plan installed modal symbol.index))
          (.cons formed .nil)) .nil))))
  change Derivation (signature plan installed modal)
    (.term (eventContext plan installed modal symbol.index) (projection plan installed modal symbol)
      ((authoredType plan installed modal (projectionCarrier plan modal symbol) 2).substitute TermExpr.var)) at tree
  rw [authoredType_substitute] at tree
  exact tree

def projectionCertificate (symbol : Projection plan modal) :=
  Certificates.Refinement.erase (projectionFormation plan installed modal symbol)

theorem projectionCertificate_checked (symbol : Projection plan modal) :
    Certificates.Refinement.check (projectionCertificate plan installed modal symbol)
      (.term (eventContext plan installed modal symbol.index) (projection plan installed modal symbol)
        (authoredType plan installed modal (projectionCarrier plan modal symbol) 2)) = true :=
  Certificates.Refinement.check_erase _

def eventCertificate (index : Fin modal.length) :=
  Certificates.Refinement.erase (eventFormed plan installed modal index)

theorem eventCertificate_checked (index : Fin modal.length) :
    Certificates.Refinement.check (eventCertificate plan installed modal index)
      (.type (inputContext plan installed modal index) (eventType plan installed modal index (.var 0))) = true :=
  Certificates.Refinement.check_erase _

end Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature
