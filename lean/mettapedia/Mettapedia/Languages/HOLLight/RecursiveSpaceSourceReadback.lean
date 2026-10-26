import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
import Mettapedia.Languages.HOLLight.ExportCodec

/-!
# Checked source roots for the recursive-space correspondence

The operation table carries the exact source declaration identities and type
annotations. Six cache indices select the Peano and recursive-space facts.
Successful readback constructs their translation and cache-membership evidence,
which instantiates the correspondence theorem for accepted source-policy replay.
The numeral wrapper is retained in the natural zero term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpaceSourceReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution ExactFormulaReadback

universe w

structure Operations where
  number : Ty
  payload : Ty
  space : Ty
  zero : Const
  numeral : Const
  successor : Const
  bottom : Const
  construct : Const

def Operations.natural (operations : Operations) : NaturalModelCategoricity.Signature where
  number := operations.number.toHOL
  zero := .app (.const (.constant operations.numeral (.function operations.number operations.number)
    (Ty.toHOL_function _ _))) (.const (.constant operations.zero operations.number rfl))
  successor := .const (.constant operations.successor (.function operations.number operations.number)
    (Ty.toHOL_function _ _))

def Operations.recursive (operations : Operations) : RecursiveSpaceModelComparison.Signature where
  number := operations.number.toHOL
  payload := operations.payload.toHOL
  space := operations.space.toHOL
  bottom := .const (.constant operations.bottom operations.space rfl)
  construct := .const (.constant operations.construct
    (.function operations.number (.function operations.payload
      (.function (.function operations.number operations.space) operations.space)))
    (by simp only [Ty.toHOL_function]))

/-- Resolve the source's declared operations. Success is syntax resolution;
only checked cache readings provide the corresponding logical evidence. -/
def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  let numberOperator ← List.lookup "num" symbols.operators
  let spaceOperator ← List.lookup "recspace" symbols.operators
  let payload := Ty.var (Name.global "A")
  return ⟨.op numberOperator [],payload,.op spaceOperator [payload],
    ← List.lookup "_0" symbols.constants, ← List.lookup "NUMERAL" symbols.constants,
    ← List.lookup "SUC" symbols.constants, ← List.lookup "BOTTOM" symbols.constants,
    ← List.lookup "CONSTR" symbols.constants⟩

structure CacheIndices where
  successorSeparation : Nat
  successorInjective : Nat
  naturalInduction : Nat
  constructorSeparation : Nat
  constructorInjective : Nat
  recursiveInduction : Nat

structure Readings (operations : Operations) (state : Registered.State) where
  naturalFacts : NaturalModelCategoricity.CachedFacts operations.natural state
  recursiveFacts : RecursiveSpaceModelComparison.CachedFacts operations.recursive state

def read? (operations : Operations) (state : Registered.State) (indices : CacheIndices) :
    Option (Readings operations state) := do
  let sn ← ExactFormulaReadback.read? state indices.successorSeparation operations.natural.successorSeparation
  let injn ← ExactFormulaReadback.read? state indices.successorInjective operations.natural.successorInjective
  let indn ← ExactFormulaReadback.read? state indices.naturalInduction operations.natural.induction
  let sr ← ExactFormulaReadback.read? state indices.constructorSeparation operations.recursive.constructorSeparation
  let injr ← ExactFormulaReadback.read? state indices.constructorInjective operations.recursive.constructorInjective
  let indr ← ExactFormulaReadback.read? state indices.recursiveInduction operations.recursive.induction
  return ⟨⟨sn.fact,injn.fact,indn.fact,sn.known,injn.known,indn.known,
    sn.closed,injn.closed,indn.closed,sn.translated,injn.translated,indn.translated⟩,
    ⟨sr.fact,injr.fact,indr.fact,sr.known,injr.known,indr.known,
      sr.closed,injr.closed,indr.closed,sr.translated,injr.translated,indr.translated⟩⟩

open SourceProfileModels TypeFamilySemantics

/-- The executable readback supplies the exact formula evidence consumed by
the operation-preserving comparison in the model constructed by source replay. -/
noncomputable def correspondence (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (readings : Readings operations after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (filler : RecursiveSpaceSemantics.Relation
      (operations.recursive.Payload ((sourceReplayFrame commands after accepted).frame.model other assignment))) :
    RecursiveSpaceModelComparison.Correspondence operations.recursive
      ((sourceReplayFrame commands after accepted).frame.model other assignment) filler :=
  RecursiveSpaceModelComparison.replayCorrespondence operations.recursive
    operations.natural.zero operations.natural.successor commands after accepted
    readings.naturalFacts readings.recursiveFacts other assignment filler

theorem checked_correspondence (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (indices : CacheIndices) (read : (read? operations after indices).isSome = true)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (filler : RecursiveSpaceSemantics.Relation
      (operations.recursive.Payload ((sourceReplayFrame commands after accepted).frame.model other assignment))) :
    Nonempty (RecursiveSpaceModelComparison.Correspondence operations.recursive
      ((sourceReplayFrame commands after accepted).frame.model other assignment) filler) :=
  ⟨correspondence operations commands after accepted ((read? operations after indices).get read)
    other assignment filler⟩

#print axioms correspondence
#print axioms checked_correspondence

end Mettapedia.Languages.HOLLight.RecursiveSpaceSourceReadback
