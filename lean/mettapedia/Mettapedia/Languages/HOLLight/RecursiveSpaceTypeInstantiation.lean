import Mettapedia.Languages.HOLLight.RecursiveSpaceSourceReadback
import Mettapedia.Languages.HOLLight.RegisteredSubstitution
import Mettapedia.Languages.HOLLight.RegisteredReplayComposition
import Mettapedia.Logic.HOL.FiniteConstructorEncoding
import Mettapedia.Languages.OpenTheory.ReverseTranslation

/-!
# Checked type instances of the recursive-space source roots

The operation table keeps the original declaration identities and substitutes
its type annotations. Six registered INST_TYPE commands instantiate the exact
cached roots. Successful replay retains its equation and is followed by exact
formula readback at the substituted signature. The caller can compose that
checked suffix with the original source history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution RecursiveSpaceSourceReadback

universe w

/-- The source type of the same predicate-handler encoding used by the typed
constructor programs. Each field retains its actual source type. -/
def constructorPayload (signature : List (List Ty)) : Ty :=
  ReverseTranslation.reverseTy
    (HOL.FiniteConstructorEncoding.payloadType (signature.map (List.map Ty.toHOL)))

theorem constructorPayload_toHOL (signature : List (List Ty)) :
    (constructorPayload signature).toHOL =
      HOL.FiniteConstructorEncoding.payloadType (signature.map (List.map Ty.toHOL)) :=
  ReverseTranslation.toHOL_reverseTy _

/-- Typed occurrence of the retained source constructor at supplied payload
and recursive-space types. Registered formation checks its actual instance. -/
def constructorAt (operations : RecursiveSpaceSourceReadback.Operations)
    (payload : HOL.Ty AtomicTy) (space : Ty) :
    HOL.ClosedTerm Symbol (operations.number.toHOL.arr
      (payload.arr ((operations.number.toHOL.arr space.toHOL).arr space.toHOL))) :=
  .const (.constant operations.construct
    (.function operations.number (.function (ReverseTranslation.reverseTy payload)
      (.function (.function operations.number space) space)))
    (by simp only [Ty.toHOL_function, ReverseTranslation.toHOL_reverseTy]))

def Operations.instantiate (operations : RecursiveSpaceSourceReadback.Operations)
    (substitution : TypeSubst) : RecursiveSpaceSourceReadback.Operations :=
  { operations with
    number := substitution.apply operations.number
    payload := substitution.apply operations.payload
    space := substitution.apply operations.space }

def substitution (entries : List (Name × Ty)) : TypeCorrectTermSubstitution :=
  SourceSubstitution.typeOnlySubstitution (PrimitiveTransport.typeEntries (TypeSubst.ofList entries))

def effectiveTypes (entries : List (Name × Ty)) : TypeSubst :=
  (RegisteredSubstitution.typePart (substitution entries)).raw.types

def commands? (before : Registered.State) (indices : CacheIndices)
    (entries : List (Name × Ty)) : Option (List Registered.Command) := do
  let witnesses := ExportReplay.instanceCertificates before.context.signature
  let sources := [indices.successorSeparation, indices.successorInjective, indices.naturalInduction,
    indices.constructorSeparation, indices.constructorInjective, indices.recursiveInduction]
  sources.zipIdx.mapM fun (index, ordinal) => do
    let input ← before.cache[index]?
    let node := RegisteredSubstitution.firstNode (substitution entries) input index
      ("recursive-space-type-instance", ordinal)
    pure (.proof node witnesses)

def outputIndices (start : Nat) : CacheIndices :=
  ⟨start, start + 1, start + 2, start + 3, start + 4, start + 5⟩

structure Result (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (operations : RecursiveSpaceSourceReadback.Operations)
    (entries : List (Name × Ty)) where
  commands : List Registered.Command
  after : Registered.State
  replayed : Registered.replayFrom policy before commands = some after
  indices : CacheIndices
  readings : Readings (Operations.instantiate operations (effectiveTypes entries)) after

def instantiate? (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (operations : RecursiveSpaceSourceReadback.Operations)
    (indices : CacheIndices) (entries : List (Name × Ty)) : Option (Result policy before operations entries) := do
  let commands ← commands? before indices entries
  match replayed : Registered.replayFrom policy before commands with
  | none => none
  | some after => do
      let targetIndices := outputIndices before.cache.size
      let readings ← read? (Operations.instantiate operations (effectiveTypes entries)) after targetIndices
      pure ⟨commands, after, replayed, targetIndices, readings⟩

theorem Result.full_replay {policy : AxiomPolicy} [DecidablePred policy]
    {before : Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {entries : List (Name × Ty)} (result : Result policy before operations entries)
    (initial : Registered.State) (earlier : List Registered.Command)
    (accepted : Registered.replayFrom policy initial earlier = some before) :
    Registered.replayFrom policy initial (earlier ++ result.commands) = some result.after :=
  Registered.replayFrom_append_accepted policy accepted result.replayed

theorem Result.old_lookup {policy : AxiomPolicy} [DecidablePred policy]
    {before : Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {entries : List (Name × Ty)} (result : Result policy before operations entries)
    {index : Nat} {fact : Theorem} (known : before.cache[index]? = some fact) :
    result.after.cache[index]? = some fact :=
  Registered.replayFrom_preserves_lookup policy before result.commands result.after result.replayed known

noncomputable def Result.correspondence
    {before : Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {entries : List (Name × Ty)} (result : Result SourceProfileModels.policy before operations entries)
    (earlier : List Registered.Command)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) earlier = some before)
    (other : TypeFamilySemantics.OperatorFamilies.{w}) (assignment : TypeFamilySemantics.Assignment.{w})
    (filler : RecursiveSpaceSemantics.Relation
      ((Operations.instantiate operations (effectiveTypes entries)).recursive.Payload
        ((SourceProfileModels.sourceReplayFrame (earlier ++ result.commands) result.after
          (result.full_replay _ earlier accepted)).frame.model other assignment))) :=
  RecursiveSpaceSourceReadback.correspondence
    (Operations.instantiate operations (effectiveTypes entries))
    (earlier ++ result.commands) result.after (result.full_replay _ earlier accepted)
    result.readings other assignment filler

#print axioms Result.full_replay
#print axioms Result.old_lookup
#print axioms Result.correspondence
#print axioms constructorPayload_toHOL

end Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation
