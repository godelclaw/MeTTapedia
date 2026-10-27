import Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions
import Mettapedia.Languages.HOLLight.SourceProfileModels

/-!
# Source-admission controls for constructor-index definitions

The child-index projection is closed and declares in the primitive core. A
result-index function with an unbound successor input is refused there.
The complete source-history qualification supplies the actual declared SUC.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
open ProofExecution DefinitionAdapters
local infixr:60 " ⇒ " => HOL.Ty.arr
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def number : HOL.Ty AtomicTy :=
  .base ⟨Ty.var (Name.global "ConstructorIndexNumber"), rfl, rfl⟩
def element : HOL.Ty AtomicTy :=
  .base ⟨Ty.var (Name.global "ConstructorIndexElement"), rfl, rfl⟩

def input (name : String) (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol type :=
  .const (.variable ⟨Name.global name, Ty.fromHOL type⟩ (by simp))

def arithmetic : Arithmetic Symbol :=
  ⟨number, element, input "indexZero" number,
    input "indexSuccessor" (number ⇒ number),
    input "indexAddition" (number ⇒ number ⇒ number)⟩

theorem result_source_agreement :
    vectorResultSource number element arithmetic.successor = source (arithmetic.resultProgram Bool) :=
  vectorResultSource_generated arithmetic Bool

theorem child_source_agreement :
    vectorChildSource number element = source (arithmetic.childProgram Bool) :=
  vectorChildSource_generated arithmetic Bool

def before : Registered.State := Registered.empty ContextControls.coreContext
def childDefinition : Option Registered.State :=
  define? emptyAxiomPolicy before ("child-index-definition", 0)
    (Name.global "childIndexProjection") (vectorChildSource number element)

theorem child_admitted : childDefinition.isSome = true := by decide +kernel

def freeSuccessorDefinition : Option Registered.State :=
  define? emptyAxiomPolicy before ("unbound-index-definition", 0)
    (Name.global "unboundResultIndex") (vectorResultSource number element arithmetic.successor)

theorem unbound_successor_refused : freeSuccessorDefinition.isNone = true := by decide +kernel

namespace GuardInstallation

/-- A finite positive operator used to exercise three actual fresh
definitions. It creates the true point and refuses the false point; it is
not a recursive-space carrier representation. -/
def signature : HOL.RecursiveSpacePredicate.Signature Symbol where
  number := .prop
  payload := .prop
  space := .prop
  bottom := .bot
  construct := .lam (.lam (.lam (.var (.vs (.vs .vz)))))
  validShape := .lam (.lam (.and (.var (.vs .vz)) (.var .vz)))
  active := .lam (.lam .bot)
  validEdge := .lam (.lam (.lam .bot))

def declarations : List (Name × SourceTerm) :=
  [(Name.global "installedShape", source signature.validShape),
   (Name.global "installedActive", source signature.active),
   (Name.global "installedEdge", source signature.validEdge)]

def commands : List Registered.Command :=
  declarations.map fun (name, body) => command before ("installed-guard-control", 0) name body

theorem replay_available : (Registered.replayFrom emptyAxiomPolicy before commands).isSome = true := by decide +kernel

def after : Registered.State := (Registered.replayFrom emptyAxiomPolicy before commands).get replay_available

theorem replayed : Registered.replayFrom emptyAxiomPolicy before commands = some after :=
  (Option.some_get replay_available).symm

def constantAt? (index : Nat) : Option Const := do
  let fact ← after.cache[index]?
  let (left, _) ← fact.sequent.concl.destEquality?
  match left.term with
  | .const constant _ => some constant
  | _ => none

theorem constants_available (index : Fin 3) : (constantAt? index.val).isSome = true := by
  fin_cases index <;> decide +kernel

def shape : HOL.ClosedTerm Symbol (.prop ⇒ .prop ⇒ .prop) :=
  .const (.constant ((constantAt? 0).get (constants_available ⟨0, by decide⟩))
    (ReverseTranslation.reverseTy (.prop ⇒ .prop ⇒ .prop)) (ReverseTranslation.toHOL_reverseTy _))
def active : HOL.ClosedTerm Symbol (.prop ⇒ .prop ⇒ .prop) :=
  .const (.constant ((constantAt? 1).get (constants_available ⟨1, by decide⟩))
    (ReverseTranslation.reverseTy (.prop ⇒ .prop ⇒ .prop)) (ReverseTranslation.toHOL_reverseTy _))
def edge : HOL.ClosedTerm Symbol (.prop ⇒ .prop ⇒ .prop ⇒ .prop) :=
  .const (.constant ((constantAt? 2).get (constants_available ⟨2, by decide⟩))
    (ReverseTranslation.reverseTy (.prop ⇒ .prop ⇒ .prop ⇒ .prop)) (ReverseTranslation.toHOL_reverseTy _))

def indices : GuardIndices := ⟨0, 1, 2⟩

theorem readings_available : (readGuards? after indices signature shape active edge).isSome = true := by decide +kernel

def readings : GuardReadings after signature shape active edge :=
  (readGuards? after indices signature shape active edge).get readings_available

noncomputable def frame := RegisteredReplayModels.replayFrame ContextControls.coreContext
  MixedDefinitionModelFamily.Controls.primitives commands after replayed

noncomputable def model := frame.model TypeFamilySemantics.Controls.initialOther
  (fun _ => TypeFamilySemantics.Controls.natural.{0})

theorem full : model.FullDomains := frame.model_fullDomains _ _

theorem installed_operator_agrees :
    HOL.RecursiveSpacePredicate.Signature.denotes model (signature.withGuards shape active edge).operator =
      HOL.RecursiveSpacePredicate.Signature.denotes model signature.operator :=
  readings.operator_denote frame _ _

theorem installed_least_agrees :
    HOL.RecursiveSpacePredicate.Signature.denotes model
      (HOL.PredicateFixedPoint.least (signature.withGuards shape active edge).operator) =
    HOL.RecursiveSpacePredicate.Signature.denotes model (HOL.PredicateFixedPoint.least signature.operator) :=
  readings.least_denote frame _ _

theorem installed_shape_changes_syntax : shape ≠ signature.validShape := by
  intro same
  cases same

theorem operator_creates_true :
    (HOL.RecursiveSpacePredicate.Signature.denotes model signature.operator
      (fun _ => ULift.up False) (ULift.up True)).down := by
  apply (signature.operator_meaning model full _ _).mpr
  refine ⟨ULift.up True, ULift.up True, (fun _ => ULift.up False), ?_, rfl, ?_⟩
  · exact ⟨True.intro, True.intro⟩
  · intro position
    exact ⟨False.elim, fun _ => rfl⟩

theorem operator_refuses_false (predicate : HOL.Ty.denote model.Carrier (.prop ⇒ .prop)) :
    ¬ (HOL.RecursiveSpacePredicate.Signature.denotes model signature.operator predicate (ULift.up False)).down := by
  intro generated
  obtain ⟨tag, payload, children, valid, same, _⟩ := (signature.operator_meaning model full _ _).mp generated
  change tag.down ∧ payload.down at valid
  change ULift.up False = tag at same
  rw [← same] at valid
  exact valid.1

theorem swapped_guard_refused : (readGuards? after ⟨1, 0, 2⟩ signature shape active edge).isNone = true := by decide +kernel

theorem changed_body_refused :
    (readGuards? after indices {signature with validShape := .lam (.lam .bot)} shape active edge).isNone = true := by decide +kernel

end GuardInstallation

def verdicts : List (String × Bool) :=
  [("constructor child-index projection declares", childDefinition.isSome),
   ("constructor result-index unbound successor refused", freeSuccessorDefinition.isNone),
   ("installed guards read their generated definitions", (readGuards? GuardInstallation.after GuardInstallation.indices
      GuardInstallation.signature GuardInstallation.shape GuardInstallation.active GuardInstallation.edge).isSome),
   ("swapped installed guard refused", (readGuards? GuardInstallation.after ⟨1, 0, 2⟩
      GuardInstallation.signature GuardInstallation.shape GuardInstallation.active GuardInstallation.edge).isNone),
   ("changed generated guard body refused", (readGuards? GuardInstallation.after GuardInstallation.indices
      {GuardInstallation.signature with validShape := .lam (.lam .bot)}
      GuardInstallation.shape GuardInstallation.active GuardInstallation.edge).isNone)]

theorem verdicts_all : ∀ verdict ∈ verdicts, verdict.2 = true := by
  intro verdict present
  simp only [verdicts, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl
  · exact child_admitted
  · exact unbound_successor_refused
  · exact GuardInstallation.readings_available
  · exact GuardInstallation.swapped_guard_refused
  · exact GuardInstallation.changed_body_refused

#print axioms result_source_agreement
#print axioms child_source_agreement
#print axioms child_admitted
#print axioms unbound_successor_refused
#print axioms GuardInstallation.installed_operator_agrees
#print axioms GuardInstallation.installed_least_agrees
#print axioms GuardInstallation.operator_creates_true
#print axioms GuardInstallation.operator_refuses_false

end Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions.Controls
