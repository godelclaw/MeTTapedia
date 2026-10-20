import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusQuery
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Consumers

/-!
# Independently authored finite contextual questions

These fixtures specify index values, rely domains and dependent targets before
running an executor. Each supplied body is checked in its generated slot's
actual dependency context. No completed assignment or receipt determines a
domain or restricts its requested inputs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsParameters

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeBindingEventAction (bound)
open FocusMeaning FiniteFocusChecking

def slotValue? {plan : GeneralExecutionAdmission.Plan} (schema : Rules.Schema plan)
    (slot : NativeEventParameters.Slot schema) (ambient : List String) (body : Pattern) :
    Option (NativeBindingSchemaCaptures.SlotValue schema slot ambient) :=
  if typed : checkHasType plan.snapshot.language plan.snapshot.free
      (slot.dependencies ++ bound ambient) body slot.expected = true then
    if object : isObjectPattern body = true then
      if canonical : body.hasCanonicalBinderMetadata = true then
        some ⟨⟨slot.dependencies, ambient.length, body⟩,
          rfl, rfl, checkHasType_sound typed, object, canonical⟩
      else none
    else none
  else none

def lookupBody (entries : List (String × Pattern)) (name : String) : Option Pattern :=
  (entries.find? (fun entry => entry.1 == name)).map (·.2)

def lookupDomain (entries : List (String × List Pattern)) (name : String) : Option (List Pattern) :=
  (entries.find? (fun entry => entry.1 == name)).map (·.2)

/-- Authored domains are read through generated slots, without any source
program, firing assignment or certificate as an input. -/
def parameters? (installed : Joined.Installed) (index : installed.Index) (ambient : List String)
    (indices : List (String × Pattern)) (domains : List (String × List Pattern))
    (target : RelyValues installed index ambient → ScopedRuleMatching.Assignment → Pattern → Bool) :
    Option (Parameters installed index ambient) := do
  let fixed ← NativeBindingModalAdmission.allFin? fun position : IndexPosition installed index => do
    let slot := installed.indexed.headers[index].indices[position].slot
    let body ← lookupBody indices slot.name
    let value ← slotValue? (installed.indexed.schema index) slot ambient body
    pure (⟨fun other => other = value, value, rfl⟩ : IndexArgument installed index ambient position)
  let relies ← NativeBindingModalAdmission.allFin? fun position : RelyPosition installed index => do
    let slot := installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely[position].slot
    let bodies ← lookupDomain domains slot.name
    NativeSignature.decodeList (slotValue? (installed.indexed.schema index) slot ambient) bodies
  pure ⟨fixed, relies, target⟩

def relyBody? {installed : Joined.Installed} {index : installed.Index} {ambient : List String}
    (values : RelyValues installed index ambient) (name : String) : Option Pattern :=
  (List.finRange _).findSome? fun position =>
    if installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely[position].slot.name == name
    then some (values position).val.body else none

def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]

def constant : Pattern := .apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.bvar 1)])]

def application (argument : Pattern) : Pattern := .apply "App" [identity, argument]

def lambdaDomains : List (String × List Pattern) := [("A", [identity, constant])]

def lambdaTarget {installed : Joined.Installed} {index : installed.Index}
    {ambient : List String} (values : RelyValues installed index ambient)
    (_assignment : ScopedRuleMatching.Assignment) (target : Pattern) : Bool :=
  relyBody? values "A" == some target

def unit : Pattern := .apply "Unit" []

def pairUnit : Pattern := .apply "Pair" [unit, unit]

def caseDomains : List (String × List Pattern) :=
  [("L", [unit, pairUnit]), ("R", [unit, pairUnit])]

def caseFocus : Pattern := .apply "Return" [.bvar 1]

def caseTarget {installed : Joined.Installed} {index : installed.Index}
    {ambient : List String} (values : RelyValues installed index ambient)
    (_assignment : ScopedRuleMatching.Assignment) (target : Pattern) : Bool :=
  (relyBody? values "L").map (fun value => .apply "Return" [value]) == some target

/-- Selecting an observation is independent of executing that observation. -/
def siteMatches (installed : Joined.Installed) (index : installed.Index)
    (ordinal : Nat) (position : List Nat) : Bool :=
  (installed.indexed.schema index).ordinal == ordinal &&
    (installed.indexed.schema index).position == position

def findSite? (installed : Joined.Installed) (ordinal : Nat) (position : List Nat) :
    Option installed.Index :=
  (List.finRange _).find? fun index => siteMatches installed index ordinal position

def prepareAt (installed : Joined.Installed) (ambient : List String)
    (ordinal : Nat) (position : List Nat) (indices : List (String × Pattern))
    (domains : List (String × List Pattern))
    (target : (index : installed.Index) → RelyValues installed index ambient →
      ScopedRuleMatching.Assignment → Pattern → Bool)
    (focus : Pattern) : Except String (FocusQuery.Question installed ambient) := do
  let some index := findSite? installed ordinal position
    | .error "Authored focus site was not generated"
  let some parameters := parameters? installed index ambient indices domains (target index)
    | .error "Independently authored index or rely domain was ill-typed"
  match FocusQuery.prepare installed index parameters focus with
  | .ok question => .ok question
  | .error reason => .error ("Generated native vocabulary refused formation: " ++ reprStr reason)

def lambdaQuestion (installed : Joined.Installed) : Except String (FocusQuery.Question installed []) :=
  prepareAt installed [] 0 [0] [] lambdaDomains (fun _ => lambdaTarget) identity

def caseQuestion (installed : Joined.Installed) : Except String (FocusQuery.Question installed []) :=
  prepareAt installed [] 1 [1, 0, 0] [] caseDomains (fun _ => caseTarget) caseFocus

def binderQuestion (installed : Joined.Installed) : Except String (FocusQuery.Question installed []) :=
  prepareAt installed [] 1 [0, 0] [] []
    (fun _ _ _ target => target == Consumers.underBinderTarget)
    (.apply "App" [identity, .bvar 0])

def rootQuestion (installed : Joined.Installed) : Except String (FocusQuery.Question installed []) :=
  prepareAt installed [] 0 [] [] [] (fun _ _ _ target => target == identity) (application identity)

def sharedQuestion (installed : Joined.Installed) (ordinal : Nat) (label : String := "F0") :
    Except String (FocusQuery.Question installed []) :=
  prepareAt installed [] ordinal [0] [("x", .apply label [])] [("x", [.apply label []])]
    (fun _ _ _ target => target == Consumers.sharedTarget) (.apply label [])

def indexedLanguage : LanguageDef :=
  {Consumers.sharedLanguage with
    name := "IndexedDiscovery"
    terms := Consumers.sharedLanguage.terms ++
      [{label := "F1", category := "Focus", params := [], syntaxPattern := []}]}

def falseTarget {installed : Joined.Installed} {ambient : List String}
    (question : FocusQuery.Question installed ambient) : FocusQuery.Question installed ambient :=
  {question with parameters := {question.parameters with target := fun _ _ _ => false}}

def constantIdentityTarget {installed : Joined.Installed}
    (question : FocusQuery.Question installed []) : FocusQuery.Question installed [] :=
  {question with parameters := {question.parameters with target := fun _ _ target => target == identity}}

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsParameters
