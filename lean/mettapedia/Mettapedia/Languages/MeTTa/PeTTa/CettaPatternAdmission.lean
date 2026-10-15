import Mettapedia.Languages.MeTTa.PeTTa.CettaOperationAdmission
import Mettapedia.GSLT.LanguageDef.NativeControlCase

/-!
# Finite preparation of ordinary CeTTa patterns

This check prepares an oracle or a selected producer; it does not reject an
unknown constructor in the language. Its input consists of exact source
occurrences and separately supplied current native observations. Captured
DATA is retained metadata, never evidence that a head is still passive.
Unobserved foreign or host facts, missing or ambiguous occurrence reads, and
nonordinary patterns refuse preparation.

The sufficient fragment has literal constructor heads, variables and scalar
leaves. Quote, typed roots, logical cons, tagged lists, dynamic or unheaded
expressions, and case defaults are outside it. Equation heads are exempt:
their arguments are the patterns. All case arms and let/let* binders are
inventoried in source order. Equation and case patterns use current reads;
let binders additionally require an observed noncalling captured plan.

The scope is a fresh reference-standard-library context without imports.
The laws prove exact finite coverage, order, retained dependencies, absence
of preparation demands in these observations, and bridges to the existing
source matcher and eager DFS transitions. They do not prove extraction of
native observations, native matching or scalar equality, compiled C
refinement, or stability across an unrecorded host/module change.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaPatternAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.OperationalAdmission (DependencySystem)
open SpaceSemantics (Equation Program Cases)

abbrev Address := CettaOperationAdmission.Address
abbrev Profile := CettaOperationAdmission.Profile
abbrev CapturedRole := CettaOperationAdmission.CapturedRole
abbrev ServiceDependency := CettaOperationAdmission.ServiceDependency

inductive Observed (α : Type) where
  | unobserved
  | observed (value : α)
  deriving DecidableEq, Repr

inductive SpecialRoot where
  | ordinary
  | quote
  | typed
  | logicalCons
  | taggedList
  | dynamic
  deriving DecidableEq, Repr

inductive Context where
  | equationArgument
  | casePattern
  | letBinder
  | letStarBinder
  deriving DecidableEq, Repr

structure Arity where
  known : Bool
  exact : Bool
  larger : Bool := false
  smaller : Bool := false
  deriving DecidableEq, Repr

structure CapturedPlan where
  role : CapturedRole
  containsCall : Bool
  deriving DecidableEq, Repr

structure Scope where
  identity : String
  profile : Profile
  freshNoImports : Observed Bool
  dependencies : List ServiceDependency
  deriving DecidableEq, Repr

structure NativeFact where
  address : Address
  expression : Atom
  head : String
  arity : Nat
  specialRoot : SpecialRoot
  handlerFamily : String
  intrinsic : Bool
  form : Nat
  grounded : Bool
  ordinaryEquations : Bool
  directionalEquations : Bool
  directionalAdmitted : Bool
  hasEquations : Bool
  builtinAllowed : Bool
  builtinEquations : Nat
  nativeArity : Arity
  foreignArity : Observed Arity
  selectedExtensionExact : Bool
  hostMode : Observed Nat
  captured : Observed (Option CapturedPlan)
  dependencies : List ServiceDependency
  deriving DecidableEq, Repr

structure Snapshot where
  scope : Scope
  facts : List NativeFact
  deriving DecidableEq, Repr

def Snapshot.read (snapshot : Snapshot) (address : Address) : List NativeFact :=
  snapshot.facts.filter (fun fact => decide (fact.address = address))

structure PatternRoot where
  address : Address
  expression : Atom
  context : Context
  deriving DecidableEq, Repr

structure Occurrence where
  address : Address
  expression : Atom
  context : Context
  head : String
  arity : Nat
  deriving DecidableEq, Repr

def childAddress (address : Address) (index : Nat) : Address :=
  { address with path := address.path ++ [index] }

def ordinaryHead (head : String) : Bool :=
  !(head ∈ ["quote", ":", "->", "cons"])

/-- This syntax class retains variable names and repeated occurrences.
It does not classify an arbitrary native operation name. -/
inductive Ordinary : Atom → Prop where
  | symbol (name : String) : Ordinary (.symbol name)
  | var (name : String) : Ordinary (.var name)
  | grounded (value : GroundedValue) : Ordinary (.grounded value)
  | constructor (head : String) (arguments : List Atom)
      (headAllowed : ordinaryHead head = true)
      (members : ∀ argument ∈ arguments, Ordinary argument) :
      Ordinary (.expression (.symbol head :: arguments))

inductive Refusal where
  | scopeUnknown
  | scopeUnsupported
  | unsupportedPattern (address : Address)
  | caseDefault (address : Address)
  | missing (address : Address)
  | ambiguous (address : Address)
  | sourceChanged (address : Address)
  | foreignUnknown (address : Address)
  | hostUnknown (address : Address)
  | planUnknown (address : Address)
  | observationInconsistent (address : Address)
  | activePattern (address : Address)
  | unsupportedControl (address : Address)
  deriving DecidableEq, Repr

/-- Preorder inventory of every compound in one ordinary pattern. Child
indices refer to the original source expression, including its head at zero. -/
def patternOccurrences (context : Context) (address : Address) :
    Atom → Except Refusal (List Occurrence)
  | .expression (.symbol head :: arguments) =>
      if ordinaryHead head then
        match children context address 1 arguments with
        | .error refusal => .error refusal
        | .ok nested =>
            .ok (⟨address, .expression (.symbol head :: arguments), context,
              head, arguments.length⟩ :: nested)
      else .error (.unsupportedPattern address)
  | .expression _ => .error (.unsupportedPattern address)
  | _ => .ok []
termination_by pattern => sizeOf pattern
where
  children (context : Context) (address : Address) (index : Nat) :
      List Atom → Except Refusal (List Occurrence)
    | [] => .ok []
    | first :: rest =>
        match patternOccurrences context (childAddress address index) first with
        | .error refusal => .error refusal
        | .ok before =>
            match children context address (index + 1) rest with
            | .error refusal => .error refusal
            | .ok after => .ok (before ++ after)
  termination_by patterns => sizeOf patterns

def rootOccurrences (root : PatternRoot) : Except Refusal (List Occurrence) :=
  if root.context = .casePattern ∧ root.expression = .symbol "Empty" then
    .error (.caseDefault root.address)
  else patternOccurrences root.context root.address root.expression

def rootInventory : List PatternRoot → Except Refusal (List Occurrence)
  | [] => .ok []
  | root :: rest =>
      match rootOccurrences root with
      | .error refusal => .error refusal
      | .ok before =>
          match rootInventory rest with
          | .error refusal => .error refusal
          | .ok after => .ok (before ++ after)

/-- Native known-arity precedence is retained: a known name at another arity
does not by itself demand a call. Foreign absence must still be observed. -/
def selectedExtension (fact : NativeFact) (foreign : Arity) : Bool :=
  if fact.nativeArity.known then fact.nativeArity.exact else foreign.exact

def currentCallable (fact : NativeFact) (foreign : Arity) (host : Nat) : Bool :=
  fact.intrinsic || fact.form != 0 || fact.hasEquations ||
    selectedExtension fact foreign || host != 0

def capturedDemand (context : Context) (captured : Option CapturedPlan) : Bool :=
  match context with
  | .equationArgument | .casePattern => false
  | .letBinder | .letStarBinder =>
      match captured with
      | some plan => plan.containsCall ||
          !(plan.role = .value ∨ plan.role = .data)
      | none => true

/-- All negative facts are current reads. The captured role cannot turn any
positive current callability observation into passive evidence. -/
def PassiveFact (context : Context) (fact : NativeFact) : Prop :=
  fact.specialRoot = .ordinary ∧
  ∃ foreign host,
    fact.foreignArity = .observed foreign ∧ fact.hostMode = .observed host ∧
    fact.selectedExtensionExact = selectedExtension fact foreign ∧
    currentCallable fact foreign host = false ∧
    (match context with
     | .equationArgument | .casePattern => True
     | .letBinder | .letStarBinder =>
         ∃ captured, fact.captured = .observed captured ∧
           capturedDemand context captured = false)

structure Requirement where
  occurrence : Occurrence
  fact : NativeFact
  deriving DecidableEq, Repr

def observeDemand (occurrence : Occurrence) (fact : NativeFact) : Except Refusal Bool :=
  if fact.expression ≠ occurrence.expression ∨ fact.head ≠ occurrence.head ∨
      fact.arity ≠ occurrence.arity then
    .error (.sourceChanged occurrence.address)
  else if fact.specialRoot ≠ .ordinary then
    .error (.unsupportedPattern occurrence.address)
  else match fact.foreignArity with
    | .unobserved => .error (.foreignUnknown occurrence.address)
    | .observed foreign =>
        match fact.hostMode with
        | .unobserved => .error (.hostUnknown occurrence.address)
        | .observed host =>
            if fact.selectedExtensionExact ≠ selectedExtension fact foreign then
              .error (.observationInconsistent occurrence.address)
            else match occurrence.context with
              | .equationArgument | .casePattern =>
                  .ok (currentCallable fact foreign host)
              | .letBinder | .letStarBinder =>
                  match fact.captured with
                  | .unobserved => .error (.planUnknown occurrence.address)
                  | .observed captured => .ok
                      (currentCallable fact foreign host || capturedDemand occurrence.context captured)

def checkRead (occurrence : Occurrence) (facts : List NativeFact) :
    Except Refusal Requirement :=
  match facts with
  | [] => .error (.missing occurrence.address)
  | [fact] =>
      match observeDemand occurrence fact with
      | .error refusal => .error refusal
      | .ok false => .ok ⟨occurrence, fact⟩
      | .ok true => .error (.activePattern occurrence.address)
  | _ => .error (.ambiguous occurrence.address)

def checkOne (snapshot : Snapshot) (occurrence : Occurrence) :
    Except Refusal Requirement := checkRead occurrence (snapshot.read occurrence.address)

def checkManifest (snapshot : Snapshot) : List Occurrence → Except Refusal (List Requirement)
  | [] => .ok []
  | occurrence :: rest =>
      match checkOne snapshot occurrence with
      | .error refusal => .error refusal
      | .ok before =>
          match checkManifest snapshot rest with
          | .error refusal => .error refusal
          | .ok after => .ok (before :: after)

def prepare (snapshot : Snapshot) (roots : List PatternRoot) :
    Except Refusal (List Requirement) :=
  match snapshot.scope.freshNoImports with
  | .unobserved => .error .scopeUnknown
  | .observed false => .error .scopeUnsupported
  | .observed true =>
      match rootInventory roots with
      | .error refusal => .error refusal
      | .ok occurrences => checkManifest snapshot occurrences

/-! ## Exact ordered coverage and current negative observations -/

mutual
  /-- An independent inventory derivation visits every compound once, before
  its children, and keeps its original expression and source position. -/
  inductive PatternInventory : Context → Address → Atom → List Occurrence → Prop where
    | symbol (context address name) : PatternInventory context address (.symbol name) []
    | var (context address name) : PatternInventory context address (.var name) []
    | grounded (context address value) : PatternInventory context address (.grounded value) []
    | constructor {context address head arguments nested}
        (headAllowed : ordinaryHead head = true)
        (children : ChildrenInventory context address 1 arguments nested) :
        PatternInventory context address (.expression (.symbol head :: arguments))
          (⟨address, .expression (.symbol head :: arguments), context,
            head, arguments.length⟩ :: nested)

  inductive ChildrenInventory : Context → Address → Nat → List Atom → List Occurrence → Prop where
    | nil (context address index) : ChildrenInventory context address index [] []
    | cons {context address index first rest before after}
        (firstInventory : PatternInventory context (childAddress address index) first before)
        (restInventory : ChildrenInventory context address (index + 1) rest after) :
        ChildrenInventory context address index (first :: rest) (before ++ after)
end

theorem patternOccurrences_sound (context : Context) (address : Address) (pattern : Atom)
    (occurrences : List Occurrence)
    (accepted : patternOccurrences context address pattern = .ok occurrences) :
    PatternInventory context address pattern occurrences := by
  match pattern with
  | .symbol name =>
      simp only [patternOccurrences, Except.ok.injEq] at accepted
      subst occurrences
      exact .symbol context address name
  | .var name =>
      simp only [patternOccurrences, Except.ok.injEq] at accepted
      subst occurrences
      exact .var context address name
  | .grounded value =>
      simp only [patternOccurrences, Except.ok.injEq] at accepted
      subst occurrences
      exact .grounded context address value
  | .expression (.symbol head :: arguments) =>
      cases allowed : ordinaryHead head with
      | false => simp [patternOccurrences, allowed] at accepted
      | true =>
          cases nested : patternOccurrences.children context address 1 arguments with
          | error refusal => simp [patternOccurrences, allowed, nested] at accepted
          | ok children =>
              simp only [patternOccurrences, allowed, ↓reduceIte, nested, Except.ok.injEq] at accepted
              subst occurrences
              exact .constructor allowed (children_sound context address 1 arguments children nested)
  | .expression [] => simp [patternOccurrences] at accepted
  | .expression (.var _ :: _) => simp [patternOccurrences] at accepted
  | .expression (.grounded _ :: _) => simp [patternOccurrences] at accepted
  | .expression (.expression _ :: _) => simp [patternOccurrences] at accepted
termination_by sizeOf pattern
where
  children_sound (context : Context) (address : Address) (index : Nat)
      (patterns : List Atom) (occurrences : List Occurrence)
      (accepted : patternOccurrences.children context address index patterns = .ok occurrences) :
      ChildrenInventory context address index patterns occurrences := by
    cases patterns with
    | nil =>
        simp only [patternOccurrences.children, Except.ok.injEq] at accepted
        subst occurrences
        exact .nil context address index
    | cons first rest =>
        cases before : patternOccurrences context (childAddress address index) first with
        | error refusal => simp [patternOccurrences.children, before] at accepted
        | ok earlier =>
            cases after : patternOccurrences.children context address (index + 1) rest with
            | error refusal => simp [patternOccurrences.children, before, after] at accepted
            | ok suffix =>
                simp only [patternOccurrences.children, before, after, Except.ok.injEq] at accepted
                subst occurrences
                exact .cons (patternOccurrences_sound context _ first earlier before)
                  (children_sound context address (index + 1) rest suffix after)
  termination_by sizeOf patterns

theorem PatternInventory.ordinary {context : Context} {address : Address} {pattern : Atom}
    {occurrences : List Occurrence} (inventory : PatternInventory context address pattern occurrences) :
    Ordinary pattern := by
  induction inventory using PatternInventory.rec
      (motive_2 := fun _ _ patterns _ _ => ∀ pattern ∈ patterns, Ordinary pattern) with
  | symbol => exact .symbol _
  | var => exact .var _
  | grounded => exact .grounded _
  | constructor allowed children members => exact .constructor _ _ allowed members
  | nil =>
      rename_i pattern member
      cases member
  | cons firstInventory restInventory firstOrdinary restOrdinary =>
      rename_i pattern member
      rcases List.mem_cons.mp member with same | later
      · subst pattern; exact firstOrdinary
      · exact restOrdinary pattern later

theorem PatternInventory.heads {context : Context} {address : Address} {pattern : Atom}
    {occurrences : List Occurrence} (inventory : PatternInventory context address pattern occurrences) :
    occurrences.map Occurrence.head = SpaceSemantics.patternHeads pattern := by
  induction inventory using PatternInventory.rec
      (motive_2 := fun _ _ patterns occurrences _ =>
        occurrences.map Occurrence.head = SpaceSemantics.patternHeads.nested patterns) with
  | symbol | var | grounded => simp [SpaceSemantics.patternHeads]
  | constructor allowed children childrenHeads =>
      simp only [List.map_cons, SpaceSemantics.patternHeads,
        SpaceSemantics.patternHeads.nested, List.singleton_append, List.nil_append,
        childrenHeads]
  | nil => simp [SpaceSemantics.patternHeads.nested]
  | cons firstInventory restInventory firstHeads restHeads =>
      simp only [List.map_append, SpaceSemantics.patternHeads.nested, firstHeads, restHeads]

theorem observeDemand_false_iff (occurrence : Occurrence) (fact : NativeFact) :
    observeDemand occurrence fact = .ok false ↔
      fact.expression = occurrence.expression ∧ fact.head = occurrence.head ∧
      fact.arity = occurrence.arity ∧ PassiveFact occurrence.context fact := by
  by_cases expression : fact.expression = occurrence.expression
  · by_cases head : fact.head = occurrence.head
    · by_cases arity : fact.arity = occurrence.arity
      · by_cases ordinary : fact.specialRoot = .ordinary
        · cases foreign : fact.foreignArity <;>
            cases host : fact.hostMode <;>
            cases context : occurrence.context <;>
            cases captured : fact.captured <;>
            simp [observeDemand, PassiveFact, expression, head, arity,
              ordinary, foreign, host, context, captured]
          all_goals split <;> simp_all [Bool.or_eq_false_iff]
        · simp [observeDemand, PassiveFact, expression, head, arity, ordinary]
      · simp [observeDemand, arity]
    · simp [observeDemand, head]
  · simp [observeDemand, expression]

theorem checkRead_ok_iff (occurrence : Occurrence) (facts : List NativeFact)
    (requirement : Requirement) :
    checkRead occurrence facts = .ok requirement ↔
      ∃ fact, facts = [fact] ∧ fact.expression = occurrence.expression ∧
        fact.head = occurrence.head ∧ fact.arity = occurrence.arity ∧
        PassiveFact occurrence.context fact ∧ requirement = ⟨occurrence, fact⟩ := by
  cases facts with
  | nil => simp [checkRead]
  | cons fact rest =>
      cases rest with
      | cons next rest => simp [checkRead]
      | nil =>
          cases observed : observeDemand occurrence fact with
          | error refusal =>
              have invalid : ¬ (fact.expression = occurrence.expression ∧
                  fact.head = occurrence.head ∧ fact.arity = occurrence.arity ∧
                  PassiveFact occurrence.context fact) := by
                rw [← observeDemand_false_iff, observed]
                simp
              simp [checkRead, observed]
              exact fun source head arity passive _ => invalid ⟨source, head, arity, passive⟩
          | ok demand =>
              cases demand with
              | false =>
                  have passive := (observeDemand_false_iff occurrence fact).mp observed
                  simp [checkRead, observed, passive, eq_comm]
              | true =>
                  have invalid : ¬ (fact.expression = occurrence.expression ∧
                      fact.head = occurrence.head ∧ fact.arity = occurrence.arity ∧
                      PassiveFact occurrence.context fact) := by
                    rw [← observeDemand_false_iff, observed]
                    simp
                  simp [checkRead, observed]
                  exact fun source head arity passive _ => invalid ⟨source, head, arity, passive⟩

theorem checkOne_ok_iff (snapshot : Snapshot) (occurrence : Occurrence)
    (requirement : Requirement) :
    checkOne snapshot occurrence = .ok requirement ↔
      ∃ fact, snapshot.read occurrence.address = [fact] ∧
        fact.expression = occurrence.expression ∧ fact.head = occurrence.head ∧
        fact.arity = occurrence.arity ∧ PassiveFact occurrence.context fact ∧
        requirement = ⟨occurrence, fact⟩ := checkRead_ok_iff occurrence _ requirement

theorem checkManifest_ok_iff (snapshot : Snapshot) (occurrences : List Occurrence)
    (requirements : List Requirement) :
    checkManifest snapshot occurrences = .ok requirements ↔
      List.Forall₂ (fun occurrence requirement => checkOne snapshot occurrence = .ok requirement)
        occurrences requirements := by
  induction occurrences generalizing requirements with
  | nil => cases requirements <;> simp [checkManifest]
  | cons occurrence rest ih =>
      cases checked : checkOne snapshot occurrence with
      | error refusal => cases requirements <;> simp [checkManifest, checked]
      | ok first =>
          cases following : checkManifest snapshot rest with
          | error refusal =>
              cases requirements with
              | nil => simp [checkManifest, checked, following]
              | cons requirement tail =>
                  have invalid : ¬ List.Forall₂ (fun occurrence requirement =>
                      checkOne snapshot occurrence = .ok requirement) rest tail := by
                    intro related
                    have := (ih tail).mpr related
                    simp [following] at this
                  simp [checkManifest, checked, following, invalid]
          | ok tail =>
              cases requirements with
              | nil => simp [checkManifest, checked, following]
              | cons requirement remaining =>
                  simp [checkManifest, checked, following, ← ih remaining]

theorem prepare_ok_iff (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) :
    prepare snapshot roots = .ok requirements ↔
      snapshot.scope.freshNoImports = .observed true ∧
      ∃ occurrences, rootInventory roots = .ok occurrences ∧
        checkManifest snapshot occurrences = .ok requirements := by
  cases fresh : snapshot.scope.freshNoImports with
  | unobserved => simp [prepare, fresh]
  | observed value =>
      cases value with
      | false => simp [prepare, fresh]
      | true =>
          cases inventory : rootInventory roots <;> simp [prepare, fresh, inventory]

theorem checkOne_retained_fact (snapshot : Snapshot) (occurrence : Occurrence)
    (requirement : Requirement) (accepted : checkOne snapshot occurrence = .ok requirement) :
    requirement.occurrence = occurrence ∧ requirement.fact ∈ snapshot.facts ∧
      requirement.fact.address = occurrence.address ∧
      requirement.fact.expression = occurrence.expression ∧
      PassiveFact occurrence.context requirement.fact := by
  obtain ⟨fact, read, source, _, _, passive, rfl⟩ :=
    (checkOne_ok_iff snapshot occurrence requirement).mp accepted
  have member : fact ∈ snapshot.read occurrence.address := by rw [read]; simp
  obtain ⟨inSnapshot, same⟩ := List.mem_filter.mp member
  simp only [decide_eq_true_eq] at same
  exact ⟨rfl, inSnapshot, same, source, passive⟩

theorem checkManifest_occurrences (snapshot : Snapshot) (occurrences : List Occurrence)
    (requirements : List Requirement)
    (accepted : checkManifest snapshot occurrences = .ok requirements) :
    requirements.map Requirement.occurrence = occurrences := by
  have related := (checkManifest_ok_iff snapshot occurrences requirements).mp accepted
  induction related with
  | nil => rfl
  | cons checked related ih =>
      have tail := ih ((checkManifest_ok_iff snapshot _ _).mpr related)
      simp only [List.map_cons, (checkOne_retained_fact snapshot _ _ checked).1, tail]

theorem checkManifest_length (snapshot : Snapshot) (occurrences : List Occurrence)
    (requirements : List Requirement)
    (accepted : checkManifest snapshot occurrences = .ok requirements) :
    requirements.length = occurrences.length := by
  have equal := congrArg List.length (checkManifest_occurrences snapshot occurrences requirements accepted)
  simpa using equal

theorem currentCallable_false (fact : NativeFact) (foreign : Arity) (host : Nat)
    (passive : currentCallable fact foreign host = false) :
    fact.intrinsic = false ∧ fact.form = 0 ∧ fact.hasEquations = false ∧
      selectedExtension fact foreign = false ∧ host = 0 := by
  simpa [currentCallable, Bool.or_eq_false_iff, and_assoc] using passive

theorem captured_data_cannot_hide_current_call (occurrence : Occurrence) (fact : NativeFact)
    (foreign : Arity) (host : Nat)
    (knownForeign : fact.foreignArity = .observed foreign)
    (knownHost : fact.hostMode = .observed host)
    (callable : currentCallable fact foreign host = true) :
    observeDemand occurrence fact ≠ .ok false := by
  intro passive
  obtain ⟨_, _, _, _, actualForeign, actualHost, readForeign, readHost, _, inactive, _⟩ :=
    (observeDemand_false_iff occurrence fact).mp passive
  have sameForeign : actualForeign = foreign := by simpa [knownForeign] using readForeign.symm
  have sameHost : actualHost = host := by simpa [knownHost] using readHost.symm
  subst actualForeign actualHost
  simp [callable] at inactive

/-! ## Source sites supplied by a separate demand analysis -/

/-- The native adapter supplies demanded control sites. A raw position with
the spelling `let` is not thereby an executing control occurrence. -/
abbrev ControlSite := CettaOperationAdmission.Request

def argumentRoots (source : Nat) (index : Nat) : List Atom → List PatternRoot
  | [] => []
  | first :: rest =>
      ⟨⟨source, [1, index]⟩, first, .equationArgument⟩ ::
        argumentRoots source (index + 1) rest

/-- Original document form identities are supplied explicitly. The LHS head
at child path [1,0] is never a pattern request. RHS control sites are separate. -/
def equationRoots (source : Nat) (equation : Equation) : List PatternRoot :=
  argumentRoots source 1 equation.arguments

def indexedPairRoots (context : Context) (address : Address) (index : Nat) :
    Cases → List PatternRoot
  | [] => []
  | (pattern, _) :: rest =>
      ⟨childAddress (childAddress address index) 0, pattern, context⟩ ::
        indexedPairRoots context address (index + 1) rest

/-- Use the actual shared pair reader. A malformed arm/binding does not
silently disappear from the population being checked. -/
def pairRoots (context : Context) (address : Address) (pairs : List Atom) :
    Except Refusal (List PatternRoot) :=
  match Eval.readCases pairs with
  | none => .error (.unsupportedControl address)
  | some rows => .ok (indexedPairRoots context address 0 rows)

def controlRoots (site : ControlSite) : Except Refusal (List PatternRoot) :=
  match site.expression with
  | .expression [.symbol "let", pattern, _, _] =>
      .ok [⟨childAddress site.address 1, pattern, .letBinder⟩]
  | .expression [.symbol "let*", .expression pairs, _] =>
      pairRoots .letStarBinder (childAddress site.address 1) pairs
  | .expression [.symbol "case", _, .expression rows] =>
      pairRoots .casePattern (childAddress site.address 2) rows
  | _ => .error (.unsupportedControl site.address)

def controlsInventory : List ControlSite → Except Refusal (List PatternRoot)
  | [] => .ok []
  | site :: rest =>
      match controlRoots site with
      | .error refusal => .error refusal
      | .ok before =>
          match controlsInventory rest with
          | .error refusal => .error refusal
          | .ok after => .ok (before ++ after)

/-- Non-equation forms retain their document index. This helper inventories
only LHS arguments; executing RHS and query controls need the demand codec. -/
def formEquationRoots (source : Nat) (form : Atom) : Except Refusal (List PatternRoot) :=
  match form with
  | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
      .ok (equationRoots source ⟨head, arguments, body⟩)
  | .expression (.symbol "=" :: _) => .error (.unsupportedControl ⟨source, []⟩)
  | _ => .ok []

def documentEquationRoots (index : Nat) : List Atom → Except Refusal (List PatternRoot)
  | [] => .ok []
  | form :: rest =>
      match formEquationRoots index form with
      | .error refusal => .error refusal
      | .ok before =>
          match documentEquationRoots (index + 1) rest with
          | .error refusal => .error refusal
          | .ok after => .ok (before ++ after)

theorem argumentRoots_patterns (source index : Nat) (patterns : List Atom) :
    (argumentRoots source index patterns).map PatternRoot.expression = patterns := by
  induction patterns generalizing index with
  | nil => rfl
  | cons first rest ih => simp only [argumentRoots, List.map_cons, ih]

theorem equationRoots_patterns (source : Nat) (equation : Equation) :
    (equationRoots source equation).map PatternRoot.expression = equation.arguments :=
  argumentRoots_patterns source 1 equation.arguments

theorem argumentRoots_exempt_head (source index : Nat) (patterns : List Atom)
    (positive : 0 < index) :
    ∀ root ∈ argumentRoots source index patterns, root.address ≠ ⟨source, [1, 0]⟩ := by
  induction patterns generalizing index with
  | nil => simp [argumentRoots]
  | cons first rest ih =>
      intro root member
      rcases List.mem_cons.mp member with same | later
      · subst root
        intro equal
        have zero : index = 0 := by simpa using congrArg (fun address => address.path) equal
        omega
      · exact ih (index + 1) (by omega) root later

theorem equationRoots_exempt_head (source : Nat) (equation : Equation) :
    ∀ root ∈ equationRoots source equation, root.address ≠ ⟨source, [1, 0]⟩ :=
  argumentRoots_exempt_head source 1 equation.arguments (by decide)

theorem indexedPairRoots_patterns (context : Context) (address : Address) (index : Nat)
    (rows : Cases) :
    (indexedPairRoots context address index rows).map PatternRoot.expression = rows.map Prod.fst := by
  induction rows generalizing index with
  | nil => rfl
  | cons row rest ih => cases row; simp only [indexedPairRoots, List.map_cons, ih]

theorem pairRoots_ok_iff (context : Context) (address : Address) (pairs : List Atom)
    (roots : List PatternRoot) :
    pairRoots context address pairs = .ok roots ↔
      ∃ rows, Eval.readCases pairs = some rows ∧ roots = indexedPairRoots context address 0 rows := by
  cases parsed : Eval.readCases pairs <;> simp [pairRoots, parsed, eq_comm]

theorem controlRoots_let (address : Address) (pattern value body : Atom) :
    controlRoots ⟨address, .expression [.symbol "let", pattern, value, body]⟩ =
      .ok [⟨childAddress address 1, pattern, .letBinder⟩] := rfl

theorem controlRoots_case (address : Address) (value : Atom) (rows : List Atom)
    (cases : Cases) (parsed : Eval.readCases rows = some cases) :
    controlRoots ⟨address, .expression [.symbol "case", value, .expression rows]⟩ =
      .ok (indexedPairRoots .casePattern (childAddress address 2) 0 cases) := by
  simp [controlRoots, pairRoots, parsed]

theorem controlRoots_letStar (address : Address) (pairs : List Atom) (body : Atom)
    (bindings : Cases) (parsed : Eval.readCases pairs = some bindings) :
    controlRoots ⟨address, .expression [.symbol "let*", .expression pairs, body]⟩ =
      .ok (indexedPairRoots .letStarBinder (childAddress address 1) 0 bindings) := by
  simp [controlRoots, pairRoots, parsed]

theorem controlRoots_case_patterns (address : Address) (value : Atom) (rows : List Atom)
    (cases : Cases) (roots : List PatternRoot) (parsed : Eval.readCases rows = some cases)
    (accepted : controlRoots ⟨address, .expression [.symbol "case", value, .expression rows]⟩ = .ok roots) :
    roots.map PatternRoot.expression = cases.map Prod.fst := by
  rw [controlRoots_case address value rows cases parsed] at accepted
  cases accepted
  exact indexedPairRoots_patterns ..

theorem controlRoots_letStar_patterns (address : Address) (pairs : List Atom) (body : Atom)
    (bindings : Cases) (roots : List PatternRoot) (parsed : Eval.readCases pairs = some bindings)
    (accepted : controlRoots ⟨address, .expression [.symbol "let*", .expression pairs, body]⟩ = .ok roots) :
    roots.map PatternRoot.expression = bindings.map Prod.fst := by
  rw [controlRoots_letStar address pairs body bindings parsed] at accepted
  cases accepted
  exact indexedPairRoots_patterns ..

theorem controlsInventory_append (first second : List ControlSite) :
    controlsInventory (first ++ second) =
      match controlsInventory first with
      | .error refusal => .error refusal
      | .ok before =>
          match controlsInventory second with
          | .error refusal => .error refusal
          | .ok after => .ok (before ++ after) := by
  induction first with
  | nil =>
      simp only [List.nil_append, controlsInventory]
      cases controlsInventory second <;> rfl
  | cons site rest ih =>
      simp only [List.cons_append, controlsInventory, ih]
      cases controlRoots site <;> cases controlsInventory rest <;>
        cases controlsInventory second <;> simp only [List.append_assoc]


/-! ## Preparation, support and source matching laws -/

theorem rootOccurrences_pattern (root : PatternRoot) (occurrences : List Occurrence)
    (accepted : rootOccurrences root = .ok occurrences) :
    patternOccurrences root.context root.address root.expression = .ok occurrences := by
  unfold rootOccurrences at accepted
  split at accepted
  · contradiction
  · exact accepted

theorem rootInventory_foreach (roots : List PatternRoot) (occurrences : List Occurrence)
    (accepted : rootInventory roots = .ok occurrences) :
    ∀ root ∈ roots, ∃ own, PatternInventory root.context root.address root.expression own := by
  induction roots generalizing occurrences with
  | nil => simp
  | cons root rest ih =>
      cases first : rootOccurrences root with
      | error refusal => simp [rootInventory, first] at accepted
      | ok before =>
          cases later : rootInventory rest with
          | error refusal => simp [rootInventory, first, later] at accepted
          | ok after =>
              intro selected member
              rcases List.mem_cons.mp member with same | tail
              · subst selected
                exact ⟨before, patternOccurrences_sound _ _ _ before
                  (rootOccurrences_pattern root before first)⟩
              · exact ih after later selected tail

theorem rootInventory_heads (roots : List PatternRoot) (occurrences : List Occurrence)
    (accepted : rootInventory roots = .ok occurrences) :
    occurrences.map Occurrence.head = roots.flatMap (fun root => SpaceSemantics.patternHeads root.expression) := by
  induction roots generalizing occurrences with
  | nil => simp [rootInventory] at accepted; subst occurrences; rfl
  | cons root rest ih =>
      cases first : rootOccurrences root with
      | error refusal => simp [rootInventory, first] at accepted
      | ok before =>
          cases later : rootInventory rest with
          | error refusal => simp [rootInventory, first, later] at accepted
          | ok after =>
              simp only [rootInventory, first, later, Except.ok.injEq] at accepted
              subst occurrences
              rw [List.map_append, List.flatMap_cons,
                (patternOccurrences_sound _ _ _ before
                  (rootOccurrences_pattern root before first)).heads, ih after later]

theorem prepare_root_ordinary (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements)
    (root : PatternRoot) (member : root ∈ roots) : Ordinary root.expression := by
  obtain ⟨_, occurrences, inventory, _⟩ := (prepare_ok_iff snapshot roots requirements).mp accepted
  obtain ⟨own, derivation⟩ := rootInventory_foreach roots occurrences inventory root member
  exact derivation.ordinary

theorem prepare_exact_heads (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements) :
    requirements.map (fun requirement => requirement.occurrence.head) =
      roots.flatMap (fun root => SpaceSemantics.patternHeads root.expression) := by
  obtain ⟨_, occurrences, inventory, checked⟩ := (prepare_ok_iff snapshot roots requirements).mp accepted
  have mapped := congrArg (List.map Occurrence.head)
    (checkManifest_occurrences snapshot occurrences requirements checked)
  simpa only [List.map_map, Function.comp_def, rootInventory_heads roots occurrences inventory] using mapped

theorem checkManifest_passive (snapshot : Snapshot) (occurrences : List Occurrence)
    (requirements : List Requirement)
    (accepted : checkManifest snapshot occurrences = .ok requirements) :
    ∀ requirement ∈ requirements, PassiveFact requirement.occurrence.context requirement.fact := by
  have related := (checkManifest_ok_iff snapshot occurrences requirements).mp accepted
  induction related with
  | nil => simp
  | cons checked related ih =>
      intro requirement member
      rcases List.mem_cons.mp member with same | tail
      · subst requirement
        obtain ⟨fact, _, _, _, _, passive, rfl⟩ := (checkOne_ok_iff snapshot _ _).mp checked
        exact passive
      · exact ih ((checkManifest_ok_iff snapshot _ _).mpr related) requirement tail

theorem prepare_current_absence (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements) :
    ∀ requirement ∈ requirements, ∃ foreign host,
      requirement.fact.foreignArity = .observed foreign ∧
      requirement.fact.hostMode = .observed host ∧
      requirement.fact.intrinsic = false ∧ requirement.fact.form = 0 ∧
      requirement.fact.hasEquations = false ∧ selectedExtension requirement.fact foreign = false ∧ host = 0 := by
  obtain ⟨_, occurrences, _, checked⟩ := (prepare_ok_iff snapshot roots requirements).mp accepted
  intro requirement member
  obtain ⟨_, foreign, host, readForeign, readHost, _, inactive, _⟩ :=
    checkManifest_passive snapshot occurrences requirements checked requirement member
  exact ⟨foreign, host, readForeign, readHost, currentCallable_false _ _ _ inactive⟩

/-- A finite obstruction footprint, not a native rewrite plan. Positive
observations retain their occurrence; failed observations stay failures. -/
def observedFootprintRead (occurrence : Occurrence) (facts : List NativeFact) :
    Except Refusal (List Occurrence) :=
  match facts with
  | [] => .error (.missing occurrence.address)
  | [fact] =>
      match observeDemand occurrence fact with
      | .error refusal => .error refusal
      | .ok false => .ok []
      | .ok true => .ok [occurrence]
  | _ => .error (.ambiguous occurrence.address)

def observedCallFootprint (snapshot : Snapshot) : List Occurrence → Except Refusal (List Occurrence)
  | [] => .ok []
  | occurrence :: rest =>
      match observedFootprintRead occurrence (snapshot.read occurrence.address) with
      | .error refusal => .error refusal
      | .ok before =>
          match observedCallFootprint snapshot rest with
          | .error refusal => .error refusal
          | .ok after => .ok (before ++ after)

theorem checkOne_no_preparation_demand (snapshot : Snapshot) (occurrence : Occurrence)
    (requirement : Requirement) (accepted : checkOne snapshot occurrence = .ok requirement) :
    observedFootprintRead occurrence (snapshot.read occurrence.address) = .ok [] := by
  obtain ⟨fact, read, source, head, arity, passive, _⟩ :=
    (checkOne_ok_iff snapshot occurrence requirement).mp accepted
  have inactive := (observeDemand_false_iff occurrence fact).mpr ⟨source, head, arity, passive⟩
  simp only [observedFootprintRead, read, inactive]

theorem checkManifest_no_preparation_demand (snapshot : Snapshot) (occurrences : List Occurrence)
    (requirements : List Requirement)
    (accepted : checkManifest snapshot occurrences = .ok requirements) :
    observedCallFootprint snapshot occurrences = .ok [] := by
  have related := (checkManifest_ok_iff snapshot occurrences requirements).mp accepted
  induction related with
  | nil => rfl
  | cons checked related ih =>
      have rest := ih ((checkManifest_ok_iff snapshot _ _).mpr related)
      simp only [observedCallFootprint, checkOne_no_preparation_demand snapshot _ _ checked,
        rest, List.nil_append]

theorem prepare_no_preparation_demand (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements) :
    ∃ occurrences, rootInventory roots = .ok occurrences ∧
      requirements.map Requirement.occurrence = occurrences ∧
      observedCallFootprint snapshot occurrences = .ok [] := by
  obtain ⟨_, occurrences, inventory, checked⟩ := (prepare_ok_iff snapshot roots requirements).mp accepted
  exact ⟨occurrences, inventory, checkManifest_occurrences snapshot _ _ checked,
    checkManifest_no_preparation_demand snapshot _ _ checked⟩

/-- A scope dependency exists even when every supplied pattern is scalar. -/
def dependencies (occurrences : List Occurrence) : DependencySystem where
  Revision := Snapshot
  Dependency := Option { address : Address // address ∈ occurrences.map Occurrence.address }
  Value := Scope × List NativeFact
  read := fun snapshot dependency =>
    (snapshot.scope, match dependency with
      | none => []
      | some address => snapshot.read address.1)

theorem checkManifest_congr (first second : Snapshot) (occurrences : List Occurrence)
    (same : ∀ occurrence ∈ occurrences, checkOne first occurrence = checkOne second occurrence) :
    checkManifest first occurrences = checkManifest second occurrences := by
  induction occurrences with
  | nil => rfl
  | cons occurrence rest ih =>
      simp only [checkManifest]
      rw [same occurrence (List.mem_cons_self ..), ih (fun row member =>
        same row (List.mem_cons_of_mem occurrence member))]

theorem checkManifest_transport (occurrences : List Occurrence) (first second : Snapshot)
    (same : (dependencies occurrences).SameDependencies first second) :
    checkManifest first occurrences = checkManifest second occurrences := by
  apply checkManifest_congr
  intro occurrence member
  have read := congrArg Prod.snd <| same <| some
    ⟨occurrence.address, List.mem_map.mpr ⟨occurrence, member, rfl⟩⟩
  simp only [dependencies] at read
  simp only [checkOne, read]

theorem prepare_transport (roots : List PatternRoot) (occurrences : List Occurrence)
    (inventory : rootInventory roots = .ok occurrences) (first second : Snapshot)
    (same : (dependencies occurrences).SameDependencies first second) :
    prepare first roots = prepare second roots := by
  have scope := congrArg Prod.fst (same none)
  simp only [dependencies] at scope
  have manifest := checkManifest_transport occurrences first second same
  simp only [prepare, scope, inventory]
  cases second.scope.freshNoImports with
  | unobserved => rfl
  | observed fresh => cases fresh <;> simp only [manifest]

theorem unrelated_append_current (occurrences : List Occurrence) (snapshot : Snapshot)
    (added : List NativeFact)
    (unrelated : ∀ fact ∈ added, fact.address ∉ occurrences.map Occurrence.address) :
    (dependencies occurrences).SameDependencies snapshot
      { snapshot with facts := snapshot.facts ++ added } := by
  intro dependency
  cases dependency with
  | none => rfl
  | some address =>
      have absent : added.filter (fun fact => decide (fact.address = address.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro fact member
        rw [decide_eq_true_eq]
        intro equal
        exact unrelated fact member (equal ▸ address.2)
      simp only [dependencies, Snapshot.read, List.filter_append, absent, List.append_nil]

def Snapshot.readDependencies (snapshot : Snapshot) (address : Address) : List ServiceDependency :=
  (snapshot.read address).flatMap NativeFact.dependencies

def retainedDependencies (snapshot : Snapshot) (requirements : List Requirement) : List ServiceDependency :=
  snapshot.scope.dependencies ++ requirements.flatMap (fun requirement => requirement.fact.dependencies)

theorem checkManifest_retains_dependencies (snapshot : Snapshot) (occurrences : List Occurrence)
    (requirements : List Requirement)
    (accepted : checkManifest snapshot occurrences = .ok requirements) :
    retainedDependencies snapshot requirements = snapshot.scope.dependencies ++
      occurrences.flatMap (fun occurrence => snapshot.readDependencies occurrence.address) := by
  have related := (checkManifest_ok_iff snapshot occurrences requirements).mp accepted
  suffices requirements.flatMap (fun requirement => requirement.fact.dependencies) =
      occurrences.flatMap (fun occurrence => snapshot.readDependencies occurrence.address) by
    exact congrArg (snapshot.scope.dependencies ++ ·) this
  induction related with
  | nil => rfl
  | cons checked related ih =>
      obtain ⟨fact, read, _, _, _, _, rfl⟩ := (checkOne_ok_iff snapshot _ _).mp checked
      have tail := ih ((checkManifest_ok_iff snapshot _ _).mpr related)
      simp only [List.flatMap_cons, Snapshot.readDependencies, read,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, tail]

theorem ordinaryHead_spec (head : String) :
    ordinaryHead head = true ↔ head ≠ "quote" ∧ head ≠ ":" ∧ head ≠ "->" ∧ head ≠ "cons" := by
  simp [ordinaryHead]

theorem Ordinary.unquoted {pattern : Atom} (ordinary : Ordinary pattern) :
    ∀ literal, pattern ≠ .expression [.symbol "quote", literal] := by
  cases ordinary with
  | symbol | var | grounded => simp
  | constructor head arguments allowed members =>
      intro literal same
      have identical : head = "quote" := by simpa using (List.cons.inj (Atom.expression.inj same)).1
      exact (ordinaryHead_spec head).mp allowed |>.1 identical

theorem Ordinary.match_value {pattern : Atom} (ordinary : Ordinary pattern)
    (bindings : Subst) (value : Atom) :
    SpaceSemantics.matchValue bindings pattern value = MORK.matchAtom bindings pattern value := by
  induction ordinary generalizing bindings value with
  | symbol | var | grounded => simp [SpaceSemantics.matchValue]
  | constructor head arguments allowed members ih =>
      have noCons : ∀ first rest, .symbol head :: arguments ≠ [.symbol "cons", first, rest] := by
        intro first rest same
        have identical : head = "cons" := by simpa using (List.cons.inj same).1
        exact (ordinaryHead_spec head).mp allowed |>.2.2.2 identical
      have lists (patterns values : List Atom)
          (pointwise : ∀ pattern ∈ patterns, ∀ bindings value,
            SpaceSemantics.matchValue bindings pattern value = MORK.matchAtom bindings pattern value) :
          SpaceSemantics.matchValue.matchValues bindings patterns values =
            MORK.matchAtom.matchAtomList bindings patterns values := by
        induction patterns generalizing bindings values with
        | nil => cases values <;> simp [SpaceSemantics.matchValue.matchValues, MORK.matchAtom.matchAtomList]
        | cons first rest tail =>
            cases values with
            | nil => simp [SpaceSemantics.matchValue.matchValues, MORK.matchAtom.matchAtomList]
            | cons value values =>
                simp only [SpaceSemantics.matchValue.matchValues, MORK.matchAtom.matchAtomList,
                  pointwise first List.mem_cons_self bindings value]
                cases matched : MORK.matchAtom bindings first value with
                | none => rfl
                | some after =>
                    exact tail after values (fun pattern member => pointwise pattern (List.mem_cons_of_mem first member))
      cases value with
      | expression values =>
          rw [SpaceSemantics.matchValue_expression_of_not_cons bindings _ values noCons]
          change SpaceSemantics.matchValue.matchValues bindings (.symbol head :: arguments) values =
            MORK.matchAtom.matchAtomList bindings (.symbol head :: arguments) values
          apply lists
          intro pattern member
          rcases List.mem_cons.mp member with same | later
          · subst pattern; intro bindings value; simp [SpaceSemantics.matchValue]
          · exact ih pattern later
      | var name | symbol name | grounded ground =>
          unfold SpaceSemantics.matchValue
          split <;> simp_all [MORK.matchAtom]

theorem Ordinary.match_binding {pattern : Atom} (ordinary : Ordinary pattern)
    (bindings : Subst) (value : Atom) :
    SpaceSemantics.matchBinding bindings pattern value = MORK.matchAtom bindings pattern value := by
  rw [SpaceSemantics.matchBinding_ordinary bindings pattern value ordinary.unquoted,
    ordinary.match_value bindings value]

theorem admitted_match_iff (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements)
    (root : PatternRoot) (member : root ∈ roots) (bindings bound : Subst) (value : Atom) :
    SpaceSemantics.matchBinding bindings root.expression value = some bound ↔
      MORK.MatchAtomRel bindings root.expression value bound := by
  rw [(prepare_root_ordinary snapshot roots requirements accepted root member).match_binding]
  exact MORK.matchAtom_iff

theorem admitted_bind_transition (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements)
    (root : PatternRoot) (member : root ∈ roots) (program : Program)
    (world : CettaEagerDFS.World) (bindings bound : Subst) (value body : Atom)
    (rest : List CettaEagerDFS.Frame)
    (matched : MORK.MatchAtomRel bindings root.expression value bound) :
    CettaEagerDFS.LocalTransition program world
      ⟨.returned value, .bind bindings root.expression body :: rest⟩
      world (.next ⟨.evaluate bound body, rest⟩) :=
  .bind_return ((admitted_match_iff snapshot roots requirements accepted root member bindings bound value).mpr matched)

theorem admitted_bind_step (snapshot : Snapshot) (roots : List PatternRoot)
    (requirements : List Requirement) (accepted : prepare snapshot roots = .ok requirements)
    (root : PatternRoot) (member : root ∈ roots) (program : Program)
    (world : CettaEagerDFS.World) (bindings bound : Subst) (value body : Atom)
    (rest : List CettaEagerDFS.Frame)
    (matched : MORK.MatchAtomRel bindings root.expression value bound) :
    CettaEagerDFS.localStep program world
      ⟨.returned value, .bind bindings root.expression body :: rest⟩ =
      some (world, .next ⟨.evaluate bound body, rest⟩) :=
  CettaEagerDFS.local_transition_step
    (admitted_bind_transition snapshot roots requirements accepted root member program world bindings bound value body rest matched)

theorem ordinary_case_selection (cases : Cases)
    (ordinary : ∀ row ∈ cases, Ordinary row.1) (bindings : Subst) (value : Atom) :
    SpaceSemantics.selectCase bindings value cases =
      Mettapedia.GSLT.LanguageDef.NativeControlCase.selectArm
        (fun entry key pattern => MORK.matchAtom entry pattern key) bindings value cases := by
  induction cases with
  | nil => rfl
  | cons row rest ih =>
      cases row with
      | mk pattern body =>
          simp only [SpaceSemantics.selectCase, Mettapedia.GSLT.LanguageDef.NativeControlCase.selectArm,
            (ordinary (pattern, body) (List.mem_cons_self ..)).match_value]
          cases MORK.matchAtom bindings pattern value with
          | some bound => rfl
          | none => exact ih (fun row member => ordinary row (List.mem_cons_of_mem _ member))

theorem patternOccurrences_complete {context : Context} {address : Address} {pattern : Atom}
    {occurrences : List Occurrence} (inventory : PatternInventory context address pattern occurrences) :
    patternOccurrences context address pattern = .ok occurrences := by
  induction inventory using PatternInventory.rec
      (motive_2 := fun address index patterns occurrences _ =>
        patternOccurrences.children context address index patterns = .ok occurrences) with
  | symbol | var | grounded => simp only [patternOccurrences]
  | constructor allowed children completed => simp only [patternOccurrences, allowed, ↓reduceIte, completed]
  | nil => simp only [patternOccurrences.children]
  | cons firstInventory restInventory firstComplete restComplete =>
      simp only [patternOccurrences.children, firstComplete, restComplete]

theorem patternOccurrences_iff (context : Context) (address : Address) (pattern : Atom)
    (occurrences : List Occurrence) :
    patternOccurrences context address pattern = .ok occurrences ↔
      PatternInventory context address pattern occurrences :=
  ⟨patternOccurrences_sound context address pattern occurrences, patternOccurrences_complete⟩

theorem controlsInventory_grouped (sites : List ControlSite) (roots : List PatternRoot)
    (accepted : controlsInventory sites = .ok roots) :
    ∃ grouped : List (List PatternRoot),
      List.Forall₂ (fun site own => controlRoots site = .ok own) sites grouped ∧
        roots = grouped.flatten := by
  induction sites generalizing roots with
  | nil =>
      simp only [controlsInventory, Except.ok.injEq] at accepted
      subst roots
      exact ⟨[], .nil, rfl⟩
  | cons site rest ih =>
      cases first : controlRoots site with
      | error refusal => simp [controlsInventory, first] at accepted
      | ok before =>
          cases later : controlsInventory rest with
          | error refusal => simp [controlsInventory, first, later] at accepted
          | ok after =>
              simp only [controlsInventory, first, later, Except.ok.injEq] at accepted
              obtain ⟨grouped, related, flat⟩ := ih after later
              refine ⟨before :: grouped, .cons first related, ?_⟩
              simp only [List.flatten_cons, ← flat, ← accepted]

theorem controlsInventory_complete (sites : List ControlSite) (grouped : List (List PatternRoot))
    (covered : List.Forall₂ (fun site own => controlRoots site = .ok own) sites grouped) :
    controlsInventory sites = .ok grouped.flatten := by
  induction covered with
  | nil => rfl
  | cons first rest ih => simp only [controlsInventory, first, ih, List.flatten_cons]

theorem admitted_case_step (snapshot : Snapshot) (address : Address) (key : Atom) (rows : List Atom)
    (cases : Cases) (roots : List PatternRoot) (requirements : List Requirement)
    (parsed : Eval.readCases rows = some cases)
    (extracted : controlRoots ⟨address, .expression [.symbol "case", key, .expression rows]⟩ = .ok roots)
    (accepted : prepare snapshot roots = .ok requirements) (program : Program)
    (world : CettaEagerDFS.World) (bindings bound : Subst) (value body : Atom)
    (rest : List CettaEagerDFS.Frame)
    (selected : Mettapedia.GSLT.LanguageDef.NativeControlCase.selectArm
      (fun entry key pattern => MORK.matchAtom entry pattern key) bindings value cases = some (bound, body)) :
    CettaEagerDFS.localStep program world
      ⟨.returned value, .select bindings cases :: rest⟩ =
      some (world, .next ⟨.evaluate bound body, rest⟩) := by
  have covered := controlRoots_case_patterns address key rows cases roots parsed extracted
  have ordinary : ∀ row ∈ cases, Ordinary row.1 := by
    intro row member
    have present : row.1 ∈ roots.map PatternRoot.expression := by
      rw [covered]
      exact List.mem_map.mpr ⟨row, member, rfl⟩
    obtain ⟨root, rootMember, same⟩ := List.mem_map.mp present
    rw [← same]
    exact prepare_root_ordinary snapshot roots requirements accepted root rootMember
  have sourceSelected : SpaceSemantics.selectCase bindings value cases = some (bound, body) := by
    rw [ordinary_case_selection cases ordinary bindings value]
    exact selected
  exact CettaEagerDFS.local_transition_step (.case_return sourceSelected)

/-! ## Small controls for the supplied-observation protocol

These are model controls. Real native observations and their source/service
identities are the responsibility of the independent adapter.
-/

namespace Examples

def pairPattern : Atom := .expression [.symbol "Pair", .var "x", .var "x"]
def pairRoot : PatternRoot := ⟨⟨7, [1]⟩, pairPattern, .letBinder⟩
def pairOccurrence : Occurrence := ⟨pairRoot.address, pairPattern, .letBinder, "Pair", 2⟩

def factFor (occurrence : Occurrence) : NativeFact where
  address := occurrence.address
  expression := occurrence.expression
  head := occurrence.head
  arity := occurrence.arity
  specialRoot := .ordinary
  handlerFamily := "constructor"
  intrinsic := false
  form := 0
  grounded := false
  ordinaryEquations := false
  directionalEquations := false
  directionalAdmitted := false
  hasEquations := false
  builtinAllowed := false
  builtinEquations := 0
  nativeArity := ⟨false, false, false, false⟩
  foreignArity := .observed ⟨false, false, false, false⟩
  selectedExtensionExact := false
  hostMode := .observed 0
  captured := .observed (some ⟨.data, false⟩)
  dependencies := [⟨.callability, "head-and-arity", "negative-current-observation"⟩]

def snapshot (facts : List NativeFact) : Snapshot where
  scope := ⟨"fresh-model-control", .plain, .observed true,
    [⟨.authority, "scope", "fresh-without-imports"⟩]⟩
  facts := facts

def pairFact : NativeFact := factFor pairOccurrence
def pairRequirement : Requirement := ⟨pairOccurrence, pairFact⟩

theorem ordinary_constructor_admitted :
    prepare (snapshot [pairFact]) [pairRoot] = .ok [pairRequirement] := by decide +kernel

theorem duplicate_pattern_requests_retained :
    prepare (snapshot [pairFact]) [pairRoot, pairRoot] = .ok [pairRequirement, pairRequirement] := by decide +kernel

theorem repeated_service_requirements_retained :
    retainedDependencies (snapshot [pairFact]) [pairRequirement, pairRequirement] =
      [⟨.authority, "scope", "fresh-without-imports"⟩,
        ⟨.callability, "head-and-arity", "negative-current-observation"⟩,
        ⟨.callability, "head-and-arity", "negative-current-observation"⟩] := by decide +kernel

def lengthPattern : Atom := .expression [.symbol "length", .expression [.symbol "a", .symbol "b"]]
def lengthOccurrence : Occurrence := ⟨⟨7, [1]⟩, lengthPattern, .letBinder, "length", 1⟩
def lengthFact : NativeFact := { factFor lengthOccurrence with hostMode := .observed 1, grounded := true }

theorem computed_pattern_refused :
    checkOne (snapshot [lengthFact]) lengthOccurrence = .error (.activePattern lengthOccurrence.address) := by decide +kernel

theorem captured_data_cannot_license_computed_pattern :
    lengthFact.captured = .observed (some ⟨.data, false⟩) ∧
      observedFootprintRead lengthOccurrence [lengthFact] = .ok [lengthOccurrence] := by decide +kernel

theorem unknown_foreign_refused :
    checkOne (snapshot [{pairFact with foreignArity := .unobserved}]) pairOccurrence =
      .error (.foreignUnknown pairOccurrence.address) := by decide +kernel

theorem unknown_host_refused :
    checkOne (snapshot [{pairFact with hostMode := .unobserved}]) pairOccurrence =
      .error (.hostUnknown pairOccurrence.address) := by decide +kernel

theorem unknown_let_plan_refused :
    checkOne (snapshot [{pairFact with captured := .unobserved}]) pairOccurrence =
      .error (.planUnknown pairOccurrence.address) := by decide +kernel

theorem missing_occurrence_refused :
    checkOne (snapshot []) pairOccurrence = .error (.missing pairOccurrence.address) := by decide +kernel

theorem ambiguous_occurrence_refused :
    checkOne (snapshot [pairFact, pairFact]) pairOccurrence = .error (.ambiguous pairOccurrence.address) := by decide +kernel

theorem changed_source_refused :
    checkOne (snapshot [{pairFact with expression := .symbol "Pair"}]) pairOccurrence =
      .error (.sourceChanged pairOccurrence.address) := by decide +kernel

theorem unknown_scope_refused :
    prepare { snapshot [pairFact] with scope := {(snapshot []).scope with freshNoImports := .unobserved} }
      [pairRoot] = .error .scopeUnknown := by decide +kernel

theorem imported_scope_refused :
    prepare { snapshot [pairFact] with scope := {(snapshot []).scope with freshNoImports := .observed false} }
      [pairRoot] = .error .scopeUnsupported := by decide +kernel

theorem noncalling_null_equation_plan_admitted :
    let occurrence := {pairOccurrence with context := .equationArgument}
    let fact := {pairFact with captured := .observed none}
    checkOne (snapshot [fact]) occurrence = .ok ⟨occurrence, fact⟩ := by decide +kernel

theorem current_case_observation_ignores_captured_call :
    let occurrence := {pairOccurrence with context := .casePattern}
    let fact := {pairFact with captured := .observed (some ⟨.call, true⟩)}
    checkOne (snapshot [fact]) occurrence = .ok ⟨occurrence, fact⟩ := by decide +kernel

theorem calling_letStar_plan_refused :
    let occurrence := {pairOccurrence with context := .letStarBinder}
    let fact := {pairFact with captured := .observed (some ⟨.data, true⟩)}
    checkOne (snapshot [fact]) occurrence = .error (.activePattern occurrence.address) := by decide +kernel

theorem inconsistent_extension_selection_refused :
    checkOne (snapshot [{pairFact with selectedExtensionExact := true}]) pairOccurrence =
      .error (.observationInconsistent pairOccurrence.address) := by decide +kernel

/-- This isolates the registry-selection law; it does not assert that a real
native head at another arity has no host or intrinsic handler. -/
theorem known_other_arity_uses_native_selection :
    let fact : NativeFact := {pairFact with
      nativeArity := ⟨true, false, true, false⟩
      foreignArity := .observed ⟨true, true, false, false⟩}
    checkOne (snapshot [fact]) pairOccurrence = .ok ⟨pairOccurrence, fact⟩ := by decide +kernel

theorem special_native_root_refused :
    checkOne (snapshot [{pairFact with specialRoot := .taggedList}]) pairOccurrence =
      .error (.unsupportedPattern pairOccurrence.address) := by decide +kernel

theorem quoted_pattern_refused :
    rootOccurrences {pairRoot with expression := .expression [.symbol "quote", pairPattern]} =
      .error (.unsupportedPattern pairRoot.address) := by decide +kernel

theorem logical_cons_pattern_refused :
    rootOccurrences {pairRoot with expression := .expression [.symbol "cons", .var "head", .var "tail"]} =
      .error (.unsupportedPattern pairRoot.address) := by decide +kernel

theorem typed_pattern_refused :
    rootOccurrences {pairRoot with expression := .expression [.symbol ":", .var "value", .symbol "Number"]} =
      .error (.unsupportedPattern pairRoot.address) := by decide +kernel

theorem dynamic_head_refused :
    rootOccurrences {pairRoot with expression := .expression [.var "head", .symbol "value"]} =
      .error (.unsupportedPattern pairRoot.address) := by decide +kernel

theorem case_default_refused :
    rootOccurrences {pairRoot with expression := .symbol "Empty", context := .casePattern} =
      .error (.caseDefault pairRoot.address) := by decide +kernel

theorem scalar_pattern_needs_no_head_fact :
    prepare (snapshot []) [{pairRoot with expression := .var "x"}] = .ok [] := by decide +kernel

theorem repeated_variable_match_preserves_alias :
    SpaceSemantics.matchBinding [] pairPattern (.expression [.symbol "Pair", .symbol "a", .symbol "a"]) =
      some [("x", .symbol "a")] := by decide +kernel

theorem repeated_variable_mismatch_refused :
    SpaceSemantics.matchBinding [] pairPattern (.expression [.symbol "Pair", .symbol "a", .symbol "b"]) = none := by decide +kernel

theorem distinct_variables_allow_distinct_values :
    SpaceSemantics.matchBinding [] (.expression [.symbol "Pair", .var "x", .var "y"])
      (.expression [.symbol "Pair", .symbol "a", .symbol "b"]) =
      some [("y", .symbol "b"), ("x", .symbol "a")] := by decide +kernel

theorem every_case_arm_is_requested :
    controlRoots ⟨⟨7, []⟩, .expression [.symbol "case", .symbol "a",
      .expression [.expression [.symbol "a", .symbol "first"],
        .expression [lengthPattern, .symbol "second"]]]⟩ =
      .ok [⟨⟨7, [2, 0, 0]⟩, .symbol "a", .casePattern⟩,
        ⟨⟨7, [2, 1, 0]⟩, lengthPattern, .casePattern⟩] := by decide +kernel

theorem malformed_case_arm_refused :
    controlRoots ⟨⟨7, []⟩, .expression [.symbol "case", .symbol "a",
      .expression [.expression [.symbol "a", .symbol "first"], .symbol "bad"]]⟩ =
      .error (.unsupportedControl ⟨7, [2]⟩) := by decide +kernel

theorem document_indices_are_not_compressed :
    documentEquationRoots 0 [.expression [.symbol ":", .symbol "f", .symbol "Number"],
      .expression [.symbol "=", .expression [.symbol "f", pairPattern], .var "x"]] =
      .ok [⟨⟨1, [1, 1]⟩, pairPattern, .equationArgument⟩] := by decide +kernel

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.CettaPatternAdmission
