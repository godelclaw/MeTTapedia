import Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel

/-!
# Source services for the guarded atom-rule calculus

These handlers use the original Atom forms, Pattern packets, primitive source
relations and conditional evidence checker. They preserve submitted source rows,
matching assignments, unknown requests and unavailable primitive results. They
do not depend on a Prime candidate or a target Data representation, and they do
not define upstream HE or PeTTa evaluation. The existing source reader remains
a separately stated text boundary.
-/

set_option autoImplicit false
open Mettapedia.Languages.MeTTa

namespace Mettapedia.Languages.GuardedAtomRule.Services.Primitive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.PeTTa
open ConfigurationEncoding
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)


/-- Original Pattern packets are a source-service boundary, independent of
any target Data representation. -/
structure Request where
  relation : String
  arguments : List Pattern

/-- Execute the existing source primitive with its existing carrier check. -/
def run (request : Request) : Option (List (List Pattern)) :=
  if (AtomServices.inputPatterns request.relation request.arguments).all
      AtomServices.checkSourceCarrier then
    AtomServices.rows? request.relation request.arguments
  else none

/-- Source authority earns the carrier gate; it is not an additional semantic
restriction on the existing admitted primitive inputs. -/
theorem run_rows (relation : String) (arguments : List Pattern) :
    run ⟨relation, arguments⟩ = AtomServices.rows? relation arguments := by
  cases response : AtomServices.rows? relation arguments with
  | none => simp only [run, response]; split <;> rfl
  | some rows =>
      have carrier := AtomServices.source_inputs_carrier ((AtomServices.rows_exact _ _ _).mp response)
      simp only [run, carrier, if_true, response]

@[simp] theorem run_exact (request : Request) (rows : List (List Pattern)) :
    run request = some rows ↔ AtomServices.Source request.relation request.arguments rows := by
  rw [run_rows, AtomServices.rows_exact]

/-- The user-level names distinguish the two actual PeTTa matching operations. -/
def matchHead : AtomMatchMode → String
  | .value => "match-value"
  | .binding => "match-binding"

def matchMode? (head : String) : Option AtomMatchMode :=
  if head = "match-value" then some .value
  else if head = "match-binding" then some .binding
  else none

@[simp] theorem matchMode?_exact (head : String) (mode : AtomMatchMode) :
    matchMode? head = some mode ↔ head = matchHead mode := by
  cases mode <;> by_cases first : head = "match-value" <;>
    by_cases second : head = "match-binding" <;> simp_all [matchMode?, matchHead]

def matchRelation : AtomMatchMode → String
  | .value => "petta-match-value-v1"
  | .binding => "petta-match-binding-v1"

def freshRequest (name : String) (subject : Atom) : Request :=
  ⟨"metta-atom-fresh-v1", [GroundData.encode (.var name),
    GroundData.encode subject]⟩

def matchRequest (mode : AtomMatchMode) (bindings pattern value : Atom) : Request :=
  ⟨matchRelation mode, [GroundData.encode bindings,
    GroundData.encode pattern, GroundData.encode value,
    .fvar "source-matching-output"]⟩

/-- Lower only the actual service forms. Unknown requests and unreadable
substitution rows remain original source atoms. -/
def lower? : Atom → Option Request
  | .expression [.symbol "fresh", .var name, subject] => some (freshRequest name subject)
  | .expression [.symbol head, bindings, pattern, value] => do
      let mode ← matchMode? head
      let _ ← readBindings bindings
      return matchRequest mode bindings pattern value
  | _ => none

/-- Independent source forms retain the actual substitution packet, rather
than replacing it with a caller-supplied success flag. -/
inductive Lowering : Atom → Request → Prop where
  | fresh (name : String) (subject : Atom) :
      Lowering (.expression [.symbol "fresh", .var name, subject]) (freshRequest name subject)
  | matching (mode : AtomMatchMode) (initial : Subst) (pattern value : Atom) :
      Lowering (.expression [.symbol (matchHead mode), bindingsData initial, pattern, value])
        (matchRequest mode (bindingsData initial) pattern value)

theorem lower_complete {atom : Atom} {request : Request} (source : Lowering atom request) :
    lower? atom = some request := by
  cases source with
  | fresh => rfl
  | matching mode initial pattern value =>
      cases mode <;> simp [lower?, matchHead, matchMode?, readBindings_bindingsData]

theorem lower_sound {atom : Atom} {request : Request} (computed : lower? atom = some request) :
    Lowering atom request := by
  unfold lower? at computed
  split at computed
  next _ name subject =>
    cases Option.some.inj computed
    exact .fresh name subject
  next _ head bindings pattern value =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
    obtain ⟨mode, selected, initial, read, final⟩ := computed
    have original := bindingsData_of_readBindings read
    have named := (matchMode?_exact head mode).mp selected
    cases Option.some.inj final
    rw [← original, named]
    exact .matching mode initial pattern value
  next => contradiction

@[simp] theorem lower_exact (atom : Atom) (request : Request) :
    lower? atom = some request ↔ Lowering atom request := ⟨lower_sound, lower_complete⟩

private def readBindingOutput (rows : List (List Pattern)) : Option Subst :=
  match rows with
  | [[_, _, _, output]] => do
      let atom ← GroundData.decode output
      readBindings atom
  | _ => none

def matched (bindings : Subst) : Atom :=
  .expression [.symbol "matched", bindingsData bindings]

def readback (original : Atom) (relation : String) (rows : List (List Pattern)) : Atom :=
  if relation = "metta-atom-fresh-v1" then
    if rows.isEmpty then Effects.boolean false
    else if rows.length = 1 then Effects.boolean true else original
  else if relation = "petta-match-value-v1" ∨ relation = "petta-match-binding-v1" then
    if rows.isEmpty then .symbol "no-match"
    else match readBindingOutput rows with
      | none => original
      | some bindings => matched bindings
  else original

/-- The source runner invokes the original primitive rows operation and
reads its result; readback does not rerun the Atom matcher. -/
def onAtom (atom : Atom) : Atom :=
  match lower? atom with
  | none => atom
  | some request =>
      match run request with
      | none => atom
      | some rows => readback atom request.relation rows

/-- Literal source retention is independent of the implementation's refusal
branch. It says there is no admitted source service form. -/
theorem onAtom_retained (atom : Atom) (unknown : ∀ request, ¬ Lowering atom request) :
    onAtom atom = atom := by
  cases lowered : lower? atom with
  | none => simp only [onAtom, lowered]
  | some request => exact (unknown request (lower_sound lowered)).elim

theorem onAtom_fresh (name : String) (subject : Atom) :
    onAtom (.expression [.symbol "fresh", .var name, subject]) =
      Effects.boolean (AtomFreshness.resolvedDecision (.var name) subject) := by
  rw [onAtom, lower_complete (.fresh name subject)]
  change (match run ⟨"metta-atom-fresh-v1",
      [GroundData.encode (.var name), GroundData.encode subject]⟩ with
    | none => _
    | some rows => readback _ "metta-atom-fresh-v1" rows) = _
  rw [run_rows]
  simp only [AtomServices.rows?, ↓reduceIte,
    AtomFreshness.queryRows, AtomFreshness.query_encoded]
  cases AtomFreshness.resolvedDecision (.var name) subject <;> simp [readback]

theorem onAtom_matching (mode : AtomMatchMode) (initial : Subst) (pattern value : Atom) :
    onAtom (.expression [.symbol (matchHead mode), bindingsData initial, pattern, value]) =
      match AtomMatching.onAtoms mode initial pattern value with
      | none => .symbol "no-match"
      | some final => matched final := by
  rw [onAtom, lower_complete (.matching mode initial pattern value)]
  change (match run ⟨matchRelation mode,
      [GroundData.encode (bindingsData initial), GroundData.encode pattern, GroundData.encode value,
        .fvar "source-matching-output"]⟩ with
    | none => _
    | some rows => readback _ (matchRelation mode) rows) = _
  rw [run_rows]
  have table : AtomServices.rows? (matchRelation mode)
      [GroundData.encode (bindingsData initial), GroundData.encode pattern, GroundData.encode value,
        .fvar "source-matching-output"] =
      some (match AtomMatching.onAtoms mode initial pattern value with
      | none => []
      | some final => [[GroundData.encode (bindingsData initial), GroundData.encode pattern,
          GroundData.encode value, GroundData.encode (bindingsData final)]]) := by
    cases mode <;> simp [AtomServices.rows?, matchRelation]
    all_goals rfl
  rw [table]
  cases result : AtomMatching.onAtoms mode initial pattern value with
  | none => cases mode <;> simp [readback, matchRelation]
  | some final =>
      cases mode <;> simp [readback, matchRelation, readBindingOutput,
        GroundData.decode_encode, readBindings_bindingsData]

inductive Observation : Atom → Atom → Prop where
  | fresh {name : String} {subject : Atom}
      (source : ResolvedAtomFreshness (.var name) subject) :
      Observation (.expression [.symbol "fresh", .var name, subject]) (Effects.boolean true)
  | notFresh {name : String} {subject : Atom}
      (source : ¬ ResolvedAtomFreshness (.var name) subject) :
      Observation (.expression [.symbol "fresh", .var name, subject]) (Effects.boolean false)
  | matched {mode : AtomMatchMode} {initial final : Subst} {pattern value : Atom}
      (source : AtomMatched mode initial pattern value final) :
      Observation (.expression [.symbol (matchHead mode), bindingsData initial, pattern, value])
        (matched final)
  | notMatched {mode : AtomMatchMode} {initial : Subst} {pattern value : Atom}
      (source : ∀ final, ¬ AtomMatched mode initial pattern value final) :
      Observation (.expression [.symbol (matchHead mode), bindingsData initial, pattern, value])
        (.symbol "no-match")
  | retained {atom : Atom} (source : ∀ request, ¬ Lowering atom request) : Observation atom atom

theorem onAtom_complete {atom observation : Atom} (source : Observation atom observation) :
    onAtom atom = observation := by
  cases source with
  | fresh held =>
      rw [onAtom_fresh, (AtomFreshness.resolvedDecision_exact _ _).mpr held]
  | notFresh refused =>
      rw [onAtom_fresh, (AtomFreshness.resolvedDecision_refused_exact _ _).mpr refused]
  | matched source =>
      rw [onAtom_matching, (AtomMatching.onAtoms_matched_exact _ _ _ _ _).mpr source]
  | notMatched source =>
      rw [onAtom_matching, (AtomMatching.onAtoms_refused_exact _ _ _ _).mpr source]
  | retained source => exact onAtom_retained _ source

theorem onAtom_source (atom : Atom) : Observation atom (onAtom atom) := by
  cases lowered : lower? atom with
  | none =>
      have unknown : ∀ request, ¬ Lowering atom request := by
        intro request source
        have found := lower_complete source
        rw [lowered] at found
        contradiction
      rw [onAtom_retained atom unknown]
      exact .retained unknown
  | some request =>
      cases lower_sound lowered with
      | fresh name subject =>
          rw [onAtom_fresh]
          cases truth : AtomFreshness.resolvedDecision (.var name) subject with
          | false => exact .notFresh ((AtomFreshness.resolvedDecision_refused_exact _ _).mp truth)
          | true => exact .fresh ((AtomFreshness.resolvedDecision_exact _ _).mp truth)
      | matching mode initial pattern value =>
          rw [onAtom_matching]
          cases computed : AtomMatching.onAtoms mode initial pattern value with
          | none => exact .notMatched ((AtomMatching.onAtoms_refused_exact _ _ _ _).mp computed)
          | some final => exact .matched ((AtomMatching.onAtoms_matched_exact _ _ _ _ _).mp computed)

@[simp] theorem onAtom_exact (atom observation : Atom) :
    onAtom atom = observation ↔ Observation atom observation := by
  constructor
  · intro same
    rw [← same]
    exact onAtom_source atom
  · exact onAtom_complete

/-- This reader boundary is the existing source reader. Per-command meaning
is the independent observation judgment above, not agreement with a second parser. -/
def onText (source : String) : Except String (List Atom) :=
  (SpaceSemantics.readSource source).map (List.map onAtom)

/-- Source observations compose per occurrence through the existing text
reader; no equation between two implementations supplies their authority. -/
def TextObservation (source : String) (outputs : List Atom) : Prop :=
  ∃ atoms, SpaceSemantics.readSource source = .ok atoms ∧
    List.Forall₂ Observation atoms outputs

private theorem observations_source (atoms : List Atom) :
    List.Forall₂ Observation atoms (atoms.map onAtom) := by
  induction atoms with
  | nil => exact .nil
  | cons atom atoms ih => exact .cons (onAtom_source atom) ih

private theorem observations_complete {atoms outputs : List Atom}
    (source : List.Forall₂ Observation atoms outputs) : atoms.map onAtom = outputs := by
  induction source with
  | nil => rfl
  | cons first _ ih => exact congrArg₂ List.cons (onAtom_complete first) ih

@[simp] theorem onText_exact (source : String) (outputs : List Atom) :
    onText source = .ok outputs ↔ TextObservation source outputs := by
  cases parsed : SpaceSemantics.readSource source with
  | error reason => simp [onText, parsed, TextObservation, Except.map]
  | ok atoms =>
      constructor
      · intro computed
        have same : atoms.map onAtom = outputs := by
          simpa only [onText, parsed, Except.map, Except.ok.injEq] using computed
        exact ⟨atoms, parsed, same ▸ observations_source atoms⟩
      · rintro ⟨other, read, observations⟩
        have same : other = atoms := Except.ok.inj (read.symm.trans parsed)
        subst other
        have result := observations_complete observations
        simp only [onText, parsed, Except.map, result]

end Mettapedia.Languages.GuardedAtomRule.Services.Primitive

namespace Mettapedia.Languages.GuardedAtomRule.Services.Article

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional (Result)
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.Wire

/-- Submitted source rows are an explicit parameter of this checker request.
They are not asserted to equal a mutable world's current declaration store. -/
def environment (rows : List Atom) : Environment :=
  ⟨rows, AtomServices.registration, AtomServices.provider⟩

/-- Independent authority for one submitted source article and endpoint. -/
def RootClaim (rows : List Atom) (article subject target : Atom) : Prop :=
  ∃ evidence, evidenceData evidence = article ∧
    RootFiring (environment rows) evidence subject target

def rootDecision (rows : List Atom) (article subject target : Atom) : Result Bool :=
  match runRoot (environment rows) article subject with
  | .accepted actual => .accepted (decide (actual = target))
  | .refused => .accepted false
  | .unavailable relation => .unavailable relation

@[simp] theorem rootDecision_true_exact (rows : List Atom) (article subject target : Atom) :
    rootDecision rows article subject target = .accepted true ↔
      RootClaim rows article subject target := by
  unfold RootClaim
  rw [← runRoot_exact]
  cases executed : runRoot (environment rows) article subject <;>
    simp [rootDecision, executed]

/-- False rejects this submitted article for this claim. It is not a
refutation of all possible proofs of the source sequent. -/
theorem rootDecision_false (rows : List Atom) (article subject target : Atom)
    (refused : rootDecision rows article subject target = .accepted false) :
    ¬ RootClaim rows article subject target := by
  intro source
  have accepted := (rootDecision_true_exact _ _ _ _).mpr source
  rw [refused] at accepted
  cases accepted

/-- Outer packet syntax is data read by the original Atom reader. A native
unavailable result keeps that literal request rather than asserting failure. -/
def rootRequest (rows : List Atom) (article subject target : Atom) : Atom :=
  .expression [.symbol "proof-root", .expression rows, article, subject, target]

def onAtom : Atom → Atom
  | request@(.expression [.symbol "proof-root", .expression rows, article, subject, target]) =>
      match rootDecision rows article subject target with
      | .accepted answer => Effects.boolean answer
      | .refused => Effects.boolean false
      | .unavailable _ => request
  | original => Primitive.onAtom original

@[simp] theorem onAtom_root_true_exact (rows : List Atom) (article subject target : Atom) :
    onAtom (rootRequest rows article subject target) = Effects.boolean true ↔
      RootClaim rows article subject target := by
  rw [← rootDecision_true_exact]
  cases executed : rootDecision rows article subject target <;>
    simp [onAtom, rootRequest, executed, Effects.boolean]

theorem onAtom_root_false (rows : List Atom) (article subject target : Atom)
    (refused : onAtom (rootRequest rows article subject target) = Effects.boolean false) :
    ¬ RootClaim rows article subject target := by
  intro source
  have accepted := (onAtom_root_true_exact _ _ _ _).mpr source
  rw [refused] at accepted
  cases accepted

/-- Existing primitive requests retain their original source computation.
The explicit proof-checker head is the only newly interpreted source form. -/
theorem onAtom_outside (atom : Atom)
    (outside : ∀ rows article subject target, atom ≠ rootRequest rows article subject target) :
    onAtom atom = Primitive.onAtom atom := by
  unfold onAtom
  split
  next rows article subject target =>
    exact (outside rows article subject target rfl).elim
  next => rfl

/-- Completion status remains available at the native result interface.
The text adapter leaves unavailable requests as their original atoms. -/
theorem onAtom_root_unavailable (rows : List Atom) (article subject target : Atom)
    (relation : String)
    (unavailable : rootDecision rows article subject target = .unavailable relation) :
    onAtom (rootRequest rows article subject target) = rootRequest rows article subject target := by
  simp only [onAtom, rootRequest, unavailable]

def onText (source : String) : Except String (List Atom) :=
  (SpaceSemantics.readSource source).map (List.map onAtom)

end Mettapedia.Languages.GuardedAtomRule.Services.Article
