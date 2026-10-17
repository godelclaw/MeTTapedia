import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.GSLT.Core.RouteTrace
import Mettapedia.GSLT.Core.OperationalPathFibration
import Mettapedia.Data.List.FiniteLookup

/-!
# Finite first-order paths and retained rule-driver traces

The existing proof-relevant `Route` and GSLT `ExecutionPath` describe supplied
finite paths. Each source edge is justified by a completed retained MeTTa
entry call. Literal provider values are independently admitted by the existing
first-order compiler, which earns closure of every intermediate subject.

The batch execution evaluates a supplied path's entry calls in order. The
`Selection` source driver instead performs selection and re-entry: each receipt
addresses one physical occurrence of the current complete ordered frontier.
Its observations retain every consumed receipt and frontier, with an unchanged
store and empty I/O. Receipt exhaustion, semantic step-budget exhaustion and
refusal have distinct wire results. Exhausting receipts does not assert a normal
form. The policy supplies the receipts; the driver performs the actual re-entry.
The finite-path correspondence concerns these complete observations, rather than
a morphism from terminal frontier observations to raw machine configurations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution

open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (ProviderRow)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval RuleExecutionProgram
open RootRuleExecution
open RelationPremiseExecution (providerEnv providerTuples VariableSourceProgram)

/-- Independently compile every actual literal payload in the finite provider.
Variables remain literal data; this check requires syntax closure, not groundness. -/
def providerFirstOrder (rows : List ProviderRow) : Bool :=
  rows.all fun row => (compilePatterns? row.values).isSome

theorem providerFirstOrder_eq_true_iff (rows : List ProviderRow) :
    providerFirstOrder rows = true ↔
      ∀ row ∈ rows, isMatchCorrectListAux row.values = true := by
  simp only [providerFirstOrder, List.all_eq_true,
    compilePatterns?_isSome_eq_isMatchCorrectListAux]

/-- Syntax closure of the literal provider is derived from its checked payloads.
Signature, mode, authority and revision admission are separate contracts. -/
theorem providerEnv_firstOrder (rows : List ProviderRow)
    (admitted : providerFirstOrder rows = true) : FirstOrderRelations (providerEnv rows) := by
  intro relation arguments _ values member
  obtain ⟨row, rowMember, selected⟩ := List.mem_filterMap.mp member
  by_cases same : row.relation = relation
  · simp only [same, ↓reduceIte, Option.some.injEq] at selected
    subst values
    exact (providerFirstOrder_eq_true_iff rows).mp admitted row rowMember
  · simp only [same, ↓reduceIte] at selected
    contradiction

section Paths

variable (state : State) (language : LanguageDef) (types terms : Term)
  (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
  (rows : List ProviderRow)

/-- The existing route type, with each edge supplied by an actual completed
source entry and a selected member of that entry's full frontier. -/
abbrev CallPath (source target : PatternPlan) :=
  Route (fun before after : PatternPlan =>
    PLift (Conditional.ObservesRootReduct state language types terms contexts compiled rows
      before after.erase)) source target

/-- Every retained source-call edge erases to the canonical language GSLT step. -/
def erasePath (equationFree : language.isEquationFree = true)
    {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) :
    ExecutionPath (langGSLTUsing (providerEnv rows) language) source.erase target.erase :=
  match route with
  | .refl subject => .refl subject.erase
  | .cons edge rest =>
      .cons ⟨(Conditional.observes_root_iff_gslt_step state language types terms contexts
        compiled rows _ equationFree _).mp edge.down⟩
        (erasePath equationFree rest)

theorem erasePath_length (equationFree : language.isEquationFree = true)
    {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) :
    (erasePath state language types terms contexts compiled rows equationFree route).length = route.length := by
  induction route with
  | refl => rfl
  | cons edge rest ih => simp only [erasePath, Route.length, ih]

/-- Erasure retains every chosen source and target in chronological order. -/
theorem erasePath_trace {Event : Type*} (event : Pattern → Pattern → Event)
    (equationFree : language.isEquationFree = true) {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) :
    Route.trace (fun {before after} _ => event before after)
      (erasePath state language types terms contexts compiled rows equationFree route) =
    Route.trace (fun {before after} _ => event before.erase after.erase) route := by
  induction route with
  | refl => rfl
  | cons edge rest ih => simp only [erasePath, Route.trace, ih]

/-- Compiled provider payloads earn all intermediate compilations. The supplied
GSLT path lifts without postulating that its reducts lie in the compiler image. -/
theorem liftPath (equationFree : language.isEquationFree = true)
    (providerAdmitted : providerFirstOrder rows = true) {first last : Pattern}
    (route : ExecutionPath (langGSLTUsing (providerEnv rows) language) first last)
    (source : PatternPlan) (sourceErases : source.erase = first) :
    ∃ (target : PatternPlan)
      (lifted : CallPath state language types terms contexts compiled rows source target),
      target.erase = last ∧ lifted.length = route.length := by
  induction route generalizing source with
  | refl subject => exact ⟨source, .refl source, sourceErases, rfl⟩
  | @cons first middle last edge rest ih =>
      have member : middle ∈ rewriteStepWithPremisesUsing (providerEnv rows) language first :=
        (mem_rootFrontier_iff_langGSLTUsing_step (providerEnv rows) language equationFree
          compiled.noncontextual_premises first middle).mpr edge.down
      have firstOrder : isMatchCorrectAux middle = true :=
        compiled.rootFrontier_firstOrder (providerEnv rows) language
          (providerEnv_firstOrder rows providerAdmitted) first
          (by simpa only [sourceErases] using isMatchCorrect_erase source) middle member
      have admitted : (compilePattern? middle).isSome = true := by
        simpa only [compilePattern?_isSome_eq_isMatchCorrectAux] using firstOrder
      cases accepted : compilePattern? middle with
      | none => simp [accepted] at admitted
      | some next =>
          have nextErases := erase_of_compilePattern? middle next accepted
          have observed : Conditional.ObservesRootReduct state language types terms contexts
              compiled rows source next.erase :=
            (Conditional.observes_root_iff_gslt_step state language types terms contexts
              compiled rows source equationFree next.erase).mpr
              (by simpa only [sourceErases, nextErases] using edge.down)
          obtain ⟨target, lifted, targetErases, length⟩ := ih next nextErases
          exact ⟨target, .cons ⟨observed⟩ lifted, targetErases,
            by simp only [Route.length, length]⟩

/-- Finite path existence, including the exact step count, is preserved and
reflected. Intermediate syntax admission is earned from the provider data. -/
theorem paths_iff (equationFree : language.isEquationFree = true)
    (providerAdmitted : providerFirstOrder rows = true) (source target : PatternPlan) (count : Nat) :
    (∃ route : CallPath state language types terms contexts compiled rows source target,
      route.length = count) ↔
    (∃ route : ExecutionPath (langGSLTUsing (providerEnv rows) language) source.erase target.erase,
      route.length = count) := by
  constructor
  · rintro ⟨route, countEq⟩
    exact ⟨erasePath state language types terms contexts compiled rows equationFree route,
      (erasePath_length state language types terms contexts compiled rows equationFree route).trans countEq⟩
  · rintro ⟨route, countEq⟩
    obtain ⟨last, lifted, sameErasure, length⟩ :=
      liftPath state language types terms contexts compiled rows equationFree providerAdmitted route source rfl
    have same := PatternPlan.erase_injective sameErasure
    subst last
    exact ⟨lifted, length.trans countEq⟩

end Paths

section Batches

variable (state : State) (language : LanguageDef) (types terms : Term)
  (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
  (rows : List ProviderRow)

/-- One real retained-source entry term for each supplied path edge. -/
def queryTerms {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) : List Term :=
  Route.trace (fun {before _after} _ =>
    Conditional.languageQueryTerm language types terms contexts compiled rows before) route

/-- The complete canonical frontier for each entry, retaining row order and
duplicates separately from the reduct selected by the supplied path. -/
def frontierTerms {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) : List Term :=
  Route.trace (fun {before _after} _ => InferenceCettaWire.encodePatterns
    (rewriteStepWithPremisesUsing (providerEnv rows) language before.erase)) route

theorem queryTerms_length {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) :
    (queryTerms state language types terms contexts compiled rows route).length = route.length :=
  Route.trace_length _ route

theorem frontierTerms_length {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) :
    (frontierTerms state language types terms contexts compiled rows route).length = route.length :=
  Route.trace_length _ route

/-- Actual ordered sequence execution of the supplied entries. The accumulated
answer prefix is retained exactly; the store and I/O do not change. -/
theorem sequence_returns {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target)
    (collected : List Atom) :
    (theory program).MultiStep
      { state, control := .sequence
          ((queryTerms state language types terms contexts compiled rows route).map
            (fun query => .evaluate [] (CettaWireAtom.encode query))) collected }
      (finished state
        (collected ++ (frontierTerms state language types terms contexts compiled rows route).map
          CettaWireAtom.encode) [] []) := by
  induction route generalizing collected with
  | refl subject =>
      simpa only [queryTerms, frontierTerms, Route.trace, List.map_nil, List.append_nil] using
        (show (theory program).MultiStep { state, control := .sequence [] collected }
          (finished state collected [] []) from .step (step_transition rfl) (.refl _))
  | @cons before middle after edge rest ih =>
      have head := Conditional.language_root_returns state language types terms contexts compiled rows before
      have tail := ih (collected ++
        [CettaWireAtom.encode (InferenceCettaWire.encodePatterns
          (rewriteStepWithPremisesUsing (providerEnv rows) language before.erase))])
      simpa only [queryTerms, frontierTerms, Route.trace, List.map_cons,
        List.append_assoc, List.singleton_append] using
        sequence_cons_answers program state state state _ _ collected _ _ head tail

/-- A native superposition of the supplied closed entry calls. -/
def batchQuery {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) : Atom :=
  .expression [.symbol "superpose", .expression
    ((queryTerms state language types terms contexts compiled rows route).map CettaWireAtom.encode)]

theorem batch_returns {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target) :
    Returns program [] state (batchQuery state language types terms contexts compiled rows route) state
      ((frontierTerms state language types terms contexts compiled rows route).map CettaWireAtom.encode) := by
  apply superpose_returns program [] state state _ _
  simpa only [List.map_map, Function.comp_def, List.nil_append] using
    sequence_returns state language types terms contexts compiled rows route []

theorem batch_completed_iff {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (batchQuery state language types terms contexts compiled rows route) } =
        .complete after answers input output) ↔
      after = state ∧
        answers = (frontierTerms state language types terms contexts compiled rows route).map CettaWireAtom.encode ∧
        input = [] ∧ output = [] :=
  path_completed_iff program _ state _ [] []
    (batch_returns state language types terms contexts compiled rows route) after answers input output

theorem batch_derivation_iff {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (batchQuery state language types terms contexts compiled rows route) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = (frontierTerms state language types terms contexts compiled rows route).map CettaWireAtom.encode ∧
        input = [] ∧ output = [] := by
  rw [← completed_run_iff_derivation]
  exact batch_completed_iff state language types terms contexts compiled rows route after answers input output

/-- Dropping duplicates, reordering frontiers or replacing an observation is
refused by the same actual completed-execution characterization. -/
theorem batch_refuses_incorrect {source target : PatternPlan}
    (route : CallPath state language types terms contexts compiled rows source target)
    (incorrect : List Atom)
    (different : incorrect ≠
      (frontierTerms state language types terms contexts compiled rows route).map CettaWireAtom.encode) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (batchQuery state language types terms contexts compiled rows route) }
      (.complete state incorrect [] []) := by
  intro accepted
  exact different ((batch_derivation_iff state language types terms contexts compiled rows route
    state incorrect [] []).mp accepted).2.1

end Batches

namespace Selection

/-- An ordinal identifies one physical occurrence in the complete canonical
frontier. Equal reduct values remain distinct possible receipts. -/
abbrev Edge (language : LanguageDef) (rows : List ProviderRow)
    (before after : PatternPlan) :=
  { index : Nat //
    (rewriteStepWithPremisesUsing (providerEnv rows) language before.erase)[index]? = some after.erase }

/-- Receipt-bearing paths reuse the existing proof-relevant route carrier. -/
abbrev Path (language : LanguageDef) (rows : List ProviderRow) (source target : PatternPlan) :=
  Route (Edge language rows) source target

def receipts {language : LanguageDef} {rows : List ProviderRow} {source target : PatternPlan}
    (path : Path language rows source target) : List Nat := Route.trace (fun edge => edge.val) path

theorem receipts_length {language : LanguageDef} {rows : List ProviderRow} {source target : PatternPlan}
    (path : Path language rows source target) : (receipts path).length = path.length :=
  Route.trace_length _ path

/-- At a fixed source, a frontier ordinal determines its reduct and its edge
evidence. This concerns positions, independently of reduct equality. -/
theorem edge_receipt_injective (language : LanguageDef) (rows : List ProviderRow) (source : PatternPlan) :
    Function.Injective (fun receipt : Σ target, Edge language rows source target => receipt.2.val) := by
  rintro ⟨first, ⟨left, leftSelected⟩⟩ ⟨second, ⟨right, rightSelected⟩⟩ same
  change left = right at same
  subst right
  have targets : first = second :=
    PatternPlan.erase_injective (Option.some.inj (leftSelected.symm.trans rightSelected))
  subst second
  rfl

/-- The consumed ordinal list identifies the whole selected route and its
endpoint, while retaining duplicate frontier occurrences. -/
theorem receipts_injective (language : LanguageDef) (rows : List ProviderRow) (source : PatternPlan) :
    Function.Injective (fun receipt : Σ target, Path language rows source target => receipts receipt.2) :=
  Route.trace_receipt_injective
    (fun {before after} (edge : Edge language rows before after) => edge.val)
    (edge_receipt_injective language rows) source

section

variable (state : State) (language : LanguageDef) (types terms : Term)
  (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites)
  (rows : List ProviderRow)

/-- Each ordinal-bearing edge is justified by the retained source entry's
actual complete frontier, not by a separate transition interpreter. -/
private theorem edge_observed {before after : PatternPlan} (edge : Edge language rows before after) :
    Conditional.ObservesRootReduct state language types terms contexts compiled rows before after.erase := by
  refine ⟨_, ?_, List.mem_of_getElem? edge.property⟩
  exact (Conditional.language_root_derivation_iff state language types terms contexts compiled rows before
    state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

def callPath {source target : PatternPlan} (path : Path language rows source target) :
    CallPath state language types terms contexts compiled rows source target :=
  match path with
  | .refl subject => .refl subject
  | .cons edge rest => .cons ⟨edge_observed state language types terms contexts compiled rows edge⟩
      (callPath rest)

theorem callPath_length {source target : PatternPlan} (path : Path language rows source target) :
    (callPath state language types terms contexts compiled rows path).length = path.length := by
  induction path with
  | refl => rfl
  | cons edge rest ih => simp only [callPath, Route.length, ih]

theorem select_call_path (equationFree : language.isEquationFree = true)
    {source target : PatternPlan}
    (path : CallPath state language types terms contexts compiled rows source target) :
    ∃ selected : Path language rows source target, selected.length = path.length := by
  induction path with
  | refl subject => exact ⟨.refl subject, rfl⟩
  | @cons before middle after edge rest ih =>
      have member := (mem_rootFrontier_iff_langGSLTUsing_step (providerEnv rows) language
        equationFree compiled.noncontextual_premises before.erase middle.erase).mpr
        ((Conditional.observes_root_iff_gslt_step state language types terms contexts compiled rows
          before equationFree middle.erase).mp edge.down)
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨tail, length⟩ := ih
      exact ⟨.cons ⟨index, selected⟩ tail, by simp only [Route.length, length]⟩

include state types terms contexts compiled in
/-- Receipt-bearing paths preserve and reflect all finite canonical GSLT
paths on the admitted profile. Provider compilation earns intermediate closure. -/
theorem paths_iff (equationFree : language.isEquationFree = true)
    (providerAdmitted : providerFirstOrder rows = true) (source target : PatternPlan) (count : Nat) :
    (∃ path : Path language rows source target, path.length = count) ↔
      (∃ path : ExecutionPath (langGSLTUsing (providerEnv rows) language) source.erase target.erase,
        path.length = count) := by
  rw [← RuleTraceExecution.paths_iff state language types terms contexts compiled rows
    equationFree providerAdmitted source target count]
  constructor
  · rintro ⟨path, length⟩
    exact ⟨callPath state language types terms contexts compiled rows path,
      (callPath_length state language types terms contexts compiled rows path).trans length⟩
  · rintro ⟨path, length⟩
    obtain ⟨selected, sameLength⟩ := select_call_path state language types terms contexts compiled rows
      equationFree path
    exact ⟨selected, sameLength.trans length⟩

/-- A global receipt recovers an actual authored row ordinal and an actual
result branch within that row. No rule occurrence or premise witness is merged. -/
theorem authored_occurrence {before after : PatternPlan} (edge : Edge language rows before after) :
    ∃ (row : Fin compiled.plans.length) (branch : Nat),
      branch < (compiled.plans[row].run (providerEnv rows) language before.erase).length ∧
      edge.val = ((compiled.plans.take row.val).flatMap
        (fun plan => plan.run (providerEnv rows) language before.erase)).length + branch ∧
      (compiled.plans[row].run (providerEnv rows) language before.erase)[branch]? = some after.erase := by
  apply List.getElem?_flatMap_decompose
    (fun plan => plan.run (providerEnv rows) language before.erase) compiled.plans edge.val after.erase
  simpa only [compiled.run_eq_rootFrontier (providerEnv rows) language before.erase] using edge.property

/-- The row/branch pair recovered from a global receipt is unique even when
several rows or several witnesses instantiate to the same reduct. -/
theorem authored_occurrence_unique {before after : PatternPlan} (edge : Edge language rows before after)
    (first second : Fin compiled.plans.length) (left right : Nat)
    (leftBounded : left < (compiled.plans[first].run (providerEnv rows) language before.erase).length)
    (rightBounded : right < (compiled.plans[second].run (providerEnv rows) language before.erase).length)
    (leftReceipt : edge.val = ((compiled.plans.take first.val).flatMap
      (fun plan => plan.run (providerEnv rows) language before.erase)).length + left)
    (rightReceipt : edge.val = ((compiled.plans.take second.val).flatMap
      (fun plan => plan.run (providerEnv rows) language before.erase)).length + right) :
    first = second ∧ left = right :=
  List.flatMap_occurrence_ordinals_unique _ _ first second left right leftBounded rightBounded
    (leftReceipt.symm.trans rightReceipt)

/-- Within one authored row, a result ordinal recovers the physical initial
match and the physical premise-result witness. RHS instantiation may identify
their values, but does not remove or reorder their positions. -/
theorem premise_occurrence (plan : RulePlan) (subject : PatternPlan) (ordinal : Nat) (result : Pattern)
    (selected : (plan.run (providerEnv rows) language subject.erase)[ordinal]? = some result) :
    ∃ (initial : Fin (plan.left.run subject.erase).length) (branch : Nat) (final : Bindings),
      branch < (runPremisePlans (providerEnv rows) language plan.premises
        (plan.left.run subject.erase)[initial]).length ∧
      ordinal = (((plan.left.run subject.erase).take initial.val).flatMap
        (fun seed => (runPremisePlans (providerEnv rows) language plan.premises seed).map
          (fun bindings => plan.right.instantiate bindings))).length + branch ∧
      (runPremisePlans (providerEnv rows) language plan.premises
        (plan.left.run subject.erase)[initial])[branch]? = some final ∧
      plan.right.instantiate final = result := by
  obtain ⟨initial, branch, bounded, offset, found⟩ := List.getElem?_flatMap_decompose
    (fun seed => (runPremisePlans (providerEnv rows) language plan.premises seed).map
      (fun bindings => plan.right.instantiate bindings)) (plan.left.run subject.erase) ordinal result selected
  rw [List.getElem?_map] at found
  obtain ⟨final, chosen, instantiated⟩ := Option.map_eq_some_iff.mp found
  exact ⟨initial, branch, final, by simpa only [List.length_map] using bounded, offset, chosen, instantiated⟩

end

def selectionsTerm (selections : List Nat) : Term := encodeList Term.natural selections

def stoppedTerm (subject : PatternPlan) : Term :=
  .application "RuleTraceStopped" [InferenceCettaWire.encodePattern subject.erase]

def fuelTerm (subject : PatternPlan) (unread : List Nat) : Term :=
  .application "RuleTraceFuelExhausted" [InferenceCettaWire.encodePattern subject.erase, selectionsTerm unread]

def refusedTerm (language : LanguageDef) (rows : List ProviderRow)
    (subject : PatternPlan) (unread : List Nat) : Term :=
  .application "RuleTraceRefused" [InferenceCettaWire.encodePattern subject.erase, selectionsTerm unread,
    InferenceCettaWire.encodePatterns (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)]

/-- Serialization of the existing selected route; each event retains the
source, consumed receipt and complete ordered frontier of that source call. -/
def pathTerm {language : LanguageDef} {rows : List ProviderRow} {source target : PatternPlan}
    (path : Path language rows source target) (terminal : Term) : Term :=
  (Route.trace (fun {before _after} edge =>
    (InferenceCettaWire.encodePattern before.erase, edge.val,
      InferenceCettaWire.encodePatterns
        (rewriteStepWithPremisesUsing (providerEnv rows) language before.erase))) path).foldr
    (fun event tail => .application "RuleTraceStep" [event.1, .natural event.2.1, event.2.2, tail]) terminal

/-- Ending conditions distinguish exhausting receipts, exhausting the semantic
step budget and refusing an unavailable frontier occurrence. A stopped receipt
stream need not end at a normal form. The failed receipt remains unread. -/
def Ending (language : LanguageDef) (rows : List ProviderRow) (subject : PatternPlan)
    (remaining : Nat) (unread : List Nat) (terminal : Term) : Prop :=
  (unread = [] ∧ terminal = stoppedTerm subject) ∨
  (unread ≠ [] ∧ remaining = 0 ∧ terminal = fuelTerm subject unread) ∨
  (∃ index rest, unread = index :: rest ∧ remaining ≠ 0 ∧
    (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)[index]? = none ∧
    terminal = refusedTerm language rows subject unread)

/-- Every finite receipt stream has a bounded selected prefix and one of the
three distinct endings. First-order compilation of actual provider values,
together with source-row admission, earns every residual representation. -/
theorem partition (language : LanguageDef) (compiled : RuleProgram language.rewrites)
    (rows : List ProviderRow) (providerAdmitted : providerFirstOrder rows = true)
    (source : PatternPlan) (selections : List Nat) (budget : Nat) :
    ∃ (target : PatternPlan) (path : Path language rows source target) (unread : List Nat) (terminal : Term),
      receipts path ++ unread = selections ∧ path.length ≤ budget ∧
      Ending language rows target (budget - path.length) unread terminal := by
  induction budget generalizing source selections with
  | zero =>
      cases selections with
      | nil =>
          exact ⟨source, .refl source, [], stoppedTerm source, rfl, by simp [Route.length],
            Or.inl ⟨rfl, rfl⟩⟩
      | cons index rest =>
          exact ⟨source, .refl source, index :: rest, fuelTerm source (index :: rest), rfl,
            by simp [Route.length], Or.inr (Or.inl ⟨by simp, rfl, rfl⟩)⟩
  | succ budget ih =>
      cases selections with
      | nil =>
          exact ⟨source, .refl source, [], stoppedTerm source, rfl, by simp [Route.length],
            Or.inl ⟨rfl, rfl⟩⟩
      | cons index rest =>
          cases selected : (rewriteStepWithPremisesUsing (providerEnv rows) language source.erase)[index]? with
          | none =>
              exact ⟨source, .refl source, index :: rest, refusedTerm language rows source (index :: rest),
                rfl, by simp [Route.length], Or.inr (Or.inr
                  ⟨index, rest, rfl, by simp [Route.length], selected, rfl⟩)⟩
          | some nextPattern =>
              have firstOrder := compiled.rootFrontier_firstOrder (providerEnv rows) language
                (providerEnv_firstOrder rows providerAdmitted) source.erase (isMatchCorrect_erase source)
                nextPattern (List.mem_of_getElem? selected)
              have admitted : (compilePattern? nextPattern).isSome = true := by
                simpa only [compilePattern?_isSome_eq_isMatchCorrectAux] using firstOrder
              cases accepted : compilePattern? nextPattern with
              | none => simp [accepted] at admitted
              | some next =>
                  have nextErases := erase_of_compilePattern? nextPattern next accepted
                  obtain ⟨target, tail, unread, terminal, consumed, bounded, ending⟩ := ih next rest
                  let edge : Edge language rows source next := ⟨index, by simpa only [nextErases] using selected⟩
                  refine ⟨target, .cons edge tail, unread, terminal, ?_, ?_, ?_⟩
                  · simpa only [receipts, Route.trace, List.cons_append, edge] using congrArg (index :: ·) consumed
                  · simpa only [Route.length, Nat.add_le_add_iff_right] using bounded
                  · simpa only [Route.length, Nat.succ_sub_succ_eq_sub] using ending

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : Term) : Atom := CettaWireAtom.encode value
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (subject : PatternPlan) : Atom :=
  encoded (InferenceCettaWire.encodePattern subject.erase)
private abbrev patternsValue (values : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns values)
private abbrev selectionsValue (selections : List Nat) : Atom := encoded (selectionsTerm selections)
private abbrev providerValue (rows : List ProviderRow) : Atom :=
  encoded (RelationPremiseExecution.providerRowsTerm rows)

attribute [local simp] a v encoded number patternValue patternsValue selectionsValue providerValue

private def driveEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:drive")[0]'(by decide +kernel)

private def driveEnvironment (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (selections : List Nat) (budget : Nat) : Subst :=
  [("budget", number budget), ("selections", selectionsValue selections), ("subject", patternValue subject),
    ("rows", providerValue rows), ("language", encoded (Conditional.languageTerm language types terms contexts compiled))]

private def consEnvironment (caller : Subst) (index : Nat) (rest : List Nat) : Subst :=
  ("rest", selectionsValue rest) :: ("index", number index) :: caller

private def nextBody : Atom :=
  a "let*" [.expression
    [.expression [v "remaining", a "-" [v "budget", number 1]],
     .expression [v "tail", a "gslt:rule:drive"
       [v "language", v "rows", v "next", v "rest", v "remaining"]]],
    a "RuleTraceStep" [v "subject", v "index", v "frontier", v "tail"]]

private def lookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", a "RuleTraceRefused" [v "subject", v "selections", v "frontier"]),
   (a "Some" [v "next"], nextBody)]

private def lookupBody : Atom :=
  a "case" [a "gslt:rule:row-at" [v "index", v "frontier"],
    .expression (lookupCases.map fun row => .expression [row.1, row.2])]

private def moreBody : Atom :=
  a "let" [v "frontier",
    a "gslt:rule:language-conditional-root-reducts" [v "language", v "rows", v "subject"], lookupBody]

private def consBody : Atom :=
  a "if" [a "==" [v "budget", number 0],
    a "RuleTraceFuelExhausted" [v "subject", v "selections"], moreBody]

private def driveCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "RuleTraceStopped" [v "subject"]),
   (a "LCons" [v "index", v "rest"], consBody)]

private theorem drive_shape : driveEquation.body =
    a "case" [v "selections", .expression (driveCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem drive_clause (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (selections : List Nat) (budget : Nat) :
    clauses program "gslt:rule:drive"
      [encoded (Conditional.languageTerm language types terms contexts compiled), providerValue rows,
       patternValue subject, selectionsValue selections, number budget] =
      [.evaluate (driveEnvironment language types terms contexts compiled rows subject selections budget)
        driveEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:drive").filterMap _ = _
  rw [show equations "gslt:rule:drive" = [driveEquation] from rfl]
  have formals : driveEquation.arguments = [v "language", v "rows", v "subject", v "selections", v "budget"] := by
    decide +kernel
  simp [formals, driveEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem drive_call (caller : Subst) (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (selections : List Nat) (budget : Nat)
    (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (Conditional.languageTerm language types terms contexts compiled), providerValue rows,
       patternValue subject, selectionsValue selections, number budget])
    (returned : PureReturns program
      (driveEnvironment language types terms contexts compiled rows subject selections budget) state
      driveEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:drive" arguments) state answer := by
  apply PureData.raw_authored_call_return program caller
    (driveEnvironment language types terms contexts compiled rows subject selections budget) state state
    "gslt:rule:drive" arguments driveEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · have length : arguments.length = 5 := by
      have sizes := congrArg List.length captured
      simpa using sizes
    intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact drive_clause language types terms contexts compiled rows subject selections budget

private theorem drive_nil_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (budget : Nat) :
    PureReturns program (driveEnvironment language types terms contexts compiled rows subject [] budget) state
      driveEquation.body state (encoded (stoppedTerm subject)) := by
  let caller := driveEnvironment language types terms contexts compiled rows subject [] budget
  rw [drive_shape]
  apply case_returns program caller caller state state state (v "selections") (.symbol "LNil")
    (a "RuleTraceStopped" [v "subject"]) _ _ driveCases (read_cases_encoded _) _ _ _
  · simpa [caller, driveEnvironment, selectionsTerm, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
      variable_returns program caller state "selections"
  · simp [driveCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · simpa [stoppedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, Subst.lookup, caller,
      driveEnvironment] using constructor_variables_return program caller state "RuleTraceStopped" ["subject"]
        (by decide +kernel) (by decide)

private theorem drive_cons_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (index : Nat) (rest : List Nat) (budget : Nat) (answer : Atom)
    (continued : PureReturns program
      (consEnvironment (driveEnvironment language types terms contexts compiled rows subject (index :: rest) budget)
        index rest) state consBody state answer) :
    PureReturns program (driveEnvironment language types terms contexts compiled rows subject (index :: rest) budget)
      state driveEquation.body state answer := by
  let caller := driveEnvironment language types terms contexts compiled rows subject (index :: rest) budget
  let selected := consEnvironment caller index rest
  rw [drive_shape]
  apply case_returns program caller selected state state state (v "selections") (selectionsValue (index :: rest))
    consBody answer _ driveCases (read_cases_encoded _) _ _ continued
  · simpa [caller, driveEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "selections"
  · simp [driveCases, selectionsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, consEnvironment, caller, driveEnvironment]

private theorem drive_fuel_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (index : Nat) (rest : List Nat) :
    PureReturns program (driveEnvironment language types terms contexts compiled rows subject (index :: rest) 0)
      state driveEquation.body state (encoded (fuelTerm subject (index :: rest))) := by
  let caller := driveEnvironment language types terms contexts compiled rows subject (index :: rest) 0
  let selected := consEnvironment caller index rest
  have tested := CettaWireAtom.equality_evaluated_returns program selected state (.natural 0) (.natural 0)
    (v "budget") (number 0) (by decide +kernel) (by decide +kernel)
    (by simpa [selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup] using
      variable_returns program selected state "budget") (grounded_returns program selected state (.int 0))
  apply drive_cons_body_returns state language types terms contexts compiled rows subject index rest 0 _
  unfold consBody
  apply if_returns program selected state state state _ _ _ _ _ tested
  simp only [decide_true]
  rw [show (Effects.boolean true == Effects.boolean true) = true from by decide +kernel]
  simp only [↓reduceIte]
  simpa [fuelTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, consEnvironment, caller,
      driveEnvironment, applySubst, Subst.lookup] using
    constructor_variables_return program selected state "RuleTraceFuelExhausted" ["subject", "selections"]
      (by decide +kernel) (by decide)

private theorem drive_more_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (index : Nat) (rest : List Nat) (budget : Nat) (answer : Atom)
    (continued : PureReturns program
      (("frontier", patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) ::
        consEnvironment (driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1))
          index rest) state lookupBody state answer) :
    PureReturns program
      (driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1))
      state driveEquation.body state answer := by
  let caller := driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1)
  let selected := consEnvironment caller index rest
  let bound := ("frontier", patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) :: selected
  have tested := CettaWireAtom.equality_evaluated_returns program selected state (.natural (budget + 1)) (.natural 0)
    (v "budget") (number 0) (by decide +kernel) (by decide +kernel)
    (by simpa [selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup] using
      variable_returns program selected state "budget") (grounded_returns program selected state (.int 0))
  apply drive_cons_body_returns state language types terms contexts compiled rows subject index rest (budget + 1) _
  unfold consBody
  apply if_returns program selected state state state _ _ _ _ _ tested
  simp only [Term.natural.injEq, Nat.add_one_ne_zero, decide_false]
  rw [show (Effects.boolean false == Effects.boolean true) = false from by decide +kernel]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold moreBody
  apply let_returns program selected bound state state state (v "frontier")
    (a "gslt:rule:language-conditional-root-reducts" [v "language", v "rows", v "subject"])
    lookupBody (patternsValue (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)) answer _ _ continued
  · exact Conditional.language_root_captured_returns selected state language types terms contexts compiled rows subject
      (v "language") (v "rows") (v "subject")
      (by simp [selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup])
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, consEnvironment, caller, driveEnvironment]

private theorem drive_refused_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject : PatternPlan) (index : Nat) (rest : List Nat) (budget : Nat)
    (unavailable : (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)[index]? = none) :
    PureReturns program
      (driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1))
      state driveEquation.body state (encoded (refusedTerm language rows subject (index :: rest))) := by
  let caller := driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1)
  let selected := consEnvironment caller index rest
  let frontier := rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase
  let bound := ("frontier", patternsValue frontier) :: selected
  have lookup : PureReturns program bound state (a "gslt:rule:row-at" [v "index", v "frontier"])
      state (.symbol "None") := by
    have computed := Matched.row_at_captured_returns bound state index
      (frontier.map InferenceCettaWire.encodePattern) (v "index") (v "frontier")
      (by simp [bound, selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup,
        InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map])
    simp only [List.getElem?_map, frontier, unavailable, Option.map_none] at computed
    change PureReturns program bound state (a "gslt:rule:row-at" [v "index", v "frontier"])
      state (encoded (.symbol "None")) at computed
    exact computed
  apply drive_more_body_returns state language types terms contexts compiled rows subject index rest budget _
  unfold lookupBody
  apply case_returns program bound bound state state state _ (.symbol "None")
    (a "RuleTraceRefused" [v "subject", v "selections", v "frontier"]) _ _ lookupCases
    (read_cases_encoded _) lookup _ _
  · simp [lookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · simpa [refusedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, bound, selected, consEnvironment,
      caller, driveEnvironment, applySubst, Subst.lookup, frontier] using
      constructor_variables_return program bound state "RuleTraceRefused" ["subject", "selections", "frontier"]
        (by decide +kernel) (by decide)

private theorem drive_step_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (subject next : PatternPlan) (index : Nat) (rest : List Nat) (budget : Nat) (tail : Term)
    (selectedNext : (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase)[index]? = some next.erase)
    (continued : PureReturns program (driveEnvironment language types terms contexts compiled rows next rest budget)
      state driveEquation.body state (encoded tail)) :
    PureReturns program
      (driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1))
      state driveEquation.body state
      (encoded (.application "RuleTraceStep" [InferenceCettaWire.encodePattern subject.erase, .natural index,
        InferenceCettaWire.encodePatterns (rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase), tail])) := by
  let caller := driveEnvironment language types terms contexts compiled rows subject (index :: rest) (budget + 1)
  let selected := consEnvironment caller index rest
  let frontier := rewriteStepWithPremisesUsing (providerEnv rows) language subject.erase
  let bound := ("frontier", patternsValue frontier) :: selected
  let nextBound := ("next", patternValue next) :: bound
  let remainingBound := ("remaining", number budget) :: nextBound
  let tailBound := ("tail", encoded tail) :: remainingBound
  have lookup : PureReturns program bound state (a "gslt:rule:row-at" [v "index", v "frontier"])
      state (a "Some" [patternValue next]) := by
    have computed := Matched.row_at_captured_returns bound state index
      (frontier.map InferenceCettaWire.encodePattern) (v "index") (v "frontier")
      (by simp [bound, selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup,
        InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map])
    simp only [List.getElem?_map, frontier, selectedNext, Option.map_some] at computed
    change PureReturns program bound state (a "gslt:rule:row-at" [v "index", v "frontier"])
      state (encoded (.application "Some" [InferenceCettaWire.encodePattern next.erase])) at computed
    exact computed
  have remaining : PureReturns program nextBound state (a "-" [v "budget", number 1]) state (number budget) := by
    apply native_binary_call_returns program nextBound state state state state "-"
      (v "budget") (number 1) (number (budget + 1)) (number 1) (number budget)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · simpa [nextBound, bound, selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup] using
        variable_returns program nextBound state "budget"
    · exact grounded_returns program nextBound state (.int 1)
    · change (Except.ok (state, [Atom.grounded (.int (((budget + 1 : Nat) : Int) - 1))]) : Effects.Result) =
        Except.ok (state, [.grounded (.int (budget : Int))])
      simp
  have nextCall := drive_call remainingBound state language types terms contexts compiled rows next rest budget
    [v "language", v "rows", v "next", v "rest", v "remaining"] (encoded tail)
    (by simp [remainingBound, nextBound, bound, selected, consEnvironment, caller, driveEnvironment,
      applySubst, Subst.lookup]) continued
  have bindings : PureData.BindingsReturn program nextBound state
      [(v "remaining", a "-" [v "budget", number 1]),
       (v "tail", a "gslt:rule:drive" [v "language", v "rows", v "next", v "rest", v "remaining"])]
      tailBound state := by
    refine .cons remaining ?_ (.cons nextCall ?_ (.nil _ _))
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, remainingBound, nextBound, bound, selected,
        consEnvironment, caller, driveEnvironment]
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, remainingBound, nextBound, bound,
        selected, consEnvironment, caller, driveEnvironment]
  apply drive_more_body_returns state language types terms contexts compiled rows subject index rest budget _
  unfold lookupBody
  apply case_returns program bound nextBound state state state _ (a "Some" [patternValue next]) nextBody _ _
    lookupCases (read_cases_encoded _) lookup _ _
  · simp [lookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, nextBound, bound, selected,
      consEnvironment, caller, driveEnvironment]
  · unfold nextBody
    apply PureData.let_bindings_return (pairs :=
      [(v "remaining", a "-" [v "budget", number 1]),
       (v "tail", a "gslt:rule:drive" [v "language", v "rows", v "next", v "rest", v "remaining"])])
      bindings state _ _
    simpa [CettaWireAtom.encode, CettaWireAtom.encodeMany, tailBound, remainingBound, nextBound, bound,
      selected, consEnvironment, caller, driveEnvironment, applySubst, Subst.lookup, frontier] using
      constructor_variables_return program tailBound state "RuleTraceStep" ["subject", "index", "frontier", "tail"]
        (by decide +kernel) (by decide)

private theorem drive_path_body_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    {source target : PatternPlan} (path : Path language rows source target)
    (unread : List Nat) (terminal : Term) (budget : Nat) (bounded : path.length ≤ budget)
    (ending : Ending language rows target (budget - path.length) unread terminal) :
    PureReturns program
      (driveEnvironment language types terms contexts compiled rows source (receipts path ++ unread) budget)
      state driveEquation.body state (encoded (pathTerm path terminal)) := by
  induction path generalizing budget with
  | refl subject =>
      simp only [Route.length, Nat.sub_zero] at ending
      rcases ending with ⟨rfl, rfl⟩ | ⟨nonempty, rfl, rfl⟩ | ⟨index, rest, rfl, positive, unavailable, rfl⟩
      · exact drive_nil_body_returns state language types terms contexts compiled rows subject budget
      · cases unread with
        | nil => exact (nonempty rfl).elim
        | cons index rest => exact drive_fuel_body_returns state language types terms contexts compiled rows subject index rest
      · cases budget with
        | zero => exact (positive rfl).elim
        | succ budget => exact drive_refused_body_returns state language types terms contexts compiled rows subject index rest budget unavailable
  | @cons before middle after edge rest ih =>
      cases budget with
      | zero => simp only [Route.length] at bounded; omega
      | succ budget =>
          have tailBounded : rest.length ≤ budget := by simp only [Route.length] at bounded; omega
          have tailEnding : Ending language rows after (budget - rest.length) unread terminal := by
            simpa only [Route.length, Nat.succ_sub_succ_eq_sub] using ending
          have continued := ih budget tailBounded tailEnding
          simpa only [receipts, Route.trace, List.cons_append, pathTerm, List.foldr_cons] using
            drive_step_body_returns state language types terms contexts compiled rows before middle edge.val
              (receipts rest ++ unread) budget (pathTerm rest terminal) edge.property continued

/-- Actual five-argument retained-source execution of the selected path and
its exact ending. Each success performs a fresh authorized frontier call and
re-enters the source driver on the selected residual. The store and I/O stay pure. -/
theorem drive_captured_returns (caller : Subst) (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    {source target : PatternPlan} (path : Path language rows source target)
    (unread : List Nat) (terminal : Term) (budget : Nat) (bounded : path.length ≤ budget)
    (ending : Ending language rows target (budget - path.length) unread terminal)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (Conditional.languageTerm language types terms contexts compiled), providerValue rows,
       patternValue source, selectionsValue (receipts path ++ unread), number budget]) :
    PureReturns program caller state (a "gslt:rule:drive" arguments) state (encoded (pathTerm path terminal)) :=
  drive_call caller state language types terms contexts compiled rows source (receipts path ++ unread) budget
    arguments _ captured
    (drive_path_body_returns state language types terms contexts compiled rows path unread terminal budget bounded ending)

def driveQueryTerm (language : LanguageDef) (types terms : Term) (contexts : RewriteRule → Term)
    (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (source : PatternPlan) (selections : List Nat) (budget : Nat) : Term :=
  .application "gslt:rule:drive"
    [Conditional.languageTerm language types terms contexts compiled, RelationPremiseExecution.providerRowsTerm rows,
     InferenceCettaWire.encodePattern source.erase, selectionsTerm selections, .natural budget]

theorem drive_returns (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    {source target : PatternPlan} (path : Path language rows source target)
    (unread : List Nat) (terminal : Term) (budget : Nat) (bounded : path.length ≤ budget)
    (ending : Ending language rows target (budget - path.length) unread terminal) :
    PureReturns program [] state
      (encoded (driveQueryTerm language types terms contexts compiled rows source (receipts path ++ unread) budget))
      state (encoded (pathTerm path terminal)) := by
  apply drive_captured_returns [] state language types terms contexts compiled rows path unread terminal budget bounded ending
  simp [CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst]

theorem drive_completed_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    {source target : PatternPlan} (path : Path language rows source target)
    (unread : List Nat) (terminal : Term) (budget : Nat) (bounded : path.length ≤ budget)
    (ending : Ending language rows target (budget - path.length) unread terminal)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (encoded
          (driveQueryTerm language types terms contexts compiled rows source (receipts path ++ unread) budget)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (pathTerm path terminal)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (drive_returns state language types terms contexts compiled rows path unread terminal budget bounded ending)
    after answers input output

theorem drive_derivation_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    {source target : PatternPlan} (path : Path language rows source target)
    (unread : List Nat) (terminal : Term) (budget : Nat) (bounded : path.length ≤ budget)
    (ending : Ending language rows target (budget - path.length) unread terminal)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded
          (driveQueryTerm language types terms contexts compiled rows source (receipts path ++ unread) budget)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (pathTerm path terminal)] ∧ input = [] ∧ output = [] := by
  rw [← completed_run_iff_derivation]
  exact drive_completed_iff state language types terms contexts compiled rows path unread terminal budget bounded ending
    after answers input output

/-- Every finite canonical input receipt stream completes with an exact route
record and one distinct ending. The semantic budget bounds the selected steps;
the sufficient PeTTa instruction fuel is derived from actual source execution. -/
theorem drive_total (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (providerAdmitted : providerFirstOrder rows = true)
    (source : PatternPlan) (selections : List Nat) (budget : Nat) :
    ∃ (target : PatternPlan) (path : Path language rows source target) (unread : List Nat) (terminal : Term),
      receipts path ++ unread = selections ∧ path.length ≤ budget ∧
      Ending language rows target (budget - path.length) unread terminal ∧
      PureReturns program [] state
        (encoded (driveQueryTerm language types terms contexts compiled rows source selections budget))
        state (encoded (pathTerm path terminal)) := by
  obtain ⟨target, path, unread, terminal, consumed, bounded, ending⟩ :=
    partition language compiled rows providerAdmitted source selections budget
  refine ⟨target, path, unread, terminal, consumed, bounded, ending, ?_⟩
  simpa only [consumed] using
    drive_returns state language types terms contexts compiled rows path unread terminal budget bounded ending

/-- Complete observations preserve and reflect the bounded selected route,
the exact consumed prefix, all ordered frontiers, the remaining receipts and
the termination reason. No independent execution or trace carrier is assumed. -/
theorem observations_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (providerAdmitted : providerFirstOrder rows = true)
    (source : PatternPlan) (selections : List Nat) (budget : Nat)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (encoded
          (driveQueryTerm language types terms contexts compiled rows source selections budget)) } =
      .complete after answers input output) ↔
      ∃ (target : PatternPlan) (path : Path language rows source target) (unread : List Nat) (terminal : Term),
        receipts path ++ unread = selections ∧ path.length ≤ budget ∧
        Ending language rows target (budget - path.length) unread terminal ∧
        after = state ∧ answers = [encoded (pathTerm path terminal)] ∧ input = [] ∧ output = [] := by
  constructor
  · intro completed
    obtain ⟨target, path, unread, terminal, consumed, bounded, ending⟩ :=
      partition language compiled rows providerAdmitted source selections budget
    refine ⟨target, path, unread, terminal, consumed, bounded, ending, ?_⟩
    apply (drive_completed_iff state language types terms contexts compiled rows path unread terminal budget
      bounded ending after answers input output).mp
    simpa only [consumed] using completed
  · rintro ⟨target, path, unread, terminal, consumed, bounded, ending, observation⟩
    have completed := (drive_completed_iff state language types terms contexts compiled rows path unread terminal budget
      bounded ending after answers input output).mpr observation
    simpa only [consumed] using completed

theorem derivations_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (providerAdmitted : providerFirstOrder rows = true)
    (source : PatternPlan) (selections : List Nat) (budget : Nat)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded
          (driveQueryTerm language types terms contexts compiled rows source selections budget)) }
      (.complete after answers input output) ↔
      ∃ (target : PatternPlan) (path : Path language rows source target) (unread : List Nat) (terminal : Term),
        receipts path ++ unread = selections ∧ path.length ≤ budget ∧
        Ending language rows target (budget - path.length) unread terminal ∧
        after = state ∧ answers = [encoded (pathTerm path terminal)] ∧ input = [] ∧ output = [] := by
  rw [← completed_run_iff_derivation]
  exact observations_iff state language types terms contexts compiled rows providerAdmitted source selections budget
    after answers input output

/-- Every finite GSLT path on the admitted profile has a receipt stream whose
real source driver consumes it and stops at the same target. Conversely every
such recorded driver path is a canonical GSLT path of the same length. -/
theorem stopped_paths_iff (state : State) (language : LanguageDef) (types terms : Term)
    (contexts : RewriteRule → Term) (compiled : VariableSourceProgram language.rewrites) (rows : List ProviderRow)
    (equationFree : language.isEquationFree = true) (providerAdmitted : providerFirstOrder rows = true)
    (source target : PatternPlan) (count : Nat) :
    (∃ path : Path language rows source target, path.length = count ∧
      DeclarativeSpec.Runs program
        { state, control := .evaluate [] (encoded
            (driveQueryTerm language types terms contexts compiled rows source (receipts path) count)) }
        (.complete state [encoded (pathTerm path (stoppedTerm target))] [] [])) ↔
      (∃ path : ExecutionPath (langGSLTUsing (providerEnv rows) language) source.erase target.erase,
        path.length = count) := by
  rw [← paths_iff state language types terms contexts compiled rows equationFree providerAdmitted source target count]
  constructor
  · rintro ⟨path, length, _⟩
    exact ⟨path, length⟩
  · rintro ⟨path, length⟩
    refine ⟨path, length, ?_⟩
    simpa only [List.append_nil] using
      (drive_derivation_iff state language types terms contexts compiled rows path [] (stoppedTerm target) count
        (by omega) (Or.inl ⟨rfl, rfl⟩) state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

end Selection

namespace Controls

def start : PatternPlan := .application "start" []
def middle : PatternPlan := .application "middle" []
def other : PatternPlan := .application "other" []
def done : PatternPlan := .application "done" []

private def guarded : RulePlan :=
  { name := "guarded", typeContext := [], premises := [⟨"ready", []⟩], left := start, right := middle }

/-- Reuse the common root-control fixture type. Duplicate rules and duplicate
provider witnesses independently contribute ordered frontier occurrences. -/
def fixture : Conditional.Controls.Fixture :=
  { name := "finite-path-ordered-frontiers"
    plans := [guarded,
      { name := "branch", typeContext := [], premises := [], left := start, right := other },
      guarded,
      { name := "finish", typeContext := [], premises := [], left := middle, right := done }]
    rows := [⟨"ready", []⟩, ⟨"ignored", []⟩, ⟨"ready", []⟩]
    subject := start }

theorem provider_admitted : providerFirstOrder fixture.rows = true := by decide +kernel

theorem first_frontier :
    rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase =
      [middle.erase, middle.erase, other.erase, middle.erase, middle.erase] := by
  decide +kernel

theorem second_frontier :
    rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language middle.erase =
      [done.erase] := by
  decide +kernel

private theorem selected (state : State) (subject target : PatternPlan)
    (member : target.erase ∈ rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language subject.erase) :
    Conditional.ObservesRootReduct state fixture.language (.symbol "LNil") (.symbol "LNil")
      (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows subject target.erase := by
  refine ⟨_, ?_, member⟩
  exact (Conditional.language_root_derivation_iff state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows subject state _ [] []).mpr
      ⟨rfl, rfl, rfl, rfl⟩

/-- A supplied two-edge path, with both edges justified by actual entry runs. -/
def path (state : State) : CallPath state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows start done :=
  .cons ⟨selected state start middle (by rw [first_frontier]; simp)⟩
    (.cons ⟨selected state middle done (by rw [second_frontier]; simp)⟩ (.refl done))

def expectedFrontiers : List Term :=
  [InferenceCettaWire.encodePatterns [middle.erase, middle.erase, other.erase, middle.erase, middle.erase],
   InferenceCettaWire.encodePatterns [done.erase]]

theorem path_frontiers (state : State) :
    frontierTerms state fixture.language (.symbol "LNil") (.symbol "LNil")
      (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (path state) = expectedFrontiers := by
  simp only [frontierTerms, path, Route.trace, first_frontier, second_frontier, expectedFrontiers]

theorem path_length (state : State) : (path state).length = 2 := rfl

theorem batch_checked (state : State) :
    Returns program [] state
      (batchQuery state fixture.language (.symbol "LNil") (.symbol "LNil")
        (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (path state)) state
      (expectedFrontiers.map CettaWireAtom.encode) := by
  rw [← path_frontiers state]
  exact batch_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (path state)

theorem reversed_observations_refused (state : State) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (batchQuery state fixture.language (.symbol "LNil") (.symbol "LNil")
          (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (path state)) }
      (.complete state (expectedFrontiers.reverse.map CettaWireAtom.encode) [] []) := by
  apply batch_refuses_incorrect state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (path state)
  rw [path_frontiers state]
  decide +kernel

theorem binder_payload_refused :
    providerFirstOrder [⟨"payload", [.lambda (some "bound") (.bvar 0)]⟩] = false := rfl

theorem literal_variable_payload_admitted :
    providerFirstOrder [⟨"payload", [.fvar "inside"]⟩] = true := rfl

def oneSelected (index : Nat)
    (chosen : (rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase)[index]? =
      some middle.erase) : Selection.Path fixture.language fixture.rows start middle :=
  .cons ⟨index, chosen⟩ (.refl middle)

def twoSelected (index : Nat)
    (chosen : (rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase)[index]? =
      some middle.erase) : Selection.Path fixture.language fixture.rows start done :=
  .cons ⟨index, chosen⟩ (.cons ⟨0, by rw [second_frontier]; rfl⟩ (.refl done))

theorem first_chosen :
    (rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase)[0]? = some middle.erase := by
  rw [first_frontier]; rfl

theorem duplicate_chosen :
    (rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase)[1]? = some middle.erase := by
  rw [first_frontier]; rfl

def driveQuery (selections : List Nat) (budget : Nat) : Term :=
  Selection.driveQueryTerm fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows start selections budget

theorem drive_stopped (state : State) (budget : Nat) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery [] budget)) state
      (CettaWireAtom.encode (Selection.stoppedTerm start)) :=
  Selection.drive_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (.refl start) [] (Selection.stoppedTerm start)
    budget (by simp [Route.length]) (Or.inl ⟨rfl, rfl⟩)

/-- Receipt exhaustion wins even with zero budget, and the residual can still
have authorized outgoing reductions. Stopping is not a normal-form claim. -/
theorem stopped_nonterminal :
    rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase ≠ [] := by
  rw [first_frontier]; simp

theorem drive_fuel_before_first (state : State) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery [0] 0)) state
      (CettaWireAtom.encode (Selection.fuelTerm start [0])) :=
  Selection.drive_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (.refl start) [0] (Selection.fuelTerm start [0])
    0 (by simp [Route.length]) (Or.inr (Or.inl ⟨by simp, rfl, rfl⟩))

theorem drive_refused_before_first (state : State) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery [99] 3)) state
      (CettaWireAtom.encode (Selection.refusedTerm fixture.language fixture.rows start [99])) :=
  Selection.drive_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (.refl start) [99]
    (Selection.refusedTerm fixture.language fixture.rows start [99]) 3 (by simp [Route.length])
    (Or.inr (Or.inr ⟨99, [], rfl, by decide, by rw [first_frontier]; rfl, rfl⟩))

theorem drive_two (state : State) (index : Nat)
    (chosen : (rewriteStepWithPremisesUsing (providerEnv fixture.rows) fixture.language start.erase)[index]? =
      some middle.erase) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery [index, 0] 2)) state
      (CettaWireAtom.encode (Selection.pathTerm (twoSelected index chosen) (Selection.stoppedTerm done))) :=
  Selection.drive_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (twoSelected index chosen) [] (Selection.stoppedTerm done)
    2 (by simp [twoSelected, Route.length]) (Or.inl ⟨rfl, rfl⟩)

theorem drive_fuel_after_one (state : State) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery [0, 0] 1)) state
      (CettaWireAtom.encode (Selection.pathTerm (oneSelected 0 first_chosen) (Selection.fuelTerm middle [0]))) :=
  Selection.drive_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (oneSelected 0 first_chosen) [0]
    (Selection.fuelTerm middle [0]) 1 (by simp [oneSelected, Route.length])
    (Or.inr (Or.inl ⟨by simp, rfl, rfl⟩))

theorem drive_refused_after_one (state : State) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery [0, 8] 3)) state
      (CettaWireAtom.encode (Selection.pathTerm (oneSelected 0 first_chosen)
        (Selection.refusedTerm fixture.language fixture.rows middle [8]))) :=
  Selection.drive_returns state fixture.language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") (fixture.sourceCompiled (by decide +kernel)) fixture.rows (oneSelected 0 first_chosen) [8]
    (Selection.refusedTerm fixture.language fixture.rows middle [8]) 3 (by simp [oneSelected, Route.length])
    (Or.inr (Or.inr ⟨8, [], rfl, by decide, by rw [second_frontier]; rfl, rfl⟩))

/-- Shared serial execution controls: name, receipt stream, semantic step
budget and exact wire result. The expected traces encode existing selected
routes; they are not computed by a second driver implementation. -/
def driveFixtures : List (String × List Nat × Nat × Term) :=
  [("receipts-empty-zero-budget", [], 0, Selection.stoppedTerm start),
   ("receipts-empty-nonterminal", [], 3, Selection.stoppedTerm start),
   ("fuel-before-first", [0], 0, Selection.fuelTerm start [0]),
   ("refusal-before-first", [99], 3, Selection.refusedTerm fixture.language fixture.rows start [99]),
   ("two-step-reentry", [0, 0], 2, Selection.pathTerm (twoSelected 0 first_chosen) (Selection.stoppedTerm done)),
   ("duplicate-witness-receipt", [1, 0], 2, Selection.pathTerm (twoSelected 1 duplicate_chosen) (Selection.stoppedTerm done)),
   ("fuel-after-one", [0, 0], 1, Selection.pathTerm (oneSelected 0 first_chosen) (Selection.fuelTerm middle [0])),
   ("refusal-after-one", [0, 8], 3, Selection.pathTerm (oneSelected 0 first_chosen)
     (Selection.refusedTerm fixture.language fixture.rows middle [8]))]

theorem drive_fixture_returns (state : State) (control : String × List Nat × Nat × Term)
    (member : control ∈ driveFixtures) :
    PureReturns program [] state (CettaWireAtom.encode (driveQuery control.2.1 control.2.2.1)) state
      (CettaWireAtom.encode control.2.2.2) := by
  simp only [driveFixtures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact drive_stopped state 0
  · exact drive_stopped state 3
  · exact drive_fuel_before_first state
  · exact drive_refused_before_first state
  · exact drive_two state 0 first_chosen
  · exact drive_two state 1 duplicate_chosen
  · exact drive_fuel_after_one state
  · exact drive_refused_after_one state

theorem duplicate_receipts_have_different_traces :
    Selection.pathTerm (twoSelected 0 first_chosen) (Selection.stoppedTerm done) ≠
      Selection.pathTerm (twoSelected 1 duplicate_chosen) (Selection.stoppedTerm done) := by
  decide +kernel

/-- Overwriting the consumed duplicate witness ordinal changes the trace and
is refused even though the residual subject and the full frontier agree. -/
theorem duplicate_receipt_overwrite_refused (state : State) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (CettaWireAtom.encode (driveQuery [1, 0] 2)) }
      (.complete state [CettaWireAtom.encode
        (Selection.pathTerm (twoSelected 0 first_chosen) (Selection.stoppedTerm done))] [] []) := by
  intro accepted
  have exactRun := (pure_returns_derivation_iff program [] state state _ _
    (drive_two state 1 duplicate_chosen) state _ [] []).mp accepted
  have equal := List.cons.inj exactRun.2.1 |>.1
  have wires := CettaWireAtom.encode_injective _ _ equal
  exact duplicate_receipts_have_different_traces wires

private theorem incorrect_trace_refused (state : State) (query correct incorrect : Term)
    (computed : PureReturns program [] state (CettaWireAtom.encode query) state (CettaWireAtom.encode correct))
    (different : incorrect ≠ correct) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (CettaWireAtom.encode query) }
      (.complete state [CettaWireAtom.encode incorrect] [] []) := by
  intro accepted
  have exactRun := (pure_returns_derivation_iff program [] state state _ _ computed state _ [] []).mp accepted
  have equal := List.cons.inj exactRun.2.1 |>.1
  exact different (CettaWireAtom.encode_injective _ _ equal)

/-- Incorrect complete observations, qualified alongside the positive source
controls. They change a status, overwrite an occurrence receipt or drop the
failed unread receipt without changing the requested program. -/
def driveRefusals : List (String × Term × Term) :=
  [("empty-receipts-claimed-fuel", driveQuery [] 0, Selection.fuelTerm start []),
   ("duplicate-receipt-overwritten", driveQuery [1, 0] 2,
     Selection.pathTerm (twoSelected 0 first_chosen) (Selection.stoppedTerm done)),
   ("failed-receipt-consumed", driveQuery [99] 3,
     Selection.refusedTerm fixture.language fixture.rows start [])]

theorem drive_fixture_refusals (state : State) (control : String × Term × Term)
    (member : control ∈ driveRefusals) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (CettaWireAtom.encode control.2.1) }
      (.complete state [CettaWireAtom.encode control.2.2] [] []) := by
  simp only [driveRefusals, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact incorrect_trace_refused state _ _ _ (drive_stopped state 0) (by decide +kernel)
  · exact duplicate_receipt_overwrite_refused state
  · exact incorrect_trace_refused state _ _ _ (drive_refused_before_first state) (by decide +kernel)

end Controls

#print axioms providerEnv_firstOrder
#print axioms erasePath_length
#print axioms erasePath_trace
#print axioms liftPath
#print axioms paths_iff
#print axioms sequence_returns
#print axioms batch_returns
#print axioms batch_completed_iff
#print axioms batch_derivation_iff
#print axioms batch_refuses_incorrect
#print axioms Selection.receipts_injective
#print axioms Selection.paths_iff
#print axioms Selection.authored_occurrence
#print axioms Selection.authored_occurrence_unique
#print axioms Selection.premise_occurrence
#print axioms Selection.partition
#print axioms Selection.drive_captured_returns
#print axioms Selection.drive_returns
#print axioms Selection.drive_completed_iff
#print axioms Selection.drive_derivation_iff
#print axioms Selection.drive_total
#print axioms Selection.observations_iff
#print axioms Selection.derivations_iff
#print axioms Selection.stopped_paths_iff
#print axioms Controls.batch_checked
#print axioms Controls.reversed_observations_refused
#print axioms Controls.binder_payload_refused
#print axioms Controls.literal_variable_payload_admitted
#print axioms Controls.drive_fixture_returns
#print axioms Controls.duplicate_receipt_overwrite_refused
#print axioms Controls.drive_fixture_refusals

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution
