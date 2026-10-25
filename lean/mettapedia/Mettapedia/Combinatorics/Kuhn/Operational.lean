import Mettapedia.Combinatorics.Kuhn.GridSimplex
import Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
import Mettapedia.GSLT.Dynamics.OrderedListFold
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mathlib.Data.List.Nodup

/-!
# Executable coordinate schedules for Kuhn simplices

A simplex in Kuhn's triangulation is a lower corner together with the order in
which every coordinate is incremented.  This module gives that order two
independent operational meanings:

* `OrderedListFold` executes typed coordinate actions; and
* `KuhnScheduleModule` executes an occurrence-preserving authored module.

The module records the reverse history while consuming the pending schedule.
Decoding that history recovers the authored order exactly.  Interpreting its
prefixes as coordinate increments recovers the existing simplex vertices.

Coordinate increments commute at the geometric point observer.  Their
retained histories do not: swapping adjacent steps preserves the endpoint but
changes the chronological trace and the intermediate vertex.  Thus the
commuting square is an observer-relative fact, not an identification of
executions.

The portable module envelope records the coordinate dimension separately.
The rewrite theory alone cannot distinguish dimensions, especially for the
empty schedule.  This is a Lean executor and serialization correspondence; it
does not assert realization by a native runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Combinatorics.Kuhn.Operational

open Mettapedia.Combinatorics.Kuhn
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

variable {n p m : ℕ}

/-! ## Typed geometric execution -/

/-- Increment one coordinate of a point. -/
def coordinateStep (point : Fin n → ℕ) (coordinate : Fin n) : Fin n → ℕ :=
  Function.update point coordinate (point coordinate + 1)

/-- Execute coordinate occurrences in authored order. -/
def runSchedule (initial : Fin n → ℕ) (steps : List (Fin n)) : Fin n → ℕ :=
  EffectTraceInterleaving.run coordinateStep initial steps

@[simp] theorem runSchedule_nil (initial : Fin n → ℕ) :
    runSchedule initial [] = initial :=
  rfl

@[simp] theorem runSchedule_cons (initial : Fin n → ℕ) (coordinate : Fin n)
    (steps : List (Fin n)) :
    runSchedule initial (coordinate :: steps) =
      runSchedule (coordinateStep initial coordinate) steps :=
  rfl

/-- Execution counts occurrences.  No `Nodup` premise is hidden here. -/
@[simp] theorem runSchedule_apply (initial : Fin n → ℕ) (steps : List (Fin n))
    (coordinate : Fin n) :
    runSchedule initial steps coordinate = initial coordinate + steps.count coordinate := by
  induction steps generalizing initial with
  | nil => simp [runSchedule]
  | cons head tail inductionHypothesis =>
      rw [runSchedule_cons, inductionHypothesis]
      by_cases same : coordinate = head
      · subst head
        simp [coordinateStep, Nat.add_comm, Nat.add_left_comm]
      · simp [coordinateStep, same, Ne.symm same]

theorem coordinateStep_commute (left right : Fin n) (point : Fin n → ℕ) :
    coordinateStep (coordinateStep point left) right =
      coordinateStep (coordinateStep point right) left := by
  by_cases same : left = right
  · subst right
    rfl
  · funext coordinate
    by_cases atLeft : coordinate = left
    · subst coordinate
      simp [coordinateStep, same]
    · by_cases atRight : coordinate = right
      · subst coordinate
        simp [coordinateStep, same, Ne.symm same]
      · simp [coordinateStep, atLeft, atRight]

theorem coordinate_actions_commute :
    Mettapedia.Machines.Cursor.PermutationInvariantFold.ActionsCommute
      (@coordinateStep n) := by
  intro point left right
  exact coordinateStep_commute left right point

theorem runSchedule_perm {first second : List (Fin n)}
    (permutation : first.Perm second) (initial : Fin n → ℕ) :
    runSchedule initial first = runSchedule initial second := by
  exact Mettapedia.Machines.Cursor.PermutationInvariantFold.foldl_perm
    coordinateStep coordinate_actions_commute permutation initial

theorem runSchedule_take_eq_vertex (σ : GridSimplex p n) (k : Fin (n + 1)) :
    runSchedule (fun i => (σ.base i : ℕ)) (σ.schedule.take k) = σ.vertex k := by
  funext coordinate
  rw [runSchedule_apply]
  by_cases visited : coordinate ∈ σ.schedule.take k
  · rw [List.count_eq_one_of_mem σ.schedule_nodup.take visited]
    simp [GridSimplex.vertex, (σ.mem_schedule_take_iff k coordinate).mp visited]
  · rw [List.count_eq_zero.mpr visited]
    simp [GridSimplex.vertex, (σ.mem_schedule_take_iff k coordinate).not.mp visited]

theorem runSchedule_eq_lastVertex (σ : GridSimplex p n) :
    runSchedule (fun i => (σ.base i : ℕ)) σ.schedule =
      σ.vertex (Fin.last n) := by
  have result := runSchedule_take_eq_vertex σ (Fin.last n)
  change runSchedule (fun i => (σ.base i : ℕ)) (σ.schedule.take n) =
    σ.vertex (Fin.last n) at result
  have taken : σ.schedule.take n = σ.schedule :=
    (List.take_eq_self_iff _).mpr (by simp)
  rw [taken] at result
  exact result

theorem runSchedule_eq_upperCorner (σ : GridSimplex p n) :
    runSchedule (fun i => (σ.base i : ℕ)) σ.schedule =
      fun i => (σ.base i : ℕ) + 1 := by
  rw [runSchedule_eq_lastVertex]
  funext i
  simp [GridSimplex.vertex]

/-! ## Portable schedule module -/

namespace KuhnScheduleModule

def signature : QuotedTheory := moduleTheory! Theory KuhnSchedule() {
  Types { Coordinate; Coordinates; State; }
  Terms {
    Zero . |- : Coordinate;
    Succ . previous:Coordinate |- : Coordinate;
    Nil . |- : Coordinates;
    Cons . head:Coordinate, tail:Coordinates |- : Coordinates;
    Active . remaining:Coordinates, history:Coordinates |- : State;
    Done . history:Coordinates |- : State;
  }
  Exports { Coordinate; Coordinates; State; }
}

def coordinatePattern : ℕ → Pattern
  | 0 => .apply "Zero" []
  | coordinate + 1 => .apply "Succ" [coordinatePattern coordinate]

def coordinatesPattern : List ℕ → Pattern
  | [] => .apply "Nil" []
  | coordinate :: rest =>
      .apply "Cons" [coordinatePattern coordinate, coordinatesPattern rest]

def finCoordinatesPattern : List (Fin n) → Pattern
  | [] => .apply "Nil" []
  | coordinate :: rest =>
      .apply "Cons" [coordinatePattern coordinate.val, finCoordinatesPattern rest]

def activePattern (remaining history : List (Fin n)) : Pattern :=
  .apply "Active" [finCoordinatesPattern remaining, finCoordinatesPattern history]

def donePattern (history : List (Fin n)) : Pattern :=
  .apply "Done" [finCoordinatesPattern history]

private def context : List (String × TypeExpr) :=
  [("coordinate", .base "Coordinate"), ("rest", .base "Coordinates"),
    ("history", .base "Coordinates")]

def consumeRule : RewriteRule :=
  RewriteRule.mk (bindings := none) "Consume" context []
    (.apply "Active"
      [.apply "Cons" [.fvar "coordinate", .fvar "rest"], .fvar "history"])
    (.apply "Active"
      [.fvar "rest", .apply "Cons" [.fvar "coordinate", .fvar "history"]])

def finishRule : RewriteRule :=
  RewriteRule.mk (bindings := none) "Finish" [("history", .base "Coordinates")] []
    (.apply "Active" [.apply "Nil" [], .fvar "history"])
    (.apply "Done" [.fvar "history"])

def language : LanguageDef :=
  { signature.toLanguageDef with «rewrites» := [consumeRule, finishRule] }

def quoted : QuotedTheory :=
  ofCore language ["Coordinate", "Coordinates", "State"]

def successors (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises .empty) language 1 source

macro "schedule_rewrite" : tactic =>
  `(tactic|
    (simp [successors, rewriteAt, language, consumeRule, finishRule,
      activePattern, donePattern, finCoordinatesPattern, coordinatesPattern,
      coordinatePattern, context,
      applyRuleUsing, matchPatternForRule, matchPatternForRuleUsing,
      applyBindingsForRule, applyBindingsForRuleUsing, applyRuleBindings,
      premisesUsing, matchingPresentationForRule?, substitutionPresentationForRule?,
      reflectiveRuleForRule?, matchPattern, matchArgs, mergeBindings,
      applyBindings, OSLF.MeTTaIL.Reflection.ReflectionProfile.empty]))

theorem consume_exact (coordinate : Fin n) (rest history : List (Fin n)) :
    successors (activePattern (coordinate :: rest) history) =
      [activePattern rest (coordinate :: history)] := by
  schedule_rewrite

theorem finish_exact (history : List (Fin n)) :
    successors (activePattern [] history) = [donePattern history] := by
  schedule_rewrite

theorem done_normal (history : List (Fin n)) :
    successors (donePattern history) = [] := by
  schedule_rewrite

private theorem rewrites_validate :
    ∀ rule ∈ language.rewrites,
      LanguageDef.validateRewrite language rule = [] := by
  intro rule membership
  simp only [language, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, language, consumeRule, finishRule,
      context, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      LanguageDef.typeNames]

set_option maxRecDepth 100000 in
theorem language_validates : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact rewrites_validate

theorem quoted_admitted : (admit? quoted).isSome = true := by
  apply (admit_isSome_iff _).mpr
  constructor
  · change language.validate.isEmpty = true
    rw [language_validates]
    rfl
  · simp only [exportsValid, quoted, ofCore, language, LanguageDef.typeNames]
    decide +kernel

/-! ## Decoding and the typed-state correspondence -/

def readCoordinate? : Pattern → Option ℕ
  | .apply "Zero" [] => some 0
  | .apply "Succ" [previous] => (readCoordinate? previous).map Nat.succ
  | _ => none

def readFin? (n : ℕ) (pattern : Pattern) : Option (Fin n) := do
  let coordinate ← readCoordinate? pattern
  if within : coordinate < n then some ⟨coordinate, within⟩ else none

def readCoordinates? (n : ℕ) : Pattern → Option (List (Fin n))
  | .apply "Nil" [] => some []
  | .apply "Cons" [head, tail] => do
      let coordinate ← readFin? n head
      let rest ← readCoordinates? n tail
      pure (coordinate :: rest)
  | _ => none

@[simp] theorem readCoordinate_coordinatePattern (coordinate : ℕ) :
    readCoordinate? (coordinatePattern coordinate) = some coordinate := by
  induction coordinate with
  | zero => rfl
  | succ coordinate inductionHypothesis =>
      simp [coordinatePattern, readCoordinate?, inductionHypothesis]

@[simp] theorem readFin_finCoordinate (coordinate : Fin n) :
    readFin? n (coordinatePattern coordinate.val) = some coordinate := by
  simp [readFin?, coordinate.isLt]

@[simp] theorem readCoordinates_finCoordinates (coordinates : List (Fin n)) :
    readCoordinates? n (finCoordinatesPattern coordinates) = some coordinates := by
  induction coordinates with
  | nil => rfl
  | cons coordinate rest inductionHypothesis =>
      simp [finCoordinatesPattern, readCoordinates?, inductionHypothesis]

abbrev TypedState (n : ℕ) :=
  OrderedListFold.State (Fin n) (List (Fin n))

def recordStep (history : List (Fin n)) (coordinate : Fin n) : List (Fin n) :=
  coordinate :: history

def encodeState : TypedState n → Pattern
  | .active remaining history => activePattern remaining history
  | .done history => donePattern history

def readState? (n : ℕ) : Pattern → Option (TypedState n)
  | .apply "Active" [remaining, history] => do
      let remaining ← readCoordinates? n remaining
      let history ← readCoordinates? n history
      pure (.active remaining history)
  | .apply "Done" [history] => do
      let history ← readCoordinates? n history
      pure (.done history)
  | _ => none

@[simp] theorem readState_encodeState (state : TypedState n) :
    readState? n (encodeState state) = some state := by
  cases state <;> simp [readState?, encodeState, activePattern, donePattern]

theorem encodeState_injective : Function.Injective (@encodeState n) := by
  intro first second same
  have decoded := congrArg (readState? n) same
  simpa using decoded

/-- The authored engine has exactly the same next state as the independent
ordered-list machine on every encoded state. -/
theorem successors_encodeState (state : TypedState n) :
    successors (encodeState state) =
      ((OrderedListFold.step? recordStep state).toList.map encodeState) := by
  cases state with
  | active remaining history =>
      cases remaining with
      | nil => simpa [encodeState, OrderedListFold.step?] using finish_exact history
      | cons coordinate rest =>
          simpa [encodeState, OrderedListFold.step?, recordStep] using
            consume_exact coordinate rest history
  | done history =>
      simpa [encodeState, OrderedListFold.step?] using done_normal history

/-! ## Proof-relevant module execution -/

private theorem equationLaws : ReductionRespectsEquationsUsing .empty language :=
  ReductionRespectsEquationsUsing.of_equation_free _ rfl

/-- The contextual GSLT denoted by the admitted schedule language. -/
def theory : GSLT :=
  languageGSLTUsing .empty language equationLaws

theorem step_of_successors_eq_singleton (before after : Pattern)
    (exact : successors before = [after]) : theory.Step before after := by
  apply (languageGSLTUsing_step .empty language equationLaws before after).2
  apply (langReducesUsing_iff_execUsing .empty language before after).2
  refine ⟨1, ?_⟩
  change after ∈ successors before
  rw [exact]
  simp

/-- The reverse history obtained after consuming every remaining item. -/
def finalHistory (remaining history : List (Fin n)) : List (Fin n) :=
  remaining.foldl recordStep history

@[simp] theorem finalHistory_nil (history : List (Fin n)) :
    finalHistory [] history = history :=
  rfl

@[simp] theorem finalHistory_cons (coordinate : Fin n)
    (remaining history : List (Fin n)) :
    finalHistory (coordinate :: remaining) history =
      finalHistory remaining (coordinate :: history) :=
  rfl

theorem finalHistory_eq_reverse_append (remaining history : List (Fin n)) :
    finalHistory remaining history = remaining.reverse ++ history := by
  induction remaining generalizing history with
  | nil => rfl
  | cons coordinate rest inductionHypothesis =>
      rw [finalHistory_cons, inductionHypothesis]
      simp [List.reverse_cons, List.append_assoc]

/-- Consume every supplied occurrence with the actual authored rewrite rules.
The target retains the reverse history rather than reconstructing it from an
endpoint. -/
noncomputable def executionPath :
    (remaining history : List (Fin n)) →
      theory.RewritePath (activePattern remaining history)
        (donePattern (finalHistory remaining history))
  | [], history =>
      .cons (step_of_successors_eq_singleton _ _ (finish_exact history)) (.nil _)
  | coordinate :: remaining, history =>
      .cons
        (step_of_successors_eq_singleton _ _
          (consume_exact coordinate remaining history))
        (executionPath remaining (coordinate :: history))

@[simp] theorem executionPath_length (remaining history : List (Fin n)) :
    (executionPath remaining history).length = remaining.length + 1 := by
  induction remaining generalizing history with
  | nil => rfl
  | cons coordinate rest inductionHypothesis =>
      change 1 + (executionPath rest (coordinate :: history)).length =
        (coordinate :: rest).length + 1
      rw [inductionHypothesis]
      simp
      omega

/-- The independently defined ordered-list execution and the authored module
account for the same number of transitions. -/
theorem executionPath_length_eq_orderedListFold
    (remaining history : List (Fin n)) :
    (executionPath remaining history).length =
      (OrderedListFold.runPath recordStep remaining history).length := by
  rw [executionPath_length]
  exact (OrderedListFold.complete_path recordStep remaining history
    (finalHistory remaining history)
    (OrderedListFold.runPath recordStep remaining history)).2.symm

/-! ## Which lists denote simplex schedules -/

/-- A list over `Fin n` is a simplex schedule exactly when it contains `n`
distinct occurrences. -/
def IsCoordinateSchedule (steps : List (Fin n)) : Prop :=
  steps.length = n ∧ steps.Nodup

instance (steps : List (Fin n)) : Decidable (IsCoordinateSchedule steps) := by
  unfold IsCoordinateSchedule
  infer_instance

theorem GridSimplex.schedule_isCoordinateSchedule (σ : GridSimplex p n) :
    IsCoordinateSchedule σ.schedule :=
  ⟨σ.schedule_length, σ.schedule_nodup⟩

theorem IsCoordinateSchedule.mem {steps : List (Fin n)}
    (valid : IsCoordinateSchedule steps)
    (coordinate : Fin n) : coordinate ∈ steps := by
  have cardAtLeast : (Finset.univ : Finset (Fin n)).card ≤ steps.toFinset.card := by
    rw [Finset.card_univ, Fintype.card_fin,
      List.toFinset_card_of_nodup valid.2, valid.1]
  have all : steps.toFinset = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) cardAtLeast
  have member : coordinate ∈ steps.toFinset := by
    rw [all]
    exact Finset.mem_univ _
  exact List.mem_toFinset.mp member

theorem isCoordinateSchedule_iff_perm_schedule
    (steps : List (Fin n)) (σ : GridSimplex p n) :
    IsCoordinateSchedule steps ↔ steps.Perm σ.schedule := by
  constructor
  · intro valid
    apply (List.perm_ext_iff_of_nodup valid.2 σ.schedule_nodup).mpr
    intro coordinate
    exact ⟨fun _ => σ.mem_schedule coordinate,
      fun _ => IsCoordinateSchedule.mem valid coordinate⟩
  · intro permutation
    exact ⟨permutation.length_eq.trans σ.schedule_length,
      (permutation.nodup_iff.mpr σ.schedule_nodup)⟩

/-! ## Geometric observation of retained histories -/

/-- Module histories are stored newest-first.  Geometric observation restores
chronological order and executes the corresponding coordinate increments. -/
def pointOfHistory (initial : Fin n → ℕ) (reverseHistory : List (Fin n)) :
    Fin n → ℕ :=
  runSchedule initial reverseHistory.reverse

theorem prefixHistory_eq_vertex (σ : GridSimplex p n) (k : Fin (n + 1)) :
    pointOfHistory (fun i => (σ.base i : ℕ)) (σ.schedule.take k).reverse =
      σ.vertex k := by
  simp [pointOfHistory, runSchedule_take_eq_vertex]

/-! ## Canonical text and UTF-8 transport -/

def schema : String := "kuhn-coordinate-schedule/1"

def envelope (dimension : ℕ) : ModuleFormat.Module ModuleFormat.upstreamLimits :=
  ⟨⟨"KuhnSchedule", [], [
      ⟨"Schedule", ModuleFormat.Portable.specification schema
        ModuleFormat.Portable.exportsCodec quoted⟩,
      ⟨"Dimension", .integer dimension⟩]⟩,
    by
      simp [ModuleFormat.RawModule.Valid, ModuleFormat.Export.Valid,
        ModuleFormat.upstreamLimits]
      decide⟩

def moduleText (dimension : ℕ) : String :=
  ModuleFormat.renderText ModuleFormat.upstreamLimits (envelope dimension)

def moduleBytes (dimension : ℕ) : ByteArray :=
  ModuleFormat.Text.renderBytes
    (ModuleFormat.Value.Wire.encode (ModuleFormat.encodeRaw (envelope dimension).val))

theorem read_moduleText (dimension : ℕ) :
    ModuleFormat.readText? ModuleFormat.upstreamLimits (moduleText dimension) =
      some (envelope dimension) :=
  ModuleFormat.readText_renderText _ _

theorem moduleBytes_eq_utf8 (dimension : ℕ) :
    moduleBytes dimension = (moduleText dimension).toUTF8 :=
  rfl

theorem read_moduleBytes (dimension : ℕ) :
    (ModuleFormat.Text.readBytes? (moduleBytes dimension)).bind (fun term =>
      (ModuleFormat.Value.Wire.decode? term).bind
        (ModuleFormat.decode? ModuleFormat.upstreamLimits)) =
      some (envelope dimension) := by
  simp [moduleBytes]

def readScheduleTheory? (expectedDimension : ℕ) (text : String) : Option QuotedTheory := do
  let parsed ← ModuleFormat.readText? ModuleFormat.upstreamLimits text
  match parsed.val.exports with
  | [scheduleExport, dimensionExport] =>
      if scheduleExport.name = "Schedule" ∧
          dimensionExport.name = "Dimension" ∧
          dimensionExport.spec = .integer expectedDimension then
        ModuleFormat.Portable.admitSpecification? schema
          ModuleFormat.Portable.exportsCodec scheduleExport.spec
      else none
  | _ => none

theorem read_scheduleTheory (dimension : ℕ) :
    readScheduleTheory? dimension (moduleText dimension) = some quoted := by
  simp [readScheduleTheory?, read_moduleText, envelope,
    ModuleFormat.Portable.specification_roundtrip]

theorem read_wrong_dimension (dimension expected : ℕ)
    (different : dimension ≠ expected) :
    readScheduleTheory? expected (moduleText dimension) = none := by
  simp [readScheduleTheory?, read_moduleText, envelope, different]

theorem moduleText_preserves_dimension {first second : ℕ}
    (same : moduleText first = moduleText second) : first = second := by
  have dimensions := congrArg (fun text =>
    (ModuleFormat.readText? ModuleFormat.upstreamLimits text).bind
      (fun parsed => parsed.val.exports[1]?.map (·.spec))) same
  simp only [read_moduleText] at dimensions
  exact Int.ofNat.inj (ModuleFormat.Value.integer.inj (Option.some.inj dimensions))

theorem moduleText_ne_of_dimension_ne {first second : ℕ}
    (different : first ≠ second) : moduleText first ≠ moduleText second :=
  fun same => different (moduleText_preserves_dimension same)

/-- Execute the theory obtained from actual serialized text. -/
theorem read_consume (coordinate : Fin n) (rest history : List (Fin n)) :
    (readScheduleTheory? n (moduleText n)).map (fun parsed =>
      rewriteAt (engineBasePremises .empty) parsed.toLanguageDef 1
        (activePattern (coordinate :: rest) history)) =
      some [activePattern rest (coordinate :: history)] := by
  rw [read_scheduleTheory]
  exact congrArg some (consume_exact coordinate rest history)

theorem read_finish (history : List (Fin n)) :
    (readScheduleTheory? n (moduleText n)).map (fun parsed =>
      rewriteAt (engineBasePremises .empty) parsed.toLanguageDef 1
        (activePattern [] history)) = some [donePattern history] := by
  rw [read_scheduleTheory]
  exact congrArg some (finish_exact history)

theorem malformed_coordinate_refused :
    readFin? 2 (coordinatePattern 2) = none ∧
      readCoordinates? 2
        (.apply "Cons" [coordinatePattern 2, .apply "Nil" []]) = none := by
  decide

end KuhnScheduleModule

/-! ## Causality and observer-relative commutation -/

theorem coordinate_crossCommutes (left right : List (Fin n)) :
    EffectTraceInterleaving.CrossCommutes coordinateStep left right := by
  intro leftCoordinate _ rightCoordinate _ point
  exact coordinateStep_commute leftCoordinate rightCoordinate point

theorem coordinate_realizations_agree (left right : List (Fin n))
    (realization : EffectTraceInterleaving.Realization left right)
    (initial : Fin n → ℕ) :
    runSchedule initial realization.trace = runSchedule initial (left ++ right) := by
  exact EffectTraceInterleaving.realization_endpoint_unique_of_crossCommutes
    coordinateStep realization (coordinate_crossCommutes left right) initial

/-- Every simplex schedule contains the same coordinate occurrences. -/
theorem simplexSchedules_perm (σ τ : GridSimplex p n) :
    σ.schedule.Perm τ.schedule := by
  apply (List.perm_ext_iff_of_nodup σ.schedule_nodup τ.schedule_nodup).mpr
  intro coordinate
  simp

/-- Adjacent exchange changes the retained authored schedule. -/
theorem swapStep_schedule_ne (σ : GridSimplex p (m + 1)) (j : Fin m) :
    (σ.swapStep j).schedule ≠ σ.schedule := by
  intro same
  apply σ.swapStep_ne j
  apply GridSimplex.ext
  · rfl
  · apply Equiv.ext
    exact congrFun (List.ofFn_injective same)

/-- The same adjacent exchange is invisible at the final geometric point. -/
theorem swapStep_endpoint (σ : GridSimplex p (m + 1)) (j : Fin m) :
    runSchedule (fun i => (σ.base i : ℕ)) (σ.swapStep j).schedule =
      runSchedule (fun i => (σ.base i : ℕ)) σ.schedule := by
  exact runSchedule_perm (simplexSchedules_perm (σ.swapStep j) σ) _

/-- The intermediate vertex between the exchanged steps remains observable. -/
theorem swapStep_middle_vertex_ne (σ : GridSimplex p (m + 1)) (j : Fin m) :
    (σ.swapStep j).vertex j.castSucc.succ ≠ σ.vertex j.castSucc.succ := by
  intro same
  have atCoordinate := congrFun same (σ.order j.castSucc)
  change (σ.base (σ.order j.castSucc) : ℕ) +
      (if (((σ.order * Equiv.swap j.castSucc j.succ).symm
          (σ.order j.castSucc) : Fin (m + 1)) : ℕ) < j + 1 then 1 else 0) =
    (σ.base (σ.order j.castSucc) : ℕ) +
      (if ((σ.order.symm (σ.order j.castSucc) : Fin (m + 1)) : ℕ) < j + 1
        then 1 else 0) at atCoordinate
  have originalPosition : σ.order.symm (σ.order j.castSucc) = j.castSucc :=
    σ.order.symm_apply_apply j.castSucc
  rw [originalPosition] at atCoordinate
  have swappedPosition :
      (σ.order * Equiv.swap j.castSucc j.succ).symm (σ.order j.castSucc) = j.succ := by
    change Equiv.swap j.castSucc j.succ (σ.order.symm (σ.order j.castSucc)) = j.succ
    rw [originalPosition, Equiv.swap_apply_left]
  rw [swappedPosition] at atCoordinate
  simp only [Fin.val_succ, Fin.val_castSucc] at atCoordinate
  rw [if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _)] at atCoordinate
  omega

open KuhnScheduleModule

/-- A complete module execution for a simplex schedule. -/
noncomputable def simplexExecution (σ : GridSimplex p n) :
    theory.RewritePath (activePattern σ.schedule [])
      (donePattern (finalHistory σ.schedule [])) :=
  executionPath σ.schedule []

@[simp] theorem simplexExecution_length (σ : GridSimplex p n) :
    (simplexExecution σ).length = n + 1 := by
  simp [simplexExecution]

theorem simplexExecution_finalHistory (σ : GridSimplex p n) :
    finalHistory σ.schedule [] = σ.schedule.reverse := by
  simp [finalHistory_eq_reverse_append]

/-- The completed module terms retain the schedule distinction erased by the
geometric endpoint. -/
theorem swapStep_done_ne (σ : GridSimplex p (m + 1)) (j : Fin m) :
    donePattern (σ.swapStep j).schedule.reverse ≠
      donePattern σ.schedule.reverse := by
  intro same
  have decoded := congrArg (readState? (m + 1)) same
  simp [readState?, donePattern] at decoded
  exact swapStep_schedule_ne σ j decoded

/-! ## Positive and negative controls -/

namespace Controls

def squareSimplex : GridSimplex 1 2 :=
  ⟨fun _ => 0, 1⟩

@[simp] theorem squareSimplex_schedule :
    squareSimplex.schedule = [0, 1] := by
  decide

theorem zero_dimension_finishes :
    successors (activePattern ([] : List (Fin 0)) []) =
      [donePattern (n := 0) []] :=
  finish_exact []

theorem square_execution_visits_two_coordinates :
    (simplexExecution squareSimplex).length = 3 := by
  rw [simplexExecution_length]

theorem square_swap_changes_middle_vertex :
    (squareSimplex.swapStep 0).vertex 1 ≠ squareSimplex.vertex 1 := by
  exact swapStep_middle_vertex_ne squareSimplex 0

theorem square_swap_same_endpoint_different_history :
    runSchedule (fun i => (squareSimplex.base i : ℕ))
        (squareSimplex.swapStep 0).schedule =
      runSchedule (fun i => (squareSimplex.base i : ℕ)) squareSimplex.schedule ∧
    donePattern (squareSimplex.swapStep 0).schedule.reverse ≠
      donePattern squareSimplex.schedule.reverse := by
  exact ⟨swapStep_endpoint squareSimplex 0, swapStep_done_ne squareSimplex 0⟩

theorem duplicate_schedule_invalid :
    ¬IsCoordinateSchedule ([0, 0] : List (Fin 2)) := by
  decide

theorem omitted_schedule_invalid :
    ¬IsCoordinateSchedule ([0] : List (Fin 2)) := by
  decide

/-- Generic schedule execution retains duplicate occurrences even though such
a schedule does not denote a simplex. -/
theorem duplicate_schedule_still_executes :
    (executionPath ([0, 0] : List (Fin 2)) []).length = 3 := by
  simpa using executionPath_length ([0, 0] : List (Fin 2)) []

end Controls

/-! ## Axiom audit -/

#print axioms runSchedule_take_eq_vertex
#print axioms KuhnScheduleModule.successors_encodeState
#print axioms KuhnScheduleModule.executionPath_length
#print axioms swapStep_endpoint
#print axioms swapStep_middle_vertex_ne

end Mettapedia.Combinatorics.Kuhn.Operational
