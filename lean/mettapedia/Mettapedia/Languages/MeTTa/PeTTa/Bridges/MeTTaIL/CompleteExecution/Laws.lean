import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.LawsSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Lower
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

/-!
# The standard form of declared laws, in MeTTa

`gslt:laws:normalize` is `CollectionLaws.normalize`, `gslt:laws:extrude` is
`CollectionLaws.extrude` and `gslt:laws:standard` is `CollectionLaws.standardForm`, for every
pattern and every list of declared laws. A law is written `(CollectionLaw kind unit)` and a
scope-extrusion law `(Extrusion kind binder)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax PatternTreeSize CollectionLaws
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open StandardWire

/-! ## The data -/

abbrev lawsValue (laws : List Laws) : Atom := encoded (CettaWire.encodeList lawTerm laws)

abbrev extrusionsValue (extrusions : List Extrusion) : Atom := encoded (CettaWire.encodeList extrusionTerm extrusions)

/-- An encoded pattern is an expression, so no symbol matches it. -/
theorem pattern_symbol_unmatched (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String)
    (pattern : Pattern) :
    SpaceSemantics.matchValue bindings (.symbol name) (CettaWireAtom.encode (encodePattern pattern)) = none := by
  cases pattern <;> simp [encodePattern, CettaWireAtom.encode, SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

/-- Walk a body of the laws library. -/
syntax "laws_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| laws_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call laws_checked; metta_eval [$facts,*] with laws_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, pattern_symbol_unmatched,
        lawsValue, extrusionsValue, $extra,*]))

/-! ## Operations from below -/

theorem laws_append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:automata:append"
        [encoded (CettaWire.encodeList element left), encoded (CettaWire.encodeList element right)])
      state (encoded (CettaWire.encodeList element (left ++ right))) := by
  metta_lift laws_checked ["left", "right"] (complete_append_returns element state left right)

theorem laws_append_patterns_returns (state : State) (left right : List Pattern) :
    PureReturns lawsLibrary.runtime [] state (apply "gslt:automata:append" [patternsValue left, patternsValue right])
      state (patternsValue (left ++ right)) := by
  simpa only [patternsValue, encodePatterns_eq_encodeList] using laws_append_returns encodePattern state left right

theorem laws_length_returns (state : State) (items : List Pattern) :
    PureReturns lawsLibrary.runtime [] state (apply "gslt:automata:length" [patternsValue items]) state
      (number items.length) := by
  have below := complete_length_returns encodePattern state items
  rw [← encodePatterns_eq_encodeList] at below
  metta_lift laws_checked ["items"] below

theorem listNodes_sum : ∀ patterns : List Pattern, listNodes patterns = (patterns.map nodes).sum
  | [] => rfl
  | pattern :: rest => by simp [listNodes, listNodes_sum rest]

theorem laws_nodes_list_returns (state : State) (patterns : List Pattern) :
    PureReturns lawsLibrary.runtime [] state (apply "gslt:deep:nodes-list" [patternsValue patterns]) state
      (number (patterns.map nodes).sum) := by
  have below := nodes_list_of state patterns (fun pattern _ => nodes_returns state pattern)
  rw [listNodes_sum] at below
  metta_lift laws_checked ["patterns"] below

open PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower in
theorem laws_lift_bvars_list_returns (state : State) (cutoff shift : Nat) (patterns : List Pattern) :
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:rule:lift-bvars-list" [number cutoff, number shift, patternsValue patterns]) state
      (patternsValue (Substitution.liftBVarsList cutoff shift patterns)) := by
  have inScoped : PureReturns RuleExecutionProgram.scopedMachineProgram [] state
      (apply "gslt:rule:lift-bvars-list" [number cutoff, number shift, patternsValue patterns]) state
      (patternsValue (Substitution.liftBVarsList cutoff shift patterns)) :=
    transport_call rule_closed rule_agreement (by decide +kernel) (by decide) (by decide +kernel)
      (by decide) ["cutoff", "shift", "patterns"] (by decide) rfl (by decide +kernel)
      (RuleInstantiationExecution.lift_bvars_list_returns state cutoff shift patterns)
  have descent : PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:lift-bvars-list" [number cutoff, number shift, patternsValue patterns]) state
      (patternsValue (Substitution.liftBVarsList cutoff shift patterns)) := by
    metta_lift descent_checked ["cutoff", "shift", "patterns"]
      (by metta_lift typed_checked ["cutoff", "shift", "patterns"]
        (transport_call scopedMachine_closed scopedMachine_agreement (by decide +kernel) (by decide)
          (by decide +kernel) (by decide) ["cutoff", "shift", "patterns"] (by decide) rfl (by decide +kernel) inScoped))
  have complete : PureReturns runtime [] state
      (apply "gslt:rule:lift-bvars-list" [number cutoff, number shift, patternsValue patterns]) state
      (patternsValue (Substitution.liftBVarsList cutoff shift patterns)) := by
    metta_lift complete_checked ["cutoff", "shift", "patterns"] descent
  metta_lift laws_checked ["cutoff", "shift", "patterns"] complete

/-! ## Collection laws -/

@[metta_head "gslt:laws:law-for"]
theorem law_for_returns (state : State) (kind : CollType) : ∀ laws : List Laws,
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:law-for" [lawsValue laws, encoded (encodeCollectionType kind)]) state
      (encoded (encodeOption lawTerm (lawFor laws kind)))
  | [] => by laws_eval unfolding [CettaWire.encodeList, lawFor]
  | law :: rest => by
    have later := law_for_returns state kind rest
    by_cases same : law.kind = kind
    · laws_eval [later] unfolding [CettaWire.encodeList, lawTerm, lawFor, same]
    · have different : encodeCollectionType law.kind ≠ encodeCollectionType kind :=
        fun equal => same (encodeCollectionType_injective equal)
      laws_eval [later] unfolding [CettaWire.encodeList, lawTerm, lawFor, same, different]

@[metta_head "gslt:laws:splice"]
theorem splice_returns (state : State) (law : Laws) (item : Pattern) :
    PureReturns lawsLibrary.runtime [] state (apply "gslt:laws:splice" [encoded (lawTerm law), patternValue item])
      state (patternsValue (splice law item)) := by
  obtain ⟨kind, unit⟩ := law
  cases item with
  | collection actual elements rest =>
    cases rest with
    | none =>
      by_cases same : actual = kind
      · subst same
        laws_eval unfolding [lawTerm, splice, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]
      · have different : encodeCollectionType actual ≠ encodeCollectionType kind :=
          fun equal => same (encodeCollectionType_injective equal)
        laws_eval unfolding [lawTerm, splice, same, different, patternValue, patternsValue, encodePattern,
          encodePatterns, encodeRest]
    | some name =>
      laws_eval unfolding [lawTerm, splice, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]
  | apply label arguments =>
    cases arguments with
    | nil =>
      cases unit with
      | none =>
        laws_eval unfolding [lawTerm, unitTerm, splice, patternValue, patternsValue, encodePattern, encodePatterns]
      | some name =>
        by_cases same : label = name
        · subst same
          laws_eval unfolding [lawTerm, unitTerm, splice, patternValue, patternsValue, encodePattern, encodePatterns]
        · have different : label ≠ name := same
          laws_eval unfolding [lawTerm, unitTerm, splice, same, Ne.symm different, patternValue, patternsValue,
            encodePattern, encodePatterns]
    | cons first others =>
      laws_eval unfolding [lawTerm, splice, patternValue, patternsValue, encodePattern, encodePatterns]
  | _ => laws_eval unfolding [lawTerm, splice, patternValue, patternsValue, encodePattern, encodePatterns,
      encodeBinder]

@[metta_head "gslt:laws:splice-all"]
theorem splice_all_returns (state : State) (law : Laws) : ∀ items : List Pattern,
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:splice-all" [encoded (lawTerm law), patternsValue items]) state
      (patternsValue (items.flatMap (splice law)))
  | [] => by laws_eval unfolding [patternsValue, encodePatterns]
  | item :: rest => by
    have here := splice_returns state law item
    have later := splice_all_returns state law rest
    have joined := laws_append_patterns_returns state (splice law item) (rest.flatMap (splice law))
    laws_eval [here, later, joined] unfolding [patternsValue, encodePatterns, List.flatMap_cons]

/-- What `gslt:laws:normalize` returns. -/
abbrev NormalizeAt (state : State) (laws : List Laws) (pattern : Pattern) : Prop :=
  PureReturns lawsLibrary.runtime [] state (apply "gslt:laws:normalize" [lawsValue laws, patternValue pattern])
    state (patternValue (CollectionLaws.normalize laws pattern))

@[metta_head "gslt:laws:normalize-list"]
theorem normalize_list_of (state : State) (laws : List Laws) : ∀ patterns : List Pattern,
    (∀ pattern ∈ patterns, NormalizeAt state laws pattern) →
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:normalize-list" [lawsValue laws, patternsValue patterns]) state
      (patternsValue (patterns.map (CollectionLaws.normalize laws)))
  | [], _ => by laws_eval unfolding [patternsValue, encodePatterns]
  | pattern :: rest, each => by
    have here := each pattern (by simp)
    have later := normalize_list_of state laws rest (fun other member => each other (by simp [member]))
    laws_eval [here, later] unfolding [patternsValue, patternValue, encodePatterns, List.map_cons]

/-- **`gslt:laws:normalize` is `CollectionLaws.normalize`.** -/
@[metta_head "gslt:laws:normalize"]
theorem normalize_returns (state : State) (laws : List Laws) (pattern : Pattern) :
    NormalizeAt state laws pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => laws_eval unfolding [CollectionLaws.normalize, patternValue, encodePattern]
  | hfvar name => laws_eval unfolding [CollectionLaws.normalize, patternValue, encodePattern]
  | happly label arguments ih =>
    have inner := normalize_list_of state laws arguments ih
    laws_eval [inner] unfolding [CollectionLaws.normalize, patternValue, patternsValue, encodePattern]
  | hlambda binder body ih =>
    laws_eval [ih] unfolding [NormalizeAt, CollectionLaws.normalize, patternValue, encodePattern]
  | hmultiLambda arity binders body ih =>
    laws_eval [ih] unfolding [NormalizeAt, CollectionLaws.normalize, patternValue, encodePattern]
  | hsubst body replacement bodyIH replacementIH =>
    laws_eval [bodyIH, replacementIH] unfolding [NormalizeAt, CollectionLaws.normalize, patternValue, encodePattern]
  | hcollection kind elements rest ih =>
    have inner := normalize_list_of state laws elements ih
    have found := law_for_returns state kind laws
    cases law : lawFor laws kind with
    | none =>
      have shape : CollectionLaws.normalize laws (.collection kind elements rest) =
          .collection kind (elements.map (CollectionLaws.normalize laws)) rest := by
        rw [CollectionLaws.normalize]; simp only [lawFor] at law; simp [law]
      rw [law] at found
      laws_eval [inner, found] unfolding [NormalizeAt, shape, patternValue, patternsValue, encodePattern]
    | some found' =>
      have shape : CollectionLaws.normalize laws (.collection kind elements rest) =
          .collection kind ((elements.map (CollectionLaws.normalize laws)).flatMap (splice found')) rest := by
        rw [CollectionLaws.normalize]; simp only [lawFor] at law; simp [law]
      rw [law] at found
      have spliced := splice_all_returns state found' (elements.map (CollectionLaws.normalize laws))
      laws_eval [inner, found, spliced] unfolding [NormalizeAt, shape, patternValue, patternsValue, encodePattern]

/-! ## Scope extrusion -/

/-- The extrusion for a kind. -/
abbrev extrusionFor (extrusions : List Extrusion) (kind : CollType) : Option Extrusion :=
  extrusions.find? (·.kind = kind)

@[metta_head "gslt:laws:extrusion-for"]
theorem extrusion_for_returns (state : State) (kind : CollType) : ∀ extrusions : List Extrusion,
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:extrusion-for" [extrusionsValue extrusions, encoded (encodeCollectionType kind)]) state
      (encoded (encodeOption extrusionTerm (extrusionFor extrusions kind)))
  | [] => by laws_eval unfolding [CettaWire.encodeList, extrusionFor]
  | extrusion :: rest => by
    have later := extrusion_for_returns state kind rest
    by_cases same : extrusion.kind = kind
    · laws_eval [later] unfolding [CettaWire.encodeList, extrusionTerm, extrusionFor, same]
    · have different : encodeCollectionType extrusion.kind ≠ encodeCollectionType kind :=
        fun equal => same (encodeCollectionType_injective equal)
      laws_eval [later] unfolding [CettaWire.encodeList, extrusionTerm, extrusionFor, same, different]

@[metta_head "gslt:laws:body-items"]
theorem body_items_returns (state : State) (kind : CollType) (body : Pattern) :
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:body-items" [encoded (encodeCollectionType kind), patternValue body]) state
      (patternsValue (bodyItems kind body)) := by
  cases body with
  | collection actual elements rest =>
    cases rest with
    | none =>
      by_cases same : actual = kind
      · subst same
        laws_eval unfolding [bodyItems, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]
      · have different : encodeCollectionType actual ≠ encodeCollectionType kind :=
          fun equal => same (encodeCollectionType_injective equal)
        laws_eval unfolding [bodyItems, same, different, patternValue, patternsValue, encodePattern, encodePatterns,
          encodeRest]
    | some name =>
      laws_eval unfolding [bodyItems, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]
  | multiLambda arity binders body =>
    cases binders <;>
      laws_eval unfolding [bodyItems, patternValue, patternsValue, encodePattern, encodePatterns,
        InferenceCettaWire.encodeList, CettaWire.encodeList]
  | _ => laws_eval unfolding [bodyItems, patternValue, patternsValue, encodePattern, encodePatterns, encodeBinder]

/-- What `gslt:laws:hoist` returns. -/
abbrev HoistAt (state : State) (extrusion : Extrusion) (fuel : Nat) (done todo : List Pattern) : Prop :=
  PureReturns lawsLibrary.runtime [] state
    (apply "gslt:laws:hoist" [encoded (extrusionTerm extrusion), number fuel, patternsValue done, patternsValue todo])
    state (patternValue (hoist extrusion fuel done todo))

/-- An element that is not hoisted: it joins the done list and hoisting goes on. -/
syntax "hoist_kept" " [" term,* "]" : tactic
macro_rules
  | `(tactic| hoist_kept [$facts,*]) => `(tactic|
      laws_eval [$facts,*] unfolding [HoistAt, hoist, extrusionTerm, patternValue, patternsValue, encodePattern,
        encodePatterns, encodeBinder, encodeRest, InferenceCettaWire.encodeList])

@[metta_head "gslt:laws:hoist"]
theorem hoist_returns (state : State) (extrusion : Extrusion) :
    ∀ (fuel : Nat) (done todo : List Pattern), HoistAt state extrusion fuel done todo
  | 0, done, todo => by
    have all := laws_append_patterns_returns state done todo
    laws_eval [all] unfolding [HoistAt, hoist, extrusionTerm, patternValue, patternsValue, encodePattern,
      encodeRest]
  | fuel + 1, done, [] => by
    laws_eval unfolding [HoistAt, hoist, extrusionTerm, patternValue, patternsValue, encodePattern, encodePatterns,
      encodeRest]
  | fuel + 1, done, item :: todo => by
    have kept := laws_append_patterns_returns state done [item]
    have later := hoist_returns state extrusion fuel (done ++ [item]) todo
    obtain ⟨kind, binder⟩ := extrusion
    cases item with
    | apply label arguments =>
      cases arguments with
      | cons first others =>
        cases others with
        | nil =>
          cases first with
          | lambda display body =>
            by_cases same : label = binder
            · subst same
              have inner := body_items_returns state kind body
              have liftedDone := laws_lift_bvars_list_returns state 0 1 done
              have liftedRest := laws_lift_bvars_list_returns state 0 1 todo
              rw [Substitution.liftBVarsList_eq_map] at liftedDone liftedRest
              have remaining := laws_append_patterns_returns state (bodyItems kind body)
                (todo.map (Substitution.liftBVars 0 1))
              have hoisted := hoist_returns state ⟨kind, label⟩ fuel (done.map (Substitution.liftBVars 0 1))
                (bodyItems kind body ++ todo.map (Substitution.liftBVars 0 1))
              hoist_kept [inner, liftedDone, liftedRest, remaining, hoisted]
            · have different : Term.string label ≠ Term.string binder := fun equal => same (by cases equal; rfl)
              laws_eval [kept, later] unfolding [HoistAt, hoist, same, different, extrusionTerm, patternValue,
                patternsValue, encodePattern, encodePatterns, encodeBinder, encodeRest, InferenceCettaWire.encodeList]
          | _ => hoist_kept [kept, later]
        | cons second more => hoist_kept [kept, later]
      | nil => hoist_kept [kept, later]
    | _ => hoist_kept [kept, later]

/-- What `gslt:laws:extrude` returns. -/
abbrev ExtrudeAt (state : State) (extrusions : List Extrusion) (pattern : Pattern) : Prop :=
  PureReturns lawsLibrary.runtime [] state (apply "gslt:laws:extrude" [extrusionsValue extrusions, patternValue pattern])
    state (patternValue (extrude extrusions pattern))

@[metta_head "gslt:laws:extrude-list"]
theorem extrude_list_of (state : State) (extrusions : List Extrusion) : ∀ patterns : List Pattern,
    (∀ pattern ∈ patterns, ExtrudeAt state extrusions pattern) →
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:extrude-list" [extrusionsValue extrusions, patternsValue patterns]) state
      (patternsValue (patterns.map (extrude extrusions)))
  | [], _ => by laws_eval unfolding [patternsValue, encodePatterns]
  | pattern :: rest, each => by
    have here := each pattern (by simp)
    have later := extrude_list_of state extrusions rest (fun other member => each other (by simp [member]))
    laws_eval [here, later] unfolding [patternsValue, patternValue, encodePatterns, List.map_cons]

/-- **`gslt:laws:extrude` is `CollectionLaws.extrude`.** -/
@[metta_head "gslt:laws:extrude"]
theorem extrude_returns (state : State) (extrusions : List Extrusion) (pattern : Pattern) :
    ExtrudeAt state extrusions pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => laws_eval unfolding [extrude, patternValue, encodePattern]
  | hfvar name => laws_eval unfolding [extrude, patternValue, encodePattern]
  | happly label arguments ih =>
    have inner := extrude_list_of state extrusions arguments ih
    laws_eval [inner] unfolding [extrude, patternValue, patternsValue, encodePattern]
  | hlambda binder body ih =>
    laws_eval [ih] unfolding [ExtrudeAt, extrude, patternValue, encodePattern]
  | hmultiLambda arity binders body ih =>
    laws_eval [ih] unfolding [ExtrudeAt, extrude, patternValue, encodePattern]
  | hsubst body replacement bodyIH replacementIH =>
    laws_eval [bodyIH, replacementIH] unfolding [ExtrudeAt, extrude, patternValue, encodePattern]
  | hcollection kind elements rest ih =>
    have inner := extrude_list_of state extrusions elements ih
    cases rest with
    | some name =>
      laws_eval [inner] unfolding [ExtrudeAt, extrude, patternValue, patternsValue, encodePattern, encodeRest]
    | none =>
      have found := extrusion_for_returns state kind extrusions
      cases chosen : extrusionFor extrusions kind with
      | none =>
        have shape : extrude extrusions (.collection kind elements none) =
            .collection kind (elements.map (extrude extrusions)) none := by
          rw [extrude]; simp only [extrusionFor] at chosen; simp [chosen]
        rw [chosen] at found
        laws_eval [inner, found] unfolding [ExtrudeAt, shape, patternValue, patternsValue, encodePattern, encodeRest]
      | some extrusion =>
        have size := laws_nodes_list_returns state (elements.map (extrude extrusions))
        have count := laws_length_returns state (elements.map (extrude extrusions))
        have hoisted := hoist_returns state extrusion
          (((elements.map (extrude extrusions)).map nodes).sum + ((elements.map (extrude extrusions)).map nodes).sum +
            (elements.map (extrude extrusions)).length + 1) [] (elements.map (extrude extrusions))
        have shape : extrude extrusions (.collection kind elements none) =
            hoist extrusion (((elements.map (extrude extrusions)).map nodes).sum +
              ((elements.map (extrude extrusions)).map nodes).sum + (elements.map (extrude extrusions)).length + 1)
              [] (elements.map (extrude extrusions)) := by
          rw [extrude]; simp only [extrusionFor] at chosen; simp only [chosen]; congr 1; omega
        rw [chosen] at found
        laws_eval [inner, found, size, count, hoisted]
          unfolding [ExtrudeAt, HoistAt, shape, patternValue, patternsValue, encodePattern, encodePatterns, encodeRest]

/-- **`gslt:laws:standard` is `CollectionLaws.standardForm`.** -/
@[metta_head "gslt:laws:standard"]
theorem standard_returns (state : State) (laws : List Laws) (extrusions : List Extrusion) (pattern : Pattern) :
    PureReturns lawsLibrary.runtime [] state
      (apply "gslt:laws:standard" [lawsValue laws, extrusionsValue extrusions, patternValue pattern]) state
      (patternValue (standardForm laws extrusions pattern)) := by
  have normal := normalize_returns state laws pattern
  have extruded := extrude_returns state extrusions (CollectionLaws.normalize laws pattern)
  laws_eval [normal, extruded] unfolding [standardForm, NormalizeAt, ExtrudeAt]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
