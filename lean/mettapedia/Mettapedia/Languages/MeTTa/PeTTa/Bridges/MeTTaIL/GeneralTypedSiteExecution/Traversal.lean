import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution

/-!
# Grammar-driven typed traversal in the authored PeTTa enumerator

Execution follows the original typed-site generator. Intermediate loops retain
physical list indices and declaration alternatives; recursive premises below are
supplied by the structural induction on the original subject.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution

open Mettapedia.GSLT.LanguageDef CettaWire WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts GeneralTypedSites GeneralRuleJobs
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval
open ScopedRuleJobReadoutExecution (siteTerm typingFrameTerm)
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm typingDeclarationTerm)
open InferenceCettaWire (encodePattern encodePatterns)
open PremiseOperationsExecution.DeclarationTyping (declarationsTerm freeContextTerm boundContextTerm)
open PremiseOperationsExecution.GeneralExecution.EnvironmentExecution (named_let_returns bool_if_returns)

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev sitesValue (sites : List SiteData) : Atom := encoded (encodeList siteTerm sites)
private abbrev listValue (values : List Term) : Atom := encoded (encodeList id values)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (encodePatterns patterns)
private abbrev permissionsValue (permissions : OperationalPermissions) : Atom :=
  encoded (InferenceCettaWire.ContextObservation.permissionsTerm permissions)

private def generateValues (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) : List Atom :=
  [encoded (declarationsTerm language.terms), encoded (freeContextTerm free), permissionsValue permissions,
   encoded (boundContextTerm bound), encoded (typeTerm expected), encoded (encodePattern source)]

private def collectionChildrenValues (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (type : TypeExpr) (kind : CollType)
    (elements : List Pattern) (origin : TypingFrame) (remaining : List Pattern) (index : Nat) : List Atom :=
  [encoded (declarationsTerm language.terms), encoded (freeContextTerm free), permissionsValue permissions,
   encoded (boundContextTerm bound), encoded (typeTerm type), encoded (InferenceCettaWire.encodeCollectionType kind),
   patternsValue elements, encoded (typingFrameTerm origin), patternsValue remaining, number index]

private def collectionChildrenSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (type : TypeExpr) (kind : CollType)
    (elements : List Pattern) (origin : TypingFrame) (remaining : List Pattern) (index : Nat) : List SiteData :=
  (remaining.zipIdx index).flatMap fun (element, position) =>
    (generate language (FreeTypeContext.ofList free) permissions bound type element).map
      (SiteData.wrapCollection origin kind elements position)

private def collectionChildrenPairs : List (Atom × Atom) :=
  [(v "next", a "+" [v "index", number 1]),
   (v "sites", a Helper.generate.head [v "declarations", v "free", v "permissions", v "bound", v "type", v "element"]),
   (v "before", a Helper.take.head [v "index", v "elements"]),
   (v "after", a Helper.drop.head [v "next", v "elements"]),
   (v "here", a Helper.wrapCollection.head [v "frame", v "kind", v "before", v "index", v "after", v "sites"]),
   (v "tail", a Helper.collectionChildren.head [v "declarations", v "free", v "permissions", v "bound", v "type",
      v "kind", v "elements", v "frame", v "rest", v "next"])]

private def collectionChildrenBody : Atom := a "let*"
  [.expression (collectionChildrenPairs.map fun pair => .expression [pair.1, pair.2]),
   a "gslt:automata:append" [v "here", v "tail"]]

private def collectionChildrenCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "element", v "rest"], collectionChildrenBody)]

private theorem collection_children_shape : (equation .collectionChildren).body =
    a "case" [v "remaining", .expression (collectionChildrenCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem collection_children_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (type : TypeExpr) (kind : CollType) (elements : List Pattern) (origin : TypingFrame)
    (remaining : List Pattern) (index : Nat)
    (children : ∀ element ∈ remaining,
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type element)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type element))) :
    PureReturns program [] state
      (a Helper.collectionChildren.head (collectionChildrenValues language free permissions bound type kind elements origin remaining index)) state
      (sitesValue (collectionChildrenSites language free permissions bound type kind elements origin remaining index)) := by
  induction remaining generalizing index with
  | nil =>
      let values := collectionChildrenValues language free permissions bound type kind elements origin [] index
      let caller := environment .collectionChildren values
      apply helper_call .collectionChildren [] state _ values _ rfl
        (by simp only [values, collectionChildrenValues, List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [collection_children_shape]
      apply case_returns program caller caller state state state (v "remaining") (.symbol "LNil")
        (.symbol "LNil") _ _ collectionChildrenCases (read_cases_encoded _)
      · simpa [caller, values, collectionChildrenValues, environment, Helper.names, patternsValue, encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "remaining"
      · simp [collectionChildrenCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons element remaining ih =>
      let values := collectionChildrenValues language free permissions bound type kind elements origin (element :: remaining) index
      let caller := environment .collectionChildren values
      let selected := ("rest", patternsValue remaining) :: ("element", encoded (encodePattern element)) :: caller
      let next := ("next", number (index + 1)) :: selected
      let generated := generate language (FreeTypeContext.ofList free) permissions bound type element
      let sites := ("sites", sitesValue generated) :: next
      let before := ("before", patternsValue (elements.take index)) :: sites
      let after := ("after", patternsValue (elements.drop (index + 1))) :: before
      let headSites := generated.map (SiteData.wrapCollection origin kind elements index)
      let here := ("here", sitesValue headSites) :: after
      let restSites := collectionChildrenSites language free permissions bound type kind elements origin remaining (index + 1)
      let final := ("tail", sitesValue restSites) :: here
      apply helper_call .collectionChildren [] state _ values _ rfl
        (by simp only [values, collectionChildrenValues, List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [collection_children_shape]
      apply case_returns program caller selected state state state (v "remaining") (patternsValue (element :: remaining))
        collectionChildrenBody _ _ collectionChildrenCases (read_cases_encoded _)
      · simpa [caller, values, collectionChildrenValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "remaining"
      · simp [collectionChildrenCases, patternsValue, encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
      · unfold collectionChildrenBody
        apply PureData.let_bindings_return (final := final) (middle := state) (pairs := collectionChildrenPairs)
        · apply PureData.BindingsReturn.cons (bound := next) (value := number (index + 1))
          · apply add_one_returns selected state index "index"
            simp [selected, caller, values, collectionChildrenValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, next,
              selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := sites) (value := sitesValue generated)
            · apply helper_capture .generate next state _ (generateValues language free permissions bound type element) _ rfl
                _ (children element (by simp))
              simp [generateValues, next, selected, caller, values, collectionChildrenValues, environment, Helper.names,
                applySubst, Subst.lookup]
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, sites, next,
                selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := before) (value := patternsValue (elements.take index))
              · have returned := take_returns state index (elements.map encodePattern)
                change PureReturns program [] state (a Helper.take.head [number index, listValue (elements.map encodePattern)]) state
                  (listValue ((elements.map encodePattern).take index)) at returned
                simp only [← List.map_take, listValue, encodeList_map, Function.comp_def, id_eq,
                  ← InferenceCettaWire.encodePatterns_eq_encodeList] at returned
                apply helper_capture .take sites state _ [number index, patternsValue elements] _ rfl _ returned
                simp [sites, next, selected, caller, values, collectionChildrenValues, environment, Helper.names,
                  applySubst, Subst.lookup]
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, before, sites, next,
                  selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := after) (value := patternsValue (elements.drop (index + 1)))
                · have returned := drop_returns state (index + 1) (elements.map encodePattern)
                  change PureReturns program [] state (a Helper.drop.head [number (index + 1), listValue (elements.map encodePattern)]) state
                    (listValue ((elements.map encodePattern).drop (index + 1))) at returned
                  simp only [← List.map_drop, listValue, encodeList_map, Function.comp_def, id_eq,
                    ← InferenceCettaWire.encodePatterns_eq_encodeList] at returned
                  apply helper_capture .drop before state _ [number (index + 1), patternsValue elements] _ rfl _ returned
                  simp [before, sites, next, selected, caller, values, collectionChildrenValues, environment, Helper.names,
                    applySubst, Subst.lookup]
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, after, before, sites, next,
                    selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
                · apply PureData.BindingsReturn.cons (bound := here) (value := sitesValue headSites)
                  · apply helper_capture .wrapCollection after state _
                      [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind),
                       patternsValue (elements.take index), number index, patternsValue (elements.drop (index + 1)), sitesValue generated]
                      _ rfl _ (wrap_collection_returns state origin kind elements index generated)
                    simp [after, before, sites, next, selected, caller, values, collectionChildrenValues, environment, Helper.names,
                      applySubst, Subst.lookup]
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, here, after, before, sites, next,
                      selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
                  · apply PureData.BindingsReturn.cons (bound := final) (value := sitesValue restSites)
                    · apply helper_capture .collectionChildren here state _
                        (collectionChildrenValues language free permissions bound type kind elements origin remaining (index + 1)) _ rfl
                        _ (ih (index + 1) (fun child member => children child (by simp [member])))
                      simp [here, after, before, sites, next, selected, caller, values, collectionChildrenValues, environment, Helper.names,
                        applySubst, Subst.lookup]
                    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, here, after, before, sites, next,
                        selected, caller, values, collectionChildrenValues, environment, Helper.names, Subst.lookup]
                    · exact .nil _ _
        · have returned := append_values_returns final state (headSites.map siteTerm) (restSites.map siteTerm) "here" "tail"
            (by simp [final, here, sitesValue, MatchAutomataSourceExecution.listValue, encodeList_map,
              applySubst, Subst.lookup])
          simpa only [collectionChildrenSites, List.zipIdx_cons, List.flatMap_cons,
            headSites, restSites, generated, sitesValue, MatchAutomataSourceExecution.listValue,
            ← List.map_append, encodeList_map, Function.comp_def, id_eq] using returned


private theorem collection_code_injective : Function.Injective InferenceCettaWire.encodeCollectionType := by
  intro left right equal
  cases left <;> cases right <;> simp_all [InferenceCettaWire.encodeCollectionType]

private def directCollectionValues (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (kind : CollType)
    (elements : List Pattern) : List Atom :=
  [encoded (declarationsTerm language.terms), encoded (freeContextTerm free), permissionsValue permissions,
   encoded (boundContextTerm bound), encoded (typeTerm expected), encoded (InferenceCettaWire.encodeCollectionType kind),
   patternsValue elements]

private def directCollectionSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (kind : CollType)
    (elements : List Pattern) : List SiteData :=
  match expected with
  | .collection actual type =>
      if actual = kind ∧ checkElementsHaveType language (FreeTypeContext.ofList free) bound elements type = true then
        collectionChildrenSites language free permissions bound type kind elements (.directCollection kind) elements 0
      else []
  | _ => []

private def directCollectionBody : Atom := a "if"
  [a "==" [v "actual", v "kind"],
   a "if" [a "gslt:premise:type-elements" [v "declarations", v "free", v "bound", v "elements", v "type"],
     a "let" [v "frame", a "TypingDirectCollection" [v "kind"],
       a Helper.collectionChildren.head [v "declarations", v "free", v "permissions", v "bound", v "type",
         v "kind", v "elements", v "frame", v "elements", number 0]],
     .symbol "LNil"],
   .symbol "LNil"]

private def directCollectionCases : SpaceSemantics.Cases :=
  [(a "TCollection" [v "actual", v "type"], directCollectionBody), (v "other", .symbol "LNil")]

private theorem direct_collection_shape : (equation .directCollection).body =
    a "case" [v "expected", .expression (directCollectionCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem direct_collection_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (kind : CollType) (elements : List Pattern)
    (children : ∀ type element, element ∈ elements →
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type element)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type element))) :
    PureReturns program [] state
      (a Helper.directCollection.head (directCollectionValues language free permissions bound expected kind elements)) state
      (sitesValue (directCollectionSites language free permissions bound expected kind elements)) := by
  let values := directCollectionValues language free permissions bound expected kind elements
  let caller := environment .directCollection values
  apply helper_call .directCollection [] state _ values _ rfl
    (by simp only [values, directCollectionValues, List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [direct_collection_shape]
  cases expected with
  | collection actual type =>
      let selected := ("type", encoded (typeTerm type)) ::
        ("actual", encoded (InferenceCettaWire.encodeCollectionType actual)) :: caller
      apply case_returns program caller selected state state state (v "expected") (encoded (typeTerm (.collection actual type)))
        directCollectionBody _ _ directCollectionCases (read_cases_encoded _)
      · simpa [caller, values, directCollectionValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "expected"
      · simp [directCollectionCases, typeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, values, directCollectionValues, environment, Helper.names, Subst.lookup]
      · unfold directCollectionBody
        apply bool_if_returns program selected state _ (decide (actual = kind))
        · have returned := CettaWireAtom.equality_captured_returns program selected state
            (InferenceCettaWire.encodeCollectionType actual) (InferenceCettaWire.encodeCollectionType kind) "actual" "kind"
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, values, directCollectionValues, environment, Helper.names, applySubst, Subst.lookup])
          simpa only [collection_code_injective.eq_iff] using returned
        · by_cases same : actual = kind
          · subst actual
            simp only [decide_true, ite_true]
            apply bool_if_returns program selected state _
              (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements type)
            · apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
              apply PremiseOperationsExecution.DeclarationTyping.check_elements_have_type_captured_returns
                selected state language free bound elements type
              simp [selected, caller, values, directCollectionValues, environment, Helper.names, applySubst, Subst.lookup]
            · cases checked : checkElementsHaveType language (FreeTypeContext.ofList free) bound elements type with
              | false =>
                  simpa [directCollectionSites, checked, sitesValue, encodeList, CettaWireAtom.encode] using
                    symbol_returns program selected state "LNil"
              | true =>
                  simp only [checked, ite_true, directCollectionSites, true_and]
                  let frame := encoded (typingFrameTerm (.directCollection kind))
                  let final := ("frame", frame) :: selected
                  apply named_let_returns program selected state "frame" _ frame
                  · simp [selected, caller, values, directCollectionValues, environment, Helper.names, Subst.lookup]
                  · have templated : PureData.Template program (a "TypingDirectCollection" [v "kind"]) :=
                      data_template _ _ (by decide) (by
                        intro child member
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                        subst child
                        exact PureData.Template.captured "kind")
                    simpa [frame, typingFrameTerm, selected, caller, values, directCollectionValues, environment, Helper.names,
                      CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
                      PureData.template_return program selected state _ templated
                  · apply helper_capture .collectionChildren final state _
                      (collectionChildrenValues language free permissions bound type kind elements (.directCollection kind) elements 0)
                      _ rfl _ (collection_children_returns_of state language free permissions bound type kind elements
                        (.directCollection kind) elements 0 (children type))
                    simp [final, frame, selected, caller, values, directCollectionValues, collectionChildrenValues,
                      environment, Helper.names, applySubst, Subst.lookup]
          · simpa [same, directCollectionSites, sitesValue, encodeList, CettaWireAtom.encode] using
              symbol_returns program selected state "LNil"
  | base sort | arrow domain codomain | multiBinder domain =>
      all_goals
        apply case_returns program caller (("other", applySubst caller (v "expected")) :: caller) state state state
          (v "expected") (applySubst caller (v "expected")) (.symbol "LNil") _ _ directCollectionCases (read_cases_encoded _)
        · simpa [caller, values, directCollectionValues, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns program caller state "expected"
        · simp [directCollectionCases, typeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, caller, values, directCollectionValues, environment, Helper.names, applySubst, Subst.lookup]
        · exact symbol_returns program _ state "LNil"


private inductive DeclarationTraversal where | application | collection

private def DeclarationTraversal.rows : DeclarationTraversal → Helper
  | .application => .applicationRows | .collection => .collectionRows
private def DeclarationTraversal.row : DeclarationTraversal → Helper
  | .application => .applicationRow | .collection => .collectionRow
private def DeclarationTraversal.selector : DeclarationTraversal → String
  | .application => "constructor" | .collection => "kind"
private def DeclarationTraversal.subjects : DeclarationTraversal → String
  | .application => "arguments" | .collection => "elements"

private def rowPrefix (form : DeclarationTraversal) : List Atom :=
  [v "declarations", v "free", v "permissions", v "bound", v "expected", v form.selector, v form.subjects]

private def rowValues (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (selector : Term) (subjects : List Pattern) : List Atom :=
  [encoded (declarationsTerm language.terms), encoded (freeContextTerm free), permissionsValue permissions,
   encoded (boundContextTerm bound), encoded (typeTerm expected), encoded selector, patternsValue subjects]

private def declarationRowsPairs (form : DeclarationTraversal) : List (Atom × Atom) :=
  [(v "here", a form.row.head (rowPrefix form ++ [v "row", v "index"])),
   (v "next", a "+" [v "index", number 1]),
   (v "tail", a form.rows.head (rowPrefix form ++ [v "rest", v "next"]))]

private def declarationRowsBody (form : DeclarationTraversal) : Atom := a "let*"
  [.expression ((declarationRowsPairs form).map fun pair => .expression [pair.1, pair.2]),
   a "gslt:automata:append" [v "here", v "tail"]]

private def declarationRowsCases (form : DeclarationTraversal) : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "row", v "rest"], declarationRowsBody form)]

private theorem declaration_rows_shape (form : DeclarationTraversal) : (equation form.rows).body =
    a "case" [v "remaining", .expression ((declarationRowsCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private theorem declaration_rows_returns_of (form : DeclarationTraversal) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (permissions : OperationalPermissions)
    (bound : List TypeExpr) (expected : TypeExpr) (selector : Term) (subjects : List Pattern)
    (selectedSites : GrammarRule → Nat → List SiteData) (remaining : List GrammarRule) (index : Nat)
    (rows : ∀ row ∈ remaining, ∀ declaration,
      PureReturns program [] state
        (a form.row.head (rowValues language free permissions bound expected selector subjects ++
          [encoded (typingDeclarationTerm row), number declaration])) state (sitesValue (selectedSites row declaration))) :
    PureReturns program [] state
      (a form.rows.head (rowValues language free permissions bound expected selector subjects ++
        [encoded (declarationsTerm remaining), number index])) state
      (sitesValue ((remaining.zipIdx index).flatMap fun (row, declaration) => selectedSites row declaration)) := by
  induction remaining generalizing index with
  | nil =>
      let values := rowValues language free permissions bound expected selector subjects ++
        [encoded (declarationsTerm []), number index]
      let caller := environment form.rows values
      apply helper_call form.rows [] state _ values _ (by cases form <;> rfl)
        (by simp only [values, rowValues, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [declaration_rows_shape]
      apply case_returns program caller caller state state state (v "remaining") (.symbol "LNil")
        (.symbol "LNil") _ _ (declarationRowsCases form) (read_cases_encoded _)
      · cases form <;> simpa [caller, values, rowValues, environment, Helper.names, DeclarationTraversal.rows,
          declarationsTerm, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "remaining"
      · simp [declarationRowsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons row remaining ih =>
      let values := rowValues language free permissions bound expected selector subjects ++
        [encoded (declarationsTerm (row :: remaining)), number index]
      let caller := environment form.rows values
      let selected := ("rest", encoded (declarationsTerm remaining)) :: ("row", encoded (typingDeclarationTerm row)) :: caller
      let headSites := selectedSites row index
      let restSites := (remaining.zipIdx (index + 1)).flatMap fun (row, declaration) => selectedSites row declaration
      let here := ("here", sitesValue headSites) :: selected
      let next := ("next", number (index + 1)) :: here
      let final := ("tail", sitesValue restSites) :: next
      apply helper_call form.rows [] state _ values _ (by cases form <;> rfl)
        (by simp only [values, rowValues, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [declaration_rows_shape]
      apply case_returns program caller selected state state state (v "remaining") (encoded (declarationsTerm (row :: remaining)))
        (declarationRowsBody form) _ _ (declarationRowsCases form) (read_cases_encoded _)
      · cases form <;> simpa [caller, values, rowValues, environment, Helper.names, DeclarationTraversal.rows,
          applySubst, Subst.lookup] using variable_returns program caller state "remaining"
      · cases form <;> simp [declarationRowsCases, declarationsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, rowValues, environment, Helper.names, DeclarationTraversal.rows, Subst.lookup]
      · unfold declarationRowsBody
        apply PureData.let_bindings_return (final := final) (middle := state) (pairs := declarationRowsPairs form)
        · apply PureData.BindingsReturn.cons (bound := here) (value := sitesValue headSites)
          · apply helper_capture form.row selected state _
              (rowValues language free permissions bound expected selector subjects ++ [encoded (typingDeclarationTerm row), number index])
              _ (by cases form <;> rfl) _ (rows row (by simp) index)
            cases form <;> simp [rowPrefix, selected, caller, values, rowValues, environment, Helper.names,
              DeclarationTraversal.rows, DeclarationTraversal.selector, DeclarationTraversal.subjects, applySubst, Subst.lookup]
          · cases form <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, here, selected,
              caller, values, rowValues, environment, Helper.names, DeclarationTraversal.rows, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := next) (value := number (index + 1))
            · apply add_one_returns here state index "index"
              cases form <;> simp [here, selected, caller, values, rowValues, environment, Helper.names,
                DeclarationTraversal.rows, applySubst, Subst.lookup]
            · cases form <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, next, here, selected,
                caller, values, rowValues, environment, Helper.names, DeclarationTraversal.rows, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := final) (value := sitesValue restSites)
              · apply helper_capture form.rows next state _
                  (rowValues language free permissions bound expected selector subjects ++ [encoded (declarationsTerm remaining), number (index + 1)])
                  _ (by cases form <;> rfl) _ (ih (index + 1) (fun entry member => rows entry (by simp [member])))
                cases form <;> simp [rowPrefix, next, here, selected, caller, values, rowValues, environment, Helper.names,
                  DeclarationTraversal.rows, DeclarationTraversal.selector, DeclarationTraversal.subjects, applySubst, Subst.lookup]
              · cases form <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, next, here, selected,
                  caller, values, rowValues, environment, Helper.names, DeclarationTraversal.rows, Subst.lookup]
              · exact .nil _ _
        · have returned := append_values_returns final state (headSites.map siteTerm) (restSites.map siteTerm) "here" "tail"
            (by simp [final, next, here, sitesValue, MatchAutomataSourceExecution.listValue, encodeList_map,
              applySubst, Subst.lookup])
          simpa only [List.zipIdx_cons, List.flatMap_cons, headSites, restSites, sitesValue,
            MatchAutomataSourceExecution.listValue, ← List.map_append, encodeList_map, Function.comp_def, id_eq] using returned


private def collectionRowSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (kind : CollType)
    (elements : List Pattern) (row : GrammarRule) (declaration : Nat) : List SiteData :=
  match bareCollectionElementType? row kind expected with
  | some type =>
      if checkElementsHaveType language (FreeTypeContext.ofList free) bound elements type then
        collectionChildrenSites language free permissions bound type kind elements (.authoredCollection declaration) elements 0
      else []
  | none => []

private def collectionRowElements : Atom :=
  a "if" [a "gslt:premise:type-elements" [v "declarations", v "free", v "bound", v "elements", v "type"],
    a "let" [v "frame", a "TypingAuthoredCollection" [v "declaration"],
      a Helper.collectionChildren.head [v "declarations", v "free", v "permissions", v "bound", v "type",
        v "kind", v "elements", v "frame", v "elements", number 0]], .symbol "LNil"]
private def collectionRowKind : Atom := a "if"
  [a "==" [v "actual", v "kind"], collectionRowElements, .symbol "LNil"]
private def collectionRowCategory : Atom := a "if"
  [a "==" [v "category", v "sort"], collectionRowKind, .symbol "LNil"]
private def collectionRowCases : SpaceSemantics.Cases :=
  [(.expression [a "GrammarTypingV1" [v "label", v "category",
      a "LCons" [a "TermSimple" [v "name", a "TCollection" [v "actual", v "type"]], .symbol "LNil"]],
      a "TBase" [v "sort"]], collectionRowCategory),
   (v "ordinary", .symbol "LNil")]

private theorem collection_row_shape : (equation .collectionRow).body =
    a "case" [.expression [v "row", v "expected"],
      .expression (collectionRowCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem collection_row_fallback (caller : Subst) (row : GrammarRule) (expected : TypeExpr)
    (fresh : Subst.lookup caller "ordinary" = none)
    (unsupported : ¬ ∃ name actual type sort,
      row.bareParams = [.simple name (.collection actual type)] ∧ expected = .base sort) :
    SpaceSemantics.selectCase caller (.expression [encoded (typingDeclarationTerm row), encoded (typeTerm expected)])
      collectionRowCases = some (("ordinary", .expression [encoded (typingDeclarationTerm row), encoded (typeTerm expected)]) :: caller,
        .symbol "LNil") := by
  simp only [Subst.lookup] at fresh
  cases mode : row.collectionRepresentation with
  | wrapped =>
    simp [collectionRowCases, typingDeclarationTerm, mode, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, fresh]
  | bare =>
    have bareShape : row.bareParams = row.params := by
      simp [GrammarRule.bareParams, mode]
    rw [bareShape] at unsupported
    cases row with
    | mk label category parameters syntaxPattern evalPolicy algebra representation =>
      change representation = .bare at mode
      cases expected <;> cases parameters with
      | nil => simp [collectionRowCases, typingDeclarationTerm, typeTerm, encodeList,
          InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, fresh, mode]
      | cons parameter rest =>
        cases rest with
        | cons next tail => simp [collectionRowCases, typingDeclarationTerm, typeTerm, encodeList,
            InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, fresh, mode]
        | nil =>
          cases parameter with
          | simple name type =>
            cases type <;>
              first
              | (exfalso; apply unsupported; exact ⟨_, _, _, _, rfl, rfl⟩)
              | simp [collectionRowCases, typingDeclarationTerm, parameterTerm, typeTerm, encodeList,
                  InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, fresh, mode]
          | abstractionNamed binder name type => simp [collectionRowCases, typingDeclarationTerm, parameterTerm, typeTerm, encodeList,
              InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, fresh, mode]
          | multiAbstractionNamed binders name type => simp [collectionRowCases, typingDeclarationTerm, parameterTerm, typeTerm, encodeList,
              InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, fresh, mode]
private theorem collection_row_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (kind : CollType) (elements : List Pattern) (row : GrammarRule) (declaration : Nat)
    (children : ∀ type element, element ∈ elements →
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type element)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type element))) :
    PureReturns program [] state
      (a Helper.collectionRow.head (rowValues language free permissions bound expected
        (InferenceCettaWire.encodeCollectionType kind) elements ++ [encoded (typingDeclarationTerm row), number declaration])) state
      (sitesValue (collectionRowSites language free permissions bound expected kind elements row declaration)) := by
  let values := rowValues language free permissions bound expected (InferenceCettaWire.encodeCollectionType kind) elements ++
    [encoded (typingDeclarationTerm row), number declaration]
  let caller := environment .collectionRow values
  apply helper_call .collectionRow [] state _ values _ rfl
    (by simp only [values, rowValues, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [collection_row_shape]
  have readValues : PureReturns program caller state (.expression [v "row", v "expected"]) state
      (.expression [encoded (typingDeclarationTerm row), encoded (typeTerm expected)]) := by
    simpa [caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup] using
      PureData.variables_return program caller state ["row", "expected"]
  by_cases supported : ∃ name actual type sort,
      row.bareParams = [.simple name (.collection actual type)] ∧ expected = .base sort
  · obtain ⟨name, actual, type, sort, shape, rfl⟩ := supported
    obtain ⟨mode, shape⟩ := (GrammarRule.bareParams_cons_iff _ _ _).mp shape
    let selected := ("sort", encoded (.string sort)) :: ("type", encoded (typeTerm type)) ::
      ("actual", encoded (InferenceCettaWire.encodeCollectionType actual)) :: ("name", encoded (.string name)) ::
      ("category", encoded (.string row.category)) :: ("label", encoded (.string row.label)) :: caller
    apply case_returns program caller selected state state state (.expression [v "row", v "expected"])
      (.expression [encoded (typingDeclarationTerm row), encoded (typeTerm (.base sort))])
      collectionRowCategory _ _ collectionRowCases (read_cases_encoded _) readValues
    · simp [collectionRowCases, typingDeclarationTerm, mode, shape, parameterTerm, typeTerm, encodeList,
        InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, selected, caller, values, rowValues, environment, Helper.names, Subst.lookup]
    · unfold collectionRowCategory
      apply bool_if_returns program selected state _ (decide (row.category = sort))
      · simpa only [Term.string.injEq] using CettaWireAtom.equality_captured_returns program selected state
          (.string row.category) (.string sort) "category" "sort"
          (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
      · by_cases categorySame : row.category = sort
        · simp only [categorySame, decide_true, ite_true]
          unfold collectionRowKind
          apply bool_if_returns program selected state _ (decide (actual = kind))
          · simpa only [collection_code_injective.eq_iff] using CettaWireAtom.equality_captured_returns program selected state
              (InferenceCettaWire.encodeCollectionType actual) (InferenceCettaWire.encodeCollectionType kind) "actual" "kind"
              (by simp [selected, applySubst, Subst.lookup])
              (by simp [selected, caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup])
          · by_cases kindSame : actual = kind
            · simp only [kindSame, decide_true, ite_true]
              unfold collectionRowElements
              apply bool_if_returns program selected state _
                (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements type)
              · apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
                apply PremiseOperationsExecution.DeclarationTyping.check_elements_have_type_captured_returns
                  selected state language free bound elements type
                simp [selected, caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup]
              · cases checked : checkElementsHaveType language (FreeTypeContext.ofList free) bound elements type with
                | false =>
                    simpa [collectionRowSites, bareCollectionElementType?, GrammarRule.bareParams, mode, shape, categorySame, kindSame, checked,
                      sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"
                | true =>
                    simp only [ite_true]
                    simp only [collectionRowSites, bareCollectionElementType?, GrammarRule.bareParams, mode, shape, categorySame, kindSame,
                      and_self, ite_true, checked]
                    let frame := encoded (typingFrameTerm (.authoredCollection declaration))
                    let final := ("frame", frame) :: selected
                    apply named_let_returns program selected state "frame" _ frame
                    · simp [selected, caller, values, rowValues, environment, Helper.names, Subst.lookup]
                    · have templated : PureData.Template program (a "TypingAuthoredCollection" [v "declaration"]) :=
                        data_template _ _ (by decide) (by
                          intro child member
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                          subst child
                          exact PureData.Template.captured "declaration")
                      simpa [frame, typingFrameTerm, selected, caller, values, rowValues, environment, Helper.names,
                        CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
                        PureData.template_return program selected state _ templated
                    · apply helper_capture .collectionChildren final state _
                        (collectionChildrenValues language free permissions bound type kind elements (.authoredCollection declaration) elements 0)
                        _ rfl _ (collection_children_returns_of state language free permissions bound type kind elements
                          (.authoredCollection declaration) elements 0 (children type))
                      simp [final, frame, selected, caller, values, rowValues, collectionChildrenValues,
                        environment, Helper.names, applySubst, Subst.lookup]
            · simpa [kindSame, collectionRowSites, bareCollectionElementType?, GrammarRule.bareParams, mode, shape,
                sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"
        · simpa [categorySame, collectionRowSites, bareCollectionElementType?, GrammarRule.bareParams, mode, shape,
            sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"
  · let selected := ("ordinary", .expression [encoded (typingDeclarationTerm row), encoded (typeTerm expected)]) :: caller
    apply case_returns program caller selected state state state (.expression [v "row", v "expected"])
      (.expression [encoded (typingDeclarationTerm row), encoded (typeTerm expected)])
      (.symbol "LNil") _ _ collectionRowCases (read_cases_encoded _) readValues
    · exact collection_row_fallback caller row expected
        (by simp [caller, values, rowValues, environment, Helper.names, Subst.lookup]) supported
    · have absent : bareCollectionElementType? row kind expected = none := by
        cases found : bareCollectionElementType? row kind expected with
        | none => rfl
        | some type =>
            obtain ⟨expectedShape, name, shape⟩ := (bareCollectionElementType?_eq_some_iff row kind expected type).mp found
            exact False.elim (supported ⟨name, kind, type, row.category, shape, expectedShape⟩)
      simpa [collectionRowSites, absent, sitesValue, encodeList, CettaWireAtom.encode] using
        symbol_returns program selected state "LNil"


private def applicationChildrenValues (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (constructor : String)
    (arguments : List Pattern) (parameters : List TermParam) (declaration : Nat) (remaining : List Pattern)
    (index : Nat) : List Atom :=
  [encoded (declarationsTerm language.terms), encoded (freeContextTerm free), permissionsValue permissions,
   encoded (boundContextTerm bound), encoded (.string constructor), patternsValue arguments,
   encoded (encodeList parameterTerm parameters), number declaration, patternsValue remaining, number index]

private def applicationChildSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (constructor : String)
    (arguments : List Pattern) (parameters : List TermParam) (declaration : Nat) (argument : Pattern)
    (index : Nat) : List SiteData :=
  if permissions.permitsArgument constructor index then
    match parameters[index]?.bind parameterType? with
    | some type => (generate language (FreeTypeContext.ofList free) permissions bound type argument).map
        (SiteData.wrapApplication declaration constructor arguments index)
    | none => []
  else []

private def applicationChildCaller (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (constructor : String)
    (arguments : List Pattern) (parameters : List TermParam) (declaration : Nat) (argument : Pattern)
    (remaining : List Pattern) (index : Nat) : Subst :=
  ("next", number (index + 1)) :: ("rest", patternsValue remaining) :: ("argument", encoded (encodePattern argument)) ::
    environment .applicationChildren
      (applicationChildrenValues language free permissions bound constructor arguments parameters declaration (argument :: remaining) index)

private def applicationTypePairs : List (Atom × Atom) :=
  [(v "sites", a Helper.generate.head [v "declarations", v "free", v "permissions", v "bound", v "type", v "argument"]),
   (v "before", a Helper.take.head [v "index", v "arguments"]),
   (v "after", a Helper.drop.head [v "next", v "arguments"])]
private def applicationTypeBody : Atom := a "let*"
  [.expression (applicationTypePairs.map fun pair => .expression [pair.1, pair.2]),
   a Helper.wrapApplication.head [v "declaration", v "constructor", v "before", v "index", v "after", v "sites"]]
private def applicationTypeCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "type"], applicationTypeBody)]
private def applicationParameterBody : Atom := a "case"
  [a "gslt:premise:parameter-type" [v "parameter"],
   .expression (applicationTypeCases.map fun row => .expression [row.1, row.2])]
private def applicationParameterCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "parameter"], applicationParameterBody)]
private def applicationChildBody : Atom := a "if"
  [a Helper.argumentPermitted.head [v "permissions", v "constructor", v "index"],
   a "case" [a "gslt:rule:row-at" [v "index", v "parameters"],
     .expression (applicationParameterCases.map fun row => .expression [row.1, row.2])],
   .symbol "LNil"]

private theorem take_patterns_returns (state : State) (count : Nat) (patterns : List Pattern) :
    PureReturns program [] state (a Helper.take.head [number count, patternsValue patterns]) state
      (patternsValue (patterns.take count)) := by
  have returned := take_returns state count (patterns.map encodePattern)
  change PureReturns program [] state (a Helper.take.head [number count, listValue (patterns.map encodePattern)]) state
    (listValue ((patterns.map encodePattern).take count)) at returned
  simpa only [← List.map_take, listValue, encodeList_map, Function.comp_def, id_eq,
    ← InferenceCettaWire.encodePatterns_eq_encodeList] using returned

private theorem drop_patterns_returns (state : State) (count : Nat) (patterns : List Pattern) :
    PureReturns program [] state (a Helper.drop.head [number count, patternsValue patterns]) state
      (patternsValue (patterns.drop count)) := by
  have returned := drop_returns state count (patterns.map encodePattern)
  change PureReturns program [] state (a Helper.drop.head [number count, listValue (patterns.map encodePattern)]) state
    (listValue ((patterns.map encodePattern).drop count)) at returned
  simpa only [← List.map_drop, listValue, encodeList_map, Function.comp_def, id_eq,
    ← InferenceCettaWire.encodePatterns_eq_encodeList] using returned

private theorem application_child_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (constructor : String) (arguments : List Pattern) (parameters : List TermParam) (declaration : Nat)
    (argument : Pattern) (remaining : List Pattern) (index : Nat)
    (child : ∀ type,
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type argument)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type argument))) :
    PureReturns program (applicationChildCaller language free permissions bound constructor arguments parameters declaration argument remaining index)
      state applicationChildBody state
      (sitesValue (applicationChildSites language free permissions bound constructor arguments parameters declaration argument index)) := by
  let caller := applicationChildCaller language free permissions bound constructor arguments parameters declaration argument remaining index
  unfold applicationChildBody
  apply bool_if_returns program caller state _ (permissions.permitsArgument constructor index)
  · apply helper_capture .argumentPermitted caller state _ [permissionsValue permissions, encoded (.string constructor), number index]
      _ rfl _ (argument_permitted_returns state permissions constructor index)
    simp [caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names, applySubst, Subst.lookup]
  · cases permitted : permissions.permitsArgument constructor index with
    | false =>
        simpa [permitted, applicationChildSites, sitesValue, encodeList, CettaWireAtom.encode] using
          symbol_returns program caller state "LNil"
    | true =>
        simp only [ite_true, applicationChildSites, permitted]
        have lookup : PureReturns program caller state (a "gslt:rule:row-at" [v "index", v "parameters"]) state
            (encoded (encodeOption parameterTerm parameters[index]?)) := by
          apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
          have returned := RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index
            (parameters.map parameterTerm) (v "index") (v "parameters")
            (by simp [caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names,
              applySubst, Subst.lookup, encodeList_map])
          cases found : parameters[index]? <;>
            simpa [List.getElem?_map, found, encodeOption, MatchAutomataBindingExecution.payloadOptionTerm] using returned
        cases found : parameters[index]? with
        | none =>
            apply case_returns program caller caller state state state (a "gslt:rule:row-at" [v "index", v "parameters"])
              (.symbol "None") (.symbol "LNil") _ _ applicationParameterCases (read_cases_encoded _)
            · simpa [found, encodeOption, CettaWireAtom.encode] using lookup
            · simp [applicationParameterCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [found, sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program caller state "LNil"
        | some parameter =>
            let selected := ("parameter", encoded (parameterTerm parameter)) :: caller
            apply case_returns program caller selected state state state (a "gslt:rule:row-at" [v "index", v "parameters"])
              (encoded (encodeOption parameterTerm (some parameter))) applicationParameterBody _ _ applicationParameterCases (read_cases_encoded _)
            · simpa only [found] using lookup
            · simp [applicationParameterCases, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                selected, caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names, Subst.lookup]
            · unfold applicationParameterBody
              have annotation : PureReturns program selected state (a "gslt:premise:parameter-type" [v "parameter"]) state
                  (encoded (encodeOption typeTerm (parameterType? parameter))) := by
                apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
                exact PremiseOperationsExecution.TypedParameters.parameter_type_captured_returns selected state parameter (v "parameter")
                  (by simp [selected, applySubst, Subst.lookup])
              cases typed : parameterType? parameter with
              | none =>
                  apply case_returns program selected selected state state state (a "gslt:premise:parameter-type" [v "parameter"])
                    (.symbol "None") (.symbol "LNil") _ _ applicationTypeCases (read_cases_encoded _)
                  · simpa [typed, encodeOption, CettaWireAtom.encode] using annotation
                  · simp [applicationTypeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · simpa [found, typed, sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"
              | some type =>
                  let admitted := ("type", encoded (typeTerm type)) :: selected
                  let generated := generate language (FreeTypeContext.ofList free) permissions bound type argument
                  let sites := ("sites", sitesValue generated) :: admitted
                  let before := ("before", patternsValue (arguments.take index)) :: sites
                  let after := ("after", patternsValue (arguments.drop (index + 1))) :: before
                  apply case_returns program selected admitted state state state (a "gslt:premise:parameter-type" [v "parameter"])
                    (encoded (encodeOption typeTerm (some type))) applicationTypeBody _ _ applicationTypeCases (read_cases_encoded _)
                  · simpa only [typed] using annotation
                  · simp [applicationTypeCases, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                      admitted, selected, caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names, Subst.lookup]
                  · simp only [Option.bind_some, typed]
                    unfold applicationTypeBody
                    apply PureData.let_bindings_return (final := after) (middle := state) (pairs := applicationTypePairs)
                    · apply PureData.BindingsReturn.cons (bound := sites) (value := sitesValue generated)
                      · apply helper_capture .generate admitted state _ (generateValues language free permissions bound type argument) _ rfl _ (child type)
                        simp [admitted, selected, caller, applicationChildCaller, applicationChildrenValues, generateValues,
                          environment, Helper.names, applySubst, Subst.lookup]
                      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, sites, admitted, selected,
                          caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names, Subst.lookup]
                      · apply PureData.BindingsReturn.cons (bound := before) (value := patternsValue (arguments.take index))
                        · apply helper_capture .take sites state _ [number index, patternsValue arguments] _ rfl _ (take_patterns_returns state index arguments)
                          simp [sites, admitted, selected, caller, applicationChildCaller, applicationChildrenValues,
                            environment, Helper.names, applySubst, Subst.lookup]
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, before, sites, admitted, selected,
                            caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names, Subst.lookup]
                        · apply PureData.BindingsReturn.cons (bound := after) (value := patternsValue (arguments.drop (index + 1)))
                          · apply helper_capture .drop before state _ [number (index + 1), patternsValue arguments] _ rfl _ (drop_patterns_returns state (index + 1) arguments)
                            simp [before, sites, admitted, selected, caller, applicationChildCaller, applicationChildrenValues,
                              environment, Helper.names, applySubst, Subst.lookup]
                          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, after, before, sites, admitted, selected,
                              caller, applicationChildCaller, applicationChildrenValues, environment, Helper.names, Subst.lookup]
                          · exact .nil _ _
                    · apply helper_capture .wrapApplication after state _
                        [number declaration, encoded (.string constructor), patternsValue (arguments.take index), number index,
                         patternsValue (arguments.drop (index + 1)), sitesValue generated]
                        _ rfl _ (wrap_application_returns state declaration constructor arguments index generated)
                      simp [after, before, sites, admitted, selected, caller, applicationChildCaller, applicationChildrenValues,
                        environment, Helper.names, applySubst, Subst.lookup]


private def applicationChildrenSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (constructor : String)
    (arguments : List Pattern) (parameters : List TermParam) (declaration : Nat) (remaining : List Pattern)
    (index : Nat) : List SiteData :=
  (remaining.zipIdx index).flatMap fun (argument, position) =>
    applicationChildSites language free permissions bound constructor arguments parameters declaration argument position

private def applicationChildrenPairs : List (Atom × Atom) :=
  [(v "next", a "+" [v "index", number 1]), (v "here", applicationChildBody),
   (v "tail", a Helper.applicationChildren.head [v "declarations", v "free", v "permissions", v "bound",
     v "constructor", v "arguments", v "parameters", v "declaration", v "rest", v "next"])]
private def applicationChildrenBody : Atom := a "let*"
  [.expression (applicationChildrenPairs.map fun pair => .expression [pair.1, pair.2]),
   a "gslt:automata:append" [v "here", v "tail"]]
private def applicationChildrenCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "argument", v "rest"], applicationChildrenBody)]

private theorem application_children_shape : (equation .applicationChildren).body =
    a "case" [v "remaining", .expression (applicationChildrenCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem application_children_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (constructor : String) (arguments : List Pattern) (parameters : List TermParam) (declaration : Nat)
    (remaining : List Pattern) (index : Nat)
    (children : ∀ type argument, argument ∈ remaining →
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type argument)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type argument))) :
    PureReturns program [] state
      (a Helper.applicationChildren.head
        (applicationChildrenValues language free permissions bound constructor arguments parameters declaration remaining index)) state
      (sitesValue (applicationChildrenSites language free permissions bound constructor arguments parameters declaration remaining index)) := by
  induction remaining generalizing index with
  | nil =>
      let values := applicationChildrenValues language free permissions bound constructor arguments parameters declaration [] index
      let caller := environment .applicationChildren values
      apply helper_call .applicationChildren [] state _ values _ rfl
        (by simp only [values, applicationChildrenValues, List.map_cons, List.map_nil,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [application_children_shape]
      apply case_returns program caller caller state state state (v "remaining") (.symbol "LNil")
        (.symbol "LNil") _ _ applicationChildrenCases (read_cases_encoded _)
      · simpa [caller, values, applicationChildrenValues, environment, Helper.names, patternsValue,
          encodePatterns, CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "remaining"
      · simp [applicationChildrenCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons argument remaining ih =>
      let values := applicationChildrenValues language free permissions bound constructor arguments parameters declaration (argument :: remaining) index
      let caller := environment .applicationChildren values
      let selected := ("rest", patternsValue remaining) :: ("argument", encoded (encodePattern argument)) :: caller
      let next := ("next", number (index + 1)) :: selected
      let headSites := applicationChildSites language free permissions bound constructor arguments parameters declaration argument index
      let restSites := applicationChildrenSites language free permissions bound constructor arguments parameters declaration remaining (index + 1)
      let here := ("here", sitesValue headSites) :: next
      let final := ("tail", sitesValue restSites) :: here
      apply helper_call .applicationChildren [] state _ values _ rfl
        (by simp only [values, applicationChildrenValues, List.map_cons, List.map_nil,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [application_children_shape]
      apply case_returns program caller selected state state state (v "remaining") (patternsValue (argument :: remaining))
        applicationChildrenBody _ _ applicationChildrenCases (read_cases_encoded _)
      · simpa [caller, values, applicationChildrenValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "remaining"
      · simp [applicationChildrenCases, patternsValue, encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, applicationChildrenValues, environment, Helper.names, Subst.lookup]
      · unfold applicationChildrenBody
        apply PureData.let_bindings_return (final := final) (middle := state) (pairs := applicationChildrenPairs)
        · apply PureData.BindingsReturn.cons (bound := next) (value := number (index + 1))
          · apply add_one_returns selected state index "index"
            simp [selected, caller, values, applicationChildrenValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, next, selected,
              caller, values, applicationChildrenValues, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := here) (value := sitesValue headSites)
            · exact application_child_returns_of state language free permissions bound constructor arguments parameters declaration
                argument remaining index (fun type => children type argument (by simp))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, here, next, selected,
                caller, values, applicationChildrenValues, environment, Helper.names, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := final) (value := sitesValue restSites)
              · apply helper_capture .applicationChildren here state _
                  (applicationChildrenValues language free permissions bound constructor arguments parameters declaration remaining (index + 1))
                  _ rfl _ (ih (index + 1) (fun type child member => children type child (by simp [member])))
                simp [here, next, selected, caller, values, applicationChildrenValues, environment, Helper.names, applySubst, Subst.lookup]
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, here, next, selected,
                  caller, values, applicationChildrenValues, environment, Helper.names, Subst.lookup]
              · exact .nil _ _
        · have returned := append_values_returns final state (headSites.map siteTerm) (restSites.map siteTerm) "here" "tail"
            (by simp [final, here, sitesValue, MatchAutomataSourceExecution.listValue, encodeList_map, applySubst, Subst.lookup])
          simpa only [applicationChildrenSites, List.zipIdx_cons, List.flatMap_cons, headSites, restSites, sitesValue,
            MatchAutomataSourceExecution.listValue, ← List.map_append, encodeList_map, Function.comp_def, id_eq] using returned


private theorem type_code_injective : Function.Injective typeTerm := by
  intro left right equal
  have decoded := congrArg InferenceCettaWire.AuthoredRule.decodeType? equal
  simpa only [InferenceCettaWire.AuthoredRule.decodeType?_typeTerm, Option.some.injEq] using decoded

private def applicationRowSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (constructor : String)
    (arguments : List Pattern) (row : GrammarRule) (declaration : Nat) : List SiteData :=
  if row.label = constructor ∧ expected = .base row.category ∧ usesBareCollection? row = false ∧
      checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments row.params = true then
    applicationChildrenSites language free permissions bound constructor arguments row.params declaration arguments 0
  else []

private def applicationArgumentsBody : Atom := a "if"
  [a "gslt:premise:type-arguments" [v "declarations", v "free", v "bound", v "arguments", v "parameters"],
   a Helper.applicationChildren.head [v "declarations", v "free", v "permissions", v "bound", v "constructor",
      v "arguments", v "parameters", v "declaration", v "arguments", number 0], .symbol "LNil"]
private def applicationRowParameterCases : SpaceSemantics.Cases :=
  [(a "LCons" [a "TermSimple" [v "name", a "TCollection" [v "kind", v "element"]], .symbol "LNil"], .symbol "LNil"),
   (v "ordinary", applicationArgumentsBody)]
private def applicationRowParameters : Atom := a "case"
  [v "parameters", .expression (applicationRowParameterCases.map fun row => .expression [row.1, row.2])]
private def applicationRowResult (mode : CollectionRepresentation) : Atom := a "let"
  [v "result", a "TBase" [v "category"],
    a "if" [a "==" [v "expected", v "result"],
      (match mode with | .bare => applicationRowParameters | .wrapped => applicationArgumentsBody), .symbol "LNil"]]
private def applicationRowBody (mode : CollectionRepresentation) : Atom := a "if"
  [a "==" [v "label", v "constructor"], applicationRowResult mode, .symbol "LNil"]
private def applicationRowCases : SpaceSemantics.Cases :=
  [(a "GrammarTypingV1" [v "label", v "category", v "parameters"], applicationRowBody .bare),
   (a "GrammarTypingWrappedV1" [v "label", v "category", v "parameters"], applicationRowBody .wrapped)]
private theorem application_row_shape : (equation .applicationRow).body =
    a "case" [v "row", .expression (applicationRowCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem application_parameters_fallback (caller : Subst) (row : GrammarRule)
    (mode : row.collectionRepresentation = .bare)
    (fresh : Subst.lookup caller "ordinary" = none) (notBare : usesBareCollection? row = false) :
    SpaceSemantics.selectCase caller (encoded (encodeList parameterTerm row.params)) applicationRowParameterCases =
      some (("ordinary", encoded (encodeList parameterTerm row.params)) :: caller, applicationArgumentsBody) := by
  simp only [Subst.lookup] at fresh
  cases row with
  | mk label category parameters syntaxPattern evalPolicy algebra representation =>
    change representation = .bare at mode
    cases parameters with
    | nil => simp [applicationRowParameterCases, encodeList, CettaWireAtom.encode,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup, fresh]
    | cons parameter rest =>
      cases rest with
      | cons next tail => simp [applicationRowParameterCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, fresh]
      | nil =>
        cases parameter with
        | simple name type =>
          cases type with
          | collection kind element => simp [usesBareCollection?, GrammarRule.bareParams, mode] at notBare
          | _ => simp [applicationRowParameterCases, parameterTerm, typeTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, fresh]
        | abstractionNamed binder name type => simp [applicationRowParameterCases, parameterTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, fresh]
        | multiAbstractionNamed binders name type => simp [applicationRowParameterCases, parameterTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, fresh]

private theorem application_row_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (constructor : String) (arguments : List Pattern) (row : GrammarRule) (declaration : Nat)
    (children : ∀ type argument, argument ∈ arguments →
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type argument)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type argument))) :
    PureReturns program [] state
      (a Helper.applicationRow.head (rowValues language free permissions bound expected (.string constructor) arguments ++
        [encoded (typingDeclarationTerm row), number declaration])) state
      (sitesValue (applicationRowSites language free permissions bound expected constructor arguments row declaration)) := by
  let values := rowValues language free permissions bound expected (.string constructor) arguments ++
    [encoded (typingDeclarationTerm row), number declaration]
  let caller := environment .applicationRow values
  let selected := ("parameters", encoded (encodeList parameterTerm row.params)) ::
    ("category", encoded (.string row.category)) :: ("label", encoded (.string row.label)) :: caller
  apply helper_call .applicationRow [] state _ values _ rfl
    (by simp only [values, rowValues, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [application_row_shape]
  apply case_returns program caller selected state state state (v "row") (encoded (typingDeclarationTerm row))
    (applicationRowBody row.collectionRepresentation) _ _ applicationRowCases (read_cases_encoded _)
  · simpa [caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "row"
  · cases mode : row.collectionRepresentation <;> simp [mode, applicationRowCases, typingDeclarationTerm, InferenceCettaWire.encodeList,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      selected, caller, values, rowValues, environment, Helper.names, Subst.lookup]
  · unfold applicationRowBody
    apply bool_if_returns program selected state _ (decide (row.label = constructor))
    · simpa only [Term.string.injEq] using CettaWireAtom.equality_captured_returns program selected state
        (.string row.label) (.string constructor) "label" "constructor"
        (by simp [selected, applySubst, Subst.lookup])
        (by simp [selected, caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup])
    · by_cases labelSame : row.label = constructor
      · simp only [labelSame, decide_true, ite_true]
        let result := ("result", encoded (typeTerm (.base row.category))) :: selected
        unfold applicationRowResult
        apply named_let_returns program selected state "result" _ (encoded (typeTerm (.base row.category)))
        · simp [selected, caller, values, rowValues, environment, Helper.names, Subst.lookup]
        · have templated : PureData.Template program (a "TBase" [v "category"]) :=
            data_template _ _ (by decide) (by
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              subst child
              exact PureData.Template.captured "category")
          simpa [typeTerm, selected, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using PureData.template_return program selected state _ templated
        · apply bool_if_returns program result state _ (decide (expected = .base row.category))
          · simpa only [type_code_injective.eq_iff] using CettaWireAtom.equality_captured_returns program result state
              (typeTerm expected) (typeTerm (.base row.category)) "expected" "result"
              (by simp [result, selected, caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup])
              (by simp [result, applySubst, Subst.lookup])
          · by_cases typeSame : expected = .base row.category
            · simp only [typeSame, decide_true, ite_true]
              cases mode : row.collectionRepresentation with
              | wrapped =>
                have notBare : usesBareCollection? row = false := by
                  simp [usesBareCollection?, GrammarRule.bareParams, mode]
                unfold applicationArgumentsBody
                apply bool_if_returns program result state _
                  (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments row.params)
                · apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
                  apply PremiseOperationsExecution.DeclarationTyping.check_arguments_have_types_captured_returns
                    result state language free bound arguments row.params
                  simp [result, selected, caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup]
                · cases checked : checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments row.params with
                  | false =>
                      simpa [applicationRowSites, GrammarRule.bareParams, mode, usesBareCollection?, checked, sitesValue, encodeList, CettaWireAtom.encode] using
                        symbol_returns program result state "LNil"
                  | true =>
                      simp only [ite_true, applicationRowSites, labelSame, notBare, checked, and_self]
                      apply helper_capture .applicationChildren result state _
                        (applicationChildrenValues language free permissions bound constructor arguments row.params declaration arguments 0)
                        _ rfl _ (application_children_returns_of state language free permissions bound constructor arguments row.params declaration
                          arguments 0 children)
                      simp [result, selected, caller, values, rowValues, applicationChildrenValues,
                        environment, Helper.names, applySubst, Subst.lookup]
              | bare =>
                unfold applicationRowParameters
                by_cases bare : usesBareCollection? row = true
                · obtain ⟨name, kind, element, shape⟩ := (usesBareCollection?_eq_true_iff row).mp bare
                  have shape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
                  let rejected := ("element", encoded (typeTerm element)) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) ::
                    ("name", encoded (.string name)) :: result
                  apply case_returns program result rejected state state state (v "parameters") (encoded (encodeList parameterTerm row.params))
                    (.symbol "LNil") _ _ applicationRowParameterCases (read_cases_encoded _)
                  · simpa [result, selected, applySubst, Subst.lookup] using variable_returns program result state "parameters"
                  · simp [applicationRowParameterCases, shape, parameterTerm, typeTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                      rejected, result, selected, caller, values, rowValues, environment, Helper.names, Subst.lookup]
                  · simpa [applicationRowSites, bare, sitesValue, encodeList, CettaWireAtom.encode] using
                      symbol_returns program rejected state "LNil"
                · have notBare : usesBareCollection? row = false := Bool.eq_false_iff.mpr bare
                  let ordinary := ("ordinary", encoded (encodeList parameterTerm row.params)) :: result
                  apply case_returns program result ordinary state state state (v "parameters") (encoded (encodeList parameterTerm row.params))
                    applicationArgumentsBody _ _ applicationRowParameterCases (read_cases_encoded _)
                  · simpa [result, selected, applySubst, Subst.lookup] using variable_returns program result state "parameters"
                  · exact application_parameters_fallback result row mode
                      (by simp [result, selected, caller, values, rowValues, environment, Helper.names, Subst.lookup]) notBare
                  · unfold applicationArgumentsBody
                    apply bool_if_returns program ordinary state _
                      (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments row.params)
                    · apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
                      apply PremiseOperationsExecution.DeclarationTyping.check_arguments_have_types_captured_returns
                        ordinary state language free bound arguments row.params
                      simp [ordinary, result, selected, caller, values, rowValues, environment, Helper.names, applySubst, Subst.lookup]
                    · cases checked : checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments row.params with
                      | false =>
                          simpa [applicationRowSites, checked, sitesValue, encodeList, CettaWireAtom.encode] using
                            symbol_returns program ordinary state "LNil"
                      | true =>
                          simp only [ite_true, applicationRowSites, labelSame, notBare, checked, and_self]
                          apply helper_capture .applicationChildren ordinary state _
                            (applicationChildrenValues language free permissions bound constructor arguments row.params declaration arguments 0)
                            _ rfl _ (application_children_returns_of state language free permissions bound constructor arguments row.params declaration
                              arguments 0 children)
                          simp [ordinary, result, selected, caller, values, rowValues, applicationChildrenValues,
                            environment, Helper.names, applySubst, Subst.lookup]
            · simpa [typeSame, applicationRowSites, sitesValue, encodeList, CettaWireAtom.encode] using
                symbol_returns program result state "LNil"
      · simpa [labelSame, applicationRowSites, sitesValue, encodeList, CettaWireAtom.encode] using
          symbol_returns program selected state "LNil"


private def descendSites (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) : Pattern → List SiteData
  | .apply constructor arguments => language.terms.zipIdx.flatMap fun (row, declaration) =>
      applicationRowSites language free permissions bound expected constructor arguments row declaration
  | .lambda binder body =>
      match expected with
      | .arrow domain codomain => if permissions.underLambda then
          (generate language (FreeTypeContext.ofList free) permissions (domain :: bound) codomain body).map
            (SiteData.wrapLambda binder domain)
        else []
      | _ => []
  | .multiLambda arity binders body =>
      match expected with
      | .arrow (.multiBinder domain) codomain => if permissions.underMultiLambda then
          (generate language (FreeTypeContext.ofList free) permissions (List.replicate arity domain ++ bound) codomain body).map
            (SiteData.wrapMultiLambda arity binders domain)
        else []
      | _ => []
  | .collection kind elements none => if kind ∈ permissions.collectionKinds then
      directCollectionSites language free permissions bound expected kind elements ++
        language.terms.zipIdx.flatMap fun (row, declaration) =>
          collectionRowSites language free permissions bound expected kind elements row declaration
    else []
  | _ => []

private theorem attach_zipIdx_flatMap {α β : Type} (items : List α) (index : Nat) (f : α → Nat → List β) :
    (items.attach.zipIdx index).flatMap (fun (item, position) => f item.val position) =
      (items.zipIdx index).flatMap (fun (item, position) => f item position) := by
  have same := congrArg (fun entries => entries.flatMap (fun (item, position) => f item position))
    (List.map_zipIdx (f := Subtype.val) (l := items.attach) (k := index))
  simpa only [List.flatMap_map, Function.comp_def, Prod.map, id_eq, List.attach_map_subtype_val] using same

private theorem generate_unfold (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :
    generate language (FreeTypeContext.ofList free) permissions bound expected source =
      if permissions.enabled = true ∧ isObjectPattern source = true ∧
          checkHasType language (FreeTypeContext.ofList free) bound source expected = true then
        SiteData.here bound expected source :: descendSites language free permissions bound expected source
      else [] := by
  rw [generate.eq_def]
  split
  · congr 1
    cases source with
    | apply constructor arguments =>
        simp only [descendSites]
        unfold applicationRowSites
        apply congrArg (List.flatMap · language.terms.zipIdx)
        funext entry
        rcases entry with ⟨row, declaration⟩
        dsimp only
        split
        · simp only [applicationChildrenSites]
          trans (arguments.attach.zipIdx).flatMap (fun entry =>
            applicationChildSites language free permissions bound constructor arguments row.params declaration entry.1.val entry.2)
          · apply congrArg (List.flatMap · arguments.attach.zipIdx)
            funext entry
            rcases entry with ⟨argument, index⟩
            dsimp only [applicationChildSites]
            split
            · cases row.params[index]?.bind parameterType? <;> rfl
            · rfl
          · exact attach_zipIdx_flatMap arguments 0
              (applicationChildSites language free permissions bound constructor arguments row.params declaration)
        · rfl
    | lambda binder body => cases expected <;> rfl
    | multiLambda arity binders body =>
        cases expected with
        | arrow domain codomain => cases domain <;> rfl
        | _ => rfl
    | collection kind elements rest =>
        cases rest with
        | some name => rfl
        | none =>
            simp only [descendSites]
            by_cases permitted : kind ∈ permissions.collectionKinds
            · simp only [permitted, ite_true]
              apply congrArg₂ List.append
              · cases expected with
                | collection actual type =>
                    simp only [directCollectionSites]
                    split
                    · exact attach_zipIdx_flatMap elements 0 (fun element index =>
                        (generate language (FreeTypeContext.ofList free) permissions bound type element).map
                          (SiteData.wrapCollection (.directCollection kind) kind elements index))
                    · rfl
                | _ => rfl
              · apply congrArg (List.flatMap · language.terms.zipIdx)
                funext entry
                rcases entry with ⟨row, declaration⟩
                dsimp only
                unfold collectionRowSites
                cases bareCollectionElementType? row kind expected with
                | none => rfl
                | some type =>
                    dsimp only
                    split
                    · exact attach_zipIdx_flatMap elements 0 (fun element index =>
                        (generate language (FreeTypeContext.ofList free) permissions bound type element).map
                          (SiteData.wrapCollection (.authoredCollection declaration) kind elements index))
                    · rfl
            · simp only [permitted, ite_false]
    | bvar index | fvar name | subst left right => rfl
  · rfl

private def descentPermissions (permissions : OperationalPermissions) (caller : Subst) : Subst :=
  [("kinds", encoded (encodeList InferenceCettaWire.encodeCollectionType permissions.collectionKinds)),
   ("multi", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underMultiLambda)),
   ("lambda", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underLambda)),
   ("slots", encoded (encodeList InferenceCettaWire.ContextObservation.slotTerm permissions.constructorArguments)),
   ("all", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.allConstructorArguments)),
   ("enabled", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.enabled))] ++ caller
private def descentCaller (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) : Subst :=
  descentPermissions permissions (environment .descend (generateValues language free permissions bound expected source))

private def lambdaPairs : List (Atom × Atom) :=
  [(v "inner", a "LCons" [v "domain", v "bound"]),
   (v "sites", a Helper.generate.head [v "declarations", v "free", v "permissions", v "inner", v "codomain", v "body"])]
private def lambdaBody : Atom := a "let*"
  [.expression (lambdaPairs.map fun pair => .expression [pair.1, pair.2]),
   a Helper.wrapLambda.head [v "binder", v "domain", v "sites"]]
private def lambdaCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "PermissionYes", a "TArrow" [v "domain", v "codomain"]], lambdaBody),
   (v "unpermitted", .symbol "LNil")]
private def lambdaDispatch : Atom := a "case"
  [.expression [v "lambda", v "expected"], .expression (lambdaCases.map fun row => .expression [row.1, row.2])]
private def multiPairs : List (Atom × Atom) :=
  [(v "inner", a "gslt:premise:type-extend-count" [v "domain", v "arity", v "bound"]),
   (v "sites", a Helper.generate.head [v "declarations", v "free", v "permissions", v "inner", v "codomain", v "body"])]
private def multiBody : Atom := a "let*"
  [.expression (multiPairs.map fun pair => .expression [pair.1, pair.2]),
   a Helper.wrapMulti.head [v "arity", v "binders", v "domain", v "sites"]]
private def multiCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "PermissionYes", a "TArrow" [a "TMultiBinder" [v "domain"], v "codomain"]], multiBody),
   (v "unpermitted", .symbol "LNil")]
private def multiDispatch : Atom := a "case"
  [.expression [v "multi", v "expected"], .expression (multiCases.map fun row => .expression [row.1, row.2])]
private def collectionPairs : List (Atom × Atom) :=
  [(v "direct", a Helper.directCollection.head [v "declarations", v "free", v "permissions", v "bound", v "expected", v "kind", v "elements"]),
   (v "authored", a Helper.collectionRows.head [v "declarations", v "free", v "permissions", v "bound", v "expected", v "kind", v "elements", v "declarations", number 0])]
private def collectionBody : Atom := a "let*"
  [.expression (collectionPairs.map fun pair => .expression [pair.1, pair.2]),
   a "gslt:automata:append" [v "direct", v "authored"]]
private def collectionDispatch : Atom := a "if"
  [a "gslt:automata:member" [v "kind", v "kinds"], collectionBody, .symbol "LNil"]
private def descentCases : SpaceSemantics.Cases :=
  [(a "PApp" [v "constructor", v "arguments"],
      a Helper.applicationRows.head [v "declarations", v "free", v "permissions", v "bound", v "expected",
        v "constructor", v "arguments", v "declarations", number 0]),
   (a "PLam" [v "binder", v "body"], lambdaDispatch),
   (a "PMultiLam" [v "arity", v "binders", v "body"], multiDispatch),
   (a "PCollection" [v "kind", v "elements", .symbol "RNone"], collectionDispatch),
   (v "leaf", .symbol "LNil")]
private def descentBody : Atom := a "case"
  [v "source", .expression (descentCases.map fun row => .expression [row.1, row.2])]
private def descentOuterCases : SpaceSemantics.Cases :=
  [(a "OperationalPermissions" [v "enabled", v "all", v "slots", v "lambda", v "multi", v "kinds"], descentBody)]
private theorem descend_shape : (equation .descend).body =
    a "case" [v "permissions", .expression (descentOuterCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem descend_dispatch_returns (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (result : Atom)
    (returned : PureReturns program (descentCaller language free permissions bound expected source) state descentBody state result) :
    PureReturns program [] state (a Helper.descend.head (generateValues language free permissions bound expected source)) state result := by
  let caller := environment .descend (generateValues language free permissions bound expected source)
  let selected := descentCaller language free permissions bound expected source
  apply helper_call .descend [] state _ (generateValues language free permissions bound expected source) _ rfl
    (by simp only [generateValues, List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [descend_shape]
  apply case_returns program caller selected state state state (v "permissions") (permissionsValue permissions)
    descentBody _ _ descentOuterCases (read_cases_encoded _)
  · simpa [caller, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "permissions"
  · simp [descentOuterCases, permissionsValue, InferenceCettaWire.ContextObservation.permissionsTerm,
      InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, descentCaller, descentPermissions, caller, generateValues, environment, Helper.names, Subst.lookup]
  · exact returned


private def lambdaCaller (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (binder : Option String) (body : Pattern) : Subst :=
  ("body", encoded (encodePattern body)) :: ("binder", encoded (InferenceCettaWire.encodeBinder binder)) ::
    descentCaller language free permissions bound expected (.lambda binder body)

private theorem lambda_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (binder : Option String) (body : Pattern)
    (child : ∀ inner type,
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions inner type body)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions inner type body))) :
    PureReturns program (lambdaCaller language free permissions bound expected binder body) state lambdaDispatch state
      (sitesValue (descendSites language free permissions bound expected (.lambda binder body))) := by
  let caller := lambdaCaller language free permissions bound expected binder body
  have readValues : PureReturns program caller state (.expression [v "lambda", v "expected"]) state
      (.expression [encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underLambda), encoded (typeTerm expected)]) := by
    simpa [caller, lambdaCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names,
      applySubst, Subst.lookup] using PureData.variables_return program caller state ["lambda", "expected"]
  unfold lambdaDispatch
  by_cases supported : ∃ domain codomain, expected = .arrow domain codomain ∧ permissions.underLambda = true
  · obtain ⟨domain, codomain, rfl, permitted⟩ := supported
    let selected := ("codomain", encoded (typeTerm codomain)) :: ("domain", encoded (typeTerm domain)) :: caller
    let inner := ("inner", encoded (boundContextTerm (domain :: bound))) :: selected
    let generated := generate language (FreeTypeContext.ofList free) permissions (domain :: bound) codomain body
    let final := ("sites", sitesValue generated) :: inner
    apply case_returns program caller selected state state state (.expression [v "lambda", v "expected"])
      (.expression [encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underLambda), encoded (typeTerm (.arrow domain codomain))])
      lambdaBody _ _ lambdaCases (read_cases_encoded _) readValues
    · simp [lambdaCases, permitted, InferenceCettaWire.ContextObservation.booleanTerm, typeTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, lambdaCaller, descentCaller,
        descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
    · unfold lambdaBody
      apply PureData.let_bindings_return (final := final) (middle := state) (pairs := lambdaPairs)
      · apply PureData.BindingsReturn.cons (bound := inner) (value := encoded (boundContextTerm (domain :: bound)))
        · have templated : PureData.Template program (a "LCons" [v "domain", v "bound"]) :=
            data_template _ _ (by decide) (by
              intro argument member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl <;> exact .captured _)
          simpa [boundContextTerm, encodeList, selected, caller, lambdaCaller, descentCaller, descentPermissions,
            generateValues, environment, Helper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using PureData.template_return program selected state _ templated
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, inner, selected,
            caller, lambdaCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := final) (value := sitesValue generated)
          · apply helper_capture .generate inner state _ (generateValues language free permissions (domain :: bound) codomain body)
              _ rfl _ (child (domain :: bound) codomain)
            simp [inner, selected, caller, lambdaCaller, descentCaller, descentPermissions, generateValues,
              environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, inner, selected,
              caller, lambdaCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
          · exact .nil _ _
      · simp only [descendSites, permitted, ite_true]
        apply helper_capture .wrapLambda final state _
          [encoded (InferenceCettaWire.encodeBinder binder), encoded (typeTerm domain), sitesValue generated]
          _ rfl _ (wrap_lambda_returns state binder domain generated)
        simp [final, inner, selected, caller, lambdaCaller, descentCaller, descentPermissions, generateValues,
          environment, Helper.names, applySubst, Subst.lookup]
  · let tuple : Atom := .expression [encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underLambda), encoded (typeTerm expected)]
    let selected := ("unpermitted", tuple) :: caller
    apply case_returns program caller selected state state state (.expression [v "lambda", v "expected"])
      tuple (.symbol "LNil") _ _ lambdaCases (read_cases_encoded _) readValues
    · cases expected <;> cases flag : permissions.underLambda <;>
        first
        | (exfalso; apply supported; exact ⟨_, _, rfl, flag⟩)
        | simp [lambdaCases, tuple, selected, flag, InferenceCettaWire.ContextObservation.booleanTerm, typeTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, caller, lambdaCaller, descentCaller,
            descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
    · have empty : descendSites language free permissions bound expected (.lambda binder body) = [] := by
        cases expected <;> simp only [descendSites]
        case arrow domain codomain =>
          have stopped : permissions.underLambda = false := by
            cases flag : permissions.underLambda with
            | false => rfl
            | true => exact False.elim (supported ⟨domain, codomain, rfl, flag⟩)
          simp [stopped]
      simpa [empty, sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"

private theorem extend_count_captured_returns (caller : Subst) (state : State) (domain : TypeExpr)
    (count : Nat) (bound : List TypeExpr) (one two three : String)
    (captured : [v one, v two, v three].map (applySubst caller) =
      [encoded (typeTerm domain), number count, encoded (boundContextTerm bound)]) :
    PureReturns program caller state (a "gslt:premise:type-extend-count" [v one, v two, v three]) state
      (encoded (boundContextTerm (List.replicate count domain ++ bound))) := by
  apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
  apply captured_call_returns RuleExecutionProgram.program [] caller state state "gslt:premise:type-extend-count"
    [encoded (typeTerm domain), number count, encoded (boundContextTerm bound)] [v one, v two, v three] _
    (by decide +kernel) (by decide) _ _ _
    (PremiseOperationsExecution.DeclarationTyping.extend_count_returns state domain count bound)
  · intro index argument member
    have bounded : index < 3 := by
      obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp member
      exact bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases small with rfl | rfl | rfl
    · exact Or.inl (by decide +kernel)
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at member
      subst argument
      exact Or.inr rfl
    · exact Or.inl (by decide +kernel)
  · intro index argument member
    have found : argument ∈ [v one, v two, v three] := List.mem_of_getElem? member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found
    rcases found with rfl | rfl | rfl <;> exact Or.inr rfl
  · simpa only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using captured.symm

private def multiCaller (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (arity : Nat) (binders : List String) (body : Pattern) : Subst :=
  ("body", encoded (encodePattern body)) :: ("binders", encoded (encodeList Term.string binders)) :: ("arity", number arity) ::
    descentCaller language free permissions bound expected (.multiLambda arity binders body)

private theorem multi_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (arity : Nat) (binders : List String) (body : Pattern)
    (child : ∀ inner type,
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions inner type body)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions inner type body))) :
    PureReturns program (multiCaller language free permissions bound expected arity binders body) state multiDispatch state
      (sitesValue (descendSites language free permissions bound expected (.multiLambda arity binders body))) := by
  let caller := multiCaller language free permissions bound expected arity binders body
  have readValues : PureReturns program caller state (.expression [v "multi", v "expected"]) state
      (.expression [encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underMultiLambda), encoded (typeTerm expected)]) := by
    simpa [caller, multiCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names,
      applySubst, Subst.lookup] using PureData.variables_return program caller state ["multi", "expected"]
  unfold multiDispatch
  by_cases supported : ∃ domain codomain, expected = .arrow (.multiBinder domain) codomain ∧ permissions.underMultiLambda = true
  · obtain ⟨domain, codomain, rfl, permitted⟩ := supported
    let selected := ("codomain", encoded (typeTerm codomain)) :: ("domain", encoded (typeTerm domain)) :: caller
    let inner := ("inner", encoded (boundContextTerm (List.replicate arity domain ++ bound))) :: selected
    let generated := generate language (FreeTypeContext.ofList free) permissions (List.replicate arity domain ++ bound) codomain body
    let final := ("sites", sitesValue generated) :: inner
    apply case_returns program caller selected state state state (.expression [v "multi", v "expected"])
      (.expression [encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underMultiLambda), encoded (typeTerm (.arrow (.multiBinder domain) codomain))])
      multiBody _ _ multiCases (read_cases_encoded _) readValues
    · simp [multiCases, permitted, InferenceCettaWire.ContextObservation.booleanTerm, typeTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller, multiCaller, descentCaller,
        descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
    · unfold multiBody
      apply PureData.let_bindings_return (final := final) (middle := state) (pairs := multiPairs)
      · apply PureData.BindingsReturn.cons (bound := inner) (value := encoded (boundContextTerm (List.replicate arity domain ++ bound)))
        · apply extend_count_captured_returns selected state domain arity bound "domain" "arity" "bound"
          simp [selected, caller, multiCaller, descentCaller, descentPermissions, generateValues,
            environment, Helper.names, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, inner, selected,
            caller, multiCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := final) (value := sitesValue generated)
          · apply helper_capture .generate inner state _ (generateValues language free permissions (List.replicate arity domain ++ bound) codomain body)
              _ rfl _ (child (List.replicate arity domain ++ bound) codomain)
            simp [inner, selected, caller, multiCaller, descentCaller, descentPermissions, generateValues,
              environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, inner, selected,
              caller, multiCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
          · exact .nil _ _
      · simp only [descendSites, permitted, ite_true]
        apply helper_capture .wrapMulti final state _
          [number arity, encoded (encodeList Term.string binders), encoded (typeTerm domain), sitesValue generated]
          _ rfl _ (wrap_multi_returns state arity binders domain generated)
        simp [final, inner, selected, caller, multiCaller, descentCaller, descentPermissions, generateValues,
          environment, Helper.names, applySubst, Subst.lookup]
  · let tuple : Atom := .expression [encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underMultiLambda), encoded (typeTerm expected)]
    let selected := ("unpermitted", tuple) :: caller
    apply case_returns program caller selected state state state (.expression [v "multi", v "expected"])
      tuple (.symbol "LNil") _ _ multiCases (read_cases_encoded _) readValues
    · cases expected <;> (try (rename_i domain codomain; cases domain)) <;>
        cases flag : permissions.underMultiLambda <;>
        first
        | (exfalso; apply supported; exact ⟨_, _, rfl, flag⟩)
        | simp [multiCases, tuple, selected, flag, InferenceCettaWire.ContextObservation.booleanTerm, typeTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, caller, multiCaller, descentCaller,
            descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
    · have empty : descendSites language free permissions bound expected (.multiLambda arity binders body) = [] := by
        cases expected with
        | arrow argument codomain =>
            cases argument with
            | multiBinder domain =>
                have stopped : permissions.underMultiLambda = false := by
                  cases flag : permissions.underMultiLambda with
                  | false => rfl
                  | true => exact False.elim (supported ⟨domain, codomain, rfl, flag⟩)
                simp [descendSites, stopped]
            | _ => rfl
        | _ => rfl
      simpa [empty, sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"


private def collectionCaller (language : LanguageDef) (free : List (String × TypeExpr))
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (kind : CollType) (elements : List Pattern) : Subst :=
  ("elements", patternsValue elements) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) ::
    descentCaller language free permissions bound expected (.collection kind elements none)

private theorem collection_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (kind : CollType) (elements : List Pattern)
    (children : ∀ type element, element ∈ elements →
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound type element)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound type element))) :
    PureReturns program (collectionCaller language free permissions bound expected kind elements) state collectionDispatch state
      (sitesValue (descendSites language free permissions bound expected (.collection kind elements none))) := by
  let caller := collectionCaller language free permissions bound expected kind elements
  unfold collectionDispatch
  apply bool_if_returns program caller state _ (decide (kind ∈ permissions.collectionKinds))
  · have returned := member_values_returns caller state (InferenceCettaWire.encodeCollectionType kind)
      (permissions.collectionKinds.map InferenceCettaWire.encodeCollectionType) "kind" "kinds"
      (by simp [caller, collectionCaller, descentCaller, descentPermissions, environment, Helper.names,
        applySubst, Subst.lookup, encodeList_map])
    have same : InferenceCettaWire.encodeCollectionType kind ∈ permissions.collectionKinds.map InferenceCettaWire.encodeCollectionType ↔
        kind ∈ permissions.collectionKinds := by
      simp only [List.mem_map, collection_code_injective.eq_iff, exists_eq_right]
    simpa only [same] using returned
  · by_cases permitted : kind ∈ permissions.collectionKinds
    · simp only [permitted, decide_true, ite_true]
      let directSites := directCollectionSites language free permissions bound expected kind elements
      let authoredSites := language.terms.zipIdx.flatMap fun (row, declaration) =>
        collectionRowSites language free permissions bound expected kind elements row declaration
      let direct := ("direct", sitesValue directSites) :: caller
      let final := ("authored", sitesValue authoredSites) :: direct
      unfold collectionBody
      apply PureData.let_bindings_return (final := final) (middle := state) (pairs := collectionPairs)
      · apply PureData.BindingsReturn.cons (bound := direct) (value := sitesValue directSites)
        · apply helper_capture .directCollection caller state _
            (directCollectionValues language free permissions bound expected kind elements) _ rfl
            _ (direct_collection_returns_of state language free permissions bound expected kind elements children)
          simp [directCollectionValues, caller, collectionCaller, descentCaller, descentPermissions,
            generateValues, environment, Helper.names, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, direct, caller,
            collectionCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := final) (value := sitesValue authoredSites)
          · apply helper_capture .collectionRows direct state _
              (rowValues language free permissions bound expected (InferenceCettaWire.encodeCollectionType kind) elements ++
                [encoded (declarationsTerm language.terms), number 0]) _ rfl _
              (declaration_rows_returns_of .collection state language free permissions bound expected
                (InferenceCettaWire.encodeCollectionType kind) elements
                (collectionRowSites language free permissions bound expected kind elements) language.terms 0
                (fun row _ declaration => collection_row_returns_of state language free permissions bound expected kind elements row declaration children))
            simp [rowValues, direct, caller, collectionCaller, descentCaller, descentPermissions,
              generateValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, final, direct, caller,
              collectionCaller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
          · exact .nil _ _
      · have returned := append_values_returns final state (directSites.map siteTerm) (authoredSites.map siteTerm) "direct" "authored"
          (by simp [final, direct, sitesValue, MatchAutomataSourceExecution.listValue, encodeList_map, applySubst, Subst.lookup])
        simpa only [descendSites, permitted, ite_true, directSites, authoredSites, sitesValue,
          MatchAutomataSourceExecution.listValue, ← List.map_append, encodeList_map, Function.comp_def, id_eq] using returned
    · simpa [permitted, descendSites, sitesValue, encodeList, CettaWireAtom.encode] using
        symbol_returns program caller state "LNil"

private theorem descend_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)
    (children : ∀ child, sizeOf child < sizeOf source → ∀ inner type,
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions inner type child)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions inner type child))) :
    PureReturns program [] state (a Helper.descend.head (generateValues language free permissions bound expected source)) state
      (sitesValue (descendSites language free permissions bound expected source)) := by
  apply descend_dispatch_returns state language free permissions bound expected source
  let caller := descentCaller language free permissions bound expected source
  unfold descentBody
  cases source with
  | apply constructor arguments =>
      let selected := ("arguments", patternsValue arguments) :: ("constructor", encoded (.string constructor)) :: caller
      apply case_returns program caller selected state state state (v "source") (encoded (encodePattern (.apply constructor arguments)))
        (a Helper.applicationRows.head [v "declarations", v "free", v "permissions", v "bound", v "expected",
          v "constructor", v "arguments", v "declarations", number 0]) _ _ descentCases (read_cases_encoded _)
      · simpa [caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "source"
      · simp [descentCases, encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
      · apply helper_capture .applicationRows selected state _
          (rowValues language free permissions bound expected (.string constructor) arguments ++
            [encoded (declarationsTerm language.terms), number 0]) _ rfl _
          (declaration_rows_returns_of .application state language free permissions bound expected (.string constructor) arguments
            (applicationRowSites language free permissions bound expected constructor arguments) language.terms 0
            (fun row _ declaration => application_row_returns_of state language free permissions bound expected constructor arguments row declaration
              (fun type argument member => children argument (by have small := List.sizeOf_lt_of_mem member; simp; omega) bound type)))
        simp [rowValues, selected, caller, descentCaller, descentPermissions, generateValues,
          environment, Helper.names, applySubst, Subst.lookup]
  | lambda binder body =>
      apply case_returns program caller (lambdaCaller language free permissions bound expected binder body) state state state
        (v "source") (encoded (encodePattern (.lambda binder body))) lambdaDispatch _ _ descentCases (read_cases_encoded _)
      · simpa [caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "source"
      · simp [descentCases, encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          lambdaCaller, caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
      · exact lambda_returns_of state language free permissions bound expected binder body
          (children body (by simp))
  | multiLambda arity binders body =>
      apply case_returns program caller (multiCaller language free permissions bound expected arity binders body) state state state
        (v "source") (encoded (encodePattern (.multiLambda arity binders body))) multiDispatch _ _ descentCases (read_cases_encoded _)
      · simpa [caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "source"
      · simp [descentCases, encodePattern, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          multiCaller, caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
      · exact multi_returns_of state language free permissions bound expected arity binders body
          (children body (by simp))
  | collection kind elements rest =>
      cases rest with
      | none =>
          apply case_returns program caller (collectionCaller language free permissions bound expected kind elements) state state state
            (v "source") (encoded (encodePattern (.collection kind elements none))) collectionDispatch _ _ descentCases (read_cases_encoded _)
          · simpa [caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns program caller state "source"
          · simp [descentCases, encodePattern, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              collectionCaller, caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
          · exact collection_returns_of state language free permissions bound expected kind elements
              (fun type element member => children element (by have small := List.sizeOf_lt_of_mem member; simp; omega) bound type)
      | some name =>
          apply case_returns program caller (("leaf", encoded (encodePattern (.collection kind elements (some name)))) :: caller) state state state
            (v "source") (encoded (encodePattern (.collection kind elements (some name)))) (.symbol "LNil") _ _ descentCases (read_cases_encoded _)
          · simpa [caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns program caller state "source"
          · simp [descentCases, encodePattern, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, Subst.lookup]
          · exact symbol_returns program _ state "LNil"
  | bvar index | fvar name | subst left right =>
      all_goals
        apply case_returns program caller (("leaf", applySubst caller (v "source")) :: caller) state state state
          (v "source") (applySubst caller (v "source")) (.symbol "LNil") _ _ descentCases (read_cases_encoded _)
        · exact variable_returns program caller state "source"
        · simp [descentCases, encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            caller, descentCaller, descentPermissions, generateValues, environment, Helper.names, applySubst, Subst.lookup]
        · exact symbol_returns program _ state "LNil"

private def generationPairs : List (Atom × Atom) :=
  [(v "tail", a Helper.descend.head [v "declarations", v "free", v "permissions", v "bound", v "expected", v "source"]),
   (v "here", a "RuleJobSite" [.symbol "LNil", .symbol "ContextHole", v "source", v "bound", v "expected", .symbol "LNil"])]

private def generationBody : Atom := a "let*"
  [.expression (generationPairs.map fun pair => .expression [pair.1, pair.2]), a "LCons" [v "here", v "tail"]]

private def generationTyped : Atom := a "if"
  [a "gslt:premise:type-has" [v "declarations", v "free", v "bound", v "source", v "expected"],
   generationBody, .symbol "LNil"]

private def generationObject : Atom := a "if"
  [a "gslt:premise:object-pattern" [v "source"], generationTyped, .symbol "LNil"]

private def generationCases : SpaceSemantics.Cases :=
  [(a "OperationalPermissions" [.symbol "PermissionNo", v "all", v "slots", v "lambda", v "multi", v "kinds"], .symbol "LNil"),
   (a "OperationalPermissions" [.symbol "PermissionYes", v "all", v "slots", v "lambda", v "multi", v "kinds"], generationObject)]

private theorem generation_shape : (equation .generate).body =
    a "case" [v "permissions", .expression (generationCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem generate_returns_of (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)
    (children : ∀ child, sizeOf child < sizeOf source → ∀ inner type,
      PureReturns program [] state (a Helper.generate.head (generateValues language free permissions inner type child)) state
        (sitesValue (generate language (FreeTypeContext.ofList free) permissions inner type child))) :
    PureReturns program [] state (a Helper.generate.head (generateValues language free permissions bound expected source)) state
      (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound expected source)) := by
  let values := generateValues language free permissions bound expected source
  let caller := environment .generate values
  let selected :=
    ("kinds", encoded (encodeList InferenceCettaWire.encodeCollectionType permissions.collectionKinds)) ::
    ("multi", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underMultiLambda)) ::
    ("lambda", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underLambda)) ::
    ("slots", encoded (encodeList InferenceCettaWire.ContextObservation.slotTerm permissions.constructorArguments)) ::
    ("all", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.allConstructorArguments)) :: caller
  apply helper_call .generate [] state _ values _ rfl
    (by simp only [values, generateValues, List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [generation_shape, generate_unfold]
  cases enabled : permissions.enabled with
  | false =>
      apply case_returns program caller selected state state state (v "permissions") (permissionsValue permissions)
        (.symbol "LNil") _ _ generationCases (read_cases_encoded _)
      · simpa [caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "permissions"
      · simp [generationCases, permissionsValue, InferenceCettaWire.ContextObservation.permissionsTerm,
          InferenceCettaWire.ContextObservation.booleanTerm, enabled, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, generateValues, environment, Helper.names, Subst.lookup]
      · simpa [enabled, sitesValue, encodeList, CettaWireAtom.encode] using symbol_returns program selected state "LNil"
  | true =>
      apply case_returns program caller selected state state state (v "permissions") (permissionsValue permissions)
        generationObject _ _ generationCases (read_cases_encoded _)
      · simpa [caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "permissions"
      · simp [generationCases, permissionsValue, InferenceCettaWire.ContextObservation.permissionsTerm,
          InferenceCettaWire.ContextObservation.booleanTerm, enabled, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, values, generateValues, environment, Helper.names, Subst.lookup]
      · unfold generationObject
        apply bool_if_returns program selected state _ (isObjectPattern source)
        · apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
          apply PremiseOperationsExecution.OpenAdmission.object_pattern_captured_returns selected state source
          simp [selected, caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup]
        · cases object : isObjectPattern source with
          | false =>
              simpa [enabled, object, sitesValue, encodeList, CettaWireAtom.encode] using
                symbol_returns program selected state "LNil"
          | true =>
              simp only [ite_true]
              unfold generationTyped
              apply bool_if_returns program selected state _
                (checkHasType language (FreeTypeContext.ofList free) bound source expected)
              · apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
                apply PremiseOperationsExecution.DeclarationTyping.check_has_type_captured_returns
                  selected state language free bound source expected
                simp [selected, caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup]
              · cases typed : checkHasType language (FreeTypeContext.ofList free) bound source expected with
                | false =>
                    simpa [enabled, object, typed, sitesValue, encodeList, CettaWireAtom.encode] using
                      symbol_returns program selected state "LNil"
                | true =>
                    simp only [ite_true, and_self]
                    let descended := descendSites language free permissions bound expected source
                    let tail := ("tail", sitesValue descended) :: selected
                    let final := ("here", encoded (siteTerm (SiteData.here bound expected source))) :: tail
                    unfold generationBody
                    apply PureData.let_bindings_return (final := final) (middle := state) (pairs := generationPairs)
                    · apply PureData.BindingsReturn.cons (bound := tail) (value := sitesValue descended)
                      · apply helper_capture .descend selected state _ values _ rfl _
                          (descend_returns_of state language free permissions bound expected source children)
                        simp [selected, caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup]
                      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                          tail, selected, caller, values, generateValues, environment, Helper.names, Subst.lookup]
                      · apply PureData.BindingsReturn.cons (bound := final)
                          (value := encoded (siteTerm (SiteData.here bound expected source)))
                        · have templated : PureData.Template program
                              (a "RuleJobSite" [.symbol "LNil", .symbol "ContextHole", v "source", v "bound", v "expected", .symbol "LNil"]) :=
                            data_template _ _ (by decide) (by
                              intro child member
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                              rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
                                first | exact .symbol _ | exact .captured _)
                          simpa [siteTerm, SiteData.here, InferenceCettaWire.ContextObservation.contextTerm,
                            boundContextTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                            tail, selected, caller, values, generateValues, environment, Helper.names,
                            applySubst, applySubst.applySubstList, Subst.lookup] using
                            PureData.template_return program tail state _ templated
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                            final, tail, selected, caller, values, generateValues, environment, Helper.names, Subst.lookup]
                        · exact .nil _ _
                    · have templated : PureData.Template program (a "LCons" [v "here", v "tail"]) :=
                        data_template _ _ (by decide) (by
                          intro child member
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                          rcases member with rfl | rfl <;> exact .captured _)
                      simpa [sitesValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                        final, tail, descended, applySubst, applySubst.applySubstList, Subst.lookup] using
                        PureData.template_return program final state _ templated

/-- The authored traversal computes the original ordered typed occurrence list. -/
theorem generate_returns (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    PureReturns program [] state
      (a "gslt:sites:generate" (generateValues language free permissions bound expected source)) state
      (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound expected source)) := by
  apply generate_returns_of state language free permissions bound expected source
  intro child smaller inner type
  exact generate_returns state language free permissions inner type child
termination_by sizeOf source

theorem generate_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = generateValues language free permissions bound expected source) :
    PureReturns program caller state (a "gslt:sites:generate" arguments) state
      (sitesValue (generate language (FreeTypeContext.ofList free) permissions bound expected source)) :=
  helper_capture .generate caller state arguments _ _ rfl captured
    (generate_returns state language free permissions bound expected source)

private abbrev rulesValue (rules : List GeneralExecutionAdmission.RulePlan) : Atom :=
  encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm rules)
private abbrev jobsValue (jobs : List Job) : Atom :=
  encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm jobs)

private theorem jobs_shape : (equation .jobs).body = a "let"
    [v "sites", a Helper.generate.head [v "declarations", v "free", v "permissions", v "bound", v "expected", v "source"],
     a Helper.crossRules.head [v "rules", v "sites", number 0]] := by
  decide +kernel

/-- Enumeration retains selected rule order, declaration alternatives and every
physical typed occurrence, including duplicate sites from distinct derivations. -/
theorem jobs_returns (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (rules : List GeneralExecutionAdmission.RulePlan) :
    PureReturns program [] state
      (a "gslt:sites:jobs" (generateValues language free permissions bound expected source ++ [rulesValue rules])) state
      (jobsValue (rules.zipIdx.flatMap fun (declaration, ordinal) =>
        (generate language (FreeTypeContext.ofList free) permissions bound expected source).map fun site =>
          ⟨ordinal, declaration, site⟩)) := by
  let values := generateValues language free permissions bound expected source ++ [rulesValue rules]
  let caller := environment .jobs values
  let sites := generate language (FreeTypeContext.ofList free) permissions bound expected source
  let selected := ("sites", sitesValue sites) :: caller
  apply helper_call .jobs [] state _ values _ rfl
    (by simp only [values, generateValues, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [jobs_shape]
  apply named_let_returns program caller state "sites" _ (sitesValue sites)
  · simp [caller, values, generateValues, environment, Helper.names, Subst.lookup]
  · apply generate_captured_returns caller state language free permissions bound expected source
    simp [caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup]
  · apply cross_rules_captured_returns selected state rules sites 0
    simp [selected, caller, values, generateValues, environment, Helper.names, applySubst, Subst.lookup]

theorem jobs_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (rules : List GeneralExecutionAdmission.RulePlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      generateValues language free permissions bound expected source ++ [rulesValue rules]) :
    PureReturns program caller state (a "gslt:sites:jobs" arguments) state
      (jobsValue (rules.zipIdx.flatMap fun (declaration, ordinal) =>
        (generate language (FreeTypeContext.ofList free) permissions bound expected source).map fun site =>
          ⟨ordinal, declaration, site⟩)) :=
  helper_capture .jobs caller state arguments _ _ rfl captured
    (jobs_returns state language free permissions bound expected source rules)

/-- A finite free-context projection covering the subject computes precisely
the original plan's jobs. Additional environment names do not alter discovery. -/
theorem jobs_plan_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (footprint : List String)
    (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns program [] state
      (a "gslt:sites:jobs"
        (generateValues (GeneralPlanEnvironment.environment plan).language
          (plan.snapshot.free.entriesOn footprint) plan.permissions.sites bound expected source ++ [rulesValue plan.rules])) state
      (jobsValue (jobs plan bound expected source)) := by
  have returned := jobs_returns state (GeneralPlanEnvironment.environment plan).language
    (plan.snapshot.free.entriesOn footprint) plan.permissions.sites bound expected source plan.rules
  simpa only [generate_snapshot _ _ _ _ _ _ footprint covers, jobs] using returned

theorem jobs_plan_captured_returns (caller : Subst) (state : State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (footprint : List String)
    (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      generateValues (GeneralPlanEnvironment.environment plan).language
        (plan.snapshot.free.entriesOn footprint) plan.permissions.sites bound expected source ++ [rulesValue plan.rules]) :
    PureReturns program caller state (a "gslt:sites:jobs" arguments) state
      (jobsValue (jobs plan bound expected source)) :=
  helper_capture .jobs caller state arguments _ _ rfl captured
    (jobs_plan_returns state plan bound expected source footprint covers)

theorem jobs_plan_captured_returns_in_extension (targetProgram : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn executionHeads program targetProgram)
    (caller : Subst) (state : State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (footprint : List String)
    (covers : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      generateValues (GeneralPlanEnvironment.environment plan).language
        (plan.snapshot.free.entriesOn footprint) plan.permissions.sites bound expected source ++ [rulesValue plan.rules])
    (supported : codeWithin executionHeads (a "gslt:sites:jobs" arguments) = true) :
    PureReturns targetProgram caller state (a "gslt:sites:jobs" arguments) state
      (jobsValue (jobs plan bound expected source)) :=
  path_of_closed_agreement program_closed agreement ⟨supported, rfl⟩
    (jobs_plan_captured_returns caller state plan bound expected source footprint covers arguments captured)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution
