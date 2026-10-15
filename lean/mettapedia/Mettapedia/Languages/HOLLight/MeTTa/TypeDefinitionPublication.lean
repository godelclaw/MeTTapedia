import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionFormation

/-!
# The actual two-publication tail of a type-definition event

The tail is extracted from the retained source helper. Both calls execute the
existing publisher, with their own keys and the same ordered existence-premise
occurrence. The local first insertion cannot escape a refused second insertion.
These paths do not yet establish execution of the helper's preceding guards,
parameter collection or equation construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval (read_cases_encoded)
open Effects (State)
open TypeDefinitionFormation (command representationKey)

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:extend-type"))[0]'(by decide)

private def third (atom : Atom) : Atom :=
  match atom with
  | .expression [_, _, value] => value
  | _ => .symbol "None"

private def firstArm (atom : Atom) : Atom :=
  match atom with
  | .expression [_, _, .expression (.expression [_, body] :: _)] => body
  | _ => .symbol "None"

/-- The actual retained source tail, following the three equation constructions. -/
def sourceTail : Atom := firstArm (firstArm (third equation.body))

private def supplied (conclusion : String) : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:Thm", .symbol "HOL:Nil", .var conclusion,
    .var "dependencies", .symbol "TYPE_DEFINITION"]]

private def firstCall : Atom := .expression [.symbol "hol-light:publish", .var "extended",
  .var "key", .var "request", supplied "first"]

private def secondCall : Atom := .expression [.symbol "hol-light:publish", .var "withFirst",
  .expression [.symbol "HOL:RepKey", .var "key"], .var "request", supplied "second"]

private def cases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "withFirst"], secondCall), (.var "duplicate", .symbol "None")]

theorem source_tail_shape : sourceTail = .expression [.symbol "case", firstCall,
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

def environment (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Subst :=
  [("second", second), ("first", first), ("dependencies", dependencies),
   ("request", command typeName abstractionName representationName premise), ("key", key),
   ("extended", ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)]

def firstWorld (operators constants axioms key first dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Atom :=
  Publication.afterState operators constants axioms key
    (command typeName abstractionName representationName premise) (.symbol "HOL:Nil")
    first dependencies [premise] cache receipts

/-- Both publication addresses retain separate origins and receipt entries. -/
def finalResult (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Atom :=
  Publication.result operators constants axioms (representationKey key)
    (command typeName abstractionName representationName premise) (.symbol "HOL:Nil")
    second dependencies [premise]
    ((key, Publication.publishedValue key (command typeName abstractionName representationName premise)
      (.symbol "HOL:Nil") first dependencies) :: cache)
    (⟨key, command typeName abstractionName representationName premise, [premise]⟩ :: receipts)

private theorem supplied_returns (bindings : Subst) (state : State) (name : String) :
    BoundCalls.CorePath.PureReturns program bindings state (supplied name) state
      (.expression [.symbol "Some", Publication.value (.symbol "HOL:Nil")
        (applySubst bindings (.var name)) (applySubst bindings (.var "dependencies")) (.symbol "TYPE_DEFINITION")]) := by
  unfold supplied Publication.value
  apply BoundCalls.CorePath.unary_constructor_of_returns program bindings state state "Some" _ _
    (by decide) (by decide)
  apply BoundCalls.CorePath.constructor_return program bindings state "HOL:Thm" _ _ (by decide) (by decide)
  exact .cons (BoundCalls.CorePath.symbol_returns program bindings state "HOL:Nil")
    (.cons (BoundCalls.CorePath.variable_returns program bindings state name)
      (.cons (BoundCalls.CorePath.variable_returns program bindings state "dependencies")
        (.cons (BoundCalls.CorePath.symbol_returns program bindings state "TYPE_DEFINITION") .nil)))

private theorem first_captured_returns (operators constants axioms key first dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State)
    (worldCaptured : applySubst bindings (.var "extended") =
      ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var "key") = key)
    (requestCaptured : applySubst bindings (.var "request") =
      command typeName abstractionName representationName premise)
    (firstCaptured : applySubst bindings (.var "first") = first)
    (dependenciesCaptured : applySubst bindings (.var "dependencies") = dependencies) :
    BoundCalls.PureReturns program bindings state firstCall state
      (Publication.result operators constants axioms key
        (command typeName abstractionName representationName premise) (.symbol "HOL:Nil") first
        dependencies [premise] cache receipts) := by
  unfold firstCall
  apply Publication.authored_publish_computed_request_bound_return operators constants axioms key
    (.symbol "HOL:Nil") first dependencies (.symbol "TYPE_DEFINITION")
    (command typeName abstractionName representationName premise) [premise]
    (fun bindings phase captured => Premises.authored_type_definition_premises_certificate bindings phase
      (.grounded (.string typeName)) (.grounded (.string abstractionName))
      (.grounded (.string representationName)) premise "request" captured)
    cache receipts bindings state "extended" "key" "request" (supplied "first")
    worldCaptured keyCaptured requestCaptured
  simpa only [firstCaptured, dependenciesCaptured] using (supplied_returns bindings state "first").extended

private theorem first_returns (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state firstCall state
      (Publication.result operators constants axioms key
        (command typeName abstractionName representationName premise) (.symbol "HOL:Nil") first
        dependencies [premise] cache receipts) :=
  first_captured_returns operators constants axioms key first dependencies
    typeName abstractionName representationName premise cache receipts _ state rfl rfl rfl rfl rfl

private theorem second_captured_returns (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State)
    (worldCaptured : applySubst bindings (.var "withFirst") =
      firstWorld operators constants axioms key first dependencies
        typeName abstractionName representationName premise cache receipts)
    (keyCaptured : applySubst bindings (.var "key") = key)
    (requestCaptured : applySubst bindings (.var "request") =
      command typeName abstractionName representationName premise)
    (secondCaptured : applySubst bindings (.var "second") = second)
    (dependenciesCaptured : applySubst bindings (.var "dependencies") = dependencies) :
    BoundCalls.PureReturns program bindings state secondCall state
      (finalResult operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts) := by
  unfold secondCall finalResult
  apply Publication.authored_publish_computed_arguments_bound_return operators constants axioms (representationKey key)
    (.symbol "HOL:Nil") second dependencies (.symbol "TYPE_DEFINITION")
    (command typeName abstractionName representationName premise) [premise]
    (fun bindings phase captured => Premises.authored_type_definition_premises_certificate bindings phase
      (.grounded (.string typeName)) (.grounded (.string abstractionName))
      (.grounded (.string representationName)) premise "request" captured)
    _ _ bindings state (.var "withFirst") (.expression [.symbol "HOL:RepKey", .var "key"])
    (.var "request") (supplied "second")
  · simpa only [worldCaptured, firstWorld, Publication.afterState] using
      BoundCalls.variable_returns program bindings state "withFirst"
  · simpa only [keyCaptured, representationKey] using
      (BoundCalls.CorePath.unary_constructor_returns program bindings state "HOL:RepKey" "key"
        (by decide) (by decide)).extended
  · simpa only [requestCaptured] using BoundCalls.variable_returns program bindings state "request"
  · simpa only [secondCaptured, dependenciesCaptured] using (supplied_returns bindings state "second").extended

/-- Extra live bindings are retained. Only the names used by the actual tail
are constrained; its newly bound publication result must be fresh. -/
theorem authored_captured_tail_returns (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State)
    (worldCaptured : applySubst bindings (.var "extended") =
      ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var "key") = key)
    (requestCaptured : applySubst bindings (.var "request") =
      command typeName abstractionName representationName premise)
    (firstCaptured : applySubst bindings (.var "first") = first)
    (secondCaptured : applySubst bindings (.var "second") = second)
    (dependenciesCaptured : applySubst bindings (.var "dependencies") = dependencies)
    (resultFresh : Subst.lookup bindings "withFirst" = none)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none) :
    BoundCalls.PureReturns program bindings state sourceTail state
      (finalResult operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts) := by
  let world := firstWorld operators constants axioms key first dependencies
    typeName abstractionName representationName premise cache receipts
  let bound := ("withFirst", world) :: bindings
  rw [source_tail_shape]
  apply BoundCalls.case_returns program bindings bound state state state firstCall
    (.expression [.symbol "Some", world]) secondCall _ _ cases (read_cases_encoded cases)
  · simpa only [world, Publication.result, receiptFresh, Bool.false_eq_true, ↓reduceIte, cacheFresh,
      firstWorld] using first_captured_returns operators constants axioms key first dependencies
        typeName abstractionName representationName premise cache receipts bindings state
        worldCaptured keyCaptured requestCaptured firstCaptured dependenciesCaptured
  · simp [cases, bound, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, resultFresh]
  · apply second_captured_returns operators constants axioms key first second dependencies
      typeName abstractionName representationName premise cache receipts bound state
    · rfl
    · simpa [bound, applySubst, Subst.lookup] using keyCaptured
    · simpa [bound, applySubst, Subst.lookup] using requestCaptured
    · simpa [bound, applySubst, Subst.lookup] using secondCaptured
    · simpa [bound, applySubst, Subst.lookup] using dependenciesCaptured

/-- Execute both actual publisher calls. A second-address conflict is retained
in the result; no second publication path is assumed. -/
theorem authored_tail_returns (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (finalResult operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts) :=
  authored_captured_tail_returns operators constants axioms key first second dependencies
    typeName abstractionName representationName premise cache receipts _ state
    rfl rfl rfl rfl rfl rfl rfl receiptFresh cacheFresh

/-- A representation publication address cannot equal its finite payload. -/
theorem representation_key_ne (key : Atom) : representationKey key ≠ key := by
  intro same
  have sizes := congrArg sizeOf same
  simp [representationKey] at sizes
  omega

def completedWorld (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Atom :=
  Publication.afterState operators constants axioms (representationKey key)
    (command typeName abstractionName representationName premise) (.symbol "HOL:Nil")
    second dependencies [premise]
    ((key, Publication.publishedValue key (command typeName abstractionName representationName premise)
      (.symbol "HOL:Nil") first dependencies) :: cache)
    (⟨key, command typeName abstractionName representationName premise, [premise]⟩ :: receipts)

/-- When both addresses are fresh, the actual tail returns both records and
both receipts. The two ordered premise lists each contain the existence key. -/
theorem authored_tail_publishes_both (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none)
    (representationReceiptFresh : ReceiptKeys.presentB (representationKey key) receipts = false)
    (representationCacheFresh : cache.lookup (representationKey key) = none) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (.expression [.symbol "Some", completedWorld operators constants axioms
        key first second dependencies typeName abstractionName representationName premise cache receipts]) := by
  have different : (representationKey key == key) = false := beq_eq_false_iff_ne.mpr (representation_key_ne key)
  have receipt : ReceiptKeys.presentB (representationKey key)
      (⟨key, command typeName abstractionName representationName premise, [premise]⟩ :: receipts) = false := by
    simpa only [ReceiptKeys.presentB, List.any_cons, different, Bool.false_or] using representationReceiptFresh
  have cached : (((key, Publication.publishedValue key (command typeName abstractionName representationName premise)
        (.symbol "HOL:Nil") first dependencies) :: cache).lookup (representationKey key)) = none := by
    simp [List.lookup, different, representationCacheFresh]
  simpa only [finalResult, Publication.result, receipt, Bool.false_eq_true, ↓reduceIte, cached, completedWorld] using
    authored_tail_returns operators constants axioms key first second dependencies
      typeName abstractionName representationName premise cache receipts state receiptFresh cacheFresh

private theorem refused_first_tail (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (refused : Publication.result operators constants axioms key
      (command typeName abstractionName representationName premise) (.symbol "HOL:Nil")
      first dependencies [premise] cache receipts = .symbol "None") :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (.symbol "None") := by
  let before := environment operators constants axioms key first second dependencies
    typeName abstractionName representationName premise cache receipts
  let bound := ("duplicate", Atom.symbol "None") :: before
  rw [source_tail_shape]
  apply BoundCalls.case_returns program before bound state state state firstCall (.symbol "None")
    (.symbol "None") (.symbol "None") _ cases (read_cases_encoded cases)
  · simpa only [refused] using first_returns operators constants axioms key first second dependencies
      typeName abstractionName representationName premise cache receipts state
  · simp [cases, bound, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup]
  · exact BoundCalls.symbol_returns program bound state "None"

/-- An occupied first receipt refuses the tail before a candidate world is returned. -/
theorem authored_tail_first_receipt_refused (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (occupied : ReceiptKeys.presentB key receipts = true) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (.symbol "None") := by
  apply refused_first_tail operators constants axioms key first second dependencies
    typeName abstractionName representationName premise cache receipts state
  simp [Publication.result, occupied]

/-- An occupied first cache address is also refused, even without a receipt. -/
theorem authored_tail_first_cache_refused (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (occupied : cache.lookup key ≠ none) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (.symbol "None") := by
  apply refused_first_tail operators constants axioms key first second dependencies
    typeName abstractionName representationName premise cache receipts state
  simp [Publication.result, occupied]

/-- A second-receipt conflict returns no world after executing the first
local insertion. The actual store and I/O state remain unchanged. -/
theorem authored_tail_second_receipt_refused (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none)
    (occupied : ReceiptKeys.presentB (representationKey key) receipts = true) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (.symbol "None") := by
  have blocked : ReceiptKeys.presentB (representationKey key)
      (⟨key, command typeName abstractionName representationName premise, [premise]⟩ :: receipts) = true := by
    change (representationKey key == key || ReceiptKeys.presentB (representationKey key) receipts) = true
    simp only [occupied, Bool.or_true]
  simpa only [finalResult, Publication.result, blocked, ↓reduceIte] using
    authored_tail_returns operators constants axioms key first second dependencies
      typeName abstractionName representationName premise cache receipts state receiptFresh cacheFresh

/-- A second-cache conflict likewise refuses the whole returned world; the
first newly formed record is not exposed as a partial successful result. -/
theorem authored_tail_second_cache_refused (operators constants axioms key first second dependencies : Atom)
    (typeName abstractionName representationName : String) (premise : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State)
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none)
    (occupied : cache.lookup (representationKey key) ≠ none) :
    BoundCalls.PureReturns program
      (environment operators constants axioms key first second dependencies
        typeName abstractionName representationName premise cache receipts)
      state sourceTail state (.symbol "None") := by
  have different : (representationKey key == key) = false := beq_eq_false_iff_ne.mpr (representation_key_ne key)
  have blocked : (((key, Publication.publishedValue key (command typeName abstractionName representationName premise)
        (.symbol "HOL:Nil") first dependencies) :: cache).lookup (representationKey key)) ≠ none := by
    simpa only [List.lookup, different] using occupied
  simpa only [finalResult, Publication.result, blocked, ↓reduceIte, ite_self] using
    authored_tail_returns operators constants axioms key first second dependencies
      typeName abstractionName representationName premise cache receipts state receiptFresh cacheFresh

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionPublication
