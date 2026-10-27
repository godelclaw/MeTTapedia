import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionJoin

/-! Retained operation controls preserve complete continuations, zippers,
physical occurrences and ordered candidate accounts. -/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperationControls

open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef CettaWire
open BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained RetainedWire

def p : TypeExpr := .base "Proc"
def q : TypeExpr := .base "Name"
def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def originals : List Pattern := [.lambda (some "kept") a, .bvar 1, b, a]

def outer : OneHoleContext :=
  .apply "Envelope" [b]
    (.lambda (some "outer")
      (.multiLambda 2 ["x", "y"]
        (.substBody
          (.substReplacement (.bvar 1)
            (.collection .hashBag [a] .hole [b] (some "kept-rest"))) a))) [a]

def occurrence (address : Nat) : SourceOccurrence :=
  ⟨.lambda (some "original") a, [9, address],
    .apply "Occurrence" [b] (.lambda (some "original") .hole) [a], a⟩

def parent : Frame :=
  ⟨[2, 1], [q, .arrow p q], .original [p, q] p (.bvar 1) outer,
    some 17, some ([[occurrence 0]], [occurrence 1])⟩

def next : Continuation .children :=
  .application parent "Result" (.lambda parent (some "display") .done)

def parameters : Parameters :=
  ⟨.empty "RetainedChildQueryData", fun _ => none, fun _ => none, "Proc", "unit"⟩

def argumentQuery (outer : Option OneHoleContext) (index : Nat)
    (schemas sources : List Pattern) (parameters : List TermParam) : Query .children :=
  .arguments [q, .arrow q p] [4, 2] [p, q, p] "Pair" outer originals index schemas sources parameters

def groupsQuery (index : Nat) (schemas : List Pattern)
    (groups : List (List SourceOccurrence)) : Query .children :=
  .groups [q, .arrow q p] [4, 2] [p, q, p] index schemas groups

def childQueries : List (String × Query .children) := Id.run do
  let schemas := [.fvar "first", .lambda none (.fvar "later")]
  let sources := [.bvar 2, .lambda (some "source-display") b]
  let later : TermParam := .multiAbstractionNamed ["u", "v"] "stored-tail" (.base "Proc")
  let args (parameter : TermParam) := [parameter, later]
  let valid := argumentQuery (some outer) 2 schemas sources
  let cases : List (String × Query .children) :=
    [("arguments-empty-without-context", argumentQuery none 0 [] [] []),
     ("arguments-simple-preserves-all-zipper-constructors", valid (args (.simple "head" p))),
     ("arguments-simple-collection-parameter", valid (args (.simple "head" (.collection .hashSet p)))),
     ("arguments-abstraction-base", valid (args (.abstractionNamed (some "binder") "head" p))),
     ("arguments-abstraction-arrow", valid (args (.abstractionNamed none "head" (.arrow p q)))),
     ("arguments-multi-base", valid (args (.multiAbstractionNamed ["x", "y"] "head" p))),
     ("arguments-multi-arrow", valid (args (.multiAbstractionNamed ["x"] "head" (.arrow (.multiBinder q) p)))),
     ("arguments-reject-wrong-single-binder-type", valid (args (.abstractionNamed none "head" (.collection .hashBag p)))),
     ("arguments-reject-wrong-multiple-binder-type", valid (args (.multiAbstractionNamed ["x"] "head" (.arrow p q)))),
     ("arguments-reject-missing-context", argumentQuery none 2 schemas sources (args (.simple "head" p))),
     ("arguments-reject-missing-schemas", argumentQuery (some outer) 2 [] sources (args (.simple "head" p))),
     ("arguments-reject-missing-sources", argumentQuery (some outer) 2 schemas [] (args (.simple "head" p))),
     ("arguments-reject-missing-parameters", argumentQuery (some outer) 2 schemas sources []),
     ("arguments-index-past-originals", argumentQuery (some outer) 9 schemas sources (args (.simple "head" p))),
     ("groups-empty", groupsQuery 0 [] []),
     ("groups-full-distinct-source-records", groupsQuery 3 schemas [[occurrence 0, occurrence 1], [occurrence 2]]),
     ("groups-empty-head-keeps-later", groupsQuery 7 schemas [[], [occurrence 2]]),
     ("groups-reject-missing-schemas", groupsQuery 3 [] [[occurrence 0]]),
     ("groups-reject-missing-groups", groupsQuery 3 schemas [])]
  return cases

inductive Operation where
  | returned {kind : Kind} (value : Value kind) (next : Continuation kind)
  | children (query : Query .children) (next : Continuation .children)
  | commit (pending : List Task) (answers : List Spelling) (children : List Task) (published : List Spelling)
  | complete (state : State)
  | answers (state : State)

def Operation.callTerm : Operation → Term
  | .returned value next => .application "gslt:collection-presentation:view-return"
      [valueTerm value,continuationTerm next]
  | .children query next => .application "gslt:collection-presentation:view-children"
      [queryTerm query,continuationTerm next]
  | .commit pending account newTasks published => .application "gslt:collection-presentation:view-commit"
      [encodeList taskTerm pending,encodeList spellingTerm account,expansionTerm (newTasks,published)]
  | .complete state => .application "gslt:collection-presentation:view-complete" [stateTerm state]
  | .answers state => .application "gslt:collection-presentation:view-answers" [stateTerm state]

def Operation.expectedTerm : Operation → Term
  | .returned value next => expansionTerm (expand parameters (.returned value next))
  | .children query next => expansionTerm (expand parameters (.request query next))
  | .commit pending account newTasks published => stateTerm ⟨newTasks ++ pending,account ++ published⟩
  | .complete state => .symbol (if Retained.complete state then "True" else "False")
  | .answers state => encodeList spellingTerm state.answers

def value : Spelling := ⟨a,[parent]⟩

def otherValue : Spelling := ⟨a,[{parent with declaration := some 18}]⟩

def pending : List Task :=
  [.request (.groups [q] [1] [p] 0 [.fvar "future"] [[occurrence 0,occurrence 1]]) next,
   .returned otherValue .done]

def controls : List (String × Operation) :=
  (childQueries.map fun (name,query) => (name,Operation.children query next)) ++
  [("return-done-complete-frames",.returned (kind := .spelling) value .done),
   ("return-application-preserves-next",.returned (kind := .children) ([a,b],[parent]) next),
   ("return-collection-preserves-equal-occurrences",.returned (kind := .children) ([b],[parent])
     (.collection parent [occurrence 0,occurrence 1] (.lambda parent (some "display") .done))),
   ("return-lambda-preserves-display",.returned (kind := .spelling) value (.lambda parent (some "display") .done)),
   ("return-multiple-lambda-preserves-order",.returned (kind := .spelling) value (.multiLambda parent 2 ["x","y"] .done)),
   ("return-tail-keeps-query-and-next",.returned (kind := .spelling) value (.tail (groupsQuery 3 [.fvar "remaining"] [[occurrence 1]]) next)),
   ("return-prepend-keeps-ordered-frames",.returned (kind := .children) ([b],[{parent with declaration := some 19}]) (.prepend value next)),
   ("commit-empty-change-keeps-complete-state",.commit pending [value,otherValue] [] []),
   ("commit-keeps-duplicate-prefix-and-publication-order",.commit pending [value,value] [.returned otherValue .done] [otherValue,value]),
   ("commit-children-before-old-pending",.commit pending [value] [.returned value .done,.returned otherValue .done] []),
   ("completion-empty-agenda",.complete ⟨[],[value,otherValue]⟩),
   ("completion-pending-work",.complete ⟨pending,[value]⟩),
   ("readout-keeps-duplicates-and-order",.answers ⟨pending,[value,otherValue,value]⟩),
   ("readout-empty-account",.answers ⟨pending,[]⟩)]

theorem child_query_controls_have_no_publications :
    childQueries.all (fun (_,query) => (expand parameters (.request query next)).2.isEmpty) = true := by
  decide +kernel

theorem two_equal_target_candidates_retain_different_frames :
    value.target = otherValue.target ∧ spellingTerm value ≠ spellingTerm otherValue := by
  decide +kernel

#print axioms child_query_controls_have_no_publications
#print axioms two_equal_target_candidates_retain_different_frames

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperationControls
