import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLowering
import Mettapedia.TypeTheory.PositiveInductiveScenarios

/-!
# Registered-list search trees through `.module` syntax data

The shared module-reader target can already spell `List (SearchTree Answer)`.
This file instantiates the generic lowering for that declaration, identifies
its erased admitted block with the existing nested search-tree semantics, and
checks refusals for an unknown container, a negative field, a changed header,
duplicate constructors and an extra module block.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.PositiveInductiveBlock
open Mettapedia.TypeTheory.PositiveInductiveScenarios
open InductiveSyntax
open PositiveInductiveLowering

namespace Search

abbrev registry := PositiveInductiveScenarios.Search.registry
abbrev interface := PositiveInductiveScenarios.Search.interface

def answerTerm : Term := .name "Answer"
def treeTerm : Term := .app (.name "SearchTree") answerTerm
def listTreeTerm : Term := .app (.name "List") treeTerm

def classify {context : List interface.SortCode} (_scope : PUnit) (source : Term) :
    Option (FieldMeaning registry interface context) :=
  if source = answerTerm then some (.data .answer)
  else if source = treeTerm then some (.recursive ())
  else if source = listTreeTerm then
    some (.nested "List" Mettapedia.TypeTheory.IndexedContainer.Examples.list
      (by simp [PositiveInductiveScenarios.Search.registry]) ())
  else none

def quoteField {context : List interface.SortCode} (_scope : PUnit) :
    FieldMeaning registry interface context → Term
  | .data .answer => answerTerm
  | .recursive () => treeTerm
  | .nested containerName _ _ () => .app (.name containerName) treeTerm

theorem classify_quote {context : List interface.SortCode} (scope : PUnit)
    (meaning : FieldMeaning registry interface context) :
    classify scope (quoteField scope meaning) = some meaning := by
  cases meaning with
  | data sort => cases sort; rfl
  | recursive index => cases index; rfl
  | nested name container registered index =>
      cases index
      by_cases same : name = "List"
      · subst name
        simp [PositiveInductiveScenarios.Search.registry] at registered
        subst container
        rfl
      · simp [PositiveInductiveScenarios.Search.registry, same] at registered

theorem quote_classify {context : List interface.SortCode} (scope : PUnit)
    (source : Term) (meaning : FieldMeaning registry interface context)
    (accepted : classify scope source = some meaning) :
    quoteField scope meaning = source := by
  by_cases answer : source = answerTerm
  · have same : meaning = .data .answer := by
      simpa [classify, answer] using accepted.symm
    subst meaning
    exact answer.symm
  · by_cases tree : source = treeTerm
    · have same : meaning = .recursive () := by
        simpa [classify, answer, tree, answerTerm, treeTerm] using accepted.symm
      subst meaning
      exact tree.symm
    · by_cases nested : source = listTreeTerm
      · have same : meaning = .nested "List"
            Mettapedia.TypeTheory.IndexedContainer.Examples.list
            (by simp [PositiveInductiveScenarios.Search.registry]) () := by
          simpa [classify, answer, tree, nested, answerTerm, treeTerm,
            listTreeTerm] using accepted.symm
        subst meaning
        exact nested.symm
      · simp [classify, answer, tree, nested] at accepted

def codec : Codec registry interface 1 [] where
  Scope := fun _ => PUnit
  initialScope := PUnit.unit
  bindData := fun _ _ _ => PUnit.unit
  block := fun _ _ => PUnit.unit
  classify := classify
  classify_arrow := by
    intro current scope domain codomain
    simp [classify, answerTerm, treeTerm, listTreeTerm]
  quoteField := quoteField
  classify_quote := classify_quote
  quote_classify := quote_classify
  result? := fun _ source => if source = treeTerm then some () else none
  quoteResult := fun _ _ => treeTerm
  result_quote := by intro current scope index; cases index; simp
  quote_result := by
    intro current scope source index accepted
    cases index
    by_cases same : source = treeTerm
    · exact same.symm
    · simp [same] at accepted
  familyName := "SearchTree"
  parameters := [⟨"Answer", .name "Type"⟩]
  indices := []
  sort := .name "Type"

def solved : ResolvedConstructor (registry := registry) (I := interface)
    (parameterCount := 1) [] :=
  ⟨"solved", .data "answer" .answer (.result ())⟩

def branch : ResolvedConstructor (registry := registry) (I := interface)
    (parameterCount := 1) [] :=
  ⟨"branch", .nested "children" "List"
    Mettapedia.TypeTheory.IndexedContainer.Examples.list
    (by simp [PositiveInductiveScenarios.Search.registry]) () (.result ())⟩

def resolvedFamily : ResolvedFamily (registry := registry) (I := interface)
    (parameterCount := 1) [] :=
  ⟨[solved, branch], by decide⟩

def textualFamily : InductiveSyntax.Family := resolvedFamily.quote codec

def resolvedModule : ResolvedModule (registry := registry) (I := interface)
    (parameterCount := 1) [] := ⟨"AgentSearch", "Data", resolvedFamily⟩

def textualModule : Module := resolvedModule.quote codec

theorem family_roundtrip : lowerFamily codec textualFamily = some resolvedFamily := by
  exact lowerFamily_quote codec resolvedFamily

theorem module_roundtrip : lowerModule codec textualModule = some resolvedModule := by
  exact lowerModule_quote codec resolvedModule

theorem module_print_data_exact : resolvedModule.quote codec = textualModule := rfl

/-- The textual route reaches exactly the previously checked nested block. -/
theorem erased_family_eq_existing : resolvedFamily.erase =
    PositiveInductiveScenarios.Search.admitted := by
  rfl

/-- The selected source List order is retained as separate registry evidence. -/
def sourceOrder : ∀ name container, registry.lookup name = some container →
    IndexedContainer.OrderedFinitary container := by
  intro name container found
  by_cases same : name = "List"
  · subst name
    simp [PositiveInductiveScenarios.Search.registry] at found
    subst container
    exact IndexedContainer.Examples.listOrderedFinitary
  · simp [PositiveInductiveScenarios.Search.registry, same] at found

def branchShape (length : Nat) :
    PositiveInductiveBlock.Code.Shape branch.body.erase
      PositiveInductiveScenarios.Search.environment () :=
  ⟨length, ⟨⟨rfl⟩⟩⟩

def positionLabel {length : Nat} :
    PositiveInductiveBlock.Code.Position branch.body.erase (branchShape length) → Nat
  | .inl position => position.val
  | .inr impossible => PEmpty.elim impossible

def sourceChildLabels (length : Nat) : List Nat :=
  (IndexedPositiveContainer.Unindexed.sourcePositions sourceOrder branch.body.erase
    branch.body.erase_registered (branchShape length)).map positionLabel

def indexedChildLabels (length : Nat) : List Nat :=
  let comparison := branch.body.erasureSignatureEquiv
  (IndexedPositiveContainer.Code.orderedPositions
      (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) branch.body.eraseIndexed
      (comparison.shape _ _ (branchShape length))).map
    (fun position => positionLabel ((comparison.position (branchShape length)).symm position))

theorem indexed_child_labels_exact (length : Nat) :
    indexedChildLabels length = sourceChildLabels length :=
  IndexedPositiveContainer.Unindexed.ordered_observations_preserved sourceOrder
    branch.body.erase branch.body.erase_registered (branchShape length) positionLabel

theorem indexed_two_children : indexedChildLabels 2 = [0, 1] := by decide +kernel

theorem indexed_three_children : indexedChildLabels 3 = [0, 1, 2] := by decide +kernel

theorem reordered_children_differ : indexedChildLabels 2 ≠ [1, 0] := by
  rw [indexed_two_children]
  decide

theorem missing_child_differs : indexedChildLabels 2 ≠ [0] := by
  rw [indexed_two_children]
  decide

def unknownContainerFamily : InductiveSyntax.Family :=
  { textualFamily with constructors :=
      [⟨"branch", [⟨"children", .app (.name "Bag") treeTerm⟩], treeTerm⟩] }

theorem unknown_container_refused : lowerFamily codec unknownContainerFamily = none := by
  rfl

def negativeFamily : InductiveSyntax.Family :=
  { textualFamily with constructors :=
      [⟨"bad", [⟨"consume", .arrow treeTerm answerTerm⟩], treeTerm⟩] }

theorem negative_field_refused : lowerFamily codec negativeFamily = none := by
  rfl

def changedHeader : InductiveSyntax.Family :=
  { textualFamily with parameters := [] }

theorem changed_header_refused : lowerFamily codec changedHeader = none := by
  rfl

def duplicateFamily : InductiveSyntax.Family :=
  { textualFamily with constructors :=
      [resolvedFamily.constructors[0].quote codec,
       resolvedFamily.constructors[0].quote codec] }

theorem duplicate_constructor_refused : lowerFamily codec duplicateFamily = none := by
  rfl

def extraBlockModule : Module :=
  { textualModule with theories :=
      [⟨"Data", [], .extend none
        [.inductives [textualFamily], .types ["Extra"]]⟩] }

theorem extra_block_refused : lowerModule codec extraBlockModule = none := by
  rfl

def verdicts : List (String × Bool) :=
  [("registered nested family lowers", (lowerFamily codec textualFamily).isSome),
   ("registered nested module lowers", (lowerModule codec textualModule).isSome),
   ("unknown container refuses", (lowerFamily codec unknownContainerFamily).isNone),
   ("negative field refuses", (lowerFamily codec negativeFamily).isNone),
   ("changed header refuses", (lowerFamily codec changedHeader).isNone),
   ("duplicate constructor refuses", (lowerFamily codec duplicateFamily).isNone),
   ("extra block refuses", (lowerModule codec extraBlockModule).isNone),
   ("indexed SearchTree retains two source positions", indexedChildLabels 2 == [0, 1]),
   ("indexed SearchTree retains three source positions", indexedChildLabels 3 == [0, 1, 2]),
   ("indexed SearchTree rejects reordered observations", indexedChildLabels 2 != [1, 0]),
   ("indexed SearchTree rejects a missing observation", indexedChildLabels 2 != [0])]

theorem all_verdicts : verdicts.all (fun entry => entry.2) = true := by
  decide +kernel

end Search

namespace WholeFamily

open PositiveInductiveScenarios.Search
open IndexedPositiveContainer.Unindexed

theorem source_registered : admitted.WellRegistered :=
  Search.resolvedFamily.erase_registered

abbrev Target := IndexedPolynomial.Fix (blockPolynomial admitted source_registered) environment ()

noncomputable def comparison : SearchTree ≃ Target :=
  blockFamilyEquiv admitted source_registered environment ()

def targetAnswerAlgebra : IndexedPolynomial.Algebra
    (blockPolynomial admitted source_registered) (fun _ _ => List Bool) :=
  (blockSignatureEquiv admitted source_registered).pushAlgebra answerAlgebra

noncomputable def targetAnswers (tree : Target) : List Bool :=
  IndexedPolynomial.Fix.fold (blockPolynomial admitted source_registered)
    targetAnswerAlgebra.act environment () tree

/-- Every search tree, rather than only a constructor endpoint, retains its
generated answer-collecting recursion after the grammar change. -/
theorem answers_preserved (tree : SearchTree) :
    targetAnswers (comparison tree) = answers tree :=
  blockRecursor_preserved admitted source_registered answerAlgebra environment () tree

theorem branch_answers_preserved (children : List SearchTree) :
    targetAnswers (comparison (branch children)) =
      (List.ofFn fun position : Fin children.length => answers (children.get position)).flatten := by
  rw [answers_preserved, answers_branch]

theorem distinct_solved_answers : comparison (solved false) ≠ comparison (solved true) := by
  intro same
  have sourceSame := comparison.injective same
  have observed := congrArg answers sourceSame
  simp only [answers_solved, List.cons.injEq, Bool.false_eq_true, false_and] at observed

theorem two_solved_children :
    targetAnswers (comparison (branch [solved false, solved true])) = [false, true] := by
  rw [branch_answers_preserved]
  simp [List.ofFn_succ, answers_solved]

theorem reordered_answers_differ :
    targetAnswers (comparison (branch [solved false, solved true])) ≠ [true, false] := by
  rw [two_solved_children]
  decide

end WholeFamily

namespace MutualIndex

open PositiveInductiveScenarios.Workflow

theorem registered : RawCode.WellRegistered scheduleCode := by trivial

def shape : PositiveInductiveBlock.Code.Shape scheduleCode environment false :=
  ⟨⟨rfl⟩⟩

def target := IndexedPositiveContainer.Unindexed.liftCode scheduleCode registered

def targetShape : IndexedPositiveContainer.Code.Shape target environment false :=
  IndexedPositiveContainer.Unindexed.shapeEquiv scheduleCode registered environment false shape

def targetPosition : IndexedPositiveContainer.Code.Position target targetShape :=
  IndexedPositiveContainer.Unindexed.positionEquiv scheduleCode registered shape none

/-- The mutual edge changes family: a Workflow constructor requires an Action
child. The embedding must not replace that requirement by the root index. -/
theorem child_index_exact : IndexedPositiveContainer.Code.next target targetShape targetPosition =
    true := by
  exact IndexedPositiveContainer.Unindexed.next_preserved scheduleCode registered shape none

theorem child_index_ne_root :
    IndexedPositiveContainer.Code.next target targetShape targetPosition ≠ false := by
  rw [child_index_exact]
  change (true : Bool) ≠ false
  decide

def verdicts : List (String × Bool) :=
  [("indexed mutual child keeps the Action index",
      (show Bool from IndexedPositiveContainer.Code.next target targetShape targetPosition) == true),
   ("indexed mutual child differs from the Workflow root",
      (show Bool from IndexedPositiveContainer.Code.next target targetShape targetPosition) != false)]

theorem all_verdicts : verdicts.all (fun entry => entry.2) = true := by decide +kernel

end MutualIndex

#print axioms Search.family_roundtrip
#print axioms Search.module_roundtrip
#print axioms Search.erased_family_eq_existing
#print axioms Search.unknown_container_refused
#print axioms Search.negative_field_refused
#print axioms Search.changed_header_refused
#print axioms Search.duplicate_constructor_refused
#print axioms Search.extra_block_refused
#print axioms Search.all_verdicts
#print axioms Search.indexed_child_labels_exact
#print axioms Search.reordered_children_differ
#print axioms Search.missing_child_differs
#print axioms WholeFamily.answers_preserved
#print axioms WholeFamily.branch_answers_preserved
#print axioms WholeFamily.distinct_solved_answers
#print axioms WholeFamily.reordered_answers_differ
#print axioms MutualIndex.child_index_exact
#print axioms MutualIndex.child_index_ne_root

end Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls
