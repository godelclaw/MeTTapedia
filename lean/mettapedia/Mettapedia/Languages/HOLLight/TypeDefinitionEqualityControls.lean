import Mettapedia.Languages.HOLLight.TypeDefinitionEquality
import Mettapedia.Languages.HOLLight.ModelInterpretation

/-!
# Equality blocks over an actual witnessed type definition

The existing identity-function witness introduces a genuine singleton subtype
of a function carrier. The local block consumes its actual abstraction law and
an assumed equality of representations of two open values of the new type.
Native qualification must replay the witness and type-definition event before
loading these external premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.TypeDefinitionEquality.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters ContextControls EqualityExpansion GraphExpansion

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def result : SourceTypeDefinitionResult :=
  (admitSourceTypeInTheory coreContext equalityCertificates identityTypeRequest).get
    ModelInterpretation.Controls.identity_source_admitted

theorem admitted : admitSourceTypeInTheory coreContext equalityCertificates identityTypeRequest = some result :=
  (Option.some_get ModelInterpretation.Controls.identity_source_admitted).symm

def sourceValue (name : Name) : CheckedSourceTerm :=
  .ofVariable ⟨name, carrier identityTypeRequest⟩

def left := sourceValue (Name.global "left")
def right := sourceValue (Name.global "right")

def equation : CanonicalTerm :=
  .equalityOfSameType
    (represented identityTypeRequest result left rfl)
    (represented identityTypeRequest result right rfl) rfl

def input : Theorem := Theorem.emptyResult {equation} equation

theorem left_roundtrip : CanonicalTerm.EqualityViewSemantics
    (roundtripTheorem identityTypeRequest result left rfl).sequent.concl
    (roundtrip identityTypeRequest result left rfl) left.canonical :=
  roundtrip_view admitted left rfl

theorem input_checked : checkAssume equation = some input := by
  apply (checkAssume_eq_some_iff _ _).mpr
  exact ⟨CanonicalTerm.EqualityConstructionSemantics.resultIsBool
    (CanonicalTerm.equalityOfSameType_semantics
      (represented identityTypeRequest result left rfl)
      (represented identityTypeRequest result right rfl) rfl), rfl, rfl, rfl⟩

def compiled := compileRepresentation identityTypeRequest result left right rfl rfl input
  emptyAxiomPolicy ("type-definition-representation", 0)

theorem compiled_checked : ∃ block, compiled = some block ∧
    BlockChecked emptyAxiomPolicy [result.output.abstractionRepresentationTheorem, input]
      (representationEqualityResult identityTypeRequest result left right rfl rfl input) block :=
  compileRepresentation_checked identityTypeRequest result left right rfl rfl input
    emptyAxiomPolicy admitted
    (equality_view (represented identityTypeRequest result left rfl)
      (represented identityTypeRequest result right rfl) rfl)
    ("type-definition-representation", 0)

theorem available : compiled.isSome = true := by
  obtain ⟨block, found, _⟩ := compiled_checked
  simp only [found, Option.isSome_some]

def block : ProofSystem.Certificate := compiled.get available

theorem block_checked : BlockChecked emptyAxiomPolicy
    [result.output.abstractionRepresentationTheorem, input]
    (representationEqualityResult identityTypeRequest result left right rfl rfl input) block := by
  obtain ⟨actual, found, checked⟩ := compiled_checked
  have same : actual = block := Option.some.inj (found.symm.trans (Option.some_get available).symm)
  exact same ▸ checked

theorem thirteen_nodes : block.1.length = 13 :=
  compileRepresentation_nodes identityTypeRequest result left right rfl rfl input
    emptyAxiomPolicy ("type-definition-representation", 0) (Option.some_get available).symm

theorem definition_axioms_empty : result.output.abstractionRepresentationTheorem.axioms = ∅ := by
  rw [(admitSourceTypeInTheory_result admitted).2.2.1]
  rfl

theorem conclusion_shape :
    (representationEqualityResult identityTypeRequest result left right rfl rfl input).sequent.concl.term =
      CanonicalTerm.equalityDB (carrier identityTypeRequest) left.canonical.term right.canonical.term := rfl

/-- A different stored definition equation cannot be substituted for the
selected abstraction/representation premise. -/
theorem wrong_definition_seed_refused :
    Mettapedia.Logic.DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy)
      #[result.output.representationAbstractionTheorem, input] block.1 = none := by
  decide +kernel

theorem result_axioms_empty :
    (representationEqualityResult identityTypeRequest result left right rfl rfl input).axioms = ∅ := by
  rw [representationEqualityResult_axioms identityTypeRequest result left right rfl rfl input admitted]
  rfl

def exactReplay : Bool :=
  match Mettapedia.Logic.DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy)
      #[result.output.abstractionRepresentationTheorem, input] block.1 with
  | none => false
  | some cache => match cache[block.2]? with
    | none => false
    | some actual => actual.structuralSame
        (representationEqualityResult identityTypeRequest result left right rfl rfl input)

theorem exactReplay_true : exactReplay = true := by
  obtain ⟨cache, replayed, selected⟩ := block_checked
  simp only [exactReplay, replayed, selected, Theorem.structuralSame_eq_true_iff]

def verdicts : List (String × Bool) :=
  [("witnessed type-definition equality block has thirteen primitive nodes", decide (block.1.length = 13)),
   ("type-definition equality block replays with its exact stored premises", exactReplay),
   ("type-definition equality block refuses the other definition equation", decide
     (Mettapedia.Logic.DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy)
       #[result.output.representationAbstractionTheorem, input] block.1 = none)),
   ("type-definition equality result retains the axiom-free existence witness", decide
     ((representationEqualityResult identityTypeRequest result left right rfl rfl input).axioms = ∅))]

#print axioms compiled_checked
#print axioms block_checked
#print axioms thirteen_nodes
#print axioms wrong_definition_seed_refused

end Mettapedia.Languages.HOLLight.TypeDefinitionEquality.Controls
