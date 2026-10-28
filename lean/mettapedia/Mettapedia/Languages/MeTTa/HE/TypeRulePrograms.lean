import Mettapedia.Languages.MeTTa.HE.TypeRuleViews
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplication
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# HE source rule instances in the existing open proof checker

An inventory contains local instances of the independent HE rules, including
their actual policy and negative-selection guards. It does not contain proofs
of their recursive premises. Compilation retains each instance occurrence and
each premise position. A finite judgment dictionary gives those exact source
requests compact, disjoint checker names; readable sequents remain available
through `TypeRuleData`.

Structural validation uses the existing calculus validator. Source reflection
uses the original local rules, not the displayed descriptions of their guards.
An arbitrary decoded rule view is therefore not an admitted inventory entry.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeRulePrograms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open InferenceChecker CertificateGSLT
open Spec.Type Spec.Type.RulePresentation

variable {space : Space} {lookup : TypeLookupRel} {matching : Matching}

abbrev Instance (space : Space) (lookup : TypeLookupRel) (matching : Matching) :=
  Σ premises : List Judgment, Σ goal : Judgment, Rule space lookup matching premises goal

def dictionary (inventory : List (Instance space lookup matching)) : List Judgment :=
  inventory.flatMap fun entry => entry.1 ++ [entry.2.1]

private def ordinal (value : Nat) : String :=
  Mettapedia.OSLF.Binding.WireCodec.Binary.Text.render
    (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith
      Mettapedia.OSLF.Binding.WireCodec.Codec.nat value)

private theorem ordinal_injective : Function.Injective ordinal := by
  intro left right same
  have decoded := congrArg (fun text => do
    let word ← Mettapedia.OSLF.Binding.WireCodec.Binary.Text.parse text
    Mettapedia.OSLF.Binding.WireCodec.Binary.decodeWith
      Mettapedia.OSLF.Binding.WireCodec.Codec.nat word) same
  simpa only [ordinal, Mettapedia.OSLF.Binding.WireCodec.Binary.Text.parse_render,
    Mettapedia.OSLF.Binding.WireCodec.Binary.decodeWith_encodeWith,
    Bind.bind, Option.bind, Option.some.injEq] using decoded

def judgmentName (judgments : List Judgment) (goal : Judgment) : String :=
  "HE-reference-judgment/" ++ ordinal (judgments.idxOf goal)

def encode (judgments : List Judgment) (goal : Judgment) : Pattern :=
  .apply (judgmentName judgments goal) []

theorem encode_injective_on {judgments : List Judgment} {left right : Judgment}
    (leftMember : left ∈ judgments) (_rightMember : right ∈ judgments)
    (same : encode judgments left = encode judgments right) : left = right := by
  have heads : judgmentName judgments left = judgmentName judgments right := by
    simpa only [encode, Pattern.apply.injEq, and_true] using same
  have positions := ordinal_injective ((String.append_right_inj "HE-reference-judgment/").mp heads)
  exact (List.idxOf_inj leftMember).mp positions

/-- Unknown requests are refused before indexing; the out-of-range index is
never used as a catch-all judgment. -/
def request? (judgments : List Judgment) (goal : Judgment) : Option Pattern :=
  if goal ∈ judgments then some (encode judgments goal) else none

def ruleId (position : Nat) : RuleId := ⟨"HE-reference-rule/" ++ ordinal position⟩

theorem ruleId_injective : Function.Injective ruleId := by
  intro left right same
  exact ordinal_injective ((String.append_right_inj "HE-reference-rule/").mp
    (congrArg RuleId.value same))

def schema (judgments : List Judgment) (position : Nat)
    (entry : Instance space lookup matching) : RuleSchema :=
  ⟨ruleId position, [], entry.1.map (encode judgments), encode judgments entry.2.1, []⟩

def compile (inventory : List (Instance space lookup matching)) : CalculusLanguageDef :=
  let judgments := dictionary inventory
  CalculusLanguageDef.extend (LanguageDef.empty "HE-reference-instances")
    { judgments := (judgments.map (judgmentName judgments)).eraseDups.map fun name => ⟨name, 0⟩
      rules := inventory.zipIdx.map fun (entry, position) => schema judgments position entry }

def compile? (inventory : List (Instance space lookup matching)) := (compile inventory).validate?

theorem entry_judgments {inventory : List (Instance space lookup matching)}
    {entry : Instance space lookup matching} (member : entry ∈ inventory) :
    entry.2.1 ∈ dictionary inventory ∧ ∀ premise ∈ entry.1, premise ∈ dictionary inventory := by
  constructor
  · exact List.mem_flatMap.mpr ⟨entry, member, by simp⟩
  · intro premise present
    exact List.mem_flatMap.mpr ⟨entry, member, List.mem_append_left _ present⟩

theorem schema_premises_ground (judgments : List Judgment) (premises : List Judgment) :
    Pattern.isGroundListAt 0 (premises.map (encode judgments)) = true := by
  induction premises with
  | nil => rfl
  | cons _ _ ih => simpa [Pattern.isGroundListAt, encode, Pattern.isGroundAt] using ih

theorem application_source {inventory : List (Instance space lookup matching)}
    (valid : (compile inventory).isValid = true)
    {call : RuleInstance} {premises : List Pattern} {goal : Pattern}
    (application : RuleApplication ⟨compile inventory, valid⟩ call premises goal) :
    ∃ entry ∈ inventory, premises = entry.1.map (encode (dictionary inventory)) ∧
      goal = encode (dictionary inventory) entry.2.1 := by
  obtain ⟨rule, found, _, _, children, conclusion⟩ := application
  have member : rule ∈ (compile inventory).rules := List.mem_of_find?_eq_some found
  obtain ⟨⟨entry, position⟩, source, equal⟩ := List.mem_map.mp member
  subst rule
  have original : entry ∈ inventory := by
    exact List.fst_mem_of_mem_zipIdx source
  refine ⟨entry, original, ?_, ?_⟩
  · have actual := instantiateSchemasAt?_complete children
    have fixed := instantiateSchemasAt?_eq_self_of_ground [] call.arguments 0
      (entry.1.map (encode (dictionary inventory))) (schema_premises_ground _ _)
    exact (Option.some.inj (actual.symm.trans fixed))
  · have actual := instantiateSchemaAt?_complete conclusion
    have fixed := instantiateSchemaAt?_eq_self_of_ground [] call.arguments 0
      (encode (dictionary inventory) entry.2.1) (by rfl)
    exact Option.some.inj (actual.symm.trans fixed)

/-- The model realizes exact dictionary requests by their independent HE
source meaning. Its operations use local rule soundness, never a whole-tree
soundness premise or an unchecked guard description. -/
abbrev SourceValue (judgments : List Judgment) (pattern : Pattern) :=
  PLift (∃ goal : Judgment, goal ∈ judgments ∧ encode judgments goal = pattern ∧
    Source space lookup matching goal)

def sourceModel (inventory : List (Instance space lookup matching))
    (valid : (compile inventory).isValid = true) :
    Model ⟨⟨compile inventory, valid⟩⟩ where
  carrier := SourceValue (space := space) (lookup := lookup) (matching := matching) (dictionary inventory)
  onRule := by
    intro call premises goal application children
    apply PLift.up
    obtain ⟨entry, member, premiseEq, goalEq⟩ := application_source valid application
    subst premises goal
    refine ⟨entry.2.1, (entry_judgments member).1, rfl, local_sound entry.2.2 ?_⟩
    intro position
    let child := children.get ⟨position.val, by simp⟩
    obtain ⟨actual, actualMember, actualEq, meaning⟩ := child.down
    have same : actual = entry.1[position] := encode_injective_on actualMember
      ((entry_judgments member).2 _ (List.getElem_mem _)) (by simpa using actualEq)
    exact same ▸ meaning

/-- Generic open-proof acceptance establishes the independent HE source
judgment. Open assumptions retain their exact positions and source meaning. -/
theorem accepted_open_source {inventory : List (Instance space lookup matching)}
    (valid : (compile inventory).isValid = true) {premises : List Pattern} {goal : Judgment}
    (member : goal ∈ dictionary inventory) {proof : RawOpenProof}
    (checked : checkOpenRaw ⟨compile inventory, valid⟩ premises
      (encode (dictionary inventory) goal) proof = true)
    (assumptions : RealizationList (sourceModel inventory valid).carrier premises) :
    Source space lookup matching goal := by
  obtain ⟨derivation, _⟩ := checkOpenRaw_exact_derivation checked
  obtain ⟨actual, actualMember, actualEq, meaning⟩ :=
    ((sourceModel inventory valid).denoteOpen derivation assumptions).down
  exact (encode_injective_on actualMember member actualEq) ▸ meaning

theorem accepted_source {inventory : List (Instance space lookup matching)}
    (valid : (compile inventory).isValid = true) {goal : Judgment}
    (member : goal ∈ dictionary inventory) {proof : RawOpenProof}
    (checked : checkOpenRaw ⟨compile inventory, valid⟩ []
      (encode (dictionary inventory) goal) proof = true) :
    Source space lookup matching goal :=
  accepted_open_source valid member checked .nil

#print axioms encode_injective_on
#print axioms application_source
#print axioms accepted_source

end Mettapedia.Languages.MeTTa.HE.TypeRulePrograms
