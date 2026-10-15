import Mettapedia.Languages.HOLLight.MeTTa.CacheUnion
import Mettapedia.Languages.HOLLight.MeTTa.TypeInstantiation
import Mettapedia.Languages.HOLLight.MeTTa.TermInstantiationRule

/-!
# Source instantiation in an authorized cache

The hypothesis image uses the source's right-to-left insertion order. Equal
encoded results coalesce while their logical image is retained. Formation is
constructed from the actual admitted maplets; axiom dependencies are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.CacheInstantiation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization

private theorem variable_type_formed (signature : Signature) (entries : List (Ty × Ty))
    (formed : ∀ entry ∈ entries, TypeFormed signature entry.1 ∧ TypeFormed signature entry.2)
    (name : Name) : TypeFormed signature (SourceSubstitution.variableType entries name) := by
  induction entries with
  | nil => simp [SourceSubstitution.variableType, TypeFormed]
  | cons entry rest ih =>
      rcases entry with ⟨replacement, key⟩
      cases key with
      | var key =>
          simp only [SourceSubstitution.variableType]
          split
          · exact (formed (replacement, .var key) (List.mem_cons_self)).1
          · exact ih (fun entry member => formed entry (List.mem_cons_of_mem _ member))
      | op operator arguments =>
          exact ih (fun entry member => formed entry (List.mem_cons_of_mem _ member))

/-- Every replacement selected by the source's first-match type table is
formed, including the behavior of duplicate and non-variable keys. -/
theorem type_replacements_formed (signature : Signature) (entries : List (Ty × Ty))
    (formed : ∀ entry ∈ entries, TypeFormed signature entry.1 ∧ TypeFormed signature entry.2)
    (name : Name) (replacement : Ty)
    (found : (SourceSubstitution.typeSubstitution entries).lookup name = some replacement) :
    TypeFormed signature replacement := by
  have result := variable_type_formed signature entries formed name
  rw [← SourceSubstitution.apply_variable] at result
  simpa only [TypeSubst.apply, found, Option.getD_some] using result

theorem type_annotations (signature : Signature) (entries : List (Ty × Ty))
    (formed : ∀ entry ∈ entries, TypeFormed signature entry.1 ∧ TypeFormed signature entry.2)
    (term : CanonicalTerm) (annotations : AnnotationsFormed signature term.term) :
    AnnotationsFormed signature ((SourceSubstitution.typeOnlySubstitution entries).apply term).term := by
  apply AnnotationsFormed.substitute signature _
    (type_replacements_formed signature entries formed) _ annotations
  intro sourceVar replacement found
  simp [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
    TermSubst.lookup] at found

/-- A successful lookup retains a replacement from the fully checked source
maplet inventory. The replacement is not recursively substituted. -/
theorem term_annotations (signature : Signature) (entries : List TermMapletReading.Entry)
    (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed signature entry)
    (term : CanonicalTerm) (annotations : AnnotationsFormed signature term.term) :
    AnnotationsFormed signature ((TermMapletReading.substitution entries admitted).apply term).term := by
  apply AnnotationsFormed.substitute signature _ _ _ annotations
  · intro name replacement found
    rw [TermMapletReading.substitution_raw] at found
    simp at found
  · intro sourceVar replacement found
    obtain ⟨stored, member, _, same⟩ := TermSubst.lookup_mem found
    rw [TermMapletReading.substitution_raw] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rw [← same]
    exact (formed original present).replacementAnnotations

def hypotheses (constants : Const → Atom) (substitution : TypeCorrectTermSubstitution)
    (items : List CanonicalTerm) : List CanonicalTerm :=
  List.KeyedUnion.merge (TheoremMetadata.hypothesisAtom constants)
    (items.map substitution.apply).reverse []

private theorem encoded_fold (constants : Const → Atom) (substitution : TypeCorrectTermSubstitution)
    (items : List CanonicalTerm) :
    (hypotheses constants substitution items).map (TheoremMetadata.hypothesisAtom constants) =
      ((items.map substitution.apply).map (TheoremMetadata.hypothesisAtom constants)).foldr
        (fun item tail => if item ∈ tail then tail else item :: tail) [] := by
  unfold hypotheses
  rw [List.KeyedUnion.map_keys, List.map_reverse, List.foldl_reverse]
  congr 1
  funext item tail
  by_cases present : item ∈ tail <;> simp [present]

theorem term_hypotheses_encoded (constants : Const → Atom) (substitution : TypeCorrectTermSubstitution)
    (items : List CanonicalTerm) :
    (hypotheses constants substitution items).map (TheoremMetadata.hypothesisAtom constants) =
      TermInstantiationRule.Hypotheses.imageOccurrences constants substitution items := by
  rw [encoded_fold]
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simpa only [List.map_cons, List.foldr_cons, TermInstantiationRule.Hypotheses.imageOccurrences] using
        congrArg (fun tail => if TheoremMetadata.hypothesisAtom constants (substitution.apply first) ∈ tail
          then tail else TheoremMetadata.hypothesisAtom constants (substitution.apply first) :: tail) ih

theorem type_hypotheses_encoded (constants : Const → Atom) (entries : List (Ty × Ty))
    (items : List CanonicalTerm) :
    (hypotheses constants (SourceSubstitution.typeOnlySubstitution entries) items).map
        (TheoremMetadata.hypothesisAtom constants) =
      TypeInstantiation.Hypotheses.imageOccurrences constants entries items := by
  rw [encoded_fold]
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simpa only [List.map_cons, List.foldr_cons, TypeInstantiation.Hypotheses.imageOccurrences] using
        congrArg (fun tail => if TheoremMetadata.hypothesisAtom constants
          ((SourceSubstitution.typeOnlySubstitution entries).apply first) ∈ tail then tail else
          TheoremMetadata.hypothesisAtom constants
            ((SourceSubstitution.typeOnlySubstitution entries).apply first) :: tail) ih

theorem hypotheses_support (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (substitution : TypeCorrectTermSubstitution)
    (items : List CanonicalTerm)
    (formed : ∀ item ∈ items, AnnotationsFormed world.signature (substitution.apply item).term) :
    (hypotheses constants substitution items).toFinset = substitution.applyHypotheses items.toFinset := by
  have imageFormed : ∀ item ∈ (items.map substitution.apply).reverse ++ [],
      AnnotationsFormed world.signature item.term := by
    intro item member
    have mapped : item ∈ items.map substitution.apply := by simpa using member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp mapped
    exact formed original present
  have support := List.KeyedUnion.readout_support (TheoremMetadata.hypothesisAtom constants) id
    (items.map substitution.apply).reverse [] (by
      intro first firstMember second secondMember same
      exact CanonicalTerm.ext_term (TermReflection.registered_termAtom_injective world constants identified []
        first.term second.term (imageFormed first firstMember) (imageFormed second secondMember) same))
  simpa only [hypotheses, List.map_id, List.toFinset_reverse, List.toFinset_nil,
    Finset.union_empty, List.toFinset_map, TypeCorrectTermSubstitution.applyHypotheses] using support

def record (constants : Const → Atom) (substitution : TypeCorrectTermSubstitution)
    (source : Record) (origin : Atom) : Record :=
  ⟨hypotheses constants substitution source.hypotheses, substitution.apply source.conclusion,
    source.dependencies, origin⟩

theorem record_fact (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (substitution : TypeCorrectTermSubstitution)
    (source : Record) (origin : Atom)
    (formed : ∀ item ∈ source.hypotheses, AnnotationsFormed world.signature (substitution.apply item).term) :
    (record constants substitution source origin).fact = substituteTheorem substitution source.fact := by
  apply HasParts.eq
  exact ⟨rfl, hypotheses_support world constants identified substitution source.hypotheses formed, rfl⟩

theorem record_formed (world : TheoryContext) (constants : Const → Atom)
    (substitution : TypeCorrectTermSubstitution) (source : Record) (origin : Atom)
    (sourceFormed : TheoremFormed world.signature source.fact)
    (preserves : ∀ term, AnnotationsFormed world.signature term.term →
      AnnotationsFormed world.signature (substitution.apply term).term) :
    TheoremFormed world.signature (record constants substitution source origin).fact := by
  refine ⟨⟨preserves _ sourceFormed.1.1, ?_⟩, sourceFormed.2⟩
  intro term member
  have retained := List.KeyedUnion.mem_subset (TheoremMetadata.hypothesisAtom constants)
    (source.hypotheses.map substitution.apply).reverse [] (List.mem_toFinset.mp member)
  have mapped : term ∈ source.hypotheses.map substitution.apply := by simpa using retained
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp mapped
  exact preserves original (sourceFormed.1.2 original (List.mem_toFinset.mpr present))

end Mettapedia.Languages.HOLLight.MeTTa.CacheInstantiation
