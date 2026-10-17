import Mettapedia.GSLT.Parsing.PreparedSortedCodecSchema
import Mettapedia.GSLT.Parsing.SortedTreePresentationTemplates

/-!
# Conservative extension of finite sorted codec schemas

The checker compares actual prepared shape tables. Tokens keep their
representation, lists keep their element sort, and every old constructor has
exactly the same unique lookup and ordered argument sorts in the new table.
The lexical acceptance provider and notation remain fixed. Previously typed
templates retain their slot constraints and structural result sorts.

This is a structural compatibility certificate. It does not certify a changed
constructor interpretation, source lexer, ambiguity policy, binding program,
native parser or printer.
Document migration must retain those separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedSchemaExtension

open SortedCanonicalSExprCodec
open PreparedSortedCodecSchema
open SortedCodecMetadataAdmission (lookup? lookup_sound)
open CanonicalGrammar (CanonicalTerm)

def shapeExtends (profile : Notation) : Shape → Shape → Bool
  | .token old, .token new => old == new
  | .list old, .list new => old == new
  | .constructors old, .constructors new =>
      old.all (fun declaration => constructor? profile new declaration.name == some declaration)
  | _, _ => false

def wellFormed (profile : Notation) (entries : List Entry) : Bool :=
  decide (entries.map Entry.name).Nodup && entries.all fun entry => match entry.shape with
    | .token _ => true
    | .list element => entries.any (fun row => row.name == element)
    | .constructors declarations =>
        decide (declarations.map Constructor.name).Nodup && declarations.all fun declaration =>
          declaration.name != profile.listName && declaration.name != profile.symbolName &&
            declaration.arguments.all (fun sort => entries.any (fun row => row.name == sort))

def check (profile : Notation) (before after : List Entry) : Bool :=
  wellFormed profile before && wellFormed profile after &&
    before.all fun entry => match lookup? Entry.name after entry.name with
    | some next => shapeExtends profile entry.shape next.shape
    | none => false

theorem constructor_member (profile : Notation) (declarations : List Constructor)
    (name : String) (declaration : Constructor)
    (found : constructor? profile declarations name = some declaration) :
    declaration ∈ declarations := by
  unfold constructor? at found
  split at found
  · contradiction
  · split at found
    · rename_i candidate filtered
      cases found
      apply List.mem_of_mem_filter
      rw [filtered]
      simp
    · contradiction

theorem checked_shape (profile : Notation) (before after : List Entry)
    (checked : check profile before after = true)
    (accepts : String → String → Bool) (sort : String) (shape : Shape)
    (present : (preparedSchema before accepts).shape? sort = some shape) :
    ∃ next, (preparedSchema after accepts).shape? sort = some next ∧
      shapeExtends profile shape next = true := by
  cases old : lookup? Entry.name before sort with
  | none => simp [preparedSchema, old] at present
  | some entry =>
      have selected := lookup_sound Entry.name before sort entry old
      have allRows : before.all (fun entry => match lookup? Entry.name after entry.name with
          | some next => shapeExtends profile entry.shape next.shape
          | none => false) = true := by
        simp only [check, Bool.and_eq_true] at checked
        exact checked.2
      have accepted := (List.all_eq_true.mp allRows) entry selected.1
      have shaped : entry.shape = shape := by simpa [preparedSchema, old] using present
      cases new : lookup? Entry.name after sort with
      | none => simp [selected.2, new] at accepted
      | some next =>
          refine ⟨next.shape, ?_, ?_⟩
          · simp [preparedSchema, new]
          · simpa [selected.2, new, shaped] using accepted

theorem token_shape (profile : Notation) (representation : TokenRepresentation)
    (shape : Shape) (compatible : shapeExtends profile (.token representation) shape = true) :
    shape = .token representation := by
  cases shape <;> simp [shapeExtends] at compatible ⊢
  exact compatible.symm

theorem list_shape (profile : Notation) (element : String)
    (shape : Shape) (compatible : shapeExtends profile (.list element) shape = true) :
    shape = .list element := by
  cases shape <;> simp [shapeExtends] at compatible ⊢
  exact compatible.symm

theorem constructor_lookup (profile : Notation) (old : List Constructor)
    (shape : Shape) (compatible : shapeExtends profile (.constructors old) shape = true)
    (name : String) (declaration : Constructor)
    (found : constructor? profile old name = some declaration) :
    ∃ next, shape = .constructors next ∧ constructor? profile next name = some declaration := by
  cases shape with
  | token _ => simp [shapeExtends] at compatible
  | list _ => simp [shapeExtends] at compatible
  | constructors next =>
      refine ⟨next, rfl, ?_⟩
      have selected := (List.all_eq_true.mp compatible) declaration (constructor_member profile old name declaration found)
      have named := constructor_name profile old name declaration found
      simpa [named] using selected

mutual
  theorem sorted_transport (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (sort : String) (term : CanonicalTerm)
      (formed : Sorted (preparedSchema before accepts) profile sort term) :
      Sorted (preparedSchema after accepts) profile sort term := by
    cases formed with
    | token sort spelling representation shape accepted =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        have same := token_shape profile representation next compatible
        subst next
        exact .token sort spelling representation present accepted
    | node sort name declarations declaration children shape found arguments =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        obtain ⟨rows, same, selected⟩ := constructor_lookup profile declarations next compatible name declaration found
        rw [same] at present
        exact .node sort name rows declaration children present selected
          (arguments_transport profile before after checked accepts _ _ arguments)
    | list sort element elements shape children =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        have same := list_shape profile element next compatible
        subst next
        exact .list sort element elements present
          (elements_transport profile before after checked accepts _ _ children)
  termination_by sizeOf term

  theorem arguments_transport (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (sorts : List String) (terms : List CanonicalTerm)
      (formed : SortedArguments (preparedSchema before accepts) profile sorts terms) :
      SortedArguments (preparedSchema after accepts) profile sorts terms := by
    cases formed with
    | nil => exact .nil
    | cons head tail =>
        exact .cons (sorted_transport profile before after checked accepts _ _ head)
          (arguments_transport profile before after checked accepts _ _ tail)
  termination_by sizeOf terms

  theorem elements_transport (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (sort : String) (terms : List CanonicalTerm)
      (formed : SortedElements (preparedSchema before accepts) profile sort terms) :
      SortedElements (preparedSchema after accepts) profile sort terms := by
    cases formed with
    | nil => exact .nil sort
    | cons head tail =>
        exact .cons (sorted_transport profile before after checked accepts _ _ head)
          (elements_transport profile before after checked accepts _ _ tail)
  termination_by sizeOf terms
end

mutual
  theorem encode_preserved (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (sort : String) (term : CanonicalTerm)
      (formed : Sorted (preparedSchema before accepts) profile sort term) :
      encode? (preparedSchema after accepts) profile sort term =
        encode? (preparedSchema before accepts) profile sort term := by
    cases formed with
    | token sort spelling representation shape accepted =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        have same := token_shape profile representation next compatible
        subst next
        simp only [encode?, shape, present]
        rfl
    | node sort name declarations declaration children shape found arguments =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        obtain ⟨rows, same, selected⟩ := constructor_lookup profile declarations next compatible name declaration found
        rw [same] at present
        simp [encode?, shape, present, found, selected,
          arguments_encode_preserved profile before after checked accepts _ _ arguments]
    | list sort element elements shape children =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        have same := list_shape profile element next compatible
        subst next
        simp [encode?, shape, present,
          elements_encode_preserved profile before after checked accepts _ _ children]
  termination_by sizeOf term

  theorem arguments_encode_preserved (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (sorts : List String) (terms : List CanonicalTerm)
      (formed : SortedArguments (preparedSchema before accepts) profile sorts terms) :
      encodeArguments? (preparedSchema after accepts) profile sorts terms =
        encodeArguments? (preparedSchema before accepts) profile sorts terms := by
    cases formed with
    | nil => rfl
    | cons head tail =>
        simp only [encodeArguments?]
        rw [encode_preserved profile before after checked accepts _ _ head,
          arguments_encode_preserved profile before after checked accepts _ _ tail]
  termination_by sizeOf terms

  theorem elements_encode_preserved (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (sort : String) (terms : List CanonicalTerm)
      (formed : SortedElements (preparedSchema before accepts) profile sort terms) :
      encodeElements? (preparedSchema after accepts) profile sort terms =
        encodeElements? (preparedSchema before accepts) profile sort terms := by
    cases formed with
    | nil => rfl
    | cons head tail =>
        simp only [encodeElements?]
        rw [encode_preserved profile before after checked accepts _ _ head,
          elements_encode_preserved profile before after checked accepts _ _ tail]
  termination_by sizeOf terms
end

theorem old_wire_preserved (profile : Notation) (before after : List Entry)
    (checked : check profile before after = true) (accepts : String → String → Bool)
    (sort : String) (wire : Mettapedia.Languages.MeTTa.OSLFCore.Atom) (term : CanonicalTerm)
    (decoded : decode? (preparedSchema before accepts) profile sort wire = some term) :
    decode? (preparedSchema after accepts) profile sort wire = some term := by
  have formed := decode_sorted (preparedSchema before accepts) profile sort wire term decoded
  have encoded := encode_decoded (preparedSchema before accepts) profile sort wire term decoded
  have same := encode_preserved profile before after checked accepts sort term formed
  exact decode_encoded (preparedSchema after accepts) profile sort term wire (same.trans encoded)

mutual
  theorem template_transport (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (slots : List String) (sort : String) (body : CheckedTreePresentation.Template)
      (formed : SortedTreePresentationTemplates.Typed (preparedSchema before accepts) profile slots sort body) :
      SortedTreePresentationTemplates.Typed (preparedSchema after accepts) profile slots sort body := by
    cases formed with
    | slot sort index selected => exact .slot sort index selected
    | text sort spelling representation shape accepted =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        have same := token_shape profile representation next compatible
        subst next
        exact .text sort spelling representation present accepted
    | node sort name children declarations declaration shape found arguments =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        obtain ⟨rows, same, selected⟩ := constructor_lookup profile declarations next compatible name declaration found
        rw [same] at present
        exact .node sort name children rows declaration present selected
          (template_arguments_transport profile before after checked accepts slots _ _ arguments)
    | seq sort element elements shape children =>
        obtain ⟨next, present, compatible⟩ := checked_shape profile before after checked accepts sort _ shape
        have same := list_shape profile element next compatible
        subst next
        exact .seq sort element elements present
          (template_elements_transport profile before after checked accepts slots _ _ children)
  termination_by sizeOf body

  theorem template_arguments_transport (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (slots sorts : List String) (bodies : List CheckedTreePresentation.Template)
      (formed : SortedTreePresentationTemplates.TypedArguments (preparedSchema before accepts) profile slots sorts bodies) :
      SortedTreePresentationTemplates.TypedArguments (preparedSchema after accepts) profile slots sorts bodies := by
    cases formed with
    | nil => exact .nil
    | cons head tail =>
        exact .cons (template_transport profile before after checked accepts slots _ _ head)
          (template_arguments_transport profile before after checked accepts slots _ _ tail)
  termination_by sizeOf bodies

  theorem template_elements_transport (profile : Notation) (before after : List Entry)
      (checked : check profile before after = true) (accepts : String → String → Bool)
      (slots : List String) (sort : String) (bodies : List CheckedTreePresentation.Template)
      (formed : SortedTreePresentationTemplates.TypedElements (preparedSchema before accepts) profile slots sort bodies) :
      SortedTreePresentationTemplates.TypedElements (preparedSchema after accepts) profile slots sort bodies := by
    cases formed with
    | nil => exact .nil sort
    | cons head tail =>
        exact .cons (template_transport profile before after checked accepts slots _ _ head)
          (template_elements_transport profile before after checked accepts slots _ _ tail)
  termination_by sizeOf bodies
end

end Mettapedia.GSLT.Parsing.SortedSchemaExtension
