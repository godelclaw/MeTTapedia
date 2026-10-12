import Mettapedia.GSLT.Parsing.CheckedTreePresentation
import Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec

/-!
# Sorted admission of reified presentation templates

The finite checker resolves every constructor and ordered argument through the
existing codec schema. Its independent typing judgment implies that template
instantiation is total and preserves sorting when the supplied holes have their
declared sorts. Duplicate/reserved constructors use the codec's refusing lookup.

This checks structural rule data. Lexical policy is a schema parameter; source
derivability, C binding, list cardinality and native interpreter correspondence
are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedTreePresentationTemplates

open CanonicalGrammar (CanonicalTerm)
open CheckedTreePresentation (Template instantiate instantiateMany)
open SortedCanonicalSExprCodec

mutual
  def check (schema : Schema) (codec : Notation) (slots : List String)
      (sort : String) : Template → Bool
    | .slot index => slots[index]? == some sort
    | .text spelling =>
        match schema.shape? sort with
        | some (.token _) => schema.acceptsToken sort spelling
        | _ => false
    | .node name children =>
        match schema.shape? sort with
        | some (.constructors declarations) =>
            match constructor? codec declarations name with
            | some declaration => checkArguments schema codec slots declaration.arguments children
            | none => false
        | _ => false
    | .seq elements =>
        match schema.shape? sort with
        | some (.list elementSort) => checkElements schema codec slots elementSort elements
        | _ => false

  def checkArguments (schema : Schema) (codec : Notation) (slots : List String) :
      List String → List Template → Bool
    | [], [] => true
    | sort :: sorts, first :: rest =>
        check schema codec slots sort first && checkArguments schema codec slots sorts rest
    | _, _ => false

  def checkElements (schema : Schema) (codec : Notation) (slots : List String)
      (sort : String) : List Template → Bool
    | [] => true
    | first :: rest =>
        check schema codec slots sort first && checkElements schema codec slots sort rest
end

mutual
  inductive Typed (schema : Schema) (codec : Notation) (slots : List String) :
      String → Template → Prop
    | slot (sort : String) (index : Nat) (selected : slots[index]? = some sort) :
        Typed schema codec slots sort (.slot index)
    | text (sort spelling : String) (representation : TokenRepresentation)
        (shape : schema.shape? sort = some (.token representation))
        (accepted : schema.acceptsToken sort spelling = true) :
        Typed schema codec slots sort (.text spelling)
    | node (sort name : String) (children : List Template)
        (declarations : List Constructor) (declaration : Constructor)
        (shape : schema.shape? sort = some (.constructors declarations))
        (found : constructor? codec declarations name = some declaration)
        (arguments : TypedArguments schema codec slots declaration.arguments children) :
        Typed schema codec slots sort (.node name children)
    | seq (sort elementSort : String) (elements : List Template)
        (shape : schema.shape? sort = some (.list elementSort))
        (children : TypedElements schema codec slots elementSort elements) :
        Typed schema codec slots sort (.seq elements)

  inductive TypedArguments (schema : Schema) (codec : Notation) (slots : List String) :
      List String → List Template → Prop
    | nil : TypedArguments schema codec slots [] []
    | cons {sort : String} {sorts : List String} {first : Template} {rest : List Template}
        (head : Typed schema codec slots sort first)
        (tail : TypedArguments schema codec slots sorts rest) :
        TypedArguments schema codec slots (sort :: sorts) (first :: rest)

  inductive TypedElements (schema : Schema) (codec : Notation) (slots : List String) :
      String → List Template → Prop
    | nil (sort : String) : TypedElements schema codec slots sort []
    | cons {sort : String} {first : Template} {rest : List Template}
        (head : Typed schema codec slots sort first)
        (tail : TypedElements schema codec slots sort rest) :
        TypedElements schema codec slots sort (first :: rest)
end

mutual
  theorem check_sound (schema : Schema) (codec : Notation) (slots : List String)
      (sort : String) (body : Template) (checked : check schema codec slots sort body = true) :
      Typed schema codec slots sort body := by
    cases body with
    | slot index => exact .slot sort index (beq_iff_eq.mp checked)
    | text spelling =>
        cases shape : schema.shape? sort with
        | none => simp [check, shape] at checked
        | some value =>
            cases value with
            | token representation => exact .text sort spelling representation shape (by simpa [check, shape] using checked)
            | list elementSort => simp [check, shape] at checked
            | constructors declarations => simp [check, shape] at checked
    | node name children =>
        cases shape : schema.shape? sort with
        | none => simp [check, shape] at checked
        | some value =>
            cases value with
            | token representation => simp [check, shape] at checked
            | list elementSort => simp [check, shape] at checked
            | constructors declarations =>
                cases found : constructor? codec declarations name with
                | none => simp [check, shape, found] at checked
                | some declaration =>
                    exact .node sort name children declarations declaration shape found
                      (checkArguments_sound schema codec slots declaration.arguments children
                        (by simpa [check, shape, found] using checked))
    | seq elements =>
        cases shape : schema.shape? sort with
        | none => simp [check, shape] at checked
        | some value =>
            cases value with
            | token representation => simp [check, shape] at checked
            | constructors declarations => simp [check, shape] at checked
            | list elementSort =>
                exact .seq sort elementSort elements shape
                  (checkElements_sound schema codec slots elementSort elements
                    (by simpa [check, shape] using checked))
  termination_by sizeOf body

  theorem checkArguments_sound (schema : Schema) (codec : Notation) (slots : List String)
      (sorts : List String) (bodies : List Template)
      (checked : checkArguments schema codec slots sorts bodies = true) :
      TypedArguments schema codec slots sorts bodies := by
    cases sorts with
    | nil => cases bodies with
      | nil => exact .nil
      | cons first rest => cases checked
    | cons sort sorts => cases bodies with
      | nil => cases checked
      | cons first rest =>
          simp only [checkArguments, Bool.and_eq_true] at checked
          exact .cons (check_sound schema codec slots sort first checked.1)
            (checkArguments_sound schema codec slots sorts rest checked.2)
  termination_by sizeOf bodies

  theorem checkElements_sound (schema : Schema) (codec : Notation) (slots : List String)
      (sort : String) (bodies : List Template)
      (checked : checkElements schema codec slots sort bodies = true) :
      TypedElements schema codec slots sort bodies := by
    cases bodies with
    | nil => exact .nil sort
    | cons first rest =>
        simp only [checkElements, Bool.and_eq_true] at checked
        exact .cons (check_sound schema codec slots sort first checked.1)
          (checkElements_sound schema codec slots sort rest checked.2)
  termination_by sizeOf bodies
end

theorem argument_lookup (schema : Schema) (codec : Notation)
    {sorts : List String} {values : List CanonicalTerm}
    (typed : SortedArguments schema codec sorts values)
    (index : Nat) (sort : String) (selected : sorts[index]? = some sort) :
    ∃ value, values[index]? = some value ∧ Sorted schema codec sort value := by
  cases typed with
  | nil => simp at selected
  | @cons firstSort sorts first values head tail =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst sort
          exact ⟨first, rfl, head⟩
      | succ index => exact argument_lookup schema codec tail index sort (by simpa using selected)
termination_by index

mutual
  theorem instantiate_sorted (schema : Schema) (codec : Notation) (slots : List String)
      (values : List CanonicalTerm) (sort : String) (body : Template)
      (typed : Typed schema codec slots sort body)
      (arguments : SortedArguments schema codec slots values) :
      ∃ result, instantiate values body = some result ∧ Sorted schema codec sort result := by
    cases typed with
    | slot sort index selected =>
        obtain ⟨value, found, valid⟩ := argument_lookup schema codec arguments index sort selected
        exact ⟨value, found, valid⟩
    | text sort spelling representation shape accepted =>
        exact ⟨.text spelling, rfl, .token sort spelling representation shape accepted⟩
    | node sort name children declarations declaration shape found childrenTyped =>
        obtain ⟨results, expanded, valid⟩ := instantiateArguments_sorted schema codec slots values
          declaration.arguments children childrenTyped arguments
        exact ⟨.node name results, by simp [instantiate, expanded],
          .node sort name declarations declaration results shape found valid⟩
    | seq sort elementSort elements shape childrenTyped =>
        obtain ⟨results, expanded, valid⟩ := instantiateElements_sorted schema codec slots values
          elementSort elements childrenTyped arguments
        exact ⟨.seq results, by simp [instantiate, expanded], .list sort elementSort results shape valid⟩
  termination_by sizeOf body

  theorem instantiateArguments_sorted (schema : Schema) (codec : Notation)
      (slots : List String) (values : List CanonicalTerm) (sorts : List String)
      (bodies : List Template) (typed : TypedArguments schema codec slots sorts bodies)
      (arguments : SortedArguments schema codec slots values) :
      ∃ results, instantiateMany values bodies = some results ∧
        SortedArguments schema codec sorts results := by
    cases typed with
    | nil => exact ⟨[], rfl, .nil⟩
    | @cons sort sorts first rest head tail =>
        obtain ⟨value, expanded, valid⟩ := instantiate_sorted schema codec slots values sort first head arguments
        obtain ⟨results, expandedRest, validRest⟩ := instantiateArguments_sorted schema codec slots values sorts rest tail arguments
        exact ⟨value :: results, by simp [instantiateMany, expanded, expandedRest], .cons valid validRest⟩
  termination_by sizeOf bodies

  theorem instantiateElements_sorted (schema : Schema) (codec : Notation)
      (slots : List String) (values : List CanonicalTerm) (sort : String)
      (bodies : List Template) (typed : TypedElements schema codec slots sort bodies)
      (arguments : SortedArguments schema codec slots values) :
      ∃ results, instantiateMany values bodies = some results ∧
        SortedElements schema codec sort results := by
    cases typed with
    | nil => exact ⟨[], rfl, .nil sort⟩
    | @cons sort first rest head tail =>
        obtain ⟨value, expanded, valid⟩ := instantiate_sorted schema codec slots values sort first head arguments
        obtain ⟨results, expandedRest, validRest⟩ := instantiateElements_sorted schema codec slots values sort rest tail arguments
        exact ⟨value :: results, by simp [instantiateMany, expanded, expandedRest], .cons valid validRest⟩
  termination_by sizeOf bodies
end

theorem checked_instantiation_sorted (schema : Schema) (codec : Notation)
    (slots : List String) (values : List CanonicalTerm) (sort : String) (body : Template)
    (checked : check schema codec slots sort body = true)
    (arguments : SortedArguments schema codec slots values) :
    ∃ result, instantiate values body = some result ∧ Sorted schema codec sort result :=
  instantiate_sorted schema codec slots values sort body
    (check_sound schema codec slots sort body checked) arguments

end Mettapedia.GSLT.Parsing.SortedTreePresentationTemplates
