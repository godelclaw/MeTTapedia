import Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable

/-!
# Reflection of registered HOL term identities

The existing representation retains positional occurrences, full free names,
formed types and registered declaration identities. Its injectivity is proved
on that admitted domain. The identity condition has concrete primitive and
definition-extension constructions in DeclarationTable; it is not a soundness
axiom for a checker. Arbitrary unregistered payload maps need not be faithful.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermReflection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Representation (termAtom registeredOperatorAtom)

/-- Equal admitted source representations reflect equality of the existing
shared positional terms, including their constant identities and annotations. -/
theorem registered_termAtom_injective (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (positions : List Ty)
    (left right : DBTerm) (leftFormed : AnnotationsFormed world.signature left)
    (rightFormed : AnnotationsFormed world.signature right)
    (same : termAtom registeredOperatorAtom constants positions left =
      termAtom registeredOperatorAtom constants positions right) : left = right := by
  induction leftFormed generalizing right positions with
  | @constant constant annotation formed declared =>
      cases rightFormed <;> try solve | simp [termAtom, Representation.variableAtom] at same
      rename_i other otherType otherFormed otherDeclared
      simp only [termAtom, Atom.expression.injEq, List.cons.injEq, true_and] at same
      obtain ⟨schema, _, found, _⟩ := declared
      obtain ⟨otherSchema, _, otherFound, _⟩ := otherDeclared
      have constantSame := DeclarationTable.registered_identity_injective world constants identified
        constant other schema otherSchema found otherFound same.1
      have typeSame := Representation.registered_typeAtom_injective world annotation otherType
        formed otherFormed same.2.1
      exact congrArg₂ DBTerm.const constantSame typeSame
  | @free sourceVar formed =>
      cases rightFormed <;> try solve | simp [termAtom, Representation.variableAtom] at same
      rename_i other otherFormed
      have freeSame := (Representation.registered_variableAtom_eq_iff world sourceVar other formed otherFormed).mp
        (by simpa only [termAtom] using same)
      exact congrArg DBTerm.free freeSame
  | bound index =>
      cases rightFormed <;> try solve | simp [termAtom, Representation.variableAtom] at same
      rename_i other
      simp [termAtom] at same
      exact congrArg DBTerm.bound (Int.ofNat.inj same.1)
  | @app function argument functionFormed argumentFormed functionIH argumentIH =>
      cases rightFormed <;> try solve | simp [termAtom, Representation.variableAtom] at same
      rename_i otherFunction otherArgument otherFunctionFormed otherArgumentFormed
      simp only [termAtom, Atom.expression.injEq, List.cons.injEq, true_and] at same
      have functions := functionIH positions otherFunction otherFunctionFormed same.1
      have arguments := argumentIH positions otherArgument otherArgumentFormed same.2.1
      exact congrArg₂ DBTerm.app functions arguments
  | @abs domain body domainFormed bodyFormed bodyIH =>
      cases rightFormed <;> try solve | simp [termAtom, Representation.variableAtom] at same
      rename_i otherDomain otherBody otherDomainFormed otherBodyFormed
      simp only [termAtom, Atom.expression.injEq, List.cons.injEq, true_and] at same
      have domains := Representation.registered_typeAtom_injective world domain otherDomain
        domainFormed otherDomainFormed same.1
      subst otherDomain
      have bodies := bodyIH (domain :: positions) otherBody otherBodyFormed same.2.1
      exact congrArg (DBTerm.abs domain) bodies

theorem registered_termAtom_equal_iff (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (positions : List Ty)
    (left right : DBTerm) (leftFormed : AnnotationsFormed world.signature left)
    (rightFormed : AnnotationsFormed world.signature right) :
    termAtom registeredOperatorAtom constants positions left =
      termAtom registeredOperatorAtom constants positions right ↔ left = right :=
  ⟨registered_termAtom_injective world constants identified positions left right leftFormed rightFormed,
    fun same => congrArg (termAtom registeredOperatorAtom constants positions) same⟩

/-- A different admitted bound occurrence cannot masquerade as the same
term merely by reusing a type annotation or displayed variable spelling. -/
theorem distinct_terms_distinct_representations (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (positions : List Ty)
    (left right : DBTerm) (leftFormed : AnnotationsFormed world.signature left)
    (rightFormed : AnnotationsFormed world.signature right) (different : left ≠ right) :
    termAtom registeredOperatorAtom constants positions left ≠
      termAtom registeredOperatorAtom constants positions right :=
  fun same => different (registered_termAtom_injective world constants identified positions
    left right leftFormed rightFormed same)

end Mettapedia.Languages.HOLLight.MeTTa.TermReflection
