import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Typing with the carriers a language declares

A language declares each of its types with a carrier (`TypeDecl.carrier`): an authored abstract syntax, or a builtin
carrier of integers or strings whose elements are atoms. The declaration-derived typing `WellSorted.HasType` reads only
the constructors; its companion `CarrierWellSorted.HasType` also admits an atom at a type whose carrier accepts it.
The generated logic's typing former reads the companion, so `42 : Integer` holds where `Integer` is declared with the
builtin integers.

- **The typed closed objects** (`CarrierTyped`), decided exactly (`checkCarrierTyped_eq_true_iff`).
- **Every declaration-derived typing is a carrier typing** (`carrierTyped_of_wellSorted`).
- **Without builtin carriers the two coincide** (`carrierTyped_iff_wellSorted`), so a language that declares none keeps
  the declaration-derived typing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- **A closed object term of a type, with the language's carriers**: typed by the carrier-aware judgment, with
canonical binder metadata, an object, scoped at the top. -/
def CarrierTyped (language : LanguageDef) (type : TypeExpr) (pattern : Pattern) : Prop :=
  Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType language FreeTypeContext.empty [] pattern type ∧
    pattern.hasCanonicalBinderMetadata = true ∧ isObjectPattern pattern = true ∧ ScopeSafeAt 0 pattern

/-- **The check of a carrier typing.** -/
def checkCarrierTyped (language : LanguageDef) (type : TypeExpr) (pattern : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType language FreeTypeContext.empty [] pattern type &&
    pattern.hasCanonicalBinderMetadata && isObjectPattern pattern && checkScopeSafeAt 0 pattern

theorem checkCarrierTyped_eq_true_iff {language : LanguageDef} {type : TypeExpr} {pattern : Pattern} :
    checkCarrierTyped language type pattern = true ↔ CarrierTyped language type pattern := by
  unfold checkCarrierTyped CarrierTyped
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨typed, canonical⟩, object⟩, scopeSafe⟩
    exact ⟨(Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_eq_true_iff object).mp typed, canonical,
      object, (checkScopeSafeAt_eq_true_iff 0 pattern).mp scopeSafe⟩
  · rintro ⟨typed, canonical, object, scopeSafe⟩
    exact ⟨⟨⟨(Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_eq_true_iff object).mpr typed, canonical⟩,
      object⟩, (checkScopeSafeAt_eq_true_iff 0 pattern).mpr scopeSafe⟩

instance (language : LanguageDef) (type : TypeExpr) (pattern : Pattern) :
    Decidable (CarrierTyped language type pattern) :=
  decidable_of_iff _ checkCarrierTyped_eq_true_iff

namespace CarrierTyping

open Mettapedia.GSLT.LanguageDef in
mutual
/-- Every declaration-derived typing is a carrier typing. -/
theorem hasType_of_wellSorted {language : LanguageDef} {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
      WellSorted.HasType language free bound pattern type →
        CarrierWellSorted.HasType language free bound pattern type
  | _, _, _, .bvar lookup => .bvar lookup
  | _, _, _, .fvar lookup => .fvar lookup
  | _, _, _, .constructor member bare arguments => .constructor member bare (argumentsHaveTypes_of_wellSorted arguments)
  | _, _, _, .lambda body => .lambda (hasType_of_wellSorted body)
  | _, _, _, .multiLambda body => .multiLambda (hasType_of_wellSorted body)
  | _, _, _, .subst body replacement => .subst (hasType_of_wellSorted body) (hasType_of_wellSorted replacement)
  | _, _, _, .collection elements => .collection (elementsHaveTypes_of_wellSorted elements)
  | _, _, _, .collectionConstructor member bare elements =>
    .collectionConstructor member bare (elementsHaveTypes_of_wellSorted elements)

theorem argumentsHaveTypes_of_wellSorted {language : LanguageDef} {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam},
      WellSorted.ArgumentsHaveTypes language free bound arguments parameters →
        CarrierWellSorted.ArgumentsHaveTypes language free bound arguments parameters
  | _, _, _, .nil => .nil
  | _, _, _, .cons representation expected argument rest =>
    .cons representation expected (hasType_of_wellSorted argument) (argumentsHaveTypes_of_wellSorted rest)

theorem elementsHaveTypes_of_wellSorted {language : LanguageDef} {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr},
      WellSorted.ElementsHaveType language free bound elements elementType →
        CarrierWellSorted.ElementsHaveTypes language free bound elements elementType
  | _, _, _, .nil _ _ => .nil
  | _, _, _, .cons head tail => .cons (hasType_of_wellSorted head) (elementsHaveTypes_of_wellSorted tail)
end

/-- **Whether a carrier accepts atoms**: the builtin integers and strings do. -/
def acceptsAtoms : CarrierKind → Bool
  | .builtinInt | .builtinString => true
  | _ => false

theorem acceptsAtoms_of_accepts {carrier : CarrierKind} {atom : String}
    (accepts : Mettapedia.GSLT.LanguageDef.CarrierWellSorted.carrierAcceptsAtom carrier atom = true) :
    acceptsAtoms carrier = true := by
  cases carrier <;> simp_all [Mettapedia.GSLT.LanguageDef.CarrierWellSorted.carrierAcceptsAtom, acceptsAtoms]

/-- **Whether a language declares no builtin carrier**: no type of it accepts atoms. -/
def NoBuiltinCarriers (language : LanguageDef) : Bool :=
  language.types.all fun declaration =>
    match declaration.carrier with
    | .builtinInt | .builtinString => false
    | _ => true

theorem not_builtinAtom {language : LanguageDef} (none : NoBuiltinCarriers language = true) {atom : String}
    {type : TypeExpr} : ¬ Mettapedia.GSLT.LanguageDef.CarrierWellSorted.BuiltinAtomHasType language atom type := by
  rintro ⟨declaration, member, -, accepts⟩
  have every := List.all_eq_true.mp none declaration member
  cases carrier : declaration.carrier <;> simp_all [Mettapedia.GSLT.LanguageDef.CarrierWellSorted.carrierAcceptsAtom]

open Mettapedia.GSLT.LanguageDef in
mutual
/-- Without builtin carriers a carrier typing is a declaration-derived typing. -/
theorem wellSorted_of_hasType {language : LanguageDef} (none : NoBuiltinCarriers language = true)
    {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
      CarrierWellSorted.HasType language free bound pattern type →
        WellSorted.HasType language free bound pattern type
  | _, _, _, .bvar lookup => .bvar lookup
  | _, _, _, .fvar lookup => .fvar lookup
  | _, _, _, .builtinAtom atom => (not_builtinAtom none atom).elim
  | _, _, _, .constructor member bare arguments =>
    .constructor member bare (wellSortedArguments_of_hasTypes none arguments)
  | _, _, _, .lambda body => .lambda (wellSorted_of_hasType none body)
  | _, _, _, .multiLambda body => .multiLambda (wellSorted_of_hasType none body)
  | _, _, _, .subst body replacement =>
    .subst (wellSorted_of_hasType none body) (wellSorted_of_hasType none replacement)
  | _, _, _, .collection elements => .collection (wellSortedElements_of_hasTypes none elements)
  | _, _, _, .collectionConstructor member bare elements =>
    .collectionConstructor member bare (wellSortedElements_of_hasTypes none elements)

theorem wellSortedArguments_of_hasTypes {language : LanguageDef} (none : NoBuiltinCarriers language = true)
    {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam},
      CarrierWellSorted.ArgumentsHaveTypes language free bound arguments parameters →
        WellSorted.ArgumentsHaveTypes language free bound arguments parameters
  | _, _, _, .nil => .nil
  | _, _, _, .cons representation expected argument rest =>
    .cons representation expected (wellSorted_of_hasType none argument) (wellSortedArguments_of_hasTypes none rest)

theorem wellSortedElements_of_hasTypes {language : LanguageDef} (none : NoBuiltinCarriers language = true)
    {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr},
      CarrierWellSorted.ElementsHaveTypes language free bound elements elementType →
        WellSorted.ElementsHaveType language free bound elements elementType
  | _, _, _, .nil => .nil _ _
  | _, _, _, .cons head tail => .cons (wellSorted_of_hasType none head) (wellSortedElements_of_hasTypes none tail)
end

theorem builtinAtom_congr {language other : LanguageDef} (types : language.types = other.types) {atom : String}
    {type : TypeExpr} :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.BuiltinAtomHasType language atom type →
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.BuiltinAtomHasType other atom type := by
  rintro ⟨declaration, member, same, accepts⟩
  exact ⟨declaration, types ▸ member, same, accepts⟩

open Mettapedia.GSLT.LanguageDef in
mutual
/-- **Carrier typing reads only the types and the constructors.** -/
theorem hasType_congr {language other : LanguageDef} (types : language.types = other.types)
    (terms : language.terms = other.terms) {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
      CarrierWellSorted.HasType language free bound pattern type →
        CarrierWellSorted.HasType other free bound pattern type
  | _, _, _, .bvar lookup => .bvar lookup
  | _, _, _, .fvar lookup => .fvar lookup
  | _, _, _, .builtinAtom atom => .builtinAtom (builtinAtom_congr types atom)
  | _, _, _, .constructor member bare arguments =>
    .constructor (terms ▸ member) bare (argumentsHaveTypes_congr types terms arguments)
  | _, _, _, .lambda body => .lambda (hasType_congr types terms body)
  | _, _, _, .multiLambda body => .multiLambda (hasType_congr types terms body)
  | _, _, _, .subst body replacement => .subst (hasType_congr types terms body) (hasType_congr types terms replacement)
  | _, _, _, .collection elements => .collection (elementsHaveTypes_congr types terms elements)
  | _, _, _, .collectionConstructor member bare elements =>
    .collectionConstructor (terms ▸ member) bare (elementsHaveTypes_congr types terms elements)

theorem argumentsHaveTypes_congr {language other : LanguageDef} (types : language.types = other.types)
    (terms : language.terms = other.terms) {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam},
      CarrierWellSorted.ArgumentsHaveTypes language free bound arguments parameters →
        CarrierWellSorted.ArgumentsHaveTypes other free bound arguments parameters
  | _, _, _, .nil => .nil
  | _, _, _, .cons representation expected argument rest =>
    .cons representation expected (hasType_congr types terms argument) (argumentsHaveTypes_congr types terms rest)

theorem elementsHaveTypes_congr {language other : LanguageDef} (types : language.types = other.types)
    (terms : language.terms = other.terms) {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr},
      CarrierWellSorted.ElementsHaveTypes language free bound elements elementType →
        CarrierWellSorted.ElementsHaveTypes other free bound elements elementType
  | _, _, _, .nil => .nil
  | _, _, _, .cons head tail => .cons (hasType_congr types terms head) (elementsHaveTypes_congr types terms tail)
end

end CarrierTyping

open CarrierTyping

/-- **Every declaration-derived typing of a closed object is a carrier typing.** -/
theorem carrierTyped_of_wellSorted {language : LanguageDef} {type : TypeExpr} {pattern : Pattern}
    (wellSorted : OpenPatternWellSorted language FreeTypeContext.empty [] type pattern) :
    CarrierTyped language type pattern :=
  ⟨hasType_of_wellSorted wellSorted.1, wellSorted.2.1, wellSorted.2.2.1, wellSorted.2.2.2⟩

/-- **Without builtin carriers, a carrier typing is a declaration-derived typing.** -/
theorem wellSorted_of_carrierTyped {language : LanguageDef} (none : NoBuiltinCarriers language = true)
    {type : TypeExpr} {pattern : Pattern} (typed : CarrierTyped language type pattern) :
    OpenPatternWellSorted language FreeTypeContext.empty [] type pattern :=
  ⟨wellSorted_of_hasType none typed.1, typed.2.1, typed.2.2.1, typed.2.2.2⟩

/-- **Without builtin carriers the two typings coincide.** -/
theorem carrierTyped_iff_wellSorted {language : LanguageDef} (none : NoBuiltinCarriers language = true)
    {type : TypeExpr} {pattern : Pattern} :
    CarrierTyped language type pattern ↔ OpenPatternWellSorted language FreeTypeContext.empty [] type pattern :=
  ⟨wellSorted_of_carrierTyped none, carrierTyped_of_wellSorted⟩

/-- **Carrier typing reads only the types and the constructors**: languages that declare the same agree on it. -/
theorem carrierTyped_congr {language other : LanguageDef} (types : language.types = other.types)
    (terms : language.terms = other.terms) {type : TypeExpr} {pattern : Pattern} :
    CarrierTyped language type pattern ↔ CarrierTyped other type pattern :=
  ⟨fun typed => ⟨hasType_congr types terms typed.1, typed.2⟩,
    fun typed => ⟨hasType_congr types.symm terms.symm typed.1, typed.2⟩⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
