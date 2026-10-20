import Mettapedia.Logic.HOL.Syntax.ClosedElaboration

/-!
# Finite interning for applicative type contracts

Names and base types in a finite contract become table positions. The source
signature remains authoritative: every entry records a lookup in that signature.
Interning is injective on the admitted type support. Missing constants cannot
alias the last constant, and no two distinct supported types are identified.

This construction prepares constant/application contracts for native checkers.
It does not infer polymorphic instances or admit declarations on its own.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NamedElaboration.FiniteApplicative

variable {Base Name : Type} [DecidableEq Base] [DecidableEq Name]

def baseNames : Ty Base → List Base
  | .prop => []
  | .base name => [name]
  | .arr domain result => baseNames domain ++ baseNames result

def encodeType (bases : List Base) : Ty Base → Ty Nat
  | .prop => .prop
  | .base name => .base (bases.idxOf name)
  | .arr domain result => .arr (encodeType bases domain) (encodeType bases result)

def Covered (bases : List Base) (type : Ty Base) : Prop :=
  ∀ name ∈ baseNames type, name ∈ bases

omit [DecidableEq Base] in
theorem covered_arr_iff (bases : List Base) (domain result : Ty Base) :
    Covered bases (.arr domain result) ↔ Covered bases domain ∧ Covered bases result := by
  simp only [Covered, baseNames, List.mem_append]
  constructor
  · intro all
    exact ⟨fun name member => all name (.inl member),
      fun name member => all name (.inr member)⟩
  · rintro ⟨left, right⟩ name (member | member)
    · exact left name member
    · exact right name member

theorem encodeType_injective_on (bases : List Base) {left right : Ty Base}
    (leftCovered : Covered bases left) (rightCovered : Covered bases right)
    (same : encodeType bases left = encodeType bases right) : left = right := by
  induction left generalizing right with
  | prop => cases right <;> simp_all [encodeType]
  | base name =>
      cases right with
      | prop | arr _ _ => simp [encodeType] at same
      | base other =>
          apply congrArg Ty.base
          exact (List.idxOf_inj (leftCovered name (by simp [baseNames]))).mp (Ty.base.inj same)
  | arr domain result domainIH resultIH =>
      cases right with
      | prop | base _ => simp [encodeType] at same
      | arr otherDomain otherResult =>
          have leftParts := (covered_arr_iff _ _ _).mp leftCovered
          have rightParts := (covered_arr_iff _ _ _).mp rightCovered
          have parts := Ty.arr.inj same
          exact congrArg₂ Ty.arr (domainIH leftParts.1 rightParts.1 parts.1)
            (resultIH leftParts.2 rightParts.2 parts.2)

/-- All constants are numbered; syntax outside the applicative fragment is
mapped to a variable, which closed applicative typing refuses. -/
def encodeTerm (names : List Name) : NamedTerm Base String Name → NamedTerm Nat String Nat
  | .constant name => .constant (names.idxOf name)
  | .app function argument => .app (encodeTerm names function) (encodeTerm names argument)
  | _ => .variable ""

def constantNames : NamedTerm Base String Name → List Name
  | .constant name => [name]
  | .app function argument => constantNames function ++ constantNames argument
  | _ => []

/-- A finite table retains each entry's actual source declaration type. -/
def Support (typeOf : Name → Option (Ty Base)) (names : List Name)
    (types : List (Ty Base)) : Prop :=
  List.Forall₂ (fun name type => typeOf name = some type) names types

omit [DecidableEq Base] [DecidableEq Name] in
theorem Support.lookup {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {index : Nat} {type : Ty Base} (found : types[index]? = some type) :
    ∃ name, names[index]? = some name ∧ typeOf name = some type := by
  induction support generalizing index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                exact ⟨_, rfl, found ▸ first⟩
      | succ index => simpa using ih found

omit [DecidableEq Base] in
theorem Support.at_name {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {name : Name} (member : name ∈ names) : types[names.idxOf name]? = typeOf name := by
  have bound : names.idxOf name < types.length := by
    rw [← support.length_eq]
    exact List.idxOf_lt_length_iff.mpr member
  have found := List.getElem?_eq_getElem bound
  obtain ⟨other, nameFound, typeFound⟩ := support.lookup found
  have equal : other = name := Option.some.inj
    (nameFound.symm.trans (List.getElem?_idxOf member))
  subst other
  exact found.trans typeFound.symm

omit [DecidableEq Base] in
theorem Support.at_index {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {name : Name} {type : Ty Base}
    (found : types[names.idxOf name]? = some type) : typeOf name = some type := by
  have bound : names.idxOf name < names.length := by
    rw [support.length_eq]
    exact (List.getElem?_eq_some_iff.mp found).1
  have member := List.idxOf_lt_length_iff.mp bound
  rw [support.at_name member] at found
  exact found

omit [DecidableEq Base] in
theorem typed_covered {signature : List (Ty Base)} {term : NamedTerm Base String Nat}
    {type : Ty Base} {bases : List Base}
    (covered : ∀ entry ∈ signature, Covered bases entry)
    (typed : ApplicativeTyped (fun index => signature[index]?) term type) : Covered bases type := by
  induction typed with
  | constant lookup => exact covered _ (List.mem_of_getElem? lookup)
  | app _ _ functionIH _ => exact ((covered_arr_iff _ _ _).mp functionIH).2

/-- Direct interning preserves source typing whenever the finite table covers
the constants in this term. -/
theorem encode_typed {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    (bases : List Base) {term : NamedTerm Base String Name} {type : Ty Base}
    (typed : ApplicativeTyped typeOf term type)
    (covered : ∀ name ∈ constantNames term, name ∈ names) :
    ApplicativeTyped (fun index => (types.map (encodeType bases))[index]?)
      (encodeTerm names term) (encodeType bases type) := by
  induction typed with
  | @constant name type lookup =>
      apply ApplicativeTyped.constant
      have member := covered name (by simp [constantNames])
      simp [support.at_name member, lookup]
  | app _ _ functionIH argumentIH =>
      exact .app
        (functionIH (fun name member => covered name (by simp [constantNames, member])))
        (argumentIH (fun name member => covered name (by simp [constantNames, member])))

/-- Every type returned from the interned signature has an original source
type. The coverage premise prevents an absent base name aliasing an index. -/
theorem decode_typed {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    (bases : List Base) (covered : ∀ type ∈ types, Covered bases type)
    {term : NamedTerm Base String Name} {targetType : Ty Nat}
    (typed : ApplicativeTyped (fun index => (types.map (encodeType bases))[index]?)
      (encodeTerm names term) targetType) :
    ∃ type, targetType = encodeType bases type ∧ Covered bases type ∧
      ApplicativeTyped typeOf term type := by
  induction term generalizing targetType with
  | constant name =>
      cases typed with
      | constant lookup =>
          simp only [List.getElem?_map] at lookup
          cases found : types[names.idxOf name]? with
          | none => simp [found] at lookup
          | some type =>
              refine ⟨type, ?_, covered type (List.mem_of_getElem? found),
                .constant (support.at_index found)⟩
              simpa [found] using lookup.symm
  | app function argument functionIH argumentIH =>
      cases typed with
      | @app _ _ domain result functionTyped argumentTyped =>
          obtain ⟨sourceFunction, sameFunction, functionCovered, sourceFunctionTyped⟩ :=
            functionIH functionTyped
          cases sourceFunction with
          | prop | base _ => simp [encodeType] at sameFunction
          | arr sourceDomain sourceResult =>
              obtain ⟨sourceArgument, sameArgument, argumentCovered, sourceArgumentTyped⟩ :=
                argumentIH argumentTyped
              have parts := Ty.arr.inj sameFunction
              have coverage := (covered_arr_iff _ _ _).mp functionCovered
              have same : sourceArgument = sourceDomain := encodeType_injective_on bases
                argumentCovered coverage.1 (sameArgument.symm.trans parts.1)
              subst sourceArgument
              exact ⟨sourceResult, parts.2, coverage.2,
                .app sourceFunctionTyped sourceArgumentTyped⟩
  | _ => cases typed

omit [DecidableEq Base] [DecidableEq Name] in
theorem support_exists {typeOf : Name → Option (Ty Base)}
    {term : NamedTerm Base String Name} {type : Ty Base}
    (typed : ApplicativeTyped typeOf term type) :
    ∃ names types, Support typeOf names types ∧
      ∀ name ∈ constantNames term, name ∈ names := by
  induction typed with
  | @constant name type lookup =>
      exact ⟨[name], [type], .cons lookup .nil, by simp [constantNames]⟩
  | app _ _ functionIH argumentIH =>
      obtain ⟨functionNames, functionTypes, functionSupport, functionCovered⟩ := functionIH
      obtain ⟨argumentNames, argumentTypes, argumentSupport, argumentCovered⟩ := argumentIH
      refine ⟨functionNames ++ argumentNames, functionTypes ++ argumentTypes,
        List.rel_append functionSupport argumentSupport, ?_⟩
      intro name member
      rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ (functionCovered name member)
      · exact List.mem_append_right _ (argumentCovered name member)

def allBases (types : List (Ty Base)) : List Base := types.flatMap baseNames

omit [DecidableEq Base] in
theorem allBases_covers (types : List (Ty Base)) :
    ∀ type ∈ types, Covered (allBases types) type := by
  intro type member name inType
  exact List.mem_flatMap.mpr ⟨type, member, inType⟩

#print axioms encode_typed
#print axioms decode_typed
#print axioms support_exists

end Mettapedia.Logic.HOL.NamedElaboration.FiniteApplicative
