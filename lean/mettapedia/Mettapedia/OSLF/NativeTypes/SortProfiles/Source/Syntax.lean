import Mettapedia.OSLF.NativeTypes.SortProfiles.Derived
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableQuotient

open Mettapedia.OSLF.Framework

/-!
# Classifiers for generated constructor-code syntax

Code constructors retain their ordinal in the authored grammar. Their carrier
and universe inputs are read from that declaration and its computed profile.
Carrier formation and universe formation are independent inductive judgments;
the executable readers decide them by checking all actual argument positions.

The equation-class classifier uses the earned typed equation consequences of
the compiled source laws. Its objects are generated constructor codes, rather
than arbitrary operational patterns or arbitrary semantic subobjects.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open ModalHypercube (HSort)

def declaration (language : LanguageDef) (index : Fin language.terms.length) : GrammarRule :=
  language.terms[index]

def operation (language : LanguageDef) (index : Fin language.terms.length) :
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language).Operation :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.constructorOperation language (declaration language index)
    (List.getElem_mem _)

inductive Code (language : LanguageDef) where
  | variableCode (index : Nat)
  | constructor (index : Fin language.terms.length)
      (arguments : Fin (declaration language index).params.length → Code language)

variable {language : LanguageDef}

abbrev Profile (language : LanguageDef) :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)

def Code.carrier? (carriers : Nat → TypeExpr) : Code language → Option TypeExpr
  | .variableCode index => some (carriers index)
  | .constructor index arguments =>
      if ∀ position, (arguments position).carrier? carriers =
          some (declaration language index).params[position].typeExpr
      then some (.base (declaration language index).category) else none

def Code.kind? (profile : Profile language) (sorts : Nat → HSort) :
    Code language → Option HSort
  | .variableCode index => some (sorts index)
  | .constructor index arguments =>
      if ∀ position, (arguments position).kind? profile sorts =
          some (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile (operation language index) position)
      then some (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (operation language index)) else none

inductive Carries (carriers : Nat → TypeExpr) : Code language → TypeExpr → Prop where
  | variableCode (index : Nat) : Carries carriers (.variableCode index) (carriers index)
  | constructor (index : Fin language.terms.length)
      (arguments : Fin (declaration language index).params.length → Code language)
      (children : ∀ position, Carries carriers (arguments position)
        (declaration language index).params[position].typeExpr) :
      Carries carriers (.constructor index arguments) (.base (declaration language index).category)

inductive Kinded (profile : Profile language) (sorts : Nat → HSort) : Code language → HSort → Prop where
  | variableCode (index : Nat) : Kinded profile sorts (.variableCode index) (sorts index)
  | constructor (index : Fin language.terms.length)
      (arguments : Fin (declaration language index).params.length → Code language)
      (children : ∀ position, Kinded profile sorts (arguments position)
        (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile (operation language index) position)) :
      Kinded profile sorts (.constructor index arguments)
        (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (operation language index))

theorem carries_read {carriers : Nat → TypeExpr} {code : Code language} {carrier : TypeExpr}
    (formed : Carries carriers code carrier) : code.carrier? carriers = some carrier := by
  induction formed with
  | variableCode index => rfl
  | constructor index arguments children ih => exact if_pos ih

theorem carrier_read_carries (carriers : Nat → TypeExpr) (code : Code language) :
    ∀ carrier, code.carrier? carriers = some carrier → Carries carriers code carrier := by
  induction code with
  | variableCode index =>
      intro carrier equal
      simp only [Code.carrier?, Option.some.injEq] at equal
      exact equal ▸ .variableCode index
  | constructor index arguments ih =>
      intro carrier equal
      simp only [Code.carrier?] at equal
      split at equal
      · rename_i checked
        simp only [Option.some.injEq] at equal
        subst carrier
        exact .constructor index arguments (fun position => ih position _ (checked position))
      · cases equal

theorem carrier_read_exact (carriers : Nat → TypeExpr) (code : Code language) (carrier : TypeExpr) :
    code.carrier? carriers = some carrier ↔ Carries carriers code carrier :=
  ⟨carrier_read_carries carriers code carrier, carries_read⟩

theorem kinded_read {profile : Profile language} {sorts : Nat → HSort}
    {code : Code language} {sort : HSort} (formed : Kinded profile sorts code sort) :
    code.kind? profile sorts = some sort := by
  induction formed with
  | variableCode index => rfl
  | constructor index arguments children ih => exact if_pos ih

theorem kind_read_kinded (profile : Profile language) (sorts : Nat → HSort) (code : Code language) :
    ∀ sort, code.kind? profile sorts = some sort → Kinded profile sorts code sort := by
  induction code with
  | variableCode index =>
      intro sort equal
      simp only [Code.kind?, Option.some.injEq] at equal
      exact equal ▸ .variableCode index
  | constructor index arguments ih =>
      intro sort equal
      simp only [Code.kind?] at equal
      split at equal
      · rename_i checked
        simp only [Option.some.injEq] at equal
        subst sort
        exact .constructor index arguments (fun position => ih position _ (checked position))
      · cases equal

theorem kind_read_exact (profile : Profile language) (sorts : Nat → HSort)
    (code : Code language) (sort : HSort) :
    code.kind? profile sorts = some sort ↔ Kinded profile sorts code sort :=
  ⟨kind_read_kinded profile sorts code sort, kinded_read⟩

def Universe (profile : Profile language) (sorts : Nat → HSort) (sort : HSort) : Set (Code language) :=
  {code | Kinded profile sorts code sort}

theorem universe_read_exact (profile : Profile language) (sorts : Nat → HSort)
    (sort : HSort) (code : Code language) :
    code ∈ Universe profile sorts sort ↔ code.kind? profile sorts = some sort :=
  (kind_read_exact profile sorts code sort).symm

theorem universes_disjoint (profile : Profile language) (sorts : Nat → HSort) :
    Disjoint (Universe profile sorts .star) (Universe profile sorts .box) := by
  rw [Set.disjoint_left]
  intro code star box
  have first := kinded_read star
  have second := kinded_read box
  rw [first] at second
  cases second

theorem unformed_code_has_no_universe (profile : Profile language) (sorts : Nat → HSort)
    (code : Code language) :
    code.kind? profile sorts = none ↔ ∀ sort, code ∉ Universe profile sorts sort := by
  constructor
  · intro rejected sort formed
    have accepted := kinded_read formed
    rw [rejected] at accepted
    cases accepted
  · intro unformed
    cases result : code.kind? profile sorts with
    | none => rfl
    | some sort => exact False.elim (unformed sort ((kind_read_exact _ _ _ _).mp result))

def Code.display : Code language → Term (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)
  | .variableCode index => .var index
  | .constructor index arguments => .op (operation language index) (fun position => (arguments position).display)

theorem kind_read_display (profile : Profile language) (sorts : Nat → HSort) (code : Code language) :
    code.kind? profile sorts = Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort profile sorts code.display := by
  induction code with
  | variableCode index => rfl
  | constructor index arguments ih =>
      change (if ∀ position, (arguments position).kind? profile sorts =
          some (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile (operation language index) position)
        then some (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (operation language index)) else none) =
        (if ∀ position, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort profile sorts (arguments position).display =
          some (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile (operation language index) position)
        then some (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (operation language index)) else none)
      simp only [← ih]

theorem kinded_display_exact (profile : Profile language) (sorts : Nat → HSort)
    (code : Code language) (sort : HSort) :
    Kinded profile sorts code sort ↔ Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formed profile sorts code.display sort := by
  rw [← kind_read_exact, kind_read_display, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort_exact]

def Convertibility (profile : Profile language) (sorts : Nat → HSort)
    (system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language))
    (first second : Code language) : Prop :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.TypedDisplayConvertibility profile system sorts first.display second.display

theorem kind_read_equation_invariant {profile : Profile language} {sorts : Nat → HSort}
    {system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)}
    (stable : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable system profile) (first second : Code language)
    (equivalent : Convertibility profile sorts system first second) :
    first.kind? profile sorts = second.kind? profile sorts := by
  rw [kind_read_display, kind_read_display]
  exact Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort_equation_invariant stable sorts _ _ equivalent

theorem universe_equation_invariant {profile : Profile language} {sorts : Nat → HSort}
    {system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)}
    (stable : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable system profile) (first second : Code language)
    (equivalent : Convertibility profile sorts system first second) (sort : HSort) :
    first ∈ Universe profile sorts sort ↔ second ∈ Universe profile sorts sort := by
  rw [universe_read_exact, universe_read_exact, kind_read_equation_invariant stable first second equivalent]

def codeSetoid (profile : Profile language) (sorts : Nat → HSort)
    (system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language)) : Setoid (Code language) where
  r := Convertibility profile sorts system
  iseqv := ⟨fun _ => .refl _, fun equivalent => .symm _ _ equivalent,
    fun first second => .trans _ _ _ first second⟩

def quotientKind (profile : Profile language) (sorts : Nat → HSort)
    (system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language))
    (stable : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable system profile) :
    Quotient (codeSetoid profile sorts system) → Option HSort :=
  Quotient.lift (fun code => code.kind? profile sorts) (kind_read_equation_invariant stable)

theorem quotient_kind_exact (profile : Profile language) (sorts : Nat → HSort)
    (system : EquationSystem (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.signature language))
    (stable : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stable system profile) (code : Code language) (sort : HSort) :
    quotientKind profile sorts system stable (Quotient.mk (codeSetoid profile sorts system) code) = some sort ↔
      Kinded profile sorts code sort :=
  kind_read_exact profile sorts code sort

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source
