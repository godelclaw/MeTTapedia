import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRealizability

/-!
# Predicate readings of formed source types

Formation retains source well-formedness and a predicate on its selected
carrier. It does not assert that the predicate is a value of a represented
universe. The distinction permits saturated type-family operators while
keeping first-class universe interpretation as a separate obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
  {Γ Ξ : HOL.Ctx Base}

structure GuardedTypeFormation (context : GuardedContext P lex Γ)
    (source : CTm Head Γ.length) (carrier : HOL.Ty Base) where
  formed : CIsType P context.source source
  predicate : HOL.Term Const Γ (carrier ⇒ .prop)
  reading : Reads lex source predicate

namespace GuardedTypeFormation
variable {context : GuardedContext P lex Γ} {source : CTm Head Γ.length} {carrier : HOL.Ty Base}

def snoc (formation : GuardedTypeFormation context source carrier) : GuardedContext P lex (carrier :: Γ) :=
  context.snoc formation.predicate formation.reading formation.formed

def substitute {roots : List (HOL.ClosedFormula Const)} {target : GuardedContext P lex Ξ}
    {raw : CSub Head Γ.length Ξ.length} {code : HOL.Subst Const Γ Ξ}
    (formation : GuardedTypeFormation context source carrier)
    (substitution : GuardedSubstitution roots context target raw code) :
    GuardedTypeFormation target (source.subst raw) carrier where
  formed := substitution.typeFormed formation.formed
  predicate := HOL.subst code formation.predicate
  reading := formation.reading.substitute code raw substitution.represented

def ofValueType {L : Type} [UniverseLevel.LevelOrder L] (levels : TypedEquality.Normalization.LevelModel R L)
    {roots : List (HOL.ClosedFormula Const)} {term : CTm Head Γ.length}
    (value : GuardedRealizer roots context term source carrier) : GuardedTypeFormation context source carrier where
  formed := value.typed.isType levels context.formed
  predicate := value.predicate
  reading := value.typeRead

def ofUniverseValue {roots : List (HOL.ClosedFormula Const)} {level : Head}
    (allowed : R.isUniverse level)
    (value : GuardedRealizer roots context source (.head level) (carrier ⇒ .prop)) :
    GuardedTypeFormation context source carrier where
  formed := ⟨level, allowed, value.typed⟩
  predicate := value.term
  reading := value.termRead

def pi {L : Type} [UniverseLevel.LevelOrder L] (levels : TypedEquality.Normalization.LevelModel R L)
    {A : CTm Head Γ.length} {B : CTm Head (Γ.length + 1)} {domain codomain : HOL.Ty Base}
    (first : GuardedTypeFormation context A domain)
    (second : GuardedTypeFormation first.snoc B codomain) :
    GuardedTypeFormation context (.pi A B) (domain ⇒ codomain) where
  formed := CIsType.pi levels first.formed second.formed
  predicate := HOL.PredicateProducts.pi first.predicate second.predicate
  reading := .product first.reading second.reading

end GuardedTypeFormation
#print axioms GuardedTypeFormation.substitute
#print axioms GuardedTypeFormation.ofUniverseValue
#print axioms GuardedTypeFormation.pi
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
