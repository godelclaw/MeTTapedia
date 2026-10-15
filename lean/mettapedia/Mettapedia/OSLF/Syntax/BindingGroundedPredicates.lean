import Mettapedia.OSLF.Syntax.BindingPredicateFutureLogic

/-!
# Closed origins and native predicate complements

Closed values enter every context by the actual empty substitution. This
map is natural. Supplied closed values at each sort give a genuine
retraction, so original closed origins remain distinct in every context.
Every native predicate reflects on these origins, and its Heyting negation
agrees there with current exclusion. The whole open program presheaf is
not replaced by this admitted closed-origin family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingGroundedPredicates

open _root_.CategoryTheory FreeBindingTerms BindingSubstitutionAlgebra
open BindingConstructorPredicates IntrinsicScopedConditionalPresheaf
open BindingPredicateFutureLogic
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.GSLT.Topos

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S} {sort : S.Srt}

def emptyEnvironment (context : Ctx S) :
    Environment S A.substitution.Carrier [] context :=
  fun _ impossible => nomatch impossible

def ground (context : Ctx S) (value : A.substitution.Carrier [] sort) :
    A.substitution.Carrier context sort :=
  A.substitution.substitute (emptyEnvironment context) value

theorem substitute_ground {first last : Ctx S}
    (env : Environment S A.substitution.Carrier first last)
    (value : A.substitution.Carrier [] sort) :
    A.substitution.substitute env (ground first value) = ground last value := by
  rw [ground, A.substitution.substitute_comp]
  congr 1
  funext s impossible
  nomatch impossible

@[simp] theorem ground_empty (value : A.substitution.Carrier [] sort) :
    ground [] value = value := by
  have identity : emptyEnvironment (A := A) [] =
      (fun _ position => A.substitution.injectVar position) := by
    funext s impossible
    nomatch impossible
  rw [ground, identity, A.substitution.substitute_identity]

def closingEnvironment (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    (context : Ctx S) : Environment S A.substitution.Carrier context [] :=
  fun s _ => defaults s

theorem closing_ground (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    (context : Ctx S) (value : A.substitution.Carrier [] sort) :
    A.substitution.substitute (closingEnvironment defaults context) (ground context value) = value := by
  rw [substitute_ground, ground_empty]

theorem ground_injective (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    (context : Ctx S) : Function.Injective
      (ground (A := A) (sort := sort) context) := by
  intro first last same
  have closed := congrArg (A.substitution.substitute (closingEnvironment defaults context)) same
  simpa only [closing_ground] using closed

def closedPrograms : Base A ⥤ Type u :=
  (Functor.const (Base A)).obj (A.substitution.Carrier [] sort)

def groundingMap : closedPrograms (A := A) (sort := sort) ⟶ semanticPrograms A sort where
  app world := TypeCat.ofHom (ground world.unop.context)
  naturality first last change := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (substitute_ground (fromPositions first.unop.context change.unop) value).symm

/-- The fibre retains the actual supplied closed origin, rather than
merely erasing it to an existential claim of groundness. -/
abbrev GroundOrigin {context : Ctx S} (value : A.substitution.Carrier context sort) :=
  {origin : A.substitution.Carrier [] sort // ground context origin = value}

def GroundOrigin.substitute {first last : Ctx S}
    {value : A.substitution.Carrier first sort}
    (env : Environment S A.substitution.Carrier first last) (origin : GroundOrigin value) :
    GroundOrigin (A.substitution.substitute env value) where
  val := origin.val
  property := (substitute_ground env origin.val).symm.trans
    (congrArg (A.substitution.substitute env) origin.property)

theorem ground_origin_unique (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    {context : Ctx S} {value : A.substitution.Carrier context sort}
    (first last : GroundOrigin value) : first = last := by
  apply Subtype.ext
  exact ground_injective defaults context (first.property.trans last.property.symm)

theorem predicate_ground_iff (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    (predicate : Predicate A sort) (context : Ctx S) (value : A.substitution.Carrier [] sort) :
    predicate.holds (ground context value) ↔ predicate.holds value := by
  constructor
  · intro admitted
    simpa only [closing_ground] using
      predicate.substitute (closingEnvironment defaults context) _ admitted
  · exact predicate.substitute (emptyEnvironment context) value

theorem nativeNegation_ground_iff (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    (predicate : Predicate A sort) (context : Ctx S) (value : A.substitution.Carrier [] sort) :
    (nativeNegation predicate).holds (ground context value) ↔ ¬ predicate.holds value := by
  constructor
  · intro negative positive
    exact nativeNegation_excludes_current predicate negative
      ((predicate_ground_iff defaults predicate context value).mpr positive)
  · intro negative future env positive
    rw [substitute_ground] at positive
    exact negative ((predicate_ground_iff defaults predicate future value).mp positive)

/-- A supplied closed origin licenses promotion of current exclusion to
native negation. No such promotion is claimed for arbitrary open terms. -/
theorem ground_origin_promotes_exclusion (defaults : (s : S.Srt) → A.substitution.Carrier [] s)
    (predicate : Predicate A sort) {context : Ctx S}
    {value : A.substitution.Carrier context sort} (origin : GroundOrigin value)
    (excluded : ¬ predicate.holds value) : (nativeNegation predicate).holds value := by
  rw [← origin.property]
  apply (nativeNegation_ground_iff defaults predicate context origin.val).mpr
  intro positive
  exact excluded (origin.property ▸
    (predicate_ground_iff defaults predicate context origin.val).mpr positive)

def closedPredicate (predicate : Predicate A sort) :
    Subfunctor (closedPrograms (A := A) (sort := sort)) where
  obj _ := {value | predicate.holds value}
  map := by intro first last change value member; exact member

def closedExclusion (predicate : Predicate A sort) :
    Subfunctor (closedPrograms (A := A) (sort := sort)) where
  obj _ := {value | ¬ predicate.holds value}
  map := by intro first last change value absent; exact absent

theorem positive_grounding_comparison
    (defaults : (s : S.Srt) → A.substitution.Carrier [] s) (predicate : Predicate A sort) :
    predicate.subfunctor.preimage groundingMap = closedPredicate predicate := by
  ext world value
  exact predicate_ground_iff defaults predicate world.unop.context value

theorem negative_grounding_comparison
    (defaults : (s : S.Srt) → A.substitution.Carrier [] s) (predicate : Predicate A sort) :
    (predicate.subfunctor ⇨ ⊥).preimage groundingMap = closedExclusion predicate := by
  rw [← nativeNegation_subfunctor]
  ext world value
  exact nativeNegation_ground_iff defaults predicate world.unop.context value

/-- This complement is the actual Heyting negation on the admitted
closed-origin presheaf, not merely a disjoint set at one world. -/
theorem closedExclusion_native (predicate : Predicate A sort) :
    closedExclusion predicate = closedPredicate predicate ⇨ ⊥ := by
  rw [← himpPointwise_eq_himp]
  ext world value
  change (¬ predicate.holds value) ↔
    ∀ (future : Base A) (change : world ⟶ future), ¬ predicate.holds value
  exact ⟨fun absent _ _ => absent, fun absent => absent world (𝟙 world)⟩

end Mettapedia.OSLF.Binding.BindingGroundedPredicates
