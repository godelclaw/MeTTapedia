import Mettapedia.OSLF.Syntax.BindingConstructorPredicatePresheaf
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting

/-!
# Native negation of binding predicates

The existing substitution-stable predicate is a genuine subfunctor. Its
native negation checks all future environments, and is proved to be the
Heyting pseudocomplement of that same subfunctor. Present exclusion is only
one of its consequences. The largest disjoint native predicate is earned
directly from substitution, without a present-absence assumption.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingPredicateFutureLogic

open _root_.CategoryTheory FreeBindingTerms BindingSubstitutionAlgebra
open BindingConstructorPredicates IntrinsicScopedConditionalPresheaf
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.GSLT.Topos

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S} {sort : S.Srt}

def nativeNegation (predicate : Predicate A sort) : Predicate A sort where
  holds := fun value => ∀ (future : Ctx S)
    (env : Environment S A.substitution.Carrier _ future),
      ¬ predicate.holds (A.substitution.substitute env value)
  substitute := by
    intro source target first value absent future second member
    apply absent future (fun s position => A.substitution.substitute second (first s position))
    simpa only [A.substitution.substitute_comp] using member

theorem nativeNegation_excludes_current (predicate : Predicate A sort)
    {context : Ctx S} {value : A.substitution.Carrier context sort}
    (absent : (nativeNegation predicate).holds value) : ¬ predicate.holds value := by
  have current := absent context (fun _ position => A.substitution.injectVar position)
  simpa only [A.substitution.substitute_identity] using current

theorem nativeNegation_disjoint (predicate : Predicate A sort)
    {context : Ctx S} (value : A.substitution.Carrier context sort) :
    ¬ (predicate.holds value ∧ (nativeNegation predicate).holds value) :=
  fun both => nativeNegation_excludes_current predicate both.2 both.1

/-- Every other substitution-stable exclusion factors through native
negation. The independent disjointness condition is used at the future. -/
theorem nativeNegation_largest (predicate exclusion : Predicate A sort)
    (disjoint : ∀ {context : Ctx S} (value : A.substitution.Carrier context sort),
      exclusion.holds value → ¬ predicate.holds value)
    {context : Ctx S} {value : A.substitution.Carrier context sort}
    (excluded : exclusion.holds value) : (nativeNegation predicate).holds value := by
  intro future env member
  exact disjoint _ (exclusion.substitute env value excluded) member

/-- Complete contextual availability must reflect before its current
complement supplies a native negative guard. -/
def ReflectsMembership (predicate : Predicate A sort) : Prop :=
  ∀ {source target : Ctx S} (env : Environment S A.substitution.Carrier source target)
    (value : A.substitution.Carrier source sort),
      predicate.holds (A.substitution.substitute env value) → predicate.holds value

theorem nativeNegation_iff_current (predicate : Predicate A sort)
    (reflection : ReflectsMembership predicate)
    {context : Ctx S} (value : A.substitution.Carrier context sort) :
    (nativeNegation predicate).holds value ↔ ¬ predicate.holds value := by
  constructor
  · exact nativeNegation_excludes_current predicate
  · intro excluded future env member
    exact excluded (reflection env value member)

/-- The environment-quantified reading agrees with the previously
constructed Heyting implication on the actual clone-context presheaf. -/
theorem nativeNegation_subfunctor (predicate : Predicate A sort) :
    (nativeNegation predicate).subfunctor = predicate.subfunctor ⇨ ⊥ := by
  rw [← himpPointwise_eq_himp]
  ext world value
  change (∀ (future : Ctx S)
    (env : Environment S A.substitution.Carrier world.unop.context future),
      ¬ predicate.holds (A.substitution.substitute env value)) ↔
    ∀ (future : Base A) (change : world ⟶ future),
      ¬ predicate.holds (A.substitution.toClone.substitute value change.unop)
  constructor
  · intro absent future change
    exact absent future.unop.context (fromPositions world.unop.context change.unop)
  · intro absent future env
    let target : Base A := Opposite.op (ContextObject.ofList A.substitution.toClone future)
    let change : world ⟶ target := Quiver.Hom.op
      (fun position => env _ (varOfIdx world.unop.context position))
    have excluded := absent target change
    change ¬ predicate.holds (A.substitution.substitute
      (fromPositions world.unop.context
        (fun position => env _ (varOfIdx world.unop.context position))) value) at excluded
    have environment : fromPositions world.unop.context
        (fun position => env _ (varOfIdx world.unop.context position)) = env := by
      funext s position
      exact fromPositions_ofEnvironment env position
    simpa only [environment] using excluded

end Mettapedia.OSLF.Binding.BindingPredicateFutureLogic
