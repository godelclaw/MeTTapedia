import Mettapedia.TypeTheory.NaturalRepresentationInterface
import Mettapedia.TypeTheory.NaturalVectorCoherence
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored

/-!
# Native observations over coherent natural presentations

The same constructor-preserving route transports values and native formulas.
Both incoming and outgoing coverage hold between faithful representations.
The authored counter connection remains restricted to its certified future
observations; no incoming coverage of arbitrary raw source syntax is inferred.

Finite queries run on the retained natural index. Neither a semantic inverse
nor an isomorphism of carriers is treated as an executable conversion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Coherent

open Mettapedia.TypeTheory.NaturalAlgebra
open Mettapedia.TypeTheory.NaturalRepresentationInterface
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.NaturalVectorCoherence (appendTotal)
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Reference.Core (Outcome)

universe i u v

variable {Index : Type i} {Carrier : Index → Type u}
  (algebra : ∀ index, Algebra (Carrier index))
  (representation : ∀ index, Mettapedia.TypeTheory.NaturalAlgebra.Representation (algebra index))

/-- Native predicates are pulled back by exactly the route acting on values. -/
theorem route_formula_iff {source target : Index}
    (route : Iso (algebra source) (algebra target)) {n : Nat}
    (formula : Formula Traversal n) (positive : fixedPointsPositive formula = true)
    (environment : Env (Carrier target) n) (value : Carrier source) :
    satisfies (transitionSystem (span (algebra target).succ)) environment formula
      ((values algebra).transport route value) ↔
    satisfies (transitionSystem (span (algebra source).succ))
      (pullEnvironment route.toEquiv environment) formula value :=
  Semantics.SuccessorObservation.formula_iff _ _ route.toEquiv route.map_succ
    formula positive environment value

/-- The vector operation uses the same dependent transport as the public
presentation interface, including its result index. -/
theorem append_transport {Element : Type v} {source target : Index}
    (route : Iso (algebra source) (algebra target))
    (left right : Indexed algebra representation
      (VectorExample.VectorP Element) source) :
    (indexedFamily algebra representation
      (VectorExample.VectorP Element)).transport route
        (appendTotal
          (representation source).canonicalIso.toEquiv left right) =
    appendTotal
      (representation target).canonicalIso.toEquiv
      ((indexedFamily algebra representation
        (VectorExample.VectorP Element)).transport route left)
      ((indexedFamily algebra representation
        (VectorExample.VectorP Element)).transport route right) :=
  Mettapedia.TypeTheory.NaturalVectorCoherence.changeRepresentation_append _ _ _ _

/-- Native behavioural questions about the result index survive the same
transport that carries the appended vector. -/
theorem append_formula_iff {Element : Type v} {source target : Index}
    (route : Iso (algebra source) (algebra target))
    (left right : Indexed algebra representation
      (VectorExample.VectorP Element) source)
    {n : Nat} (formula : Formula Traversal n)
    (positive : fixedPointsPositive formula = true) (environment : Env (Carrier target) n) :
    satisfies (transitionSystem (span (algebra target).succ)) environment formula
      (appendTotal
        (representation target).canonicalIso.toEquiv
        ((indexedFamily algebra representation
          (VectorExample.VectorP Element)).transport route left)
        ((indexedFamily algebra representation
          (VectorExample.VectorP Element)).transport route right)).1 ↔
    satisfies (transitionSystem (span (algebra source).succ))
      (pullEnvironment route.toEquiv environment) formula
      (appendTotal
        (representation source).canonicalIso.toEquiv left right).1 := by
  rw [← append_transport algebra representation route left right,
    indexed_transport_index]
  exact route_formula_iff algebra route formula positive environment _

include representation in
/-- Route independence includes every supported native observation, rather
than only equality of the transported numeral. -/
theorem route_formula_independent {source target : Index}
    (first second : Iso (algebra source) (algebra target)) {n : Nat}
    (formula : Formula Traversal n) (environment : Env (Carrier target) n)
    (value : Carrier source) :
    satisfies (transitionSystem (span (algebra target).succ)) environment formula
      ((values algebra).transport first value) ↔
    satisfies (transitionSystem (span (algebra target).succ)) environment formula
      ((values algebra).transport second value) := by
  rw [transport_route_independent algebra representation (values algebra) first second value]

/-- A finite positive verdict has its path meaning after any structured
representation change, with the observation moved to that representation. -/
theorem check_at_route_iff {source target : Index}
    (route : Iso (algebra source) (algebra target)) (phases : Finset (Fin 2))
    (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase number)).map Outcome.answer = some (some true) ↔
    BuchiPath (transitionSystem (span (algebra target).succ)) .future
      (Representation.accepted (representation target) phases)
      (route.toEquiv ((representation source).encode number)) := by
  rw [route_encode algebra representation]
  exact Representation.check_encoded_buchi_iff (representation target) phases budget number enough

theorem check_negative_at_route_iff {source target : Index}
    (route : Iso (algebra source) (algebra target)) (phases : Finset (Fin 2))
    (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase number)).map Outcome.answer = some (some false) ↔
    ¬ BuchiPath (transitionSystem (span (algebra target).succ)) .future
      (Representation.accepted (representation target) phases)
      (route.toEquiv ((representation source).encode number)) := by
  rw [route_encode algebra representation]
  exact Representation.check_encoded_negative_iff (representation target) phases budget number enough

/-- The actual parsed module and the transported model have the same future
recurrence property. This compares two independently defined transition systems. -/
theorem authored_at_route_iff {source target : Index}
    (route : Iso (algebra source) (algebra target)) (base : BasePremiseEvaluator)
    (phases : Finset (Fin 2)) (number : Nat) :
    BuchiPath (transitionSystem
      (gsltSpan (Authored.theory base))) .future
      (Authored.accepting phases)
      (Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.counter number) ↔
    BuchiPath (transitionSystem (span (algebra target).succ)) .future
      (Representation.accepted (representation target) phases)
      (route.toEquiv ((representation source).encode number)) := by
  rw [route_encode algebra representation]
  exact Authored.representation_buchi_iff (representation target) base phases number

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Coherent
