import Mettapedia.Logic.WorldModel.Observation
import Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial observations of general world models

A world model whose values form a commutative semiring can interpret polynomial
combinations of its primitive query answers. This extends its query language;
it neither changes revision nor assumes that primitive extraction is additive.
The coefficients are natural numbers, reusing the free provenance semiring.

A product of readouts means their semiring product. Interpreting it as a joint
probability or a relational join requires a separate semantic bridge. Polynomial
queries can be nonlinear in the state even when every primitive query is linear.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WorldModel.PolynomialObservations

open MvPolynomial

variable {State Query Value Target Request Result : Type*}
  [CommSemiring Value] [CommSemiring Result]
  [WorldModel State Query Value] [WorldModel Target Request Result]

abbrev PolynomialQuery (Query : Type*) := MvPolynomial Query ℕ

noncomputable def observe (state : State) (query : PolynomialQuery Query) : Value :=
  eval₂ (Nat.castRingHom Value) (WorldModel.extract state) query

/-- The general update operations are retained exactly; only the query
carrier is extended. This is an explicit model, not an overlapping instance. -/
@[instance_reducible] noncomputable def model :
    WorldModel State (PolynomialQuery Query) Value where
  revise := WorldModel.revise Query Value
  empty := WorldModel.empty Query Value
  extract := observe

@[simp] theorem observe_generator (state : State) (query : Query) :
    observe state (X query) = (WorldModel.extract state query : Value) := by simp [observe]

@[simp] theorem observe_zero (state : State) :
    observe state (0 : PolynomialQuery Query) = (0 : Value) := by simp [observe]

@[simp] theorem observe_one (state : State) :
    observe state (1 : PolynomialQuery Query) = (1 : Value) := by simp [observe]

@[simp] theorem observe_add (state : State) (first second : PolynomialQuery Query) :
    observe state (first + second) = (observe state first + observe state second : Value) := by
  simp [observe, eval₂_add]

@[simp] theorem observe_mul (state : State) (first second : PolynomialQuery Query) :
    observe state (first * second) = (observe state first * observe state second : Value) := by
  simp [observe, eval₂_mul]

/-- The primitive-query embedding preserves every observation and update. -/
noncomputable def embedding :
    @RevisionMap State Query Value State (PolynomialQuery Query) Value
      inferInstance (model (State := State) (Query := Query) (Value := Value)) := by
  letI := model (State := State) (Query := Query) (Value := Value)
  exact {
    state := id
    query := X
    value := id
    observe state request := observe_generator state request
    empty := rfl
    revise _ _ := rfl }

/-- Every semiring-compatible observation map extends to polynomial requests.
A general function between values need not preserve these combinations. -/
noncomputable def lift (map : ObservationMap State Query Value Target Request Result)
    (hom : Value →+* Result) (compatible : map.value = hom) :
    @ObservationMap State (PolynomialQuery Query) Value Target (PolynomialQuery Request) Result
      (model (State := State) (Query := Query) (Value := Value))
      (model (State := Target) (Query := Request) (Value := Result)) := by
  letI := model (State := State) (Query := Query) (Value := Value)
  letI := model (State := Target) (Query := Request) (Value := Result)
  exact {
    state := map.state
    query := rename map.query
    value := hom
    observe source request := by
      change eval₂ (Nat.castRingHom Result) (WorldModel.extract (map.state source))
        (rename map.query request) = hom (eval₂ (Nat.castRingHom Value) (WorldModel.extract source) request)
      rw [eval₂_rename, hom_eval₂]
      have coefficients : hom.comp (Nat.castRingHom Value) = Nat.castRingHom Result := by
        ext
        simp
      rw [coefficients]
      congr 1
      funext query
      simpa only [Function.comp_apply, compatible] using map.observe source query }

/-- Revision preservation is inherited from the original map rather than
inferred from its observation behavior. -/
noncomputable def liftRevision (map : RevisionMap State Query Value Target Request Result)
    (hom : Value →+* Result) (compatible : map.value = hom) :
    @RevisionMap State (PolynomialQuery Query) Value Target (PolynomialQuery Request) Result
      (model (State := State) (Query := Query) (Value := Value))
      (model (State := Target) (Query := Request) (Value := Result)) := by
  letI := model (State := State) (Query := Query) (Value := Value)
  letI := model (State := Target) (Query := Request) (Value := Result)
  exact {
    toObservationMap := lift map.toObservationMap hom compatible
    empty := map.empty
    revise := map.revise }

/-- This is the existing provenance interpretation, now as a query of any
semiring-valued WM. Stable cause identities remain the query generators. -/
theorem observe_provenance {Cause Output : Type} [CommSemiring Output]
    [WorldModel State Cause Output] (state : State)
    (derivations : List (Mettapedia.GSLT.Dynamics.ProvenanceInterpretation.Derivation Cause)) :
    observe state (Mettapedia.GSLT.Dynamics.ProvenanceInterpretation.provenance derivations) =
      Mettapedia.GSLT.Dynamics.ProvenanceInterpretation.interpSet
        (WorldModel.extract state : Cause → Output) derivations :=
  Mettapedia.GSLT.Dynamics.ProvenanceInterpretation.interp_provenance _ _

/-- A product query has cross terms under additive primitive extraction.
No equation removes those cross terms. -/
theorem generator_product_revise (first second : State) (left right : Query)
    (additive : ∀ (source update : State) (query : Query), WorldModel.extract
      (WorldModel.revise Query Value source update) query =
        (WorldModel.extract source query + WorldModel.extract update query : Value)) :
    observe (WorldModel.revise Query Value first second) (X left * X right) =
      observe first (X left * X right) + observe second (X left * X right) +
        ((WorldModel.extract first left : Value) * WorldModel.extract second right +
          WorldModel.extract second left * WorldModel.extract first right) := by
  simp only [observe_mul, observe_generator, additive]
  ring

namespace Controls

local instance : WorldModel (ℕ × ℕ) Bool ℕ where
  revise := (· + ·)
  empty := 0
  extract state query := if query then state.1 else state.2

theorem primitive_queries_additive (first second : ℕ × ℕ) (query : Bool) :
    WorldModel.extract (WorldModel.revise Bool ℕ first second) query =
      (WorldModel.extract first query + WorldModel.extract second query : ℕ) := by
  cases query <;> rfl

/-- The combined state answers a product query although neither update
answers it separately. Its primitive queries are nevertheless additive. -/
theorem polynomial_query_not_additive :
    observe (WorldModel.revise Bool ℕ (1, 0) (0, 1)) (X true * X false) = (1 : ℕ) ∧
      observe (1, 0) (X true * X false) + observe (0, 1) (X true * X false) = (0 : ℕ) := by
  norm_num [observe_mul, observe_generator, WorldModel.extract, WorldModel.revise]

/-- An event of probability `1/2` cannot be interpreted by a semiring
homomorphism that also identifies its repeated use with the same event. -/
theorem no_probability_hom_for_repeated_cause :
    ¬ ∃ hom : PolynomialQuery (Fin 1) →+* ℚ,
      hom (X 0) = 1/2 ∧ hom (X 0 * X 0) = 1/2 := by
  rintro ⟨hom, generator, repeated⟩
  rw [map_mul, generator] at repeated
  norm_num at repeated

end Controls

end Mettapedia.Logic.WorldModel.PolynomialObservations
