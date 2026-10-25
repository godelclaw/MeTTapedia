import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Logic.HOL.Embedding.RelativizedCarrier

/-!
# Typed guarded quantifier transport

Two explicit maps preserve the guards and are inverse on valid values.
Universal and existential observations then transport along the forward map.
The comparison remains part of each statement, so its action on predicates
is retained. Empty valid carriers are permitted.

These are logical transport laws. A datatype realization must separately
supply its constructor, recursion and comparison evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.GuardedQuantifierTransport

inductive Base where
  | source | target
  deriving DecidableEq, Repr

abbrev Const (_type : Ty Base) := Empty
abbrev source : Ty Base := .base .source
abbrev target : Ty Base := .base .target
abbrev guardSource : Ty Base := source ⇒ .prop
abbrev guardTarget : Ty Base := target ⇒ .prop
abbrev forward : Ty Base := source ⇒ target
abbrev backward : Ty Base := target ⇒ source
abbrev Context : Ctx Base := [guardTarget, backward, forward, guardTarget, guardSource]

def leftComparison : Formula Const Context :=
  .all (σ := source)
    (.imp (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var .vz))
      (.and
        (.app (.var (.vs (.vs (.vs (.vs .vz)))))
          (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)))
        (.eq (.app (.var (.vs (.vs .vz)))
          (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))) (.var .vz))))

def rightComparison : Formula Const Context :=
  .all (σ := target)
    (.imp (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var .vz))
      (.and
        (.app (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
          (.app (.var (.vs (.vs .vz))) (.var .vz)))
        (.eq (.app (.var (.vs (.vs (.vs .vz))))
          (.app (.var (.vs (.vs .vz))) (.var .vz))) (.var .vz))))

def comparison : Formula Const Context := .and leftComparison rightComparison

def sourceAll : Formula Const Context :=
  .all (σ := source)
    (.imp (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var .vz))
      (.app (.var (.vs .vz)) (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))))

def targetAll : Formula Const Context :=
  .all (σ := target)
    (.imp (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var .vz))
      (.app (.var (.vs .vz)) (.var .vz)))

def sourceExists : Formula Const Context :=
  .ex (σ := source)
    (.and (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var .vz))
      (.app (.var (.vs .vz)) (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))))

def targetExists : Formula Const Context :=
  .ex (σ := target)
    (.and (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var .vz))
      (.app (.var (.vs .vz)) (.var .vz)))

def close (body : Formula Const Context) : ClosedFormula Const :=
  .all (σ := guardSource) (.all (σ := guardTarget) (.all (σ := forward)
    (.all (σ := backward) (.all (σ := guardTarget) body))))

inductive Fact where
  | universal | existential
  deriving DecidableEq, Repr

def formula : Fact → ClosedFormula Const
  | .universal => close (.imp comparison (.eq sourceAll targetAll))
  | .existential => close (.imp comparison (.eq sourceExists targetExists))

def erasedUniversal : ClosedFormula Const :=
  close (.imp comparison (.eq sourceAll
    (.all (σ := target) (.app (.var (.vs .vz)) (.var .vz)))))

def model (Source Target : Type 1) : HenkinModel.{0, 0, 0} Base Const :=
  HenkinModel.standard (fun | .source => Source | .target => Target)
    (fun {_type} impossible => impossible.elim)

theorem models_universal (M : HenkinModel.{0, 0, 0} Base Const) :
    M.models (formula .universal) := by
  intro G _ H _ f _ g _ P _ laws
  obtain ⟨left, right⟩ := laws
  constructor
  · intro holds y _ valid
    obtain ⟨preimageValid, roundtrip⟩ := right y (M.base_mem .target y) valid
    have observed := holds (g y) (M.base_mem .source _) preimageValid
    change f (g y) = y at roundtrip
    change (P (f (g y))).down at observed
    change (P y).down
    simpa only [roundtrip] using observed
  · intro holds x _ valid
    exact holds (f x) (M.base_mem .target _) (left x (M.base_mem .source x) valid).1

theorem models_existential (M : HenkinModel.{0, 0, 0} Base Const) :
    M.models (formula .existential) := by
  intro G _ H _ f _ g _ P _ laws
  obtain ⟨left, right⟩ := laws
  constructor
  · rintro ⟨x, _, valid, observed⟩
    exact ⟨f x, M.base_mem .target _, (left x (M.base_mem .source x) valid).1, observed⟩
  · rintro ⟨y, _, valid, observed⟩
    obtain ⟨preimageValid, roundtrip⟩ := right y (M.base_mem .target y) valid
    refine ⟨g y, M.base_mem .source _, preimageValid, ?_⟩
    change f (g y) = y at roundtrip
    change (P y).down at observed
    change (P (f (g y))).down
    simpa only [roundtrip] using observed

theorem all_models (M : HenkinModel.{0, 0, 0} Base Const) (fact : Fact) :
    M.models (formula fact) := by
  cases fact
  · exact models_universal M
  · exact models_existential M

theorem empty_guard_separates :
    (∀ value : Option Empty,
      Embedding.RelativizedCarrier.Valid value → False) ∧
      ¬ (∀ _value : Option Empty, False) := by
  constructor
  · intro value valid
    cases value with
    | none => exact valid
    | some impossible => exact impossible.elim
  · intro unguarded
    exact unguarded none

/-- Removing the target guard changes the actual intrinsic HOL statement.
Both raw carriers are inhabited, while their represented carriers are empty. -/
theorem guard_erasure_counterexample :
    ¬ (model (Option (ULift.{1} Empty)) (Option (ULift.{1} Empty))).models erasedUniversal := by
  intro validated
  let emptyPredicate : Option (ULift.{1} Empty) → ULift.{1} Prop := fun _ => ⟨False⟩
  have compared := validated emptyPredicate trivial emptyPredicate trivial
    id trivial id trivial emptyPredicate trivial
  have opposite := compared (by
    constructor <;> intro value _ impossible <;> exact impossible.elim)
  exact (opposite.mp (by intro value _ impossible; exact impossible.elim)) none trivial

namespace Examples

abbrev Carrier := Option (ULift.{1} Bool)

def swap : Carrier → Carrier := Option.map (fun value => ⟨!value.down⟩)

theorem swap_comparison (value : Carrier) (valid : Embedding.RelativizedCarrier.Valid value) :
    Embedding.RelativizedCarrier.Valid (swap value) ∧ swap (swap value) = value := by
  cases value with
  | none => exact valid.elim
  | some value =>
      rcases value with ⟨value⟩
      cases value <;> exact ⟨trivial, rfl⟩

/-- A valid comparison can act nontrivially on a selected value. The
transported predicate must retain that chosen action. -/
theorem swap_changes_observation :
    swap (some ⟨false⟩) = some ⟨true⟩ ∧ swap (some ⟨false⟩) ≠ id (some ⟨false⟩) := by
  decide +kernel

theorem swap_false_checked :
    Embedding.RelativizedCarrier.Valid (swap (some ⟨false⟩)) ∧
      swap (swap (some ⟨false⟩)) = some ⟨false⟩ :=
  swap_comparison _ trivial

end Examples

section ObservationBoundary

universe u v

/-- Exact existential truth transport for every predicate characterizes the
image of the valid source values. It does not assert injectivity. -/
theorem exists_observations_iff_image {A : Type u} {B : Type v}
    (validSource : A → Prop) (validTarget : B → Prop) (map : A → B) :
    (∀ predicate : B → Prop,
      (∃ value, validSource value ∧ predicate (map value)) ↔
        ∃ value, validTarget value ∧ predicate value) ↔
      ∀ value, validTarget value ↔ ∃ source, validSource source ∧ map source = value := by
  constructor
  · intro observations value
    have singleton := observations (fun candidate => candidate = value)
    constructor
    · intro valid
      exact singleton.mpr ⟨value, valid, rfl⟩
    · intro represented
      obtain ⟨candidate, valid, same⟩ := singleton.mp represented
      exact same ▸ valid
  · intro image predicate
    constructor
    · rintro ⟨value, valid, observed⟩
      exact ⟨map value, (image _).mpr ⟨value, valid, rfl⟩, observed⟩
    · rintro ⟨value, valid, observed⟩
      obtain ⟨original, originalValid, same⟩ := (image value).mp valid
      exact ⟨original, originalValid, same.symm ▸ observed⟩

/-- Universal truth observations have the same exact-image boundary. This
uses all predicates, rather than an unspecified restricted query language. -/
theorem all_observations_iff_image {A : Type u} {B : Type v}
    (validSource : A → Prop) (validTarget : B → Prop) (map : A → B) :
    (∀ predicate : B → Prop,
      (∀ value, validSource value → predicate (map value)) ↔
        ∀ value, validTarget value → predicate value) ↔
      ∀ value, validTarget value ↔ ∃ source, validSource source ∧ map source = value := by
  constructor
  · intro observations value
    have preserve := (observations validTarget).mpr (fun _ valid => valid)
    have cover := (observations (fun candidate =>
      ∃ original, validSource original ∧ map original = candidate)).mp
        (fun original valid => ⟨original, valid, rfl⟩)
    exact ⟨cover value, by
      rintro ⟨original, valid, same⟩
      exact same ▸ preserve original valid⟩
  · intro image predicate
    constructor
    · intro observed value valid
      obtain ⟨original, originalValid, same⟩ := (image value).mp valid
      exact same ▸ observed original originalValid
    · intro observed value valid
      exact observed (map value) ((image _).mpr ⟨value, valid, rfl⟩)

/-- Projection preserves every quantified truth observation but identifies
distinct source values. This is a negative control for inferring a faithful
value comparison from truth agreement alone. -/
theorem truth_transport_does_not_force_injectivity :
    ∃ map : Bool × Bool → Bool,
      (∀ predicate : Bool → Prop,
        ((∃ value, predicate (map value)) ↔ ∃ value, predicate value) ∧
        ((∀ value, predicate (map value)) ↔ ∀ value, predicate value)) ∧
      ¬ Function.Injective map := by
  refine ⟨Prod.fst, ?_, ?_⟩
  · intro predicate
    constructor
    · constructor
      · rintro ⟨value, observed⟩; exact ⟨value.1, observed⟩
      · rintro ⟨value, observed⟩; exact ⟨(value, false), observed⟩
    · constructor
      · intro observed value; exact observed (value, false)
      · intro observed value; exact observed value.1
  · intro injective
    have same : (false, false) = (false, true) := injective rfl
    exact Bool.false_ne_true (congrArg Prod.snd same)

end ObservationBoundary

theorem standard_instance (fact : Fact) :
    (model Examples.Carrier Examples.Carrier).models (formula fact) :=
  all_models _ fact

def verdicts : List (String × Bool) :=
  [("guarded comparison retains a nonidentity swap", decide
      (Examples.swap (some ⟨false⟩) = some ⟨true⟩ ∧
        Examples.swap (some ⟨false⟩) ≠ id (some ⟨false⟩))),
   ("guarded comparison retains inverse action", decide
      (Examples.swap (Examples.swap (some ⟨false⟩)) = some ⟨false⟩)),
   ("comparison preserves the padding point", decide
      (Examples.swap none = none))]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

#print axioms models_universal
#print axioms models_existential
#print axioms empty_guard_separates
#print axioms guard_erasure_counterexample
#print axioms Examples.swap_comparison
#print axioms exists_observations_iff_image
#print axioms all_observations_iff_image
#print axioms truth_transport_does_not_force_injectivity

end Mettapedia.Logic.HOL.GuardedQuantifierTransport
