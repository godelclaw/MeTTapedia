import Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyCwf

/-!
# Full HOL interpretation in well-founded codes of hypersets

Valid graph codes carry interpreted membership and actual coded operations.
Decoding preserves every open HOL term, every higher-order quantifier and
context substitution. The codes are ordinary well-founded sets one level
above the graphs. Their interpreted membership admits cycles; their host
membership does not. Thus the comparison does not identify the two relations.

The comparison uses the existing valid-code equivalence and retains its
classical host dependency. A supplied closed universe containing `carrierCode`
bounds this entire interpretation; existence or inaccessibility of that bound
is not inferred from the presence of this one fragment.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ZFSetHenkinInterpretation (Symbol)
open CodedFamilies

universe u v

abbrev carrier (_ : Unit) : Type (u + 2) := Code.{u}

def separation (bound : Code.{u}) (predicate : Code.{u} → Prop) : Code.{u} :=
  encode (HSet.sep (fun value => predicate (encode value)) (decode bound))

def replacement (presentation : HSet.Presentation.{u}) (bound : Code.{u})
    (function : Code.{u} → Code.{u}) : Code.{u} :=
  encode (HSet.image presentation (decode bound)
    (fun value => decode (function (encode value.1))))

def denoteSymbol (presentation : HSet.Presentation.{u}) :
    {A : Ty Unit} → Symbol A → Ty.denote.{0, u + 2} carrier.{u} A
  | _, .member => fun element bound => .up (codeMem bound.1 element.1)
  | _, .empty => encode (∅ : HSet.{u})
  | _, .union => fun bound => encode (HSet.sUnion (decode bound))
  | _, .power => fun bound => encode (HSet.powerset (decode bound))
  | _, .separate => fun bound predicate => separation bound (fun value => (predicate value).down)
  | _, .replace => replacement presentation

def model (presentation : HSet.Presentation.{u}) : HenkinModel.{0, 0, u + 2} Unit Symbol :=
  HenkinModel.standard carrier (denoteSymbol presentation)

theorem fullDomains (presentation : HSet.Presentation.{u}) : (model presentation).FullDomains :=
  HenkinModel.fullDomains_standard carrier (denoteSymbol presentation)

def baseEquiv (_ : Unit) : carrier.{u} () ≃ HypersetHenkinInterpretation.carrier.{u} () :=
  carrierEquiv

/-- Each independently coded operation decodes to the actual hyperset operation. -/
theorem constants_transport (presentation : HSet.Presentation.{u}) {A : Ty Unit} (constant : Symbol A) :
    StandardTransport.liftEquiv baseEquiv A ((model presentation).constDen constant) =
      (HypersetHenkinInterpretation.model presentation).constDen constant := by
  cases constant with
  | member =>
      funext element bound
      change HSet.{u} at element bound
      apply ULift.ext
      change (decode (encode element) ∈ decode (encode bound)) = (element ∈ bound)
      simp
  | empty => exact decode_encode _
  | union =>
      funext bound
      change HSet.{u} at bound
      change decode (encode (HSet.sUnion (decode (encode bound)))) = HSet.sUnion bound
      simp
  | power =>
      funext bound
      change HSet.{u} at bound
      change decode (encode (HSet.powerset (decode (encode bound)))) = HSet.powerset bound
      simp
  | separate =>
      funext bound predicate
      change HSet.{u} at bound
      change HSet.{u} → ULift.{u + 1} Prop at predicate
      change decode (separation (encode bound) (fun value => (predicate (decode value)).down)) =
        HSet.sep (fun value => (predicate value).down) bound
      simp [separation]
  | replace =>
      funext bound function
      change HSet.{u} at bound
      change HSet.{u} → HSet.{u} at function
      change decode (replacement presentation (encode bound) (fun value => encode (function (decode value)))) =
        HypersetHenkinInterpretation.replacement presentation bound function
      simp [replacement, HypersetHenkinInterpretation.replacement]
      exact congrArg (fun actual => HSet.image presentation actual
        (fun value => function value.1)) (decode_encode bound)

theorem denote_transport (presentation : HSet.Presentation.{u}) {Γ : Ctx Unit} {A : Ty Unit}
    (term : Term Symbol Γ A) (valuation : (model presentation).Valuation Γ) :
    (HypersetHenkinInterpretation.model presentation).denote term
      (StandardTransport.valuationEquiv (model presentation) (HypersetHenkinInterpretation.model presentation)
        baseEquiv Γ valuation) =
      StandardTransport.liftEquiv baseEquiv A ((model presentation).denote term valuation) :=
  StandardTransport.denote_transport _ _ (fullDomains presentation)
    (HypersetHenkinInterpretation.fullDomains presentation) baseEquiv
    (constants_transport presentation) term valuation

theorem models_iff (presentation : HSet.Presentation.{u}) (formula : ClosedFormula Symbol) :
    (model presentation).models formula ↔ (HypersetHenkinInterpretation.model presentation).models formula :=
  (StandardTransport.models_transport _ _ (fullDomains presentation)
    (HypersetHenkinInterpretation.fullDomains presentation) baseEquiv
    (constants_transport presentation) formula).symm

/-- All retained source rules are valid in the coded interpretation. -/
theorem proof_sound (presentation : HSet.Presentation.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula Symbol Γ)} {conclusion : Formula Symbol Γ}
    (proof : ProofSyntax Symbol hypotheses conclusion) (valuation : (model presentation).Valuation Γ)
    (satisfied : Soundness.SatisfiesHyps (model presentation) valuation hypotheses) :
    ((model presentation).denote conclusion valuation).down :=
  Soundness.extDerivation_sound proof.erase
    ((model presentation).functionsRespectEqv_of_fullDomains (fullDomains presentation))
    (fun _ => fullDomains presentation _ _) satisfied

theorem operationTheory_valid (presentation : HSet.Presentation.{u}) :
    ∀ formula ∈ HypersetHenkinInterpretation.operationTheory, (model presentation).models formula :=
  fun formula member => (models_iff presentation formula).mpr
    (HypersetHenkinInterpretation.operationTheory_valid presentation formula member)

theorem setInduction_invalid (presentation : HSet.Presentation.{u}) :
    ¬ (model presentation).models ZFSetHenkinInterpretation.setInduction :=
  fun valid => HypersetHenkinInterpretation.setInduction_invalid presentation
    ((models_iff presentation _).mp valid)

/-- The same well-founded code has an interpreted self-member and no host
self-member. The distinction is exhibited on an actual Quine-atom code. -/
theorem memberships_distinct :
    codeMem (encode HSet.quineAtom.{u}).1 (encode HSet.quineAtom.{u}).1 ∧
      (encode HSet.quineAtom.{u}).1 ∉ (encode HSet.quineAtom.{u}).1 :=
  ⟨codeMem_code.mpr HSet.quineAtom_mem_self, ZFSet.mem_irrefl _⟩

/-- Host universes may contain every code while interpreted membership still
refutes induction. Closure does not turn the interpreted relation into host membership. -/
theorem bounded_cycles {bound : ZFSet.{u + 1}}
    (closed : ZFSetUniverseClosure.Closed bound)
    (contains : ZFSetUniverseLift.carrierCode.{u} ∈ bound) :
    ∃ value : Code.{u}, value.1 ∈ bound ∧ codeMem value.1 value.1 ∧ value.1 ∉ value.1 :=
  ⟨encode HSet.quineAtom, encode_mem_of_carrier_mem closed contains _, memberships_distinct⟩

/-- Even forward membership preservation into host set membership is
impossible on the whole hyperset carrier. Injectivity is not needed for the
obstruction: the Quine atom already forces a host self-member. -/
theorem no_membership_preserving_map_to_sets (map : HSet.{u} → ZFSet.{v}) :
    ¬ ∀ {element bound : HSet.{u}}, element ∈ bound → map element ∈ map bound := by
  intro preserves
  exact ZFSet.mem_irrefl _ (preserves HSet.quineAtom_mem_self)

end Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation
