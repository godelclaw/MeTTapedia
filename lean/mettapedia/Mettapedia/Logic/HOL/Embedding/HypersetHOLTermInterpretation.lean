import Mettapedia.Logic.HOL.Embedding.HypersetHOLTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetSimpleTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTarskiUniverses

/-!
# Hyperset HOL terms evaluated as well-founded graph codes

The same structural material interpreter used for well-founded sets receives
actual coded hyperset operations here. Functions are material graphs, and
predicates are applied to the codes of the original values. All term formers,
context extension, and simultaneous substitution retain those values.

The interpreted membership can be cyclic although every representation is a
well-founded host set. The source axiom inventory is explicit: the six common
operation laws hold, while membership induction fails.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.HOL.Embedding.HypersetHOLTermInterpretation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ZFSetHenkinInterpretation (Symbol set predicate mapping)
open HypersetHOLTypeInterpretation
open ZFSetHOLTypeInterpretation (truth holds)
open ZFSetDependentProducts (Elements)

universe u

abbrev Valuation (Γ : Ctx Unit) := ZFSetSimpleTypeInterpretation.Valuation bases.{u} Γ

abbrev RawValuation (Γ : Ctx Unit) :=
  ∀ {type}, Var Γ type → Ty.denote.{0, u + 1} HypersetHenkinInterpretation.carrier.{u} type

def decodeValuation {Γ : Ctx Unit} (valuation : Valuation.{u} Γ) : RawValuation.{u} Γ :=
  fun {_} index => decode _ (valuation index)

def encodeValuation {Γ : Ctx Unit} (valuation : RawValuation.{u} Γ) : Valuation.{u} Γ :=
  ZFSetSimpleTypeInterpretation.encodeValuation bases (fun _ => CodedFamilies.carrierEquiv) valuation

theorem decode_encode_valuation {Γ : Ctx Unit} (valuation : RawValuation.{u} Γ) :
    (decodeValuation (encodeValuation valuation) : RawValuation Γ) = (valuation : RawValuation Γ) :=
  ZFSetSimpleTypeInterpretation.decode_encode_valuation bases (fun _ => CodedFamilies.carrierEquiv) valuation

theorem encode_decode_valuation {Γ : Ctx Unit} (valuation : Valuation.{u} Γ) :
    (encodeValuation (decodeValuation valuation) : Valuation Γ) = (valuation : Valuation Γ) :=
  ZFSetSimpleTypeInterpretation.encode_decode_valuation bases (fun _ => CodedFamilies.carrierEquiv) valuation


def separateValue (bound : Value.{u} set) (property : Value predicate) : Value set :=
  CodedFamilies.encode (HSet.sep
    (fun value => holds (app property (CodedFamilies.encode value))) (CodedFamilies.decode bound))

def replaceValue (presentation : HSet.Presentation.{u}) (bound : Value.{u} set)
    (function : Value mapping) : Value set :=
  CodedFamilies.encode (HSet.image presentation (CodedFamilies.decode bound)
    (fun value => CodedFamilies.decode (app function (CodedFamilies.encode value.1))))

def constants (presentation : HSet.Presentation.{u}) : {type : Ty Unit} → Symbol type → Value.{u} type
  | _, .member => lam (fun element => lam (fun bound => truth (codeMem bound.1 element.1)))
  | _, .empty => CodedFamilies.encode (∅ : HSet.{u})
  | _, .union => lam (fun bound => CodedFamilies.encode (HSet.sUnion (CodedFamilies.decode bound)))
  | _, .power => lam (fun bound => CodedFamilies.encode (HSet.powerset (CodedFamilies.decode bound)))
  | _, .separate => lam (fun bound => lam (separateValue bound))
  | _, .replace => lam (fun bound => lam (replaceValue presentation bound))

theorem decode_separateValue (bound : Value.{u} set) (property : Value predicate) :
    decode set (separateValue bound property) =
      HSet.sep (fun value => (decode predicate property value).down) (decode set bound) := by
  change CodedFamilies.decode (CodedFamilies.encode _) = _
  rw [CodedFamilies.decode_encode]
  congr 1

theorem decode_replaceValue (presentation : HSet.Presentation.{u}) (bound : Value.{u} set)
    (function : Value mapping) :
    decode set (replaceValue presentation bound function) =
      HypersetHenkinInterpretation.replacement presentation (decode set bound) (decode mapping function) := by
  change CodedFamilies.decode (CodedFamilies.encode _) = _
  rw [CodedFamilies.decode_encode]
  unfold HypersetHenkinInterpretation.replacement
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Every actual material operation agrees with its independent hyperset meaning. -/
theorem decode_constants (presentation : HSet.Presentation.{u}) {type : Ty Unit} (symbol : Symbol type) :
    decode type (constants presentation symbol) = HypersetHenkinInterpretation.denoteSymbol presentation symbol := by
  cases symbol with
  | member =>
      rw [constants, decode_lam]
      funext element
      rw [decode_lam]
      funext bound
      change HSet.{u} at element bound
      change ZFSetHOLTypeInterpretation.truthEquiv (truth _) = _
      rw [ZFSetHOLTypeInterpretation.truthEquiv_truth]
      apply ULift.ext
      change (CodedFamilies.decode ((decode set).symm element) ∈
        CodedFamilies.decode ((decode set).symm bound)) = (element ∈ bound)
      exact congrArg₂ (fun element bound : HSet.{u} => element ∈ bound)
        ((decode set).apply_symm_apply element) ((decode set).apply_symm_apply bound)
  | empty => exact CodedFamilies.decode_encode _
  | union =>
      rw [constants, decode_lam]
      funext bound
      change CodedFamilies.decode (CodedFamilies.encode _) = _
      rw [CodedFamilies.decode_encode]
      exact congrArg HSet.sUnion ((decode set).apply_symm_apply bound)
  | power =>
      rw [constants, decode_lam]
      funext bound
      change CodedFamilies.decode (CodedFamilies.encode _) = _
      rw [CodedFamilies.decode_encode]
      exact congrArg HSet.powerset ((decode set).apply_symm_apply bound)
  | separate =>
      rw [constants, decode_lam]
      funext bound
      rw [decode_lam]
      funext property
      rw [decode_separateValue, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
  | replace =>
      rw [constants, decode_lam]
      funext bound
      rw [decode_lam]
      funext function
      rw [decode_replaceValue, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl

def interpret (presentation : HSet.Presentation.{u}) :
    {Γ : Ctx Unit} → {type : Ty Unit} → Term Symbol Γ type → Valuation Γ → Value type :=
  ZFSetSimpleTypeInterpretation.interpret bases (constants presentation)

/-- Full term-level agreement uses the shared structural induction. -/
theorem term_agreement (presentation : HSet.Presentation.{u}) {Γ : Ctx Unit} {type : Ty Unit}
    (term : Term Symbol Γ type) (valuation : Valuation.{u} Γ) :
    decode type (interpret presentation term valuation) =
      (HypersetHenkinInterpretation.model presentation).denote term (decodeValuation valuation) :=
  ZFSetSimpleTypeInterpretation.decode_interpret bases (fun _ => CodedFamilies.carrierEquiv)
    (HypersetHenkinInterpretation.denoteSymbol presentation) (constants presentation)
    (decode_constants presentation) term valuation

/-- All 29 proof constructors preserve truth in the actual graph interpreter. -/
theorem proof_sound (presentation : HSet.Presentation.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula Symbol Γ)} {conclusion : Formula Symbol Γ}
    (proof : ProofSyntax Symbol hypotheses conclusion) (valuation : Valuation.{u} Γ)
    (satisfied : ∀ formula ∈ hypotheses, holds (interpret presentation formula valuation)) :
    holds (interpret presentation conclusion valuation) := by
  change (decode .prop (interpret presentation conclusion valuation)).down
  rw [term_agreement]
  apply Soundness.extDerivation_sound proof.erase
    (HypersetHenkinInterpretation.functionsRespectEqv presentation)
    (fun _ => HypersetHenkinInterpretation.fullDomains presentation _ _)
  intro formula member
  have truth := congrArg ULift.down (term_agreement presentation formula valuation)
  exact truth ▸ satisfied formula member


def substValuation (presentation : HSet.Presentation.{u}) {Γ Δ : Ctx Unit}
    (substitution : Subst Symbol Γ Δ) (valuation : Valuation.{u} Δ) : Valuation.{u} Γ :=
  ZFSetSimpleTypeInterpretation.substValuation bases (constants presentation) substitution valuation

theorem decode_substValuation (presentation : HSet.Presentation.{u}) {Γ Δ : Ctx Unit}
    (substitution : Subst Symbol Γ Δ) (valuation : Valuation.{u} Δ) :
    (decodeValuation (substValuation presentation substitution valuation) : RawValuation Γ) =
      (Soundness.substVal (HypersetHenkinInterpretation.model presentation) substitution
        (decodeValuation valuation) : RawValuation Γ) :=
  ZFSetSimpleTypeInterpretation.decode_substValuation bases (fun _ => CodedFamilies.carrierEquiv)
    (HypersetHenkinInterpretation.denoteSymbol presentation) (constants presentation)
    (decode_constants presentation) substitution valuation

theorem interpret_substitution (presentation : HSet.Presentation.{u}) {Γ Δ : Ctx Unit} {type : Ty Unit}
    (term : Term Symbol Γ type) (substitution : Subst Symbol Γ Δ) (valuation : Valuation.{u} Δ) :
    interpret presentation (HOL.subst substitution term) valuation =
      interpret presentation term (substValuation presentation substitution valuation) :=
  ZFSetSimpleTypeInterpretation.interpret_substitution bases (fun _ => CodedFamilies.carrierEquiv)
    (HypersetHenkinInterpretation.denoteSymbol presentation) (constants presentation)
    (decode_constants presentation) term substitution valuation

/-- The membership of the cyclic value is evaluated by the interpreted
relation, even though its material code belongs to a well-founded host. -/
theorem quine_self_member (presentation : HSet.Presentation.{u}) :
    holds (interpret presentation
      (ZFSetHenkinInterpretation.member (.var .vz) (.var .vz) : Formula Symbol [set])
      (fun {_} index => match index with | .vz => HypersetHOLTypeInterpretation.quine)) := by
  let formula : Formula Symbol [set] := ZFSetHenkinInterpretation.member (.var .vz) (.var .vz)
  let valuation : Valuation.{u} [set] :=
    fun {_} index => match index with | .vz => HypersetHOLTypeInterpretation.quine.{u}
  have actual := congrArg ULift.down (term_agreement presentation formula valuation)
  change holds (interpret presentation formula valuation) =
    (CodedFamilies.decode (CodedFamilies.encode HSet.quineAtom.{u}) ∈
      CodedFamilies.decode (CodedFamilies.encode HSet.quineAtom.{u})) at actual
  rw [CodedFamilies.decode_encode] at actual
  exact actual.symm ▸ HSet.quineAtom_mem_self

/-- A single explicitly justified host universe contains every simple-type
code and every value produced by the actual structural interpreter. Both
universe predicates concern that same host set at the same size index. -/
theorem exists_tarski_envelope
    (cofinal : ZFSetUniverseClosure.CofinalInaccessibles.{u + 1})
    (presentation : HSet.Presentation.{u}) :
    ∃ U : ZFSet.{u + 1}, ZFSetUniverseClosure.Closed U ∧
      ZFSetTarskiUniverses.IsTarskiUniverse U ∧
      (∀ type : Ty Unit, typeCode.{u} type ∈ U) ∧
      (∀ (Γ : Ctx Unit) (type : Ty Unit) (term : Term Symbol Γ type)
        (valuation : Valuation.{u} Γ), (interpret presentation term valuation).1 ∈ U) := by
  obtain ⟨U, contains, closed, tarski⟩ :=
    ZFSetTarskiUniverses.exists_common_enclosure cofinal hsetCode.{u}
  exact ⟨U, closed, tarski, (all_typeCodes_mem_iff closed).mpr contains,
    fun _ type term valuation => value_mem closed contains type (interpret presentation term valuation)⟩

/-- A Tarski host enclosure also contains an actual cyclic guest value.
The two membership relations still disagree on that value's own code. -/
theorem exists_tarski_host_with_cyclic_guest
    (cofinal : ZFSetUniverseClosure.CofinalInaccessibles.{u + 1}) :
    ∃ U : ZFSet.{u + 1}, ZFSetUniverseClosure.Closed U ∧
      ZFSetTarskiUniverses.IsTarskiUniverse U ∧
      quine.{u}.1 ∈ U ∧ codeMem quine.{u}.1 quine.{u}.1 ∧ quine.{u}.1 ∉ quine.{u}.1 := by
  obtain ⟨U, contains, closed, tarski⟩ :=
    ZFSetTarskiUniverses.exists_common_enclosure cofinal hsetCode.{u}
  exact ⟨U, closed, tarski, value_mem closed contains set quine, quine_memberships⟩

end Mettapedia.Logic.HOL.Embedding.HypersetHOLTermInterpretation
