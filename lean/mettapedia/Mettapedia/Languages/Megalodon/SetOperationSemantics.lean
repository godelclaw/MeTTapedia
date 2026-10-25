import Mettapedia.Languages.Megalodon.SetOperationProofCompilation
import Mettapedia.Languages.Megalodon.HenkinProofSoundness
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation

/-!
# Material meanings of the common Megalodon signature

The six opaque declarations are interpreted by the supplied material HOL
model's actual operations. Reading the signature back preserves each named
operation, including union and powerset, which have the same simple type.
The comparison concerns values, contexts and accepted monomorphic proofs;
the material laws remain hypotheses of those proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.SetOperationSemantics

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation
open SetOperationProofCompilation

universe w

/-- All schematic target sorts are interpreted in the supplied material
carrier; the common signature itself uses only base sort zero. -/
def materialBase (_ : Base) : Ty Unit := set

def materialType (value : Ty Base) : Ty Unit := value.substitute materialBase

theorem materialType_type (value : Ty Unit) : materialType (type value) = value := by
  induction value with
  | prop => rfl
  | base value => cases value; rfl
  | arr first second ihf ihs => exact congrArg₂ Ty.arr ihf ihs

/-- A declaration's lookup and type evidence select its mathematical symbol.
Type alone would not distinguish union from powerset. -/
def materialSymbol {value : Ty Base}
    (constant : Constant environment value) : Symbol (materialType value) := by
  cases constant with
  | primitive index lookup => simp [environment] at lookup
  | named name entry lookup typed =>
      have member := lookupTermList?_mem environment.terms name lookup
      by_cases memberEntry : entry = declaration Symbol.member
      · subst entry
        have same := reifyType_injective typed
        subst value
        exact .member
      by_cases emptyEntry : entry = declaration Symbol.empty
      · subst entry
        have same := reifyType_injective typed
        subst value
        exact .empty
      by_cases unionEntry : entry = declaration Symbol.union
      · subst entry
        have same := reifyType_injective typed
        subst value
        exact .union
      by_cases powerEntry : entry = declaration Symbol.power
      · subst entry
        have same := reifyType_injective typed
        subst value
        exact .power
      by_cases separateEntry : entry = declaration Symbol.separate
      · subst entry
        have same := reifyType_injective typed
        subst value
        exact .separate
      by_cases replaceEntry : entry = declaration Symbol.replace
      · subst entry
        have same := reifyType_injective typed
        subst value
        exact .replace
      simp [environment, memberEntry, emptyEntry, unionEntry, powerEntry, separateEntry, replaceEntry] at member

theorem materialSymbol_symbol {value : Ty Unit} (constant : Symbol value) :
    HEq (materialSymbol (symbol constant)) constant := by
  cases constant <;> rfl

/-- Extend an actual material interpretation to the native signature by the
standard type-reduct construction. No material axiom is added here. -/
noncomputable def model (source : HenkinModel.{0, 0, w} Unit Symbol) :
    HenkinModel.{0, 0, w} Base (Constant environment) :=
  HenkinModel.standardTypeReduct materialBase materialSymbol source

theorem fullDomains (source : HenkinModel.{0, 0, w} Unit Symbol) :
    (model source).FullDomains :=
  HenkinModel.standardTypeReduct_fullDomains _ _ _

/-- Returning along the six-symbol inclusion recovers exactly the supplied
carrier and operations. Restricted admissibility is standardized explicitly. -/
theorem sourceReduct_standard (source : HenkinModel.{0, 0, w} Unit Symbol) :
    HenkinModel.standardTypeReduct base symbol (model source) =
      HenkinModel.standard source.Carrier source.constDen := by
  apply HenkinModel.standard_ext rfl
  intro value constant
  refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
  refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
  cases constant <;> rfl

theorem sourceReduct_eq (source : HenkinModel.{0, 0, w} Unit Symbol)
    (full : source.FullDomains) :
    HenkinModel.standardTypeReduct base symbol (model source) = source :=
  (sourceReduct_standard source).trans (HenkinModel.standard_eq_of_fullDomains source full)

/-- Pull back an actual native-context valuation, preserving variable positions. -/
noncomputable def sourceValuation (source : HenkinModel.{0, 0, w} Unit Symbol)
    {gamma : Ctx Unit} (values : (model source).Valuation (gamma.map type)) :
    source.Valuation gamma :=
  HenkinModel.typeReductValuation base symbol (model source) values

theorem sourceValuation_extend (source : HenkinModel.{0, 0, w} Unit Symbol)
    {gamma : Ctx Unit} {value : Ty Unit}
    (values : (model source).Valuation (gamma.map type))
    (argument : Ty.denote (model source).Carrier (type value)) :
    (sourceValuation source (gamma := value :: gamma)
      ((model source).extend values argument) :
      source.Valuation (value :: gamma)) =
      (fun {_result} index => source.extend (sourceValuation source values)
        ((Ty.denoteSubstituteEquiv base (model source).Carrier value).symm argument) index) := by
  funext result index
  cases index <;> rfl

/-- The complete typed term translation preserves actual values, including
function values and arbitrary open contexts. -/
theorem denote_term (source : HenkinModel.{0, 0, w} Unit Symbol)
    (full : source.FullDomains) {gamma : Ctx Unit} {value : Ty Unit}
    (expression : Term Symbol gamma value)
    (values : (model source).Valuation (gamma.map type)) :
    Ty.denoteSubstituteEquiv base (model source).Carrier value
      (source.denote expression (sourceValuation source values)) =
      (model source).denote (term expression) values := by
  have comparison := HenkinModel.denote_mapTypes base symbol (model source)
    (fullDomains source) expression values
  have denotations : HEq
      @(HenkinModel.standardTypeReduct base symbol (model source)).denote
      @source.denote := by rw [sourceReduct_eq source full]
  rw [eq_of_heq denotations] at comparison
  exact comparison

theorem denote_encoded_formula (source : HenkinModel.{0, 0, w} Unit Symbol)
    (full : source.FullDomains) {gamma : Ctx Unit} (formula : Formula Symbol gamma)
    (values : (model source).Valuation (gamma.map type)) :
    (model source).denote (HOLTermEncoding.encode (term formula)) values =
      source.denote formula (sourceValuation source values) :=
  (HOLTermEncoding.denote_encode _ (fullDomains source) _ values).trans
    (denote_term source full formula values).symm

theorem lookup_opaque (name : Name) (entry : TermDecl)
    (lookup : environment.lookupTerm? name = some entry) : entry.definition = none := by
  have member := lookupTermList?_mem environment.terms name lookup
  simp only [environment, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem checkedDefinitions : CheckedPlainDefinitions environment where
  body name entry body lookup defined _ := by
    rw [lookup_opaque name entry lookup] at defined
    contradiction

theorem definitionEquations (source : HenkinModel.{0, 0, w} Unit Symbol) :
    DefinitionEquations checkedDefinitions (model source) where
  equation name entry lookup _ body defined := by
    rw [lookup_opaque name entry lookup] at defined
    contradiction

theorem knownValidity (source : HenkinModel.{0, 0, w} Unit Symbol) :
    NativeProof.KnownValidity (model source) := by
  intro name raw lookup
  simp [Environment.lookupKnown?, environment, lookupKnownList?] at lookup

/-- Actual native acceptance implies the supplied material meaning, at every
open valuation satisfying the original ordered hypotheses. The supported
proof fragment excludes prefix type abstraction; normalization success and
the independently interpreted hypotheses remain explicit. -/
theorem accepted_material (source : HenkinModel.{0, 0, w} Unit Symbol)
    (full : source.FullDomains) {gamma : Ctx Unit}
    (assumptions : List (Formula Symbol gamma)) (conclusion : Formula Symbol gamma)
    {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment environment depth program)
    (accepted : checkProof environment fuel depth ((gamma.map type).map reifyType)
      (assumptions.map (fun formula => HOLTermEncoding.native (term formula)))
      program (HOLTermEncoding.native (term conclusion)) = true)
    (values : (model source).Valuation (gamma.map type))
    (satisfied : Soundness.SatisfiesHyps source (sourceValuation source values) assumptions) :
    (source.denote conclusion (sourceValuation source values)).down := by
  have erased : NativeProof.ErasedHypotheses
      (assumptions.map (fun formula => HOLTermEncoding.encode (term formula)))
      (assumptions.map (fun formula => HOLTermEncoding.native (term formula))) := by
    change (assumptions.map (fun formula => HOLTermEncoding.encode (term formula))).map erase =
      (assumptions.map (fun formula => HOLTermEncoding.native (term formula))).map some
    simp only [List.map_map]
    apply List.map_congr_left
    intro formula _
    exact HOLTermEncoding.native_erased _
  have encodedSatisfied : Soundness.SatisfiesHyps (model source) values
      (assumptions.map (fun formula => HOLTermEncoding.encode (term formula))) := by
    intro formula member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [denote_encoded_formula source full]
    exact satisfied original originalMember
  have valid := NativeProof.checkProof_sound checkedDefinitions (model source)
    (definitionEquations source) (knownValidity source) fragment erased
    (HOLTermEncoding.encode (term conclusion)) (HOLTermEncoding.native_erased _)
    accepted values (fun _ => fullDomains source _ _) encodedSatisfied
  rwa [denote_encoded_formula source full] at valid

/-- The common-profile checker theorem, with the source theory's assumptions
kept separate from the native declaration environment. -/
theorem accepted_closed (source : HenkinModel.{0, 0, w} Unit Symbol)
    (full : source.FullDomains) (assumptions : List (ClosedFormula Symbol))
    (conclusion : ClosedFormula Symbol) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment environment depth program)
    (accepted : checkProof environment fuel depth []
      (assumptions.map (fun formula => HOLTermEncoding.native (term formula)))
      program (HOLTermEncoding.native (term conclusion)) = true)
    (satisfied : ∀ formula ∈ assumptions, source.models formula) :
    source.models conclusion := by
  simp only [HenkinModel.models, PreModel.models] at satisfied ⊢
  have closedDenotation (formula : ClosedFormula Symbol) :
      source.denote formula
        (sourceValuation source (gamma := []) (fun index => nomatch index)) =
      source.denote formula (fun index => nomatch index) := by
    congr 1
    funext value index
    nomatch index
  have hypotheses : Soundness.SatisfiesHyps source
      (sourceValuation source (gamma := []) (fun index => nomatch index)) assumptions := by
    intro formula present
    rw [closedDenotation]
    convert satisfied formula present using 1
    congr 2
    funext value index
    nomatch index
  have valid := accepted_material source full assumptions conclusion fragment accepted
    (fun index => nomatch index) hypotheses
  rw [closedDenotation] at valid
  convert valid using 1
  congr 2
  funext value index
  nomatch index

/-- A material countermodel prevents every supported native proof from
passing, rather than merely refuting one attempted certificate. -/
theorem refused_of_countermodel (source : HenkinModel.{0, 0, w} Unit Symbol)
    (full : source.FullDomains) (assumptions : List (ClosedFormula Symbol))
    (conclusion : ClosedFormula Symbol) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment environment depth program)
    (satisfied : ∀ formula ∈ assumptions, source.models formula)
    (refuted : ¬ source.models conclusion) :
    checkProof environment fuel depth []
      (assumptions.map (fun formula => HOLTermEncoding.native (term formula)))
      program (HOLTermEncoding.native (term conclusion)) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact refuted (accepted_closed source full assumptions conclusion fragment accepted satisfied)

open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-- Global membership induction cannot be inferred from the shared operation
laws: the actual hyperset interpretation is a countermodel. -/
theorem setInduction_refused (presentation : HSet.Presentation.{w})
    {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment environment depth program) :
    checkProof environment fuel depth []
      (Embedding.HypersetHenkinInterpretation.operationTheory.map
        (fun formula => HOLTermEncoding.native (term formula)))
      program (HOLTermEncoding.native (term setInduction)) = false :=
  refused_of_countermodel (Embedding.HypersetHenkinInterpretation.model presentation)
    (Embedding.HypersetHenkinInterpretation.fullDomains presentation) _ _ fragment
    (Embedding.HypersetHenkinInterpretation.operationTheory_valid presentation)
    (Embedding.HypersetHenkinInterpretation.setInduction_invalid presentation)

/-- Nor do the same laws entail cyclic self-membership: the well-founded
material interpretation remains an admissible reading. -/
theorem selfMember_refused (presentation : HSet.Presentation.{w})
    {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment environment depth program) :
    checkProof environment fuel depth []
      (Embedding.HypersetHenkinInterpretation.operationTheory.map
        (fun formula => HOLTermEncoding.native (term formula)))
      program (HOLTermEncoding.native (term Embedding.HypersetHenkinInterpretation.selfMember)) = false :=
  refused_of_countermodel (Embedding.WellFoundedHypersetInterpretation.model presentation)
    (Embedding.WellFoundedHypersetInterpretation.fullDomains presentation) _ _ fragment
    (Embedding.HypersetHenkinInterpretation.wellFounded_operationTheory_valid presentation)
    (Embedding.HypersetHenkinInterpretation.wellFounded_refutes_selfMember presentation)

#print axioms materialSymbol_symbol
#print axioms sourceReduct_standard
#print axioms sourceValuation_extend
#print axioms denote_term
#print axioms accepted_material
#print axioms accepted_closed
#print axioms setInduction_refused
#print axioms selfMember_refused

end Mettapedia.Languages.Megalodon.SetOperationSemantics
