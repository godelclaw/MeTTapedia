import Mettapedia.Logic.HOL.Embedding.WellFoundedHypersetInterpretation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf
import Mettapedia.SetTheory.Profiles.Diaconescu

/-!
# Higher-order set operations with non-well-founded membership

The same HOL signature is interpreted in all material hypersets, with their
actual membership, union, powerset, separation and replacement. Extensionality
and the set-operation laws hold. Membership induction fails at the cyclic
hyperset, whereas the well-founded interpretation satisfies it.

Both interpretations validate the same six operation axioms. Their difference
therefore proves independence of membership induction and of self-membership
over that explicit common HOL theory. These are statements about all 29 rules
of retained extensional HOL, without adopting a foundation or anti-foundation
axiom in the source. Replacement takes an explicit graph presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ZFSetHenkinInterpretation (Symbol set predicate mapping member iffFormula
  extensionality emptyLaw unionLaw powerLaw separationLaw replacementLaw setInduction)

universe u

abbrev carrier (_ : Unit) : Type (u + 1) := HSet.{u}

def replacement (presentation : HSet.Presentation.{u}) (bound : HSet.{u})
    (function : HSet.{u} → HSet.{u}) : HSet.{u} :=
  HSet.image presentation bound (fun element => function element.1)

theorem mem_replacement (presentation : HSet.Presentation.{u})
    {bound value : HSet.{u}} {function : HSet.{u} → HSet.{u}} :
    value ∈ replacement presentation bound function ↔
      ∃ element ∈ bound, function element = value := by
  constructor
  · intro present
    obtain ⟨element, same⟩ := HSet.mem_image.mp present
    exact ⟨element.1, element.2, same⟩
  · rintro ⟨element, present, same⟩
    exact HSet.mem_image.mpr ⟨⟨element, present⟩, same⟩

def denoteSymbol (presentation : HSet.Presentation.{u}) :
    {A : Ty Unit} → Symbol A → Ty.denote.{0, u + 1} carrier.{u} A
  | _, .member => fun (element bound : HSet.{u}) => .up (element ∈ bound)
  | _, .empty => (∅ : HSet.{u})
  | _, .union => HSet.sUnion
  | _, .power => HSet.powerset
  | _, .separate => fun bound predicate => HSet.sep (fun element => (predicate element).down) bound
  | _, .replace => replacement presentation

def model (presentation : HSet.Presentation.{u}) : HenkinModel.{0, 0, u + 1} Unit Symbol :=
  HenkinModel.standard carrier (denoteSymbol presentation)

theorem fullDomains (presentation : HSet.Presentation.{u}) : (model presentation).FullDomains :=
  HenkinModel.fullDomains_standard carrier (denoteSymbol presentation)

theorem functionsRespectEqv (presentation : HSet.Presentation.{u}) :
    (model presentation).FunctionsRespectEqv :=
  (model presentation).functionsRespectEqv_of_fullDomains (fullDomains presentation)

theorem extensionality_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models extensionality := by
  intro first _ second _ same
  exact HSet.ext (fun element => ⟨(same element trivial).1, (same element trivial).2⟩)

theorem emptyLaw_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models emptyLaw := by
  intro element _
  exact HSet.notMem_empty element

theorem unionLaw_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models unionLaw := by
  intro bound _ element _
  constructor
  · intro present
    obtain ⟨intermediate, outer, inner⟩ := HSet.mem_sUnion.mp present
    exact ⟨intermediate, trivial, outer, inner⟩
  · rintro ⟨intermediate, _, outer, inner⟩
    exact HSet.mem_sUnion.mpr ⟨intermediate, outer, inner⟩

theorem powerLaw_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models powerLaw := by
  intro bound _ subset _
  constructor
  · intro present element _ belongs
    exact (HSet.mem_powerset.mp present) belongs
  · intro contained
    exact HSet.mem_powerset.mpr (fun _ belongs => contained _ trivial belongs)

theorem separationLaw_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models separationLaw := by
  intro bound _ predicate _ element _
  change HSet.{u} at bound element
  change HSet.{u} → ULift.{u + 1} Prop at predicate
  change (element ∈ HSet.sep (fun value => (predicate value).down) bound →
      element ∈ bound ∧ (predicate element).down) ∧
    (element ∈ bound ∧ (predicate element).down →
      element ∈ HSet.sep (fun value => (predicate value).down) bound)
  exact ⟨(HSet.mem_sep (P := fun value : HSet.{u} => (predicate value).down)).mp,
    (HSet.mem_sep (P := fun value : HSet.{u} => (predicate value).down)).mpr⟩

theorem replacementLaw_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models replacementLaw := by
  intro bound _ function _ value _
  constructor
  · intro present
    obtain ⟨element, belongs, same⟩ := (mem_replacement presentation).mp present
    exact ⟨element, trivial, belongs, same⟩
  · rintro ⟨element, _, belongs, same⟩
    exact (mem_replacement presentation).mpr ⟨element, belongs, same⟩

/-- The well-foundedness predicate is closed under the induction step, but
does not hold at the self-membered hyperset. -/
theorem setInduction_invalid (presentation : HSet.Presentation.{u}) :
    ¬ (model presentation).models setInduction := by
  intro induction
  have allWellFounded := induction (fun value => .up value.WF) trivial
    (fun value _ previous => HSet.wf_of_forall_mem
      (fun child belongs => previous child trivial belongs))
  exact HSet.not_wf_quineAtom (allWellFounded HSet.quineAtom trivial)

def selfMember : ClosedFormula Symbol :=
  .ex (member (.var .vz) (.var .vz))

theorem selfMember_valid (presentation : HSet.Presentation.{u}) :
    (model presentation).models selfMember :=
  ⟨HSet.quineAtom, trivial, HSet.quineAtom_mem_self⟩

theorem wellFounded_refutes_selfMember (presentation : HSet.Presentation.{u}) :
    ¬ (WellFoundedHypersetInterpretation.model presentation).models selfMember := by
  rintro ⟨value, _, member⟩
  exact value.2.notMem_self member

/-- The shared theory has all six actual set-operation laws, but no
membership-induction or anti-foundation premise. -/
def operationTheory : List (ClosedFormula Symbol) :=
  [extensionality, emptyLaw, unionLaw, powerLaw, separationLaw, replacementLaw]

theorem operationTheory_valid (presentation : HSet.Presentation.{u}) :
    ∀ formula ∈ operationTheory, (model presentation).models formula := by
  intro formula present
  simp only [operationTheory, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact extensionality_valid presentation
  · exact emptyLaw_valid presentation
  · exact unionLaw_valid presentation
  · exact powerLaw_valid presentation
  · exact separationLaw_valid presentation
  · exact replacementLaw_valid presentation

theorem wellFounded_operationTheory_valid (presentation : HSet.Presentation.{u}) :
    ∀ formula ∈ operationTheory,
      (WellFoundedHypersetInterpretation.model presentation).models formula := by
  intro formula present
  apply (WellFoundedHypersetInterpretation.models_iff presentation formula).mpr
  simp only [operationTheory, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZFSetHenkinInterpretation.extensionality_valid
  · exact ZFSetHenkinInterpretation.emptyLaw_valid
  · exact ZFSetHenkinInterpretation.unionLaw_valid
  · exact ZFSetHenkinInterpretation.powerLaw_valid
  · exact ZFSetHenkinInterpretation.separationLaw_valid
  · exact ZFSetHenkinInterpretation.replacementLaw_valid

theorem operationProof_sound (presentation : HSet.Presentation.{u})
    {conclusion : ClosedFormula Symbol} (proof : ProofSyntax Symbol operationTheory conclusion) :
    (model presentation).models conclusion :=
  Soundness.extDerivation_sound proof.erase (functionsRespectEqv presentation)
    (fun index => nomatch index) (operationTheory_valid presentation)

theorem wellFounded_operationProof_sound (presentation : HSet.Presentation.{u})
    {conclusion : ClosedFormula Symbol} (proof : ProofSyntax Symbol operationTheory conclusion) :
    (WellFoundedHypersetInterpretation.model presentation).models conclusion := by
  apply WellFoundedHypersetInterpretation.proof_sound presentation proof
  intro formula present
  exact wellFounded_operationTheory_valid presentation formula present

/-- Membership induction is independent of the shared higher-order
set-operation theory, as witnessed by the two actual material models. -/
theorem setInduction_independent (presentation : HSet.Presentation.{u}) :
    IsEmpty (ProofSyntax Symbol operationTheory setInduction) ∧
      IsEmpty (ProofSyntax Symbol operationTheory (.not setInduction)) :=
  ⟨⟨fun proof => setInduction_invalid presentation (operationProof_sound presentation proof)⟩,
    ⟨fun proof => (wellFounded_operationProof_sound presentation proof)
      (WellFoundedHypersetInterpretation.setInduction_valid presentation)⟩⟩

/-- The same common theory decides neither the existence nor the absence
of a self-membered set. -/
theorem selfMember_independent (presentation : HSet.Presentation.{u}) :
    IsEmpty (ProofSyntax Symbol operationTheory selfMember) ∧
      IsEmpty (ProofSyntax Symbol operationTheory (.not selfMember)) :=
  ⟨⟨fun proof => wellFounded_refutes_selfMember presentation
      (wellFounded_operationProof_sound presentation proof)⟩,
    ⟨fun proof => (operationProof_sound presentation proof) (selfMember_valid presentation)⟩⟩

/-! ## HOL choice and material dependent families -/

/-- The HOL selector is applied to the actual membership predicate. -/
def materialPicker (presentation : HSet.Presentation.{u})
    (choice : (model presentation).HilbertChoice) (bound : HSet.{u}) : HSet.{u} :=
  choice.choose set (fun element => .up (element ∈ bound))

theorem materialPicker_mem (presentation : HSet.Presentation.{u})
    (choice : (model presentation).HilbertChoice) {bound : HSet.{u}}
    (inhabited : ∃ element, element ∈ bound) :
    materialPicker presentation choice bound ∈ bound := by
  apply choice.specified set (fun element : HSet.{u} => .up (element ∈ bound))
    (fullDomains presentation _ _)
  obtain ⟨element, present⟩ := inhabited
  exact ⟨element, trivial, present⟩

/-- A HOL choice interpretation on the full material predicate domain
supplies exactly the selector needed by the existing Diaconescu argument. -/
theorem excludedMiddle_of_holChoice (presentation : HSet.Presentation.{u})
    (choice : (model presentation).HilbertChoice) :
    ∀ proposition : Prop, proposition ∨ ¬ proposition := by
  apply Mettapedia.SetTheory.Profiles.lem_of_pairSubsetChoice
    (mem := fun element bound : HSet.{u} => element ∈ bound)
    (fun first second same => HSet.ext same)
    (fun bound predicate => ⟨HSet.sep predicate bound, fun _ => HSet.mem_sep⟩)
    ⟨∅, HSet.notMem_empty⟩
    (fun first second => ⟨{first, second}, fun _ => HSet.mem_pair⟩)
    (materialPicker presentation choice)
  intro first second bound _ inhabited
  exact materialPicker_mem presentation choice inhabited

/-- Choice gives a dependent section when every actual fibre is inhabited. -/
def sectionOfInhabited (presentation : HSet.Presentation.{u})
    (choice : (model presentation).HilbertChoice) {context : HSet.{u}}
    (family : FamilyCwf.Family context)
    (inhabited : ∀ point, ∃ value, value ∈ family point) : FamilyCwf.Section family :=
  fun point => ⟨materialPicker presentation choice (family point),
    materialPicker_mem presentation choice (inhabited point)⟩

/-- The chosen section commutes with substitution of material contexts,
including the selected member value in every fibre. -/
theorem sectionOfInhabited_substitution (presentation : HSet.Presentation.{u})
    (choice : (model presentation).HilbertChoice) {source target : HSet.{u}}
    (substitution : FamilyCwf.Substitution source target)
    (family : FamilyCwf.Family target)
    (inhabited : ∀ point, ∃ value, value ∈ family point) :
    sectionOfInhabited presentation choice (family ∘ substitution)
        (fun point => inhabited (substitution point)) =
      fun point => sectionOfInhabited presentation choice family inhabited (substitution point) := rfl

/-- A genuine inhabited context with an empty material type over it. -/
def emptyFamily : FamilyCwf.Family ({∅} : HSet.{u}) := fun _ => ∅

theorem emptyFamily_has_no_section : IsEmpty (FamilyCwf.Section emptyFamily.{u}) :=
  ⟨fun value => HSet.notMem_empty
    (value ⟨∅, HSet.mem_singleton_self ∅⟩).1
    (value ⟨∅, HSet.mem_singleton_self ∅⟩).2⟩

/-- Total selection from every material type would select a member of the empty set. -/
theorem no_unrestricted_material_selector :
    ¬ Nonempty ((bound : HSet.{u}) → FamilyCwf.Elements bound) := by
  rintro ⟨select⟩
  exact HSet.notMem_empty (select ∅).1 (select ∅).2

/-- The classical host constructs HOL choice on its inhabited simple sorts. -/
noncomputable def holChoice (presentation : HSet.Presentation.{u}) :
    (model presentation).HilbertChoice :=
  HenkinModel.HilbertChoice.ofFullInhabitedDomains (fullDomains presentation)
    ((model presentation).inhabitedDomains_of_fullDomains (fullDomains presentation)
      (fun _ => (∅ : HSet.{u})))

/-- In this one material model, HOL choice coexists with an empty dependent
type. Inhabitation of a HOL carrier does not inhabit every set it contains. -/
theorem holChoice_with_empty_material_family (presentation : HSet.Presentation.{u}) :
    Nonempty (model presentation).HilbertChoice ∧ IsEmpty (FamilyCwf.Section emptyFamily.{u}) :=
  ⟨⟨holChoice presentation⟩, emptyFamily_has_no_section⟩

end Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation
