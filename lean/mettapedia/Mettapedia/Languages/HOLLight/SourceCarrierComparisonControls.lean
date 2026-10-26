import Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
import Mettapedia.Languages.HOLLight.SourceProfileModelsControls

/-!
# Natural and recursive-space interpretation controls

The positive model interprets natural operations and a genuinely branching
recursive space, followed by the actual nine Boolean definition extensions.
Changing successor to a two-step advance preserves separation and injectivity
but loses induction. Thus the categoricity premise is independently exercised.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.SourceCarrierComparisonControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReferenceBooleanSemantics StandardTheoryInterpretation ModelInterpretation

theorem replayed_booleans : Meanings
    ((SourceProfileModels.sourceReplayFrame
      SourceProfileModels.Controls.Phases.commands SourceProfileModels.Controls.Phases.after
      SourceProfileModels.Controls.Phases.replayed).frame.model
        TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})) :=
  replay_meanings _ _ _ _ _

abbrev Trees := Mettapedia.TypeTheory.RecursiveSpace.Tree (ULift.{1} Bool)

def numberRaw : Ty := .var (Name.global "N")
def payloadRaw : Ty := .var (Name.global "A")
def spaceRaw : Ty := .var (Name.global "R")
abbrev number : HOL.Ty AtomicTy := .base ⟨numberRaw, by exact ⟨rfl,rfl⟩⟩
abbrev payload : HOL.Ty AtomicTy := .base ⟨payloadRaw, by exact ⟨rfl,rfl⟩⟩
abbrev space : HOL.Ty AtomicTy := .base ⟨spaceRaw, by exact ⟨rfl,rfl⟩⟩
theorem number_toHOL : numberRaw.toHOL = number := Ty.toHOL_of_isAtomic ⟨rfl,rfl⟩
theorem payload_toHOL : payloadRaw.toHOL = payload := Ty.toHOL_of_isAtomic ⟨rfl,rfl⟩
theorem space_toHOL : spaceRaw.toHOL = space := Ty.toHOL_of_isAtomic ⟨rfl,rfl⟩

theorem space_ne_number : space ≠ number := by
  intro same
  have raw := congrArg Subtype.val (HOL.Ty.base.inj same)
  simp [spaceRaw,numberRaw,Name.global] at raw

def constructorType : HOL.Ty AtomicTy := number.arr (payload.arr ((number.arr space).arr space))

noncomputable def carriers (atom : AtomicTy) : Type 1 := by
  classical
  exact if atom.1 = numberRaw then ULift.{1} Nat
  else if atom.1 = payloadRaw then ULift.{1} Bool
  else Trees

noncomputable def defaultBase (atom : AtomicTy) : carriers atom := by
  classical
  unfold carriers
  split
  · exact .up 0
  · split
    · exact .up false
    · exact Mettapedia.TypeTheory.RecursiveSpace.bottom

noncomputable def defaultValue : (type : HOL.Ty AtomicTy) → HOL.Ty.denote.{0,1} carriers type
  | .prop => .up True
  | .base atom => defaultBase atom
  | .arr _ target => fun _ => defaultValue target

theorem number_carrier : HOL.Ty.denote.{0,1} carriers number = ULift.{1} Nat := by
  simp [numberRaw, carriers, HOL.Ty.denote]

theorem payload_carrier : HOL.Ty.denote.{0,1} carriers payload = ULift.{1} Bool := by
  simp [payloadRaw, numberRaw, carriers, HOL.Ty.denote, Name.global]

theorem space_carrier : HOL.Ty.denote.{0,1} carriers space = Trees := by
  simp [spaceRaw, payloadRaw, numberRaw, carriers, HOL.Ty.denote, Name.global]

def numberValues : ULift.{1} Nat ≃ HOL.Ty.denote.{0,1} carriers number :=
  (Equiv.cast number_carrier).symm

def payloadValues : ULift.{1} Bool ≃ HOL.Ty.denote.{0,1} carriers payload :=
  (Equiv.cast payload_carrier).symm

def treeValues : Trees ≃ HOL.Ty.denote.{0,1} carriers space :=
  (Equiv.cast space_carrier).symm

noncomputable def meanings (origin : Nat) (successor : Nat → Nat) :
    {type : HOL.Ty AtomicTy} → Symbol type → HOL.Ty.denote.{0,1} carriers type := by
  classical
  intro type _
  exact if same : type = number then same ▸ numberValues (.up origin)
    else if same : type = number.arr number then same ▸
      (fun n => numberValues (.up (successor (numberValues.symm n).down)))
    else if same : type = space then same ▸ treeValues Mettapedia.TypeTheory.RecursiveSpace.bottom
    else if same : type = constructorType then same ▸
      (fun tag value children => treeValues (Mettapedia.TypeTheory.RecursiveSpace.construct
        (numberValues.symm tag).down (payloadValues.symm value)
        (fun n => treeValues.symm (children (numberValues (.up n))))))
    else defaultValue type

noncomputable def baseModel (origin : Nat) (successor : Nat → Nat) : HOL.HenkinModel.{0,0,1} AtomicTy Symbol :=
  .standard carriers (meanings origin successor)

noncomputable def model (origin : Nat) (successor : Nat → Nat) : HOL.HenkinModel.{0,0,1} AtomicTy Symbol :=
  Interpretation.ontoModel (baseModel origin successor)

theorem full (origin : Nat) (successor : Nat → Nat) : (model origin successor).FullDomains :=
  Interpretation.ontoModel_fullDomains _ (HOL.HenkinModel.fullDomains_standard _ _)

theorem booleans (origin : Nat) (successor : Nat → Nat) : Meanings (model origin successor) :=
  reference_extension_meanings _ (HOL.HenkinModel.fullDomains_standard _ _)

@[reducible] def natural : NaturalModelCategoricity.Signature where
  number := number
  zero := .const (.variable ⟨Name.global "origin", numberRaw⟩ number_toHOL)
  successor := .const (.variable ⟨Name.global "next", .function numberRaw numberRaw⟩ (by simp only [Ty.toHOL_function, number_toHOL]))

@[reducible] def recursive : RecursiveSpaceModelComparison.Signature where
  number := number
  payload := payload
  space := space
  bottom := .const (.variable ⟨Name.global "bottom", spaceRaw⟩ space_toHOL)
  construct := .const (.variable ⟨Name.global "construct",
    .function numberRaw (.function payloadRaw (.function (.function numberRaw spaceRaw) spaceRaw))⟩ (by simp only [Ty.toHOL_function, number_toHOL, payload_toHOL, space_toHOL]))

theorem natural_origin (origin : Nat) (successor : Nat → Nat) :
    natural.origin (model origin successor) = numberValues (.up origin) := by
  dsimp only [NaturalModelCategoricity.Signature.origin, natural, model, HOL.HenkinModel.denote, HOL.PreModel.denote]
  rw [reference_extension_variable]
  simp [baseModel, HOL.HenkinModel.standard, meanings]
  rfl

theorem natural_next (origin : Nat) (successor : Nat → Nat) (n : natural.Carrier (model origin successor)) :
    natural.next (model origin successor) n = numberValues (.up (successor (numberValues.symm n).down)) := by
  dsimp only [NaturalModelCategoricity.Signature.next, natural, model, HOL.HenkinModel.denote, HOL.PreModel.denote]
  rw [reference_extension_variable]
  simp [baseModel, HOL.HenkinModel.standard, meanings, number, numberRaw]
  rfl

theorem natural_separation : (model 0 Nat.succ).models natural.successorSeparation := by
  rw [natural.successorSeparation_meaning _ (full _ _) (booleans _ _)]
  intro n same
  rw [natural_next, natural_origin] at same
  have := congrArg ULift.down (numberValues.injective same)
  exact Nat.noConfusion this

theorem natural_injectivity : (model 0 Nat.succ).models natural.successorInjective := by
  rw [natural.successorInjective_meaning _ (full _ _) (booleans _ _)]
  intro n m same
  rw [natural_next, natural_next] at same
  apply numberValues.symm.injective
  apply ULift.ext
  exact Nat.succ.inj (congrArg ULift.down (numberValues.injective same))

theorem natural_induction : (model 0 Nat.succ).models natural.induction := by
  rw [natural.induction_meaning _ (full _ _) (booleans _ _)]
  intro property atZero atNext n
  obtain ⟨⟨n⟩,rfl⟩ := numberValues.surjective n
  induction n with
  | zero => simpa only [natural_origin] using atZero
  | succ n ih =>
    have step := atNext (numberValues (.up n)) ih
    have same := natural_next 0 Nat.succ (numberValues (.up n))
    rw [Equiv.symm_apply_apply] at same
    exact same ▸ step

noncomputable def natural_equivalence : Nat ≃ natural.Carrier (model 0 Nat.succ) :=
  natural.naturalEquivalence _ (full _ _) (booleans _ _) natural_separation natural_injectivity natural_induction

theorem skipped_successor_separation : (model 0 (fun n => n+2)).models natural.successorSeparation := by
  rw [natural.successorSeparation_meaning _ (full _ _) (booleans _ _)]
  intro n same
  rw [natural_next, natural_origin] at same
  have impossible := congrArg ULift.down (numberValues.injective same)
  exact Nat.noConfusion impossible

theorem skipped_successor_injectivity : (model 0 (fun n => n+2)).models natural.successorInjective := by
  rw [natural.successorInjective_meaning _ (full _ _) (booleans _ _)]
  intro n m same
  rw [natural_next, natural_next] at same
  apply numberValues.symm.injective
  apply ULift.ext
  exact Nat.add_right_cancel (congrArg ULift.down (numberValues.injective same))

theorem skipped_successor_induction_refused : ¬ (model 0 (fun n => n+2)).models natural.induction := by
  rw [natural.induction_meaning _ (full _ _) (booleans _ _)]
  intro induction
  have impossible := induction (fun n => (numberValues.symm n).down % 2 = 0)
    (by rw [natural_origin, Equiv.symm_apply_apply]; rfl)
    (by intro n even; rw [natural_next]; simpa using even)
    (numberValues (.up 1))
  norm_num at impossible

theorem recursive_origin : recursive.origin (model 0 Nat.succ) =
    treeValues Mettapedia.TypeTheory.RecursiveSpace.bottom := by
  dsimp only [RecursiveSpaceModelComparison.Signature.origin, recursive, model,
    HOL.HenkinModel.denote, HOL.PreModel.denote]
  rw [reference_extension_variable]
  simp [baseModel, HOL.HenkinModel.standard, meanings]
  split
  · rename_i impossible
    exact False.elim (space_ne_number impossible)
  · rfl

theorem recursive_constructor (tag : recursive.Numbers (model 0 Nat.succ))
    (value : recursive.Payload (model 0 Nat.succ))
    (children : recursive.Numbers (model 0 Nat.succ) → recursive.Carrier (model 0 Nat.succ)) :
    recursive.constructor (model 0 Nat.succ) tag value children =
      treeValues (Mettapedia.TypeTheory.RecursiveSpace.construct
        (numberValues.symm tag).down (payloadValues.symm value)
        (fun n => treeValues.symm (children (numberValues (.up n))))) := by
  dsimp only [RecursiveSpaceModelComparison.Signature.constructor, recursive, model,
    HOL.HenkinModel.denote, HOL.PreModel.denote]
  rw [reference_extension_variable]
  simp [baseModel, HOL.HenkinModel.standard, meanings, constructorType, space, number, payload,
    spaceRaw, numberRaw, payloadRaw, Name.global]
  rfl

theorem recursive_separation : (model 0 Nat.succ).models recursive.constructorSeparation := by
  rw [recursive.constructorSeparation_meaning _ (full _ _) (booleans _ _)]
  intro tag value children same
  rw [recursive_constructor, recursive_origin] at same
  exact Mettapedia.TypeTheory.RecursiveSpace.construct_ne_bottom _ _ _ (treeValues.injective same)

theorem recursive_injectivity : (model 0 Nat.succ).models recursive.constructorInjective := by
  rw [recursive.constructorInjective_meaning _ (full _ _) (booleans _ _)]
  intro tag value children tag' value' children'
  constructor
  · intro same
    rw [recursive_constructor, recursive_constructor] at same
    obtain ⟨tags,values,recursive⟩ :=
      (Mettapedia.TypeTheory.RecursiveSpace.construct_injective _ _ _ _ _ _).mp (treeValues.injective same)
    refine ⟨numberValues.symm.injective (ULift.ext _ _ tags), payloadValues.symm.injective values, ?_⟩
    funext n
    obtain ⟨⟨n⟩,rfl⟩ := numberValues.surjective n
    exact treeValues.symm.injective (congrFun recursive n)
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

theorem recursive_induction : (model 0 Nat.succ).models recursive.induction := by
  rw [recursive.induction_meaning _ (full _ _) (booleans _ _)]
  intro property atBottom atConstructor value
  obtain ⟨value,rfl⟩ := treeValues.surjective value
  apply Mettapedia.TypeTheory.RecursiveSpace.induction (fun value => property (treeValues value)) ?_ ?_ value
  · exact recursive_origin ▸ atBottom
  · intro tag payload children hypotheses
    have result := atConstructor (numberValues (.up tag)) (payloadValues payload)
      (fun n => treeValues (children (numberValues.symm n).down))
      (fun n => hypotheses (numberValues.symm n).down)
    have same := recursive_constructor (numberValues (.up tag)) (payloadValues payload)
      (fun n => treeValues (children (numberValues.symm n).down))
    simp only [Equiv.symm_apply_apply] at same
    exact same ▸ result

def naturalIndices : Nat ≃ recursive.Numbers (model 0 Nat.succ) := Equiv.ulift.symm.trans numberValues

instance : Nonempty (recursive.Payload (model 0 Nat.succ)) := ⟨payloadValues (.up false)⟩

def filler : RecursiveSpaceSemantics.Relation (recursive.Payload (model 0 Nat.succ)) := fun _ _ => False

noncomputable def relational_equivalence : recursive.Carrier (model 0 Nat.succ) ≃
    RecursiveSpaceSemantics.Carrier filler :=
  recursive.relationalEquivalence _ (full _ _) (booleans _ _) naturalIndices
    recursive_separation recursive_injectivity recursive_induction filler

theorem relational_bottom : relational_equivalence (recursive.origin (model 0 Nat.succ)) =
    RecursiveSpaceSemantics.bottom filler :=
  recursive.relationalEquivalence_bottom _ (full _ _) (booleans _ _) naturalIndices
    recursive_separation recursive_injectivity recursive_induction filler

theorem relational_constructor (tag : recursive.Numbers (model 0 Nat.succ))
    (payload : recursive.Payload (model 0 Nat.succ))
    (children : recursive.Numbers (model 0 Nat.succ) → recursive.Carrier (model 0 Nat.succ)) :
    relational_equivalence (recursive.constructor (model 0 Nat.succ) tag payload children) =
      RecursiveSpaceSemantics.construct filler (naturalIndices.symm tag) payload
        (fun n => relational_equivalence (children (naturalIndices n))) :=
  recursive.relationalEquivalence_constructor _ (full _ _) (booleans _ _) naturalIndices
    recursive_separation recursive_injectivity recursive_induction filler tag payload children

theorem constructor_only_recursion_not_unique :
    ∃ first second : recursive.Carrier (model 0 Nat.succ) → Bool, first ≠ second ∧
      (∀ tag payload children,
        first ((recursive.algebra _ (full _ _) (booleans _ _) naturalIndices
          recursive_separation recursive_injectivity recursive_induction).construct tag payload children) = false) ∧
      (∀ tag payload children,
        second ((recursive.algebra _ (full _ _) (booleans _ _) naturalIndices
          recursive_separation recursive_injectivity recursive_induction).construct tag payload children) = false) :=
  Mettapedia.TypeTheory.RecursiveSpace.constructor_recursion_not_unique
    (recursive.algebra _ (full _ _) (booleans _ _) naturalIndices
      recursive_separation recursive_injectivity recursive_induction)

#print axioms natural_equivalence
#print axioms skipped_successor_induction_refused
#print axioms relational_equivalence
#print axioms relational_constructor
#print axioms constructor_only_recursion_not_unique

end Mettapedia.Languages.HOLLight.SourceCarrierComparisonControls
