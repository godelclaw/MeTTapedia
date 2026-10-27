import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversion
import Mettapedia.TypeTheory.BubbleReindexing
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution

/-!
# Typed caller substitution of interpreted natural computations

The source and HOL substitutions retain their componentwise annotated
reading. Moving a state substitutes its actual term, displayed source type
and HOL code. Original row instances compose their caller assignments;
beta instances move through the source and HOL lifted binder substitutions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {profile : Programs.ComputationProfiles.Selection}

structure Substitution (operations : Operations Base Const)
    (profile : Programs.ComputationProfiles.Selection)
    (Γ Ξ : HOL.Ctx Base) (sourceContext : CCtx Tower.Head Γ.length)
    (targetContext : CCtx Tower.Head Ξ.length) where
  targetFormed : CCtxFormed (Programs.Annotated.church profile) targetContext
  source : CSub Tower.Head Γ.length Ξ.length
  target : HOL.Subst Const Γ Ξ
  typed : CSubstMor (Programs.Annotated.church profile) sourceContext targetContext source
  represented : ∀ {type} (index : HOL.Var Γ type),
    AnnotatedReads operations (source (variableIndex index)) (target index)

namespace Substitution

variable {Γ Ξ : HOL.Ctx Base} {sourceContext : CCtx Tower.Head Γ.length}
    {targetContext : CCtx Tower.Head Ξ.length}

def state (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)
    {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    (value : State operations profile ⟨Γ, sourceContext, type, carrier⟩) :
    State operations profile ⟨Ξ, targetContext, type.subst substitution.source, carrier⟩ where
  contextFormed := substitution.targetFormed
  term := value.term.subst substitution.source
  typed := value.typed.substitute substitution.typed
  code := HOL.subst substitution.target value.code
  reading := value.reading.substitute substitution.target substitution.source substitution.represented

theorem lifted_components (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)
    {domain type : HOL.Ty Base} (index : HOL.Var (domain :: Γ) type) :
    AnnotatedReads operations (Γ := domain :: Ξ)
      (CTm.liftSub substitution.source (variableIndex index)) (HOL.Subst.lift substitution.target index) := by
  cases index with
  | vz => exact .var .vz
  | vs prior => exact (substitution.represented prior).rename HOL.Rename.weaken wk (fun _ => rfl)

def instantiate (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)
    {row : Row} (inst : Instance operations profile row Γ sourceContext) :
    Instance operations profile row Ξ targetContext where
  contextFormed := substitution.targetFormed
  sourceSubstitution := fun index => (inst.sourceSubstitution index).subst substitution.source
  targetSubstitution := HOL.Subst.comp substitution.target inst.targetSubstitution
  typed := by
    intro index
    simpa only [CTm.subst_comp] using (inst.typed index).substitute substitution.typed
  represented := fun index => (inst.represented index).substitute
    substitution.target substitution.source substitution.represented

def beta (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)
    (inst : BetaInstance operations profile Γ sourceContext) :
    BetaInstance operations profile Ξ targetContext where
  contextFormed := substitution.targetFormed
  domain := inst.domain.subst substitution.source
  body := inst.body.subst (CTm.liftSub substitution.source)
  argument := inst.argument.subst substitution.source
  family := inst.family.subst (CTm.liftSub substitution.source)
  domainLevel := inst.domainLevel
  productLevel := inst.productLevel
  domainUniverse := inst.domainUniverse
  productUniverse := inst.productUniverse
  domainTyped := inst.domainTyped.substitute substitution.typed
  productTyped := inst.productTyped.substitute substitution.typed
  bodyTyped := inst.bodyTyped.substitute (substitution.typed.lift inst.domain)
  argumentTyped := inst.argumentTyped.substitute substitution.typed
  domainCarrier := inst.domainCarrier
  resultCarrier := inst.resultCarrier
  domainCode := HOL.subst substitution.target inst.domainCode
  bodyCode := HOL.subst (HOL.Subst.lift substitution.target) inst.bodyCode
  argumentCode := HOL.subst substitution.target inst.argumentCode
  domainReading := inst.domainReading.substitute substitution.target substitution.source substitution.represented
  bodyReading := inst.bodyReading.substitute (HOL.Subst.lift substitution.target)
    (CTm.liftSub substitution.source) substitution.lifted_components
  argumentReading := inst.argumentReading.substitute substitution.target substitution.source substitution.represented

end Substitution

section DisplayedType

variable {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    {firstType secondType : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}

/-- Transport only the displayed source type. The source term and HOL code
remain literal fields, rather than being hidden behind a whole-index cast. -/
def State.castType (same : firstType = secondType)
    (value : State operations profile ⟨Γ, context, firstType, carrier⟩) :
    State operations profile ⟨Γ, context, secondType, carrier⟩ where
  contextFormed := value.contextFormed
  term := value.term
  typed := same ▸ value.typed
  code := value.code
  reading := value.reading

def Step.castType {enabled : Programs.ComputationProfiles.Selection}
    (same : firstType = secondType)
    {source target : State operations profile ⟨Γ, context, firstType, carrier⟩}
    (step : Step operations profile enabled source target) :
    Step operations profile enabled (source.castType same) (target.castType same) := by
  cases same
  exact step

theorem Step.proof_castType {enabled : Programs.ComputationProfiles.Selection}
    (same : firstType = secondType)
    {source target : State operations profile ⟨Γ, context, firstType, carrier⟩}
    (step : Step operations profile enabled source target) :
    (step.castType same).proof = step.proof := by
  cases same
  rfl

end DisplayedType

def Step.castStates {enabled : Programs.ComputationProfiles.Selection} {index : Index Base}
    {source target source' target' : State operations profile index}
    (left : source = source') (right : target = target')
    (step : Step operations profile enabled source target) :
    Step operations profile enabled source' target' := left ▸ right ▸ step

theorem Step.proof_castStates_heq {enabled : Programs.ComputationProfiles.Selection} {index : Index Base}
    {source target source' target' : State operations profile index}
    (left : source = source') (right : target = target')
    (step : Step operations profile enabled source target) :
    HEq (step.castStates left right).proof step.proof := by
  cases left
  cases right
  rfl

namespace Substitution

variable [DecidableEq Base] {Γ Ξ : HOL.Ctx Base}
    {sourceContext : CCtx Tower.Head Γ.length} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)

omit [DecidableEq Base] in
theorem row_type {row : Row} (inst : Instance operations profile row Γ sourceContext) :
    (substitution.instantiate inst).index.sourceType = inst.index.sourceType.subst substitution.source :=
  (CTm.subst_comp substitution.source inst.sourceSubstitution (row.type operations)).symm

theorem row_source {row : Row} (inst : Instance operations profile row Γ sourceContext) :
    (substitution.instantiate inst).source.castType (substitution.row_type inst) =
      substitution.state inst.source := by
  apply State.ext
  exact (CTm.subst_comp substitution.source inst.sourceSubstitution (row.left operations)).symm

theorem row_target {row : Row} (inst : Instance operations profile row Γ sourceContext) :
    (substitution.instantiate inst).target.castType (substitution.row_type inst) =
      substitution.state inst.target := by
  apply State.ext
  exact (CTm.subst_comp substitution.source inst.sourceSubstitution (row.right operations)).symm

omit [DecidableEq Base] in
theorem beta_type (inst : BetaInstance operations profile Γ sourceContext) :
    (substitution.beta inst).index.sourceType = inst.index.sourceType.subst substitution.source :=
  (CTm.subst_inst0 substitution.source inst.argument inst.family).symm

theorem beta_source (inst : BetaInstance operations profile Γ sourceContext) :
    (substitution.beta inst).source.castType (substitution.beta_type inst) =
      substitution.state inst.source := by
  apply State.ext
  rfl

theorem beta_target (inst : BetaInstance operations profile Γ sourceContext) :
    (substitution.beta inst).target.castType (substitution.beta_type inst) =
      substitution.state inst.target := by
  apply State.ext
  exact (CTm.subst_inst0 substitution.source inst.argument inst.body).symm

def step {enabled : Programs.ComputationProfiles.Selection} {type : CTm Tower.Head Γ.length}
    {carrier : HOL.Ty Base} {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (original : Step operations profile enabled source target) :
    Step operations profile enabled (substitution.state source) (substitution.state target) := by
  cases original with
  | row inst inProfile permitted =>
      exact ((Step.row (substitution.instantiate inst) inProfile permitted).castType
        (substitution.row_type inst)).castStates (substitution.row_source inst) (substitution.row_target inst)
  | beta inst =>
      exact ((Step.beta (substitution.beta inst)).castType
        (substitution.beta_type inst)).castStates (substitution.beta_source inst) (substitution.beta_target inst)

/-- The actual typed caller supplies a fibre map of the constructed bubble. -/
def fibreMap (enabled : Programs.ComputationProfiles.Selection)
    (type : CTm Tower.Head Γ.length) (carrier : HOL.Ty Base) :
    BubbleReindexing.FibreMap (bubbles operations profile) enabled
      ⟨Γ, sourceContext, type, carrier⟩ ⟨Ξ, targetContext, type.subst substitution.source, carrier⟩ where
  state := substitution.state
  step := substitution.step

omit [DecidableEq Base] in
def proof {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (original : HOL.ProofSyntax Const (assumptions operations Γ) (.eq source.code target.code)) :
    HOL.ProofSyntax Const (assumptions operations Ξ)
      (.eq (substitution.state source).code (substitution.state target).code) :=
  HOL.ProofSyntax.castIndices (assumptions_substitute operations substitution.target) rfl
    (HOL.ProofSyntax.subst substitution.target original)

omit [DecidableEq Base] in
theorem row_proof_heq {row : Row} (inst : Instance operations profile row Γ sourceContext) :
    HEq (substitution.instantiate inst).proof (substitution.proof inst.proof) := by
  apply (HOL.ProofSyntax.castIndices_heq _ _ _).trans
  apply (HOL.ProofSyntax.subst_comp_heq (row.proof operations) substitution.target inst.targetSubstitution).trans
  refine HEq.trans ?_ (HOL.ProofSyntax.castIndices_heq _ _ _).symm
  exact (HOL.ProofSyntax.subst_heq_of_heq substitution.target
    (assumptions_substitute operations inst.targetSubstitution).symm rfl
    (HOL.ProofSyntax.castIndices_heq _ _ _)).symm

omit [DecidableEq Base] in
theorem beta_proof_heq (inst : BetaInstance operations profile Γ sourceContext) :
    HEq (substitution.beta inst).proof (substitution.proof inst.proof) := by
  refine HEq.trans ?_ (HOL.ProofSyntax.castIndices_heq _ _ _).symm
  dsimp only [BetaInstance.proof, beta, HOL.ProofSyntax.subst]
  refine HEq.trans ?_ (HOL.ProofSyntax.mpr_heq _ _).symm
  congr 1
  exact (assumptions_substitute operations substitution.target).symm

theorem step_proof {enabled : Programs.ComputationProfiles.Selection}
    {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (original : Step operations profile enabled source target) :
    (substitution.step original).proof = substitution.proof original.proof := by
  apply eq_of_heq
  cases original with
  | row inst inProfile permitted =>
      refine (Step.proof_castStates_heq (substitution.row_source inst) (substitution.row_target inst)
        ((Step.row (substitution.instantiate inst) inProfile permitted).castType
          (substitution.row_type inst))).trans ?_
      refine (heq_of_eq (Step.proof_castType (substitution.row_type inst)
        (Step.row (substitution.instantiate inst) inProfile permitted))).trans ?_
      exact substitution.row_proof_heq inst
  | beta inst =>
      refine (Step.proof_castStates_heq (substitution.beta_source inst) (substitution.beta_target inst)
        ((Step.beta (substitution.beta inst)).castType (substitution.beta_type inst))).trans ?_
      refine (heq_of_eq (Step.proof_castType (substitution.beta_type inst)
        (Step.beta (substitution.beta inst)))).trans ?_
      exact substitution.beta_proof_heq inst

end Substitution

section ProofIndices

variable {Γ : HOL.Ctx Base} {Δ Δ' : List (HOL.Formula Const Γ)}
    {carrier : HOL.Ty Base} {source middle target : HOL.Term Const Γ carrier}

private theorem cast_refl (same : Δ = Δ') (term : HOL.Term Const Γ carrier) :
    HOL.ProofSyntax.castIndices same rfl (HOL.ProofSyntax.eqRefl term) =
      (HOL.ProofSyntax.eqRefl term : HOL.ProofSyntax Const Δ' _) := by
  cases same
  rfl

private theorem cast_symm (same : Δ = Δ') (proof : HOL.ProofSyntax Const Δ (.eq source target)) :
    HOL.ProofSyntax.castIndices same rfl (.eqSymm proof) =
      .eqSymm (HOL.ProofSyntax.castIndices same rfl proof) := by
  cases same
  rfl

private theorem cast_trans (same : Δ = Δ')
    (first : HOL.ProofSyntax Const Δ (.eq source middle))
    (second : HOL.ProofSyntax Const Δ (.eq middle target)) :
    HOL.ProofSyntax.castIndices same rfl (.eqTrans first second) =
      .eqTrans (HOL.ProofSyntax.castIndices same rfl first) (HOL.ProofSyntax.castIndices same rfl second) := by
  cases same
  rfl

end ProofIndices

namespace Substitution

variable [DecidableEq Base] {Γ Ξ : HOL.Ctx Base}
    {sourceContext : CCtx Tower.Head Γ.length} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)

/-- The actual retained HOL substitution preserves all three equality-tree
operations. This is a receipt action, not a field assuming its naturality. -/
def receiptAction (enabled : Programs.ComputationProfiles.Selection)
    (type : CTm Tower.Head Γ.length) (carrier : HOL.Ty Base) :
    BubbleReindexing.ReceiptAction (holEquality operations profile)
      (substitution.fibreMap enabled type carrier) where
  map := substitution.proof
  map_refl source := by
    exact cast_refl (assumptions_substitute operations substitution.target) (HOL.subst substitution.target source.code)
  map_symm original := by
    exact cast_symm (assumptions_substitute operations substitution.target) (HOL.ProofSyntax.subst substitution.target original)
  map_trans first second := by
    exact cast_trans (assumptions_substitute operations substitution.target)
      (HOL.ProofSyntax.subst substitution.target first) (HOL.ProofSyntax.subst substitution.target second)

/-- Substituting the source trace and elaborating gives the same retained
proof as elaborating first and substituting that proof. -/
theorem elaborate_mapConv {enabled : Programs.ComputationProfiles.Selection}
    {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (path : (bubbles operations profile).Conv enabled source target) :
    elaborate ((substitution.fibreMap enabled type carrier).mapConv path) =
      substitution.proof (elaborate path) :=
  BubbleReindexing.sound_mapConv (substitution.fibreMap enabled type carrier)
    (substitution.receiptAction enabled type carrier) Step.proof substitution.step_proof path

theorem stepCount_mapConv {enabled : Programs.ComputationProfiles.Selection}
    {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (path : (bubbles operations profile).Conv enabled source target) :
    BubbleElaboration.stepCount ((substitution.fibreMap enabled type carrier).mapConv path) =
      BubbleElaboration.stepCount path :=
  (substitution.fibreMap enabled type carrier).stepCount_mapConv path

/-- Context movement and permission widening commute on the actual retained
HOL proof, using the separately constructed laws for each operation. -/
theorem elaborate_widen_mapConv {small large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, small row = true → large row = true)
    {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (path : (bubbles operations profile).Conv small source target) :
    elaborate ((substitution.fibreMap large type carrier).mapConv
      ((bubbles operations profile).widen (Step.widen included) path)) =
    elaborate ((bubbles operations profile).widen (Step.widen included)
      ((substitution.fibreMap small type carrier).mapConv path)) := by
  rw [substitution.elaborate_mapConv, elaborate_widen, elaborate_widen,
    substitution.elaborate_mapConv]

end Substitution

#print axioms Substitution.instantiate
#print axioms Substitution.beta
#print axioms Substitution.row_source
#print axioms Substitution.beta_target
#print axioms Substitution.fibreMap
#print axioms Substitution.step_proof
#print axioms Substitution.receiptAction
#print axioms Substitution.elaborate_mapConv
#print axioms Substitution.stepCount_mapConv
#print axioms Substitution.elaborate_widen_mapConv

end AnnotatedConversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
