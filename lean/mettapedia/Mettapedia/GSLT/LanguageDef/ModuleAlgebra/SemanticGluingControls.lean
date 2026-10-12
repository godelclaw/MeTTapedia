import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluing
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Composition

/-!
# Semantic module gluing controls

The semantic fixture has genuine context-dependent carriers: a value is a
Boolean function of the typed var valuation. Substitution composes
valuations. Two private constants can vary independently over the same
var carrier. The fixed Boolean interpretation of zero and one is an
explicit admitted scope; unrestricted equation models can collapse them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls

open Mettapedia.OSLF.Binding
open Mettapedia.Logic.TheoryModel
open SemanticGluing

inductive Op where
  | zero | one | first | second
  deriving DecidableEq

def signature : Signature where
  Srt := Unit
  Op _ := Op
  arity _ := []

abbrev Valuation (Γ : Ctx signature) := (sort : Unit) → Var Γ sort → Bool

/-- The ordinary valuation model, including all typed contexts. -/
def substitution : BindingSubstitutionAlgebra.Algebra signature where
  Carrier Γ _ := Valuation Γ → Bool
  injectVar var := fun valuation => valuation _ var
  substitute env value := fun valuation => value (fun sort var => env sort var valuation)
  substitute_var := by intro Γ Δ env sort x; rfl
  substitute_identity _ := rfl
  substitute_comp _ _ _ := rfl

def constant (first second : Bool) : Op → Bool
  | .zero => false
  | .one => true
  | .first => first
  | .second => second

/-- Private operators have independent values; the var and parameter
carriers are shared. -/
def pointAlgebra (first second : Bool) : BindingCloneAlgebra.Algebra signature where
  substitution := substitution
  operation op _ := fun _ => constant first second op
  operation_substitute _ _ _ := rfl

def schema (spec : Op × Op) : EqAxiom signature [] where
  ctx := []
  sort := ()
  lhs := .op (.inl spec.1) .nil
  rhs := .op (.inl spec.2) .nil

private def noVariables {sort : Unit} (var : Var ([] : Ctx signature) sort) : Bool :=
  nomatch var

theorem point_satisfies_iff (first second : Bool) (spec : Op × Op) :
    equationSat schema (pointAlgebra first second) spec ↔
      constant first second spec.1 = constant first second spec.2 := by
  constructor
  · intro satisfies
    have equal := satisfies 0 (Γ := []) (Δ := [])
      (fun index => index.elim0) (fun _ var => nomatch var)
      (fun _ var => nomatch var)
    exact congrFun equal (fun _ var => noVariables var)
  · intro equal index Γ Δ body ambient ordinary
    have zero : index = 0 := Fin.eq_zero index
    subst index
    exact congrArg (fun value : Bool => fun _ : Valuation Δ => value) equal

abbrev P := Presentation Nat String (Op × Op)

def parameter : Entry Nat String (Op × Op) := ⟨0, "Parameter", (.zero, .zero)⟩
def ownFirst : Entry Nat String (Op × Op) := ⟨1, "First", (.first, .zero)⟩
def ownSecond : Entry Nat String (Op × Op) := ⟨2, "Second", (.second, .one)⟩
def oppositeFirst : Entry Nat String (Op × Op) := ⟨3, "Other", (.first, .one)⟩

def shared : P := ⟨{parameter}, by decide⟩
def left : P := ⟨{parameter, ownFirst}, by decide⟩
def right : P := ⟨{parameter, ownSecond}, by decide⟩
def whole : P := ⟨{parameter, ownFirst, ownSecond}, by decide⟩
def conflicting : P := ⟨{parameter, oppositeFirst}, by decide⟩
def inconsistent : P := ⟨{parameter, ownFirst, oppositeFirst}, by decide⟩

theorem private_instances_join : join left right = some whole := by
  apply join_eq_some_iff.mpr
  decide

theorem declarations_join_despite_conflicting_constraints :
    join left conflicting = some inconsistent := by
  apply join_eq_some_iff.mpr
  decide

theorem point_left_iff (first second : Bool) :
    BindingEquationInterpretation.Satisfies (pointAlgebra first second) (equations schema left) ↔
      first = false := by
  rw [satisfies_iff_models]
  simp only [models, bodyTheory, left, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro satisfies
    exact (point_satisfies_iff first second _).mp (satisfies ⟨ownFirst, Or.inr rfl, rfl⟩)
  · intro equal spec member
    obtain ⟨entry, member, rfl⟩ := member
    rcases member with rfl | rfl
    · exact (point_satisfies_iff first second _).mpr rfl
    · exact (point_satisfies_iff first second _).mpr equal

theorem point_right_iff (first second : Bool) :
    BindingEquationInterpretation.Satisfies (pointAlgebra first second) (equations schema right) ↔
      second = true := by
  rw [satisfies_iff_models]
  simp only [models, bodyTheory, right, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro satisfies
    exact (point_satisfies_iff first second _).mp (satisfies ⟨ownSecond, Or.inr rfl, rfl⟩)
  · intro equal spec member
    obtain ⟨entry, member, rfl⟩ := member
    rcases member with rfl | rfl
    · exact (point_satisfies_iff first second _).mpr rfl
    · exact (point_satisfies_iff first second _).mpr equal

theorem point_conflicting_iff (first second : Bool) :
    BindingEquationInterpretation.Satisfies (pointAlgebra first second)
      (equations schema conflicting) ↔ first = true := by
  rw [satisfies_iff_models]
  simp only [models, bodyTheory, conflicting, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro satisfies
    exact (point_satisfies_iff first second _).mp
      (satisfies ⟨oppositeFirst, Or.inr rfl, rfl⟩)
  · intro equal spec member
    obtain ⟨entry, member, rfl⟩ := member
    rcases member with rfl | rfl
    · exact (point_satisfies_iff first second _).mpr rfl
    · exact (point_satisfies_iff first second _).mpr equal

/-- A model of the two instances keeps distinct private values. -/
def independentModel : Model schema whole where
  algebra := pointAlgebra false true
  satisfies := (satisfies_join schema _ private_instances_join).mpr
    ⟨(point_left_iff _ _).mpr rfl, (point_right_iff _ _).mpr rfl⟩

theorem private_values_remain_distinct :
    independentModel.algebra.operation .first (Γ := []) (s := ()) .nil ≠
      independentModel.algebra.operation .second (Γ := []) (s := ()) .nil := by
  intro equal
  exact Bool.false_ne_true (congrFun equal (fun _ var => noVariables var))

theorem shared_parameter_reducts_agree :
    restrict schema (show shared.val ⊆ left.val by decide)
        (splitModel schema private_instances_join independentModel).val.1 =
      restrict schema (show shared.val ⊆ right.val by decide)
        (splitModel schema private_instances_join independentModel).val.2 := model_ext rfl

theorem let_shared_instance_once : join left left = some left ∧ left.val.card = 2 :=
  ⟨join_self left, by decide⟩

theorem fresh_declarations_are_distinct : ownFirst.origin ≠ ownSecond.origin ∧
    whole.val.card = 3 := by decide

/-- The join has no model in the stated Boolean scope. This makes no claim
that all unrestricted equation models are inconsistent. -/
theorem no_admitted_join_model (first second : Bool) :
    ¬ BindingEquationInterpretation.Satisfies (pointAlgebra first second)
      (equations schema inconsistent) := by
  intro satisfies
  obtain ⟨onLeft, onRight⟩ :=
    (satisfies_join schema _ declarations_join_despite_conflicting_constraints).mp satisfies
  have zero := (point_left_iff _ _).mp onLeft
  have one := (point_conflicting_iff _ _).mp onRight
  exact Bool.false_ne_true (zero.symm.trans one)

/-- The free quotient is an unrestricted model even for these equations;
the Boolean-scope counterexample cannot be advertised without its scope. -/
theorem unrestricted_join_model_exists : Nonempty (Model.{0} schema inconsistent) :=
  equation_model_exists schema inconsistent

def admittedSat (value : Bool) (spec : Op × Op) : Prop :=
  equationSat schema (pointAlgebra value false) spec

def coarse (_ : Bool) : Bool := false

/-- The local scopes each have a model and the same coarse observation. -/
theorem coarse_local_models_agree :
    false ∈ coarse '' models admittedSat (bodyTheory left) ∧
      false ∈ coarse '' models admittedSat (bodyTheory conflicting) := by
  refine ⟨⟨false, ?_, rfl⟩, ⟨true, ?_, rfl⟩⟩
  · exact (satisfies_iff_models schema _ left).mp ((point_left_iff _ _).mpr rfl)
  · exact (satisfies_iff_models schema _ conflicting).mp
      ((point_conflicting_iff _ _).mpr rfl)

theorem coarse_agreement_does_not_glue :
    coarse '' models admittedSat (bodyTheory inconsistent) ≠
      (coarse '' models admittedSat (bodyTheory left)) ∩
        (coarse '' models admittedSat (bodyTheory conflicting)) := by
  intro equal
  have member : false ∈ (coarse '' models admittedSat (bodyTheory left)) ∩
      (coarse '' models admittedSat (bodyTheory conflicting)) := coarse_local_models_agree
  rw [← equal] at member
  obtain ⟨value, member, _⟩ := member
  exact no_admitted_join_model value false ((satisfies_iff_models schema _ inconsistent).mpr member)

/-- The forgotten constraint is not observable through the coarse view. -/
theorem conflicting_constraint_not_visible :
    ¬ bodyTheory conflicting ⊆
      observable admittedSat (Setoid.ker coarse) := by
  intro visible
  have same : (Setoid.ker coarse).r true false := rfl
  have observable := visible (show oppositeFirst.body ∈ bodyTheory conflicting from
    ⟨oppositeFirst, by decide, rfl⟩)
  have truth := (point_satisfies_iff true false oppositeFirst.body).mpr rfl
  have untruth := (observable same).mp truth
  have impossible := (point_satisfies_iff false false _).mp untruth
  exact Bool.false_ne_true impossible

/-- Substitution acts on vars, and does not erase an independent private constant. -/
theorem substitution_has_content :
    substitution.substitute
        (fun _ _ => fun _ => true)
        (substitution.injectVar (.zero : Var [()] ())) =
      (fun _ : Valuation [] => true) ∧
    (pointAlgebra false true).operation .first (Γ := []) (s := ()) .nil ≠
      (fun _ : Valuation [] => true) := by
  refine ⟨rfl, ?_⟩
  intro equal
  exact Bool.false_ne_true (congrFun equal (fun _ var => noVariables var))

/-- Exchange the two independent private operators. -/
def swapOp : Op → Op
  | .zero => .zero
  | .one => .one
  | .first => .second
  | .second => .first

def swapAlgebra (algebra : BindingCloneAlgebra.Algebra signature) :
    BindingCloneAlgebra.Algebra signature where
  substitution := algebra.substitution
  operation op args := algebra.operation (swapOp op) args
  operation_substitute env op args := algebra.operation_substitute env (swapOp op) args

theorem swapAlgebra_involutive (algebra : BindingCloneAlgebra.Algebra signature) :
    swapAlgebra (swapAlgebra algebra) = algebra := by
  cases algebra with
  | mk sub operation law =>
    have equal :
        (fun {Γ} {sort} (op : signature.Op sort)
          (args : FreeBindingTerms.FamilyArgs signature sub.Carrier (signature.arity op) Γ) =>
            operation (swapOp (swapOp op)) args) = @operation := by
      funext Γ sort op args
      cases op <;> rfl
    simp only [swapAlgebra]
    congr 1

def sharedModel (algebra : BindingCloneAlgebra.Algebra signature) : Model schema shared where
  algebra := algebra
  satisfies := by
    apply (satisfies_iff_models schema algebra shared).mpr
    intro spec member
    obtain ⟨entry, member, rfl⟩ := member
    have equal : entry = parameter := Finset.mem_singleton.mp member
    subst entry
    intro index Γ Δ body ambient ordinary
    have zero : index = 0 := Fin.eq_zero index
    subst index
    rfl

/-- A nontrivial equivalence of actual module models, changing their private
operator meanings while retaining all substitution and parameter structure. -/
def swapModel : Model schema shared ≃ Model schema shared where
  toFun model := sharedModel (swapAlgebra model.algebra)
  invFun model := sharedModel (swapAlgebra model.algebra)
  left_inv model := model_ext (swapAlgebra_involutive model.algebra)
  right_inv model := model_ext (swapAlgebra_involutive model.algebra)

open Mettapedia.GSLT.Scope.Twisted

def cycleCoordinate {i j : Vertex} : CycleEdge i j →
    Model schema shared ≃ Model schema shared
  | .ab => Equiv.refl _
  | .bc => Equiv.refl _
  | .ca => swapModel

def modelCycle := modelViewSystem.{0} (fun _ : Vertex => shared) schema CycleEdge cycleCoordinate

def cycle : modelCycle.Walk Vertex.a Vertex.a :=
  .forward CycleEdge.ab (.forward CycleEdge.bc (.forward CycleEdge.ca (.nil Vertex.a)))

/-- Traversing the cycle exchanges two unequal private meanings. -/
theorem nontrivial_model_holonomy : ¬ modelCycle.TrivialHolonomy := by
  intro trivial
  have fixed := trivial cycle (sharedModel (pointAlgebra false true))
  have equal := congrArg (fun model : Model.{0} schema shared => model.algebra) fixed
  change swapAlgebra (pointAlgebra false true) = pointAlgebra false true at equal
  injection equal with _ operations
  have same := operations
  have value := congrFun (congrFun (congrFun (congrFun same []) ()) Op.first) .nil
  exact Bool.false_ne_true (congrFun value (fun _ var => noVariables var)).symm

theorem model_cycle_has_no_global_charts : ¬ Nonempty modelCycle.Gluing := by
  rintro ⟨gluing⟩
  exact nontrivial_model_holonomy gluing.trivialHolonomy

theorem equal_private_values_are_fixed :
    swapModel (sharedModel (pointAlgebra false false)) =
      sharedModel (pointAlgebra false false) := by
  apply model_ext
  change swapAlgebra (pointAlgebra false false) = pointAlgebra false false
  have equal :
      (fun {Γ : Ctx signature} {sort : signature.Srt} (op : signature.Op sort)
        (_ : FreeBindingTerms.FamilyArgs signature substitution.Carrier (signature.arity op) Γ) =>
        fun _ : Valuation Γ => constant false false (swapOp op)) =
      (fun {Γ : Ctx signature} {sort : signature.Srt} (op : signature.Op sort)
        (_ : FreeBindingTerms.FamilyArgs signature substitution.Carrier (signature.arity op) Γ) =>
        fun _ : Valuation Γ => constant false false op) := by
    funext Γ sort op args valuation
    cases op <;> rfl
  simp only [swapAlgebra, pointAlgebra]
  congr 1

/-- A compatible model family can exist although global chart gluing fails. -/
def fixedModelSection : modelCycle.Sections :=
  ⟨fun _ => sharedModel (pointAlgebra false false), fun edge => by
    cases edge
    · rfl
    · rfl
    · exact equal_private_values_are_fixed⟩

theorem section_exists_without_global_charts :
    Nonempty modelCycle.Sections ∧ ¬ Nonempty modelCycle.Gluing :=
  ⟨⟨fixedModelSection⟩, model_cycle_has_no_global_charts⟩

def untwistedCoordinate {i j : Vertex} : CycleEdge i j →
    Model schema shared ≃ Model schema shared
  | .ab => swapModel
  | .bc => Equiv.refl _
  | .ca => swapModel

/-- Two nontrivial changes of coordinates cancel around the cycle. -/
def untwistedModelCycle :=
  modelViewSystem.{0} (fun _ : Vertex => shared) schema CycleEdge untwistedCoordinate

def untwistedModelGluing : untwistedModelCycle.Gluing where
  Global := Model.{0} schema shared
  chart
    | .a => Equiv.refl _
    | .b => swapModel
    | .c => swapModel
  compatible := by
    intro i j edge model
    cases edge
    · rfl
    · rfl
    · exact swapModel.left_inv model

theorem nontrivial_coordinates_can_glue :
    Nonempty untwistedModelCycle.Gluing ∧ untwistedModelCycle.TrivialHolonomy :=
  ⟨⟨untwistedModelGluing⟩, untwistedModelGluing.trivialHolonomy⟩

/-- Independently chosen local private meanings extend to one actual model
without changing either selected operator interpretation. -/
theorem independent_private_extensions (first second : Bool)
    (onLeft : first = false) (onRight : second = true) :
    ∃ model : Model schema whole,
      model.algebra = pointAlgebra first second ∧
      HEq (model.algebra.operation .first (Γ := []) (s := ()) .nil)
        ((pointAlgebra first false).operation .first (Γ := []) (s := ()) .nil) ∧
      HEq (model.algebra.operation .second (Γ := []) (s := ()) .nil)
        ((pointAlgebra false second).operation .second (Γ := []) (s := ()) .nil) := by
  exact ⟨⟨pointAlgebra first second,
    (satisfies_join schema _ private_instances_join).mpr
      ⟨(point_left_iff _ _).mpr onLeft, (point_right_iff _ _).mpr onRight⟩⟩,
    rfl, HEq.rfl, HEq.rfl⟩

/-- Retaining the complete model makes every equation constraint visible. -/
theorem exact_model_observation_glues :
    (id : BindingCloneAlgebra.Algebra.{0} signature → _) ''
        models (equationSat schema) (bodyTheory whole) =
      (id '' models (equationSat schema) (bodyTheory left)) ∩
        (id '' models (equationSat schema) (bodyTheory right)) := by
  apply observed_models_join schema private_instances_join id
  intro spec _ first second same
  change first = second at same
  subst second
  rfl

/-- Future-word observation also glues when it retains the model already
at the empty word; the established future observer is used without a new
behaviour representation. -/
theorem future_model_observation_glues :
    Mettapedia.GSLT.PrivilegedView.wordBehaviour
        (fun (algebra : BindingCloneAlgebra.Algebra.{0} signature) (_ : Unit) => swapAlgebra algebra)
        id '' models (equationSat schema) (bodyTheory whole) =
      (Mettapedia.GSLT.PrivilegedView.wordBehaviour
        (fun (algebra : BindingCloneAlgebra.Algebra.{0} signature) (_ : Unit) => swapAlgebra algebra)
        id '' models (equationSat schema) (bodyTheory left)) ∩
      (Mettapedia.GSLT.PrivilegedView.wordBehaviour
        (fun (algebra : BindingCloneAlgebra.Algebra.{0} signature) (_ : Unit) => swapAlgebra algebra)
        id '' models (equationSat schema) (bodyTheory right)) := by
  apply future_observed_models_join schema private_instances_join _ id
  intro spec _ first second same
  have equal : first = second := congrFun same []
  subst second
  rfl

/-- A current readout can agree while a future input distinguishes the values. -/
theorem current_readout_does_not_determine_future :
    Mettapedia.GSLT.PrivilegedView.Signal.light .idle =
      Mettapedia.GSLT.PrivilegedView.Signal.light .primed ∧
      Mettapedia.GSLT.PrivilegedView.wordBehaviour
        (fun signal (_ : Unit) => Mettapedia.GSLT.PrivilegedView.Signal.step signal)
        Mettapedia.GSLT.PrivilegedView.Signal.light .idle ≠
      Mettapedia.GSLT.PrivilegedView.wordBehaviour
        (fun signal (_ : Unit) => Mettapedia.GSLT.PrivilegedView.Signal.step signal)
        Mettapedia.GSLT.PrivilegedView.Signal.light .primed := by
  refine ⟨rfl, ?_⟩
  intro equal
  exact Bool.false_ne_true (congrFun equal [()])

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls

-- Existing semantic/runtime controls are imported rather than reconstructed.
#check Mettapedia.GSLT.LanguageDef.ScopePolicies.join_not_conservative
#check Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls.generative_rig_join
#check Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls.compatible_join_not_conservative
#check Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls.join_has_mixed_path
