import Mettapedia.CategoryTheory.RelativeClosedCartesianActionPresentation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperations
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Independent weighted-action models and complete diagram admission

The action shifts both endpoints while retaining its supplied evidence
weight. A second operation has the same endpoint behavior but increments
that weight at every application, so it fails both whole-edge diagrams.
The operations are independent meanings of a small authored signature;
the actual generated action presentation admits and rejects the respective
models from computed complete arrow readouts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.CartesianMonoidAction.Controls

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory Interpretation

abbrev Evidence := Nat × Nat × Nat

def shift (increments : Bool) : Evidence ⊗ Nat ⟶ Evidence := TypeCat.ofHom (fun supplied =>
  (supplied.1.1 + supplied.2, supplied.1.2.1 + supplied.2,
    supplied.1.2.2 + if increments then 1 else 0))

abbrev arithmetic (increments : Bool) : Data Type where
  edge := Evidence
  scalar := Nat
  zero := TypeCat.ofHom (fun _ => 0)
  merge := TypeCat.ofHom (fun supplied => supplied.1 + supplied.2)
  act := shift increments

theorem arithmetic_scalar_laws (increments : Bool) : ScalarLaws (arithmetic increments) where
  unit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext scalar
    exact Nat.add_zero scalar
  associativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    exact Nat.add_assoc supplied.1.1 supplied.1.2 supplied.2
  commutativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    exact Nat.add_comm supplied.1 supplied.2

theorem retained_action_laws : Laws (arithmetic false) where
  unit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    change (supplied.1 + 0, supplied.2.1 + 0, supplied.2.2 + 0) = supplied
    simp only [Nat.add_zero, Prod.eta]
  associativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext supplied
    change ((supplied.1.1.1 + supplied.1.2) + supplied.2,
      (supplied.1.1.2.1 + supplied.1.2) + supplied.2,
      (supplied.1.1.2.2 + 0) + 0) =
        (supplied.1.1.1 + (supplied.1.2 + supplied.2),
          supplied.1.1.2.1 + (supplied.1.2 + supplied.2), supplied.1.1.2.2 + 0)
    simp only [Nat.add_assoc, Nat.add_zero]

def source : Evidence ⟶ Nat := TypeCat.ofHom Prod.fst
def target : Evidence ⟶ Nat := TypeCat.ofHom (fun supplied => supplied.2.1)

theorem same_complete_endpoints (increments : Bool) :
    shift increments ≫ source = lift (fst _ _ ≫ source) (snd _ _) ≫ (arithmetic increments).merge ∧
      shift increments ≫ target = lift (fst _ _ ≫ target) (snd _ _) ≫ (arithmetic increments).merge := by
  constructor <;> apply TypeCat.Hom.ext <;> apply TypeCat.Fun.ext <;> funext supplied <;> rfl

theorem incrementing_action_rejected : ¬ Laws (arithmetic true) := by
  intro laws
  have value := congrArg (fun arrow : Evidence ⟶ Evidence => arrow (2, 5, 7)) laws.unit
  have impossible := congrArg (fun supplied : Evidence => supplied.2.2) value
  change (8 : Nat) = 7 at impossible
  exact (by decide : (8 : Nat) ≠ 7) impossible

theorem incrementing_associativity_fails : twiceDiagram (arithmetic true) ≠ mergedDiagram (arithmetic true) := by
  intro same
  have value := congrArg (fun arrow : (Evidence ⊗ Nat) ⊗ Nat ⟶ Evidence => arrow (((2, 5, 7), 3), 4)) same
  have impossible := congrArg (fun supplied : Evidence => supplied.2.2) value
  change (9 : Nat) = 8 at impossible
  exact (by decide : (9 : Nat) ≠ 8) impossible

theorem complete_retained_readout (first second weight frame : Nat) :
    shift false ((first, second, weight), frame) = (first + frame, second + frame, weight) := by
  change (first + frame, second + frame, weight + 0) = _
  rw [Nat.add_zero]

theorem nonidentity_frame : shift false (((2, 5, 7) : Evidence), 3) ≠ (2, 5, 7) := by
  intro same
  have impossible := congrArg Prod.fst same
  exact (by decide : (5 : Nat) ≠ 2) impossible

theorem no_endpoint_evidence_decoder :
    ¬ ∃ decode : Nat × Nat → Nat, ∀ edge : Evidence, decode (source edge, target edge) = edge.2.2 := by
  rintro ⟨decode, read⟩
  exact (by decide : (7 : Nat) ≠ 9) ((read (2, 5, 7)).symm.trans (read (2, 5, 9)))

abbrev Base := Discrete Empty

inductive ObjectName where
  | edge
  | scalar

inductive Primitive where
  | zero
  | merge
  | act

abbrev symbols : Symbols where
  ObjectName := ObjectName
  ArrowName := Primitive
  EquationName := Empty

abbrev signature : Signature (C := Base) (symbols := symbols) where
  objectRank _ := 0
  arrowRank _ := 1
  source
    | .zero => .terminal
    | .merge => .product (.name .scalar) (.name .scalar)
    | .act => .product (.name .edge) (.name .scalar)
  target
    | .zero | .merge => .name .scalar
    | .act => .name .edge
  source_before origin := by cases origin <;> simp only [ObjectCode.before] <;> decide
  target_before origin := by cases origin <;> change (0 : Nat) < 1 <;> decide
  equationRank := Empty.elim
  equationSource := Empty.elim
  equationTarget := Empty.elim
  left := Empty.elim
  right := Empty.elim
  equation_before origin := nomatch origin

abbrev edge : Object signature :=
  ⟨.name ObjectName.edge, ⟨.objectName (signature := signature) ObjectName.edge⟩⟩
abbrev scalar : Object signature :=
  ⟨.name ObjectName.scalar, ⟨.objectName (signature := signature) ObjectName.scalar⟩⟩

def rawZero : RawHom (terminal signature) scalar :=
  ⟨.name Primitive.zero, ⟨.arrowName (signature := signature) Primitive.zero
    .terminalObject (.objectName (signature := signature) ObjectName.scalar)⟩⟩
def rawMerge : RawHom (GeneratedCategory.product scalar scalar) scalar :=
  ⟨.name Primitive.merge, ⟨.arrowName (signature := signature) Primitive.merge
    (.productObject (.objectName (signature := signature) ObjectName.scalar)
      (.objectName (signature := signature) ObjectName.scalar))
    (.objectName (signature := signature) ObjectName.scalar)⟩⟩
def rawAction : RawHom (GeneratedCategory.product edge scalar) edge :=
  ⟨.name Primitive.act, ⟨.arrowName (signature := signature) Primitive.act
    (.productObject (.objectName (signature := signature) ObjectName.edge)
      (.objectName (signature := signature) ObjectName.scalar))
    (.objectName (signature := signature) ObjectName.edge)⟩⟩

abbrev generated : Data (Object signature) :=
  ⟨edge, scalar, classOf rawZero, classOf rawMerge, classOf rawAction⟩

def rawUnit : RawHom edge edge :=
  (RawHom.pair (RawHom.identity edge) ((RawHom.toTerminal edge).compose rawZero)).compose rawAction

def stage : Object signature := GeneratedCategory.product (GeneratedCategory.product edge scalar) scalar
def rawEdge : RawHom stage edge := (RawHom.first (GeneratedCategory.product edge scalar) scalar).compose (RawHom.first edge scalar)
def rawFirst : RawHom stage scalar := (RawHom.first (GeneratedCategory.product edge scalar) scalar).compose (RawHom.second edge scalar)
def rawSecond : RawHom stage scalar := RawHom.second (GeneratedCategory.product edge scalar) scalar

def rawTwice : RawHom stage edge :=
  (RawHom.pair ((RawHom.pair rawEdge rawFirst).compose rawAction) rawSecond).compose rawAction
def rawMerged : RawHom stage edge :=
  (RawHom.pair rawEdge ((RawHom.pair rawFirst rawSecond).compose rawMerge)).compose rawAction

theorem raw_unit_read : classOf rawUnit = unitDiagram generated := rfl
theorem raw_twice_read : classOf rawTwice = twiceDiagram generated := rfl
theorem raw_merged_read : classOf rawMerged = mergedDiagram generated := rfl

def meanings (increments : Bool) : Assignment Base symbols Type where
  base := Discrete.functor Empty.elim
  object
    | .edge => Evidence
    | .scalar => Nat
  arrow
    | .zero => ⟨PUnit, Nat, (arithmetic increments).zero⟩
    | .merge => ⟨Nat ⊗ Nat, Nat, (arithmetic increments).merge⟩
    | .act => ⟨Evidence ⊗ Nat, Evidence, shift increments⟩

theorem realized (increments : Bool) : Realization signature (meanings increments) where
  source origin := by cases origin <;> rfl
  target origin := by cases origin <;> rfl
  equation origin := nomatch origin

abbrev evaluate (increments : Bool) := Interpretation.functor (meanings increments) (realized increments)

theorem read_edge_object (increments : Bool) :
    (meanings increments).evaluateObject edge.code = some Evidence := rfl

theorem read_scalar_object (increments : Bool) :
    (meanings increments).evaluateObject scalar.code = some Nat := rfl

theorem read_unit (increments : Bool) : (meanings increments).evaluateArrow rawUnit.code =
    some (⟨Evidence, Evidence, unitDiagram (arithmetic increments)⟩ : ArrowValue Type) := by
  exact (meanings increments).evaluate_compose _ _
    ((meanings increments).evaluate_pair _ _
      ((meanings increments).evaluate_identity (read_edge_object increments))
      ((meanings increments).evaluate_compose _ _
        ((meanings increments).evaluate_terminal_arrow rfl) rfl)) rfl

theorem read_twice (increments : Bool) : (meanings increments).evaluateArrow rawTwice.code =
    some (⟨(Evidence ⊗ Nat) ⊗ Nat, Evidence, twiceDiagram (arithmetic increments)⟩ : ArrowValue Type) := by
  have firstRead := (meanings increments).evaluate_first
    ((meanings increments).evaluate_product (read_edge_object increments) (read_scalar_object increments))
      (read_scalar_object increments)
  have edgeRead := (meanings increments).evaluate_compose _ _ firstRead
    ((meanings increments).evaluate_first (read_edge_object increments) (read_scalar_object increments))
  have scalarRead := (meanings increments).evaluate_compose _ _ firstRead
    ((meanings increments).evaluate_second (read_edge_object increments) (read_scalar_object increments))
  exact (meanings increments).evaluate_compose _ _
    ((meanings increments).evaluate_pair _ _
      ((meanings increments).evaluate_compose _ _
        ((meanings increments).evaluate_pair _ _ edgeRead scalarRead) rfl)
      ((meanings increments).evaluate_second
        ((meanings increments).evaluate_product (read_edge_object increments) (read_scalar_object increments))
        (read_scalar_object increments))) rfl

theorem read_merged (increments : Bool) : (meanings increments).evaluateArrow rawMerged.code =
    some (⟨(Evidence ⊗ Nat) ⊗ Nat, Evidence, mergedDiagram (arithmetic increments)⟩ : ArrowValue Type) := by
  have firstRead := (meanings increments).evaluate_first
    ((meanings increments).evaluate_product (read_edge_object increments) (read_scalar_object increments))
      (read_scalar_object increments)
  have edgeRead := (meanings increments).evaluate_compose _ _ firstRead
    ((meanings increments).evaluate_first (read_edge_object increments) (read_scalar_object increments))
  have scalarRead := (meanings increments).evaluate_compose _ _ firstRead
    ((meanings increments).evaluate_second (read_edge_object increments) (read_scalar_object increments))
  exact (meanings increments).evaluate_compose _ _
    ((meanings increments).evaluate_pair _ _ edgeRead
      ((meanings increments).evaluate_compose _ _
        ((meanings increments).evaluate_pair _ _ scalarRead
          ((meanings increments).evaluate_second
            ((meanings increments).evaluate_product (read_edge_object increments) (read_scalar_object increments))
            (read_scalar_object increments))) rfl)) rfl

theorem complete_unit (increments : Bool) :
    (⟨(evaluate increments).obj edge, (evaluate increments).obj edge,
      (evaluate increments).map (classOf rawUnit)⟩ : ArrowValue Type) =
        ⟨Evidence, Evidence, unitDiagram (arithmetic increments)⟩ :=
  Option.some.inj ((functor_complete_readout (meanings increments) (realized increments) rawUnit).symm.trans
    (read_unit increments))

theorem complete_identity (increments : Bool) :
    (⟨(evaluate increments).obj edge, (evaluate increments).obj edge,
      (evaluate increments).map (𝟙 edge)⟩ : ArrowValue Type) = ⟨Evidence, Evidence, 𝟙 Evidence⟩ :=
  Option.some.inj ((functor_complete_readout (meanings increments) (realized increments)
    (RawHom.identity edge)).symm.trans ((meanings increments).evaluate_identity (read_edge_object increments)))

theorem complete_twice (increments : Bool) :
    (⟨(evaluate increments).obj stage, (evaluate increments).obj edge,
      (evaluate increments).map (classOf rawTwice)⟩ : ArrowValue Type) =
        ⟨(Evidence ⊗ Nat) ⊗ Nat, Evidence, twiceDiagram (arithmetic increments)⟩ :=
  Option.some.inj ((functor_complete_readout (meanings increments) (realized increments) rawTwice).symm.trans
    (read_twice increments))

theorem complete_merged (increments : Bool) :
    (⟨(evaluate increments).obj stage, (evaluate increments).obj edge,
      (evaluate increments).map (classOf rawMerged)⟩ : ArrowValue Type) =
        ⟨(Evidence ⊗ Nat) ⊗ Nat, Evidence, mergedDiagram (arithmetic increments)⟩ :=
  Option.some.inj ((functor_complete_readout (meanings increments) (realized increments) rawMerged).symm.trans
    (read_merged increments))

theorem positive_local_satisfaction : EquationExtension.Satisfies signature
    (CartesianActionPresentation.declaration signature generated) (meanings false) (realized false) := by
  rintro ⟨origin⟩
  cases origin with
  | unit =>
      have equality := (complete_unit false).trans
        ((congrArg (fun arrow : Evidence ⟶ Evidence => (⟨Evidence, Evidence, arrow⟩ : ArrowValue Type))
          retained_action_laws.unit).trans (complete_identity false).symm)
      have whole := ArrowValue.arrow_injective equality
      simpa only [CartesianActionPresentation.declaration, classOf_representative, classOf_identity,
        ← raw_unit_read] using whole
  | associativity =>
      have equality := (complete_twice false).trans
        ((congrArg (fun arrow : (Evidence ⊗ Nat) ⊗ Nat ⟶ Evidence =>
          (⟨(Evidence ⊗ Nat) ⊗ Nat, Evidence, arrow⟩ : ArrowValue Type))
          retained_action_laws.associativity).trans (complete_merged false).symm)
      have whole := ArrowValue.arrow_injective equality
      simpa only [CartesianActionPresentation.declaration, classOf_representative,
        ← raw_twice_read, ← raw_merged_read] using whole

theorem positive_model_admitted : Realization (CartesianActionPresentation.extended signature generated)
    (EquationExtension.extendAssignment (Index := ULift.{0} CartesianActionPresentation.Law) (meanings false)) :=
  EquationExtension.extended_realization signature
    (CartesianActionPresentation.declaration signature generated) (meanings false) (realized false)
      positive_local_satisfaction

theorem positive_interpreted_action : Laws
    (CartesianActionPresentation.modelOperations signature generated (meanings false) (realized false)) :=
  (CartesianActionPresentation.satisfaction_iff_action signature generated (meanings false) (realized false)).mp
    positive_local_satisfaction

theorem incrementing_original_model_rejects_unit :
    (evaluate true).map (classOf rawUnit) ≠ (evaluate true).map (𝟙 edge) := by
  intro same
  have complete := congrArg (fun arrow : (evaluate true).obj edge ⟶ (evaluate true).obj edge =>
    (⟨(evaluate true).obj edge, (evaluate true).obj edge, arrow⟩ : ArrowValue Type)) same
  have interpreted := ArrowValue.arrow_injective
    ((complete_unit true).symm.trans (complete.trans (complete_identity true)))
  have value := congrArg (fun arrow : Evidence ⟶ Evidence => arrow (2, 5, 7)) interpreted
  have impossible := congrArg (fun supplied : Evidence => supplied.2.2) value
  change (8 : Nat) = 7 at impossible
  exact (by decide : (8 : Nat) ≠ 7) impossible

theorem negative_model_not_admitted : ¬ Realization (CartesianActionPresentation.extended signature generated)
    (EquationExtension.extendAssignment (Index := ULift.{0} CartesianActionPresentation.Law) (meanings true)) := by
  intro extended
  have satisfaction := EquationExtension.necessary_satisfaction signature
    (CartesianActionPresentation.declaration signature generated) (meanings true) (realized true) extended
  have unit := satisfaction ⟨.unit⟩
  apply incrementing_original_model_rejects_unit
  simpa only [CartesianActionPresentation.declaration, classOf_representative, classOf_identity,
    ← raw_unit_read] using unit

theorem original_presentation_does_not_identify_unit : unitDiagram generated ≠ 𝟙 edge := by
  intro same
  exact incrementing_original_model_rejects_unit (congrArg (evaluate true).map same)

theorem extended_positive_model_retains_whole_original :
    (CartesianActionPresentation.inclusion signature generated).functor ⋙
      CartesianActionPresentation.interpretation signature generated (meanings false) (realized false)
        positive_interpreted_action = evaluate false :=
  CartesianActionPresentation.complete_restriction signature generated (meanings false) (realized false)
    positive_interpreted_action

end Mettapedia.CategoryTheory.CartesianMonoidAction.Controls
