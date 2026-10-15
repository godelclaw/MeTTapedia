import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionConstructorComparison
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionControls
import Mettapedia.GSLT.Core.LambdaTheoryClosedControls
import Mettapedia.CategoryTheory.InternalCategoryPathDiagram

/-!
# Complete return functions and matching paths through a nonidentity map

Exchange of two independently supplied components changes the actual edge
endpoints. The canonical closed-category comparison retains both arguments
of a return function, both matching edges, and their ordered origins. Omitting
a supplied argument changes the result even when the origin is unchanged.

The concrete free path model tests the generic comparison. Separate controls
exercise the actual generated compiler's constructor restriction and edge
classes, whose receipt origins remain independently retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparisonControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory

namespace CompleteFunctions

open InternalCategoryPathDiagram
open Mettapedia.GSLT.Core.LambdaTheoryClosedControls (Diagrams numbers swapMap)

abbrev Event := Nat × Nat × Nat

def events : Diagrams := Discrete.functor fun _ => Event

def source : events ⟶ numbers := Discrete.natTrans fun _ => TypeCat.ofHom fun event => event.2.1
def target : events ⟶ numbers := Discrete.natTrans fun _ => TypeCat.ofHom fun event => event.2.2
def graph : InternalGraph Diagrams := ⟨numbers, events, source, target⟩
abbrev original := InternalCategoryPathDiagram.category graph
abbrev F : Diagrams ⥤ Diagrams := Mettapedia.GSLT.Core.LambdaTheoryClosedControls.swapEquivalence.functor

instance F_finite : PreservesFiniteLimits F := swapMap.preservesFiniteLimits
instance F_closed : MonoidalClosedFunctor F :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts F
    Mettapedia.GSLT.Core.LambdaTheoryClosedControls.swapEquivalence.symm.toAdjunction

def step (index : Discrete Bool) : Nat := if index.as then 2 else 1

def firstEvents : numbers ⟶ events :=
  Discrete.natTrans fun index => TypeCat.ofHom fun (number : Nat) => (7, number, number + step index)

def secondEvents : numbers ⟶ events :=
  Discrete.natTrans fun index => TypeCat.ofHom fun (number : Nat) =>
    (9, number + step index, number + step index + 3)

def first : numbers ⟶ original.edge := firstEvents ≫ edgeInclusion graph
def second : numbers ⟶ original.edge := secondEvents ≫ edgeInclusion graph

theorem matching : first ≫ original.target = second ≫ original.source := by
  ext index number
  rfl

def composed : numbers ⟶ original.edge := original.compose first second matching

def origins {index : Discrete Bool} {first : Vertex graph index} : {last : Vertex graph index} →
    Path graph index first last → List Nat
  | _, .nil => []
  | _, .cons before event => origins before ++ [event.1.1]

def readout (index : Discrete Bool) (path : InternalCategoryDiagram.Arrow ((diagram graph).obj index)) : List Nat :=
  origins path.2.2

theorem origins_comp {index : Discrete Bool} {a b c : Vertex graph index}
    (before : Path graph index a b) (after : Path graph index b c) :
    origins (before.comp after) = origins before ++ origins after := by
  induction after with
  | nil => exact (List.append_nil _).symm
  | cons prior event ih =>
      exact (congrArg (fun xs => xs ++ [event.1.1]) ih).trans (List.append_assoc _ _ _)

theorem origins_cast {index : Discrete Bool} {a b : Vertex graph index} (same : a = b) :
    origins (eqToHom same : (show (diagram graph).obj index from a) ⟶
      (show (diagram graph).obj index from b)) = [] := by
  cases same
  rfl

theorem composition_readout (index : Discrete Bool)
    (before after : InternalCategoryDiagram.Arrow ((diagram graph).obj index))
    (matched : InternalCategoryDiagram.Arrow.target before = InternalCategoryDiagram.Arrow.source after) :
    readout index (InternalCategoryDiagram.Arrow.compose before after matched) =
      readout index before ++ readout index after := by
  change origins (before.2.2.comp
    ((eqToHom matched : (show (diagram graph).obj index from before.2.1) ⟶
      (show (diagram graph).obj index from after.1)).comp after.2.2)) = _
  rw [origins_comp, origins_comp, origins_cast, List.nil_append]
  rfl

theorem complete_composition_origins (index : Discrete Bool) (number : Nat) :
    readout index (composed.app index number) = [7, 9] := by
  have computed := InternalCategoryDiagram.composeWith_apply (diagram graph) first second matching index number
  exact (congrArg (readout index) computed).trans
    (composition_readout index (first.app index number) (second.app index number) _)

abbrev mapped := InternalCategoryFiniteLimitTransport.category F original
def mappedFirst : F.obj numbers ⟶ mapped.edge := F.map first
def mappedSecond : F.obj numbers ⟶ mapped.edge := F.map second

theorem mapped_matching : mappedFirst ≫ mapped.target = mappedSecond ≫ mapped.source :=
  InternalCategoryFiniteLimitTransport.mapped_matching F original first second matching

def mappedComposed : F.obj numbers ⟶ mapped.edge := mapped.compose mappedFirst mappedSecond mapped_matching

theorem complete_mapped_composition : mappedComposed = F.map composed :=
  InternalCategoryFiniteLimitTransport.category_compose_read F original first second matching

theorem swapped_composition_origins (number : Nat) :
    readout ⟨true⟩ (mappedComposed.app ⟨false⟩ number) = [7, 9] := by
  rw [complete_mapped_composition]
  exact complete_composition_origins ⟨true⟩ number

theorem changed_endpoint : mapped.target.app ⟨false⟩ (mappedComposed.app ⟨false⟩ (10 : Nat)) = (15 : Nat) := by
  rw [complete_mapped_composition]
  change original.target.app ⟨true⟩ (composed.app ⟨true⟩ (10 : Nat)) = _
  have whole := original.compose_target first second matching
  exact congrArg (fun arrow : numbers ⟶ original.vertex => arrow.app ⟨true⟩ (10 : Nat)) whole

theorem original_endpoint : original.target.app ⟨false⟩ (composed.app ⟨false⟩ (10 : Nat)) = (14 : Nat) := by
  have whole := original.compose_target first second matching
  exact congrArg (fun arrow : numbers ⟶ original.vertex => arrow.app ⟨false⟩ (10 : Nat)) whole

def sumArguments : numbers ⊗ numbers ⟶ numbers :=
  Discrete.natTrans fun _ => TypeCat.ofHom fun (pair : Nat × Nat) => pair.1 + pair.2

def body : numbers ⊗ numbers ⟶ original.edge := sumArguments ≫ first
def returnFunction : numbers ⟶ (ihom numbers).obj original.edge := MonoidalClosed.curry body
def completeComparison := InternalCategoryClosedFunctorComparison.comparison F numbers original

def returnReadout : F.obj numbers ⊗ F.obj numbers ⟶ F.obj original.edge :=
  MonoidalClosed.uncurry (F.map returnFunction ≫ completeComparison.hom.edge)

theorem whole_return_function : returnReadout =
    inv (CartesianMonoidalCategory.prodComparison F numbers numbers) ≫ F.map body :=
  InternalCategoryClosedFunctorComparison.whole_abstraction F numbers original body

def arguments : numbers ⟶ numbers ⊗ numbers :=
  lift (𝟙 numbers) Mettapedia.GSLT.Core.LambdaTheoryClosedControls.shift

def probe : F.obj numbers ⟶ F.obj original.edge :=
  F.map arguments ≫ CartesianMonoidalCategory.prodComparison F numbers numbers ≫ returnReadout

theorem whole_probe : probe = F.map (arguments ≫ body) := by
  rw [probe, whole_return_function,
    IsIso.hom_inv_id_assoc, ← F.map_comp]

theorem probe_keeps_origin (number : Nat) : readout ⟨true⟩ (probe.app ⟨false⟩ number) = [7] := by
  rw [whole_probe]
  rfl

theorem probe_keeps_full_argument : original.target.app ⟨true⟩ (probe.app ⟨false⟩ (10 : Nat)) = (24 : Nat) := by
  rw [whole_probe]
  rfl

def omittedArguments : numbers ⟶ numbers ⊗ numbers := lift (𝟙 numbers) (𝟙 numbers)
def omittedProbe : F.obj numbers ⟶ F.obj original.edge :=
  F.map omittedArguments ≫ CartesianMonoidalCategory.prodComparison F numbers numbers ≫ returnReadout

theorem omitted_probe_readout : omittedProbe = F.map (omittedArguments ≫ body) := by
  rw [omittedProbe, whole_return_function,
    IsIso.hom_inv_id_assoc, ← F.map_comp]

theorem omitted_argument_changes_whole_edge : probe.app ⟨false⟩ (10 : Nat) ≠ omittedProbe.app ⟨false⟩ (10 : Nat) := by
  rw [whole_probe, omitted_probe_readout]
  intro same
  have impossible := congrArg (original.target.app ⟨true⟩) same
  exact (by decide : (24 : Nat) ≠ 22) impossible

theorem omission_preserves_the_origin :
    readout ⟨true⟩ (probe.app ⟨false⟩ (10 : Nat)) = readout ⟨true⟩ (omittedProbe.app ⟨false⟩ (10 : Nat)) := by
  rw [whole_probe, omitted_probe_readout]
  rfl

theorem same_endpoint_different_occurrence :
    edge graph ⟨true⟩ (7, 1, 2) ≠ edge graph ⟨true⟩ (8, 1, 2) := by
  intro same
  have impossible := congrArg (readout ⟨true⟩) same
  change ([7] : List Nat) = [8] at impossible
  cases impossible

theorem lex_alone_does_not_supply_the_function_comparison :
    ¬ ∃ route : Mettapedia.GSLT.Core.LambdaTheoryMap
      Mettapedia.GSLT.Core.LambdaTheoryClosedControls.typesTheory
      Mettapedia.GSLT.Core.LambdaTheoryClosedControls.typesTheory,
      route.functor = Mettapedia.CategoryTheory.CartesianClosedPowerFunctor.power Bool :=
  Mettapedia.GSLT.Core.LambdaTheoryClosedControls.power_is_not_theory_map

end CompleteFunctions

namespace ActualGuest

open NamePassingGeneratedParallelActionConstructorComparison

universe k

theorem all_five_constructor_certificates
    (operator : Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.Operator .tm) :
    (⟨quotient.obj (NamePassingGeneratedConstructorComparison.targetValue.{k} operator).source,
      quotient.obj (NamePassingGeneratedConstructorComparison.targetValue operator).target,
      (nativeDomainComparison operator).inv ≫
        constructorCompiler.map (NamePassingBindingClosedConstructorReadout.arrow sourceOperations operator) ≫
          (nativeProgramComparison operator).hom⟩ :
        Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue Target) = targetValue operator :=
  whole_constructor_certificate operator

theorem target_unit_keeps_receipt_origins_separate :
    NamePassingGeneratedParallelActionControls.EdgeClasses.supplied.{k} ⟨.plain⟩
      (𝟙 BindingClosedGeneratedParallelAction.operations.edge) ≠
        NamePassingGeneratedParallelActionControls.EdgeClasses.supplied ⟨.emptyFrame⟩
          (𝟙 BindingClosedGeneratedParallelAction.operations.edge) :=
  NamePassingGeneratedParallelActionControls.EdgeClasses.different_receipt_origins _

end ActualGuest

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparisonControls
