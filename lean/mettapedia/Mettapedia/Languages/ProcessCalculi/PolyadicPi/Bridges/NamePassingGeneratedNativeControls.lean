import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeLanguage
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelControls
import Mathlib.Tactic.NormNum

/-!
# Full authored origins, future arguments and chosen composition controls

The actual native compiler is exercised at all five authored rule domains.
An independent indexed-arrow model computes on distinct root, passive and
function-valued premise shapes, including restriction and erased origins.
A nonidentity vertex comparison transports a genuinely weighted category;
its chosen matching-pair composition retains both edge weights.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeControls

open _root_.CategoryTheory Opposite MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.GSLT.Topos.PresheafTheoryAction

namespace ActualCompiler

open NamePassingGeneratedNativeLanguage

universe k

def supplied (origin : Origin.{k}) :
    ((inverseImage compilerFunctor).obj targetReceipts).obj (op (domain origin)) :=
  ⟨origin, ULift.up (𝟙 (targetDomain origin))⟩

theorem all_five_native_firings (origin : Origin.{k}) :
    (nativeFiring.app (op (domain origin)) (supplied origin)).down ≫ (resultComparison origin).hom =
      (premiseComparison origin).hom ≫ NamePassingGeneratedOperationalInterpretation.firing origin := by
  have actual := complete_independent_firing (supplied origin)
  erw [Category.id_comp] at actual
  exact actual

def simultaneousDomain : Source.{k} := domain ⟨.beta⟩ ⊗ domain ⟨.fetch⟩

def betaReceipt : ((inverseImage compilerFunctor).obj targetReceipts.{k}).obj (op simultaneousDomain) :=
  ⟨⟨.beta⟩, ULift.up (compilerFunctor.map
    (CartesianMonoidalCategory.fst (domain ⟨.beta⟩) (domain ⟨.fetch⟩)))⟩

def fetchReceipt : ((inverseImage compilerFunctor).obj targetReceipts.{k}).obj (op simultaneousDomain) :=
  ⟨⟨.fetch⟩, ULift.up (compilerFunctor.map
    (CartesianMonoidalCategory.snd (domain ⟨.beta⟩) (domain ⟨.fetch⟩)))⟩

theorem actual_compiler_keeps_distinct_origins : betaReceipt.{k} ≠ fetchReceipt := by
  intro same
  have origins := congrArg Sigma.fst same
  have impossible := congrArg ULift.down origins
  cases impossible

theorem all_five_future_origins {first second : Source.{k}} (change : first ⟶ second)
    (origin : Origin) (argument : compilerFunctor.obj second ⟶ targetDomain origin) :
    (((inverseImage compilerFunctor).obj targetReceipts).map change.op ⟨origin,ULift.up argument⟩).1 = origin :=
  future_origin change ⟨origin,ULift.up argument⟩

end ActualCompiler

namespace IndependentRules

abbrev Origin := NamePassingGeneratedOperationalPresentation.Origin
abbrev Edge := Nat × Nat

def domains : Origin → Type
  | .beta => (Nat → Nat) × Nat
  | .fetch => Nat × Nat
  | .application => Edge × Nat
  | .definition => Nat × (Nat → Edge)
  | .carrier => Nat × (Nat × Edge)

def firing : ∀ origin, domains origin ⟶ Edge
  | .beta => ↾fun input => (input.1 input.2 + 1,input.1 input.2)
  | .fetch => ↾fun input => (input.1 + input.2 + 1,input.2)
  | .application => ↾fun input => (10 * input.1.1 + input.2,10 * input.1.2 + input.2)
  | .definition => ↾fun input => (input.1 + (input.2 42).1,input.1 + (input.2 42).2)
  | .carrier => ↾fun input =>
      (100 * input.1 + 10 * input.2.1 + input.2.2.1,100 * input.1 + 10 * input.2.1 + input.2.2.2)

abbrev receipts := IndexedArrowReceiptPresheaf.receipts.{1,0,0,0} domains
abbrev evaluate := IndexedArrowReceiptPresheaf.evaluate.{1,0,0,0} domains firing

def output {stage : Type} (receipt : receipts.obj (op stage)) : stage ⟶ Edge :=
  (evaluate.app (op stage) receipt).down

def input : (origin : Origin) → domains origin
  | .beta => (fun name => name,2)
  | .fetch => (0,2)
  | .application => ((3,7),5)
  | .definition => (10,fun name => (name,name+1))
  | .carrier => (3,(5,(7,9)))

def supplied (origin : Origin) : receipts.obj (op PUnit) :=
  ⟨origin,ULift.up (TypeCat.ofHom (fun _ => input origin))⟩

theorem beta_firing : output (supplied .beta) PUnit.unit = (3,2) := rfl
theorem fetch_firing : output (supplied .fetch) PUnit.unit = (3,2) := rfl
theorem application_firing : output (supplied .application) PUnit.unit = (35,75) := rfl
theorem definition_firing : output (supplied .definition) PUnit.unit = (52,53) := rfl
theorem carrier_firing : output (supplied .carrier) PUnit.unit = (357,359) := rfl

theorem distinct_origins_same_complete_edge : supplied .beta ≠ supplied .fetch ∧
    evaluate.app (op PUnit) (supplied .beta) = evaluate.app (op PUnit) (supplied .fetch) := by
  constructor
  · exact IndexedArrowReceiptPresheaf.different_origins domains .beta .fetch (by decide) _ _
  · rfl

theorem no_edge_origin_decoder :
    ¬ ∃ decoder : (uliftYoneda.{0}.obj Edge).obj (op PUnit) → Origin,
      ∀ origin, decoder (evaluate.app (op PUnit) (supplied origin)) = origin := by
  rintro ⟨decoder,reads⟩
  have same := (reads .beta).symm.trans (reads .fetch)
  cases same

def futureArgument : receipts.obj (op Nat) :=
  ⟨.beta,ULift.up (TypeCat.ofHom (fun stage => (fun name => stage+name,2*stage)))⟩

theorem complete_future_readout (stage : Nat) :
    output (receipts.map (TypeCat.ofHom Nat.succ).op futureArgument) stage =
      (3*(stage+1)+1,3*(stage+1)) := by
  change ((stage+1)+(2*(stage+1))+1,(stage+1)+(2*(stage+1))) = _
  congr 1 <;> omega

theorem restriction_retains_complete_body (stage name : Nat) :
    (((receipts.map (TypeCat.ofHom Nat.succ).op futureArgument).2.down stage).1 name) = stage+1+name := rfl

theorem omitting_future_change_alters_edge :
    output (receipts.map (TypeCat.ofHom Nat.succ).op futureArgument) 1 ≠
      output futureArgument 1 := by
  intro same
  have impossible := congrArg Prod.snd same
  change (6 : Nat) = 3 at impossible
  omega

def firstBody : Nat → Edge := fun name => (name,name+1)
def changedBody : Nat → Edge := fun name =>
  if name=42 then (name+1,name+2) else (name,name+1)

def definitionReceipt (body : Nat → Edge) : receipts.obj (op PUnit) :=
  ⟨.definition,ULift.up (TypeCat.ofHom (fun _ => (10,body)))⟩

theorem bodies_agree_at_present_argument : firstBody 0 = changedBody 0 := rfl

theorem complete_body_firings_differ :
    output (definitionReceipt firstBody) PUnit.unit = (52,53) ∧
      output (definitionReceipt changedBody) PUnit.unit = (53,54) := by
  constructor <;> rfl

theorem no_present_argument_decoder :
    ¬ ∃ decoder : Edge → Edge, ∀ body,
      decoder (body 0) = output (definitionReceipt body) PUnit.unit := by
  rintro ⟨decoder,reads⟩
  have same := (reads firstBody).symm.trans (reads changedBody)
  rw [complete_body_firings_differ.1,complete_body_firings_differ.2] at same
  cases same

end IndependentRules

namespace ChosenCategory

open RelativeClosedInternalCategory
open Controls ModelControls

def shifted := InternalCategoryVertexIso.category CategoryControls.weightedCategory programComparison
def forward := InternalCategoryVertexIso.toOriginal CategoryControls.weightedCategory programComparison
def comparison := InternalCategoryIso.iso forward programComparison (Iso.refl Controls.Evidence) rfl rfl

theorem nonidentity_vertex : comparison.hom.vertex false = true := rfl

theorem matching : ModelControls.firstEdge ≫ shifted.target = ModelControls.secondEdge ≫ shifted.source :=
  ModelControls.supplied_edges_match

def composition : PUnit ⟶ Controls.Evidence :=
  shifted.compose ModelControls.firstEdge ModelControls.secondEdge matching ≫ comparison.hom.edge

theorem entire_chosen_composition : composition = CategoryControls.weightedCategory.compose
    ModelControls.firstEdge ModelControls.secondEdge
      (InternalCategoryVertexIso.matching CategoryControls.weightedCategory programComparison _ _ matching) := by
  have actual := comparison.hom.compose_readout ModelControls.firstEdge ModelControls.secondEdge matching
  change composition = _ at actual
  change composition = CategoryControls.weightedCategory.compose
    (ModelControls.firstEdge ≫ (𝟙 Controls.Evidence))
    (ModelControls.secondEdge ≫ (𝟙 Controls.Evidence)) _ at actual
  simpa only [Category.comp_id] using actual

theorem chosen_pair_retains_both_weights : composition PUnit.unit = ((false,false,10) : Controls.Evidence) := by
  rw [entire_chosen_composition]
  exact CategoryControls.category_retains_complete_composition _ _ _ PUnit.unit

theorem inverse_retains_whole_edge (receipt : Controls.Evidence) :
    comparison.inv.edge (comparison.hom.edge receipt) = receipt := rfl

end ChosenCategory

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeControls
