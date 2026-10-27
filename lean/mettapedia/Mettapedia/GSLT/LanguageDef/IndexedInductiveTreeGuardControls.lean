import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
import Mettapedia.Logic.HOL.IndexedConstructorGuardCompilation
import Mettapedia.Logic.HOL.IndexedConstructorGuardPrograms
import Mettapedia.Logic.HOL.FixedConstructorPositionPrograms
import Mettapedia.TypeTheory.RecursiveSpace

/-!
# Generated root and edge guards in a recursive-tree model

The constructor operation denotes the actual recursive-space constructor.
Nil, a singleton and a two-element tree have distinct retained shapes and
canonical bottom padding. The generated root program recognizes their
indices, refuses bottom and a wrong index, and the edge program refuses
inactive slots and children at the wrong index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveTreeGuardControls

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedInductiveNatVec IndexedInductiveHOLTerms FiniteConstructorEncoding

inductive SortCode where | number | space
abbrev number : Ty SortCode := .base .number
abbrev space : Ty SortCode := .base .space
abbrev payload : Ty SortCode := payloadType [[], [number, .prop]]
abbrev NumberValue := ULift.{1} Nat
abbrev PayloadValue := ULift.{1} Prop → (NumberValue → ULift.{1} Prop → ULift.{1} Prop) → ULift.{1} Prop
abbrev Tree := Mettapedia.TypeTheory.RecursiveSpace.Tree PayloadValue

inductive Symbol : Ty SortCode → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)
  | addition : Symbol (number ⇒ number ⇒ number)
  | bottom : Symbol space
  | node : Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)

def carrier : SortCode → Type 1
  | .number => NumberValue
  | .space => Tree

def model : HenkinModel.{0,0,0} SortCode Symbol := .standard carrier
  (fun symbol => match symbol with
    | .zero => .up 0
    | .successor => fun n => .up (n.down + 1)
    | .addition => fun n m => .up (n.down + m.down)
    | .bottom => Mettapedia.TypeTheory.RecursiveSpace.bottom
    | .node => fun tag data children => Mettapedia.TypeTheory.RecursiveSpace.construct
        tag.down data (fun n => children (.up n)))

def values : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def arithmetic : Arithmetic Symbol :=
  ⟨number, .prop, .const .zero, .const .successor, .const .addition⟩
def numeral : Nat → ClosedTerm Symbol number
  | 0 => arithmetic.zero
  | n + 1 => .app arithmetic.successor (numeral n)

theorem numeral_denote (n : Nat) : model.denote (numeral n) values = ULift.up n := by
  induction n with
  | zero => rfl
  | succ n hypothesis =>
      change ULift.up ((model.denote (numeral n) values).down + 1) = _
      rw [hypothesis]

noncomputable def inventory : IndexedConstructorGuards.Inventory Symbol [] :=
  IndexedConstructorGuardCompilation.inventory (arithmetic.reading Bool) (Vectors.constructors Bool)
    number numeral (fun _ => CurriedPredicates.constant _ .top)

def nilOccurrence : Fin inventory.fields.length := ⟨0, by change 0 < 2; decide⟩
def consOccurrence : Fin inventory.fields.length := ⟨1, by change 1 < 2; decide⟩
def nilData : inventory.toConstructorPrograms.Data model := ⟨nilOccurrence, PUnit.unit⟩
def consData (n : Nat) : inventory.toConstructorPrograms.Data model := ⟨consOccurrence, ULift.up n, ULift.up True, PUnit.unit⟩
def construct : ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) :=
  .const .node

theorem allowed (data : inventory.toConstructorPrograms.Data model) : inventory.toConstructorPrograms.dataAllowed model values data := by
  change CurriedPredicates.holds model _ (CurriedPredicates.constant _ .top) values data.2
  exact (CurriedPredicates.constant_holds model _ .top values data.2).mpr True.intro

theorem cons_result (n : Nat) : inventory.toConstructorPrograms.resultValue model values (consData n) = ULift.up (n + 1) := by
  unfold IndexedConstructorGuards.ConstructorPrograms.resultValue
  change CurriedPredicates.applyValues model [number, .prop]
    (model.denote (arithmetic.resultProgram Bool) values) _ = _
  rw [Arithmetic.resultProgram_body]
  rfl

theorem cons_child (n : Nat) : inventory.childValue model values (consData n)
    ⟨0, by change 0 < 1; decide⟩ = ULift.up n := by
  unfold IndexedConstructorGuards.Inventory.childValue
  change CurriedPredicates.applyValues model [number, .prop]
    (model.denote (arithmetic.childProgram Bool) values) _ = _
  rw [Arithmetic.childProgram_body]
  rfl

noncomputable def nilValue : Tree := Mettapedia.TypeTheory.RecursiveSpace.construct 0
  (inventory.toConstructorPrograms.packedData model nilData) (fun _ => Mettapedia.TypeTheory.RecursiveSpace.bottom)
noncomputable def consValue (n : Nat) (child : Tree) : Tree :=
  Mettapedia.TypeTheory.RecursiveSpace.construct 1 (inventory.toConstructorPrograms.packedData model (consData n))
    (fun slot => if slot = 0 then child else Mettapedia.TypeTheory.RecursiveSpace.bottom)
noncomputable def singleton := consValue 0 nilValue
noncomputable def two := consValue 1 singleton

theorem nil_root : inventory.toConstructorPrograms.rootMeaning construct model values nilValue (ULift.up 0) := by
  refine ⟨nilData, allowed _, ?_, (fun _ => Mettapedia.TypeTheory.RecursiveSpace.bottom), rfl⟩
  unfold IndexedConstructorGuards.ConstructorPrograms.resultValue
  change model.denote (arithmetic.term (Vectors.IndexExpr.zero (context := []))) values = _
  rw [Arithmetic.term]
  rfl

theorem cons_root (n : Nat) (child : Tree) :
    inventory.toConstructorPrograms.rootMeaning construct model values (consValue n child) (ULift.up (n + 1)) := by
  exact ⟨consData n, allowed _, cons_result n,
    (fun slot => if slot.down = 0 then child else Mettapedia.TypeTheory.RecursiveSpace.bottom), rfl⟩

theorem payload_injective : ∀ tag data children tag' data' children',
    model.denote construct values tag data children = model.denote construct values tag' data' children' →
      data = data' := by
  intro tag data children tag' data' children' same
  exact ((Mettapedia.TypeTheory.RecursiveSpace.construct_injective _ _ _ _ _ _).mp same).2.1

theorem root_accepts_singleton : (model.denote (inventory.toConstructorPrograms.rootProgram construct) values singleton (ULift.up 1)).down :=
  (inventory.toConstructorPrograms.rootProgram_denote construct model full values singleton (ULift.up 1)).mpr (cons_root 0 nilValue)

/-- A closed non-vacuity witness for all premises of index uniqueness. -/
theorem singleton_uniqueness_instance : (ULift.up 1 : NumberValue) = ULift.up 1 :=
  inventory.toConstructorPrograms.rootMeaning_unique_index construct model values payload_injective
    (cons_root 0 nilValue) (cons_root 0 nilValue)

theorem root_refuses_wrong_index : ¬ (model.denote (inventory.toConstructorPrograms.rootProgram construct) values singleton (ULift.up 2)).down := by
  intro valid
  have root := (inventory.toConstructorPrograms.rootProgram_denote construct model full values singleton (ULift.up 2)).mp valid
  have impossible := inventory.toConstructorPrograms.rootMeaning_unique_index construct model values payload_injective (cons_root 0 nilValue) root
  have numerals := congrArg ULift.down impossible
  change (1 : Nat) = 2 at numerals
  cases numerals

theorem root_refuses_bottom : ¬ (model.denote (inventory.toConstructorPrograms.rootProgram construct) values
    Mettapedia.TypeTheory.RecursiveSpace.bottom (ULift.up 0)).down := by
  intro valid
  apply inventory.toConstructorPrograms.rootMeaning_refuses_bottom construct model values Mettapedia.TypeTheory.RecursiveSpace.bottom
    (fun tag data children => Mettapedia.TypeTheory.RecursiveSpace.construct_ne_bottom tag.down data
      (fun n => children (ULift.up n))) (ULift.up 0)
  exact (inventory.toConstructorPrograms.rootProgram_denote construct model full values _ _).mp valid

theorem edge_accepts_singleton : (model.denote (inventory.edgeProgram construct) values
    (inventory.toConstructorPrograms.packedData model (consData 1)) (ULift.up 0) singleton).down := by
  apply (inventory.edgeProgram_denote construct model full values _ _ _).mpr
  refine ⟨consData 1, allowed _, ?_, ⟨0, by change 0 < 1; decide⟩, rfl, ?_⟩
  · exact (payloadEquivalence model inventory.fields).apply_symm_apply _
  · rw [cons_child]
    exact cons_root 0 nilValue

theorem position_adapter_edge : (model.denote (inventory.toPositionPrograms.edgeProgram construct) values
    (inventory.toConstructorPrograms.packedData model (consData 1)) (ULift.up 0) singleton).down :=
  (inventory.edgeProgram_agreement model full construct values _ _ _).mpr edge_accepts_singleton

theorem edge_refuses_wrong_child : ¬ (model.denote (inventory.edgeProgram construct) values
    (inventory.toConstructorPrograms.packedData model (consData 1)) (ULift.up 0) two).down := by
  intro valid
  obtain ⟨data, _, agrees, position, _, root⟩ :=
    (inventory.edgeProgram_denote construct model full values _ _ _).mp valid
  have same : consData 1 = data :=
    Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective _ _
      (((payloadEquivalence model inventory.fields).apply_symm_apply _).symm.trans agrees)
  cases same
  have pos : position = ⟨0, by change 0 < 1; decide⟩ := by
    apply Fin.ext
    change position.val = 0
    have bound := position.isLt
    change position.val < 1 at bound
    omega
  subst position
  rw [cons_child] at root
  have impossible := inventory.toConstructorPrograms.rootMeaning_unique_index construct model values payload_injective
    (cons_root 1 singleton) root
  have numerals := congrArg ULift.down impossible
  change (2 : Nat) = 1 at numerals
  cases numerals

theorem edge_refuses_nil_parent : ¬ (model.denote (inventory.edgeProgram construct) values
    (inventory.toConstructorPrograms.packedData model nilData) (ULift.up 0) singleton).down := by
  intro valid
  obtain ⟨data, _, agrees, position, _⟩ :=
    (inventory.edgeProgram_denote construct model full values _ _ _).mp valid
  have same : nilData = data :=
    Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective _ _
      (((payloadEquivalence model inventory.fields).apply_symm_apply _).symm.trans agrees)
  cases same
  exact Fin.elim0 position

#print axioms root_accepts_singleton
#print axioms root_refuses_wrong_index
#print axioms root_refuses_bottom
#print axioms edge_accepts_singleton
#print axioms edge_refuses_wrong_child
#print axioms edge_refuses_nil_parent

end Mettapedia.GSLT.LanguageDef.IndexedInductiveTreeGuardControls
