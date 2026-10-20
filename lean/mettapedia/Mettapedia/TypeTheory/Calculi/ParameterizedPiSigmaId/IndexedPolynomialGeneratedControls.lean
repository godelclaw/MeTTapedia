import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedPolynomialGeneratedReceipts

/-!
# Generated recursor controls

Naturals use the declaration library's existing constructor inventory. A second
datatype mixes closed payloads with two recursive fields. The controls preserve
the payload order, the original recursive arguments, and both computed results.
Receipts distinguish equal-endpoint source occurrences; declaration admission
separately rejects the duplicate constructor names in that negative inventory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace IndexedPolynomialGenerated.Controls

open TypedEquality Normalization Annotated
open Mettapedia.TypeTheory

private def name (text : String) : DeclName := Lean.Name.mkSimple text
private def atom (value : Nat) : Tm Unit 0 := .const (.num .anonymous value)
private def quote (_type : Tm Unit 0) (value : Nat) : Tm Unit 0 := atom value
private abbrev Payload (_type : Tm Unit 0) := Nat

abbrev naturalConstructors := exampleNat (Head := Unit)

def naturalZero : Tree naturalConstructors Payload :=
  .roll ⟨⟨0, by decide⟩, PUnit.unit⟩ (fun position => nomatch position)

def naturalSucc (value : Tree naturalConstructors Payload) : Tree naturalConstructors Payload :=
  .roll ⟨⟨1, by decide⟩, PUnit.unit⟩ fun
    | .here => value
    | .recursiveTail impossible => nomatch impossible

def naturalMethods : Fin naturalConstructors.length → Tm Unit 0 :=
  fun index => if index.val = 0 then .const (name "base") else .const (name "step")

theorem natural_two_computes :
    eliminate naturalConstructors quote naturalMethods (naturalSucc (naturalSucc naturalZero)) =
      appSpine (.const (name "step"))
        [appSpine (.const (name "suc")) [.const (name "zero")],
          appSpine (.const (name "step")) [.const (name "zero"), .const (name "base")]] := rfl

theorem natural_two_guest_reduces :
    Steps naturalConstructors (name "natRec")
      (recApp (name "natRec") (.head () :: List.ofFn naturalMethods)
        (encode naturalConstructors quote (naturalSucc (naturalSucc naturalZero))))
      (appSpine (.const (name "step"))
        [appSpine (.const (name "suc")) [.const (name "zero")],
          appSpine (.const (name "step")) [.const (name "zero"), .const (name "base")]]) := by
  rw [← natural_two_computes]
  exact recursor_reduces _ _ _ _ _ _

def treeConstructors : List (DeclName × List (Field Unit)) :=
  [(name "leaf", [.closed (.head ())]), (name "fork", [.recursive, .recursive])]

def leaf (value : Nat) : Tree treeConstructors Payload :=
  .roll ⟨⟨0, by decide⟩, value, PUnit.unit⟩ fun
    | .closedTail impossible => nomatch impossible

def fork (left right : Tree treeConstructors Payload) : Tree treeConstructors Payload :=
  .roll ⟨⟨1, by decide⟩, PUnit.unit⟩ fun
    | .here => left
    | .recursiveTail .here => right
    | .recursiveTail (.recursiveTail impossible) => nomatch impossible

def treeMethods : Fin treeConstructors.length → Tm Unit 0 :=
  fun index => if index.val = 0 then .const (name "onLeaf") else .const (name "onFork")

def treeResult : Tm Unit 0 :=
  appSpine (.const (name "onFork"))
    [appSpine (.const (name "leaf")) [atom 3], appSpine (.const (name "leaf")) [atom 5],
      appSpine (.const (name "onLeaf")) [atom 3], appSpine (.const (name "onLeaf")) [atom 5]]

theorem tree_keeps_fields_and_results :
    eliminate treeConstructors quote treeMethods (fork (leaf 3) (leaf 5)) = treeResult := rfl

theorem tree_guest_reduces :
    Steps treeConstructors (name "treeRec")
      (recApp (name "treeRec") (.head () :: List.ofFn treeMethods)
        (encode treeConstructors quote (fork (leaf 3) (leaf 5)))) treeResult := by
  rw [← tree_keeps_fields_and_results]
  exact recursor_reduces _ _ _ _ _ _

theorem changed_payload_rejected :
    eliminate treeConstructors quote treeMethods (fork (leaf 3) (leaf 3)) ≠ treeResult := by
  decide +kernel

theorem reordered_payload_rejected :
    eliminate treeConstructors quote treeMethods (fork (leaf 5) (leaf 3)) ≠ treeResult := by
  decide +kernel

theorem schema_inventory_covers_both_constructors :
    (origins treeConstructors).map Origin.index = [0, 1] := rfl

theorem omitted_branch_detected :
    ((origins treeConstructors).take 1).map Origin.index ≠ [0, 1] := by decide +kernel

theorem no_third_constructor_receipt (receipt : Receipt treeConstructors 0) :
    receipt.origin.index ≠ 2 := by
  have bound := receipt.origin.index_lt
  change receipt.origin.index < 2 at bound
  omega

private def duplicateConstructors : List (DeclName × List (Field Unit)) :=
  [(name "same", []), (name "same", [])]

def duplicateFirst : Receipt duplicateConstructors 0 where
  origin := ⟨0, name "same", [], rfl⟩
  assignment := listSub 3 [.head (), atom 7, atom 7]

def duplicateSecond : Receipt duplicateConstructors 0 where
  origin := ⟨1, name "same", [], rfl⟩
  assignment := listSub 3 [.head (), atom 7, atom 7]

theorem equal_endpoints_retain_origins :
    duplicateFirst.left (name "rec") = duplicateSecond.left (name "rec") ∧
    duplicateFirst.right (name "rec") = duplicateSecond.right (name "rec") ∧
    duplicateFirst ≠ duplicateSecond := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have wrong := congrArg (fun receipt : Receipt duplicateConstructors 0 => receipt.origin.index) equal
  exact Nat.zero_ne_one wrong

theorem duplicate_declaration_refused :
    ¬ DistinctNames (name "D") duplicateConstructors (name "rec") := by
  intro distinct
  have nodup := distinct.ctorsNodup
  simp [duplicateConstructors] at nodup

/-- This intentionally restricted head policy distinguishes formation from raw
execution; it is not claimed to be a model of a whole dependent type theory. -/
def restrictedHeads : Rules Bool where
  headTyping _ _ := False
  isUniverse head := head = false
  join first second result := first = false ∧ second = false ∧ result = false
  cumulative := Eq
  headEq := Eq

def restrictedChurch : ChurchRules restrictedHeads :=
  ChurchRules.empty restrictedHeads (fun _ => rfl)

def forbiddenMotive : Datatype Bool where
  type := name "N"
  typeUniverse := false
  ctors := exampleNat
  recursor := name "natRec"
  motiveUniverse := true

theorem raw_iota_does_not_grant_admission :
    IotaStep forbiddenMotive.recursor forbiddenMotive.ctors
      (recApp forbiddenMotive.recursor [.head true, .head false, .head false]
        (.const (name "zero"))) (.head false : Tm Bool 0) ∧
    ¬ forbiddenMotive.Admissible restrictedChurch := by
  constructor
  · exact ⟨.head true, [.head false, .head false], 0, name "zero", [], [], .head false,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro admitted
    exact Bool.noConfusion admitted.motiveUniverse

end IndexedPolynomialGenerated.Controls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
