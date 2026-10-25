import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralWeakHeadSearch
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWeakHead

/-!
# Comparison programs using checked transparent definitions

Vector induction compares the two result readings after an evidence-universe
map. The cons program applies declared identity elimination to the actual
recursive identity proof. All four operation names have independently checked
stored bodies. Finite replay of these programs is a separate obligation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Comparison
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open TypedEquality.Normalization
open NativeNaturalVectorFamilies
open NativeVectorAll.ResultView
open NativeVectorAllTypedMaps (Direction source target)

abbrev rules := Named.rules

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Named.base) (signature := Named.signature)
    NativeVectorAllResultComparison.decoder (.ofEmpty _ rfl)

def searchRoot {n : Nat} (term : Tower.Tm n) : Option (decoder.Code n) :=
  match term with
  | .const actual =>
    if (Named.signature.valueOf? actual).isSome then some (.delta actual)
    else (NativeVectorAllResultComparison.searchRoot term).map .inherited
  | _ => (NativeVectorAllResultComparison.searchRoot term).map .inherited

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def rootEvaluator : ExecutableReduction.RootEvaluator rules := fun {_} term =>
  match searchRoot term with
  | none => none
  | some code => match decoded : decoder.decode code with
    | none => none
    | some (left, right) =>
      if same : left = term then some ⟨right, same ▸ decoder.sound code decoded⟩ else none

def weakHead {n : Nat} (fuel : Nat) (term : Tower.Tm n) : Tower.Tm n :=
  (ExecutableWeakHead.value rules rootEvaluator (fun _ => []) fuel term).getD term

theorem weakHead_reduces {n : Nat} (fuel : Nat) (term : Tower.Tm n) :
    TypedEquality.Reduces rules term (weakHead fuel term) := by
  unfold weakHead
  cases computed : ExecutableWeakHead.value rules rootEvaluator (fun _ => []) fuel term with
  | none => exact .refl
  | some result => exact ExecutableWeakHead.value_sound rules rootEvaluator (fun _ => []) computed

/-- Expose type constructors throughout products and families without
normalizing the proof endpoints of an identity type. -/
def typeView : (fuel : Nat) → {n : Nat} → Tower.Tm n → Tower.Tm n
  | 0, _, term => term
  | fuel + 1, _, term => match weakHead (fuel + 1) term with
    | .pi domain body => .pi (typeView fuel domain) (typeView fuel body)
    | .sigma domain body => .sigma (typeView fuel domain) (typeView fuel body)
    | .id carrier left right => .id (typeView fuel carrier) left right
    | result => result
termination_by structural fuel _ _ => fuel

theorem typeView_reduces : ∀ (fuel : Nat) {n : Nat} (term : Tower.Tm n),
    TypedEquality.Reduces rules term (typeView fuel term)
  | 0, _, _ => .refl
  | fuel + 1, _, term => by
    have initial := weakHead_reduces (fuel + 1) term
    cases viewed : weakHead (fuel + 1) term with
    | pi domain body =>
      rw [typeView, viewed]
      rw [viewed] at initial
      exact initial.trans ((TypedEquality.Normalization.Reduces.congr (fun step => .congPiDom step)
        (typeView_reduces fuel domain)).trans
          (TypedEquality.Normalization.Reduces.congr (fun step => .congPiCod step) (typeView_reduces fuel body)))
    | sigma domain body =>
      rw [typeView, viewed]
      rw [viewed] at initial
      exact initial.trans ((TypedEquality.Normalization.Reduces.congr (fun step => .congSigmaDom step)
        (typeView_reduces fuel domain)).trans
          (TypedEquality.Normalization.Reduces.congr (fun step => .congSigmaCod step) (typeView_reduces fuel body)))
    | id carrier left right =>
      rw [typeView, viewed]
      rw [viewed] at initial
      exact initial.trans (TypedEquality.Normalization.Reduces.congr (fun step => .congIdTy step)
        (typeView_reduces fuel carrier))
    | var _ | const _ | head _ | lam _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
      simpa only [typeView, viewed] using initial

/-- These hints are untrusted. Publication replays the complete produced code. -/
def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (rules.cumulative first second)
  normalize fuel term := typeView fuel term
  conversion fuel left right := StructuralWeakHeadSearch.compareCore decoder.decode searchRoot fuel left right

def sourceProjection : Direction → Operation
  | .forward => .lowerResults
  | .backward => .upperResults

def targetProjection : Direction → Operation
  | .forward => .upperResults
  | .backward => .lowerResults

def evidenceMap : Direction → Operation
  | .forward => .raiseEvidence
  | .backward => .lowerEvidence

def project {n : Nat} (operation : Operation)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  appSpine (.const (Named.name operation)) [element, result, length, vector, evidence]

def mapped {n : Nat} (direction : Direction)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  appSpine (.const (Named.name (evidenceMap direction)))
    [element, predicate result, length, vector, evidence]

def goal {n : Nat} (direction : Direction)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  .id (OriginalInputUniverses.upperVec result length)
    (project (targetProjection direction) element result length vector
      (mapped direction element result length vector evidence))
    (project (sourceProjection direction) element result length vector evidence)

def motive {n : Nat} (direction : Direction) (element result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.pi
    (NativeVectorAllCommonRecursorProfile.Projection.inputType (source direction)
      (NativeVectorAll.weaken2 element) (NativeVectorAll.weaken2 result) (.var 1) (.var 0))
    (goal direction (rename wk (NativeVectorAll.weaken2 element))
      (rename wk (NativeVectorAll.weaken2 result)) (.var 2) (.var 1) (.var 0))))

def nilCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (.refl (.app (.const `CumulativeTower.VecUpper.nil) (rename wk result)))

def consCase {n : Nat} (direction : Direction) (element result : Tower.Tm n) : Tower.Tm n :=
  let A := NativeVectorAllResultComparison.weaken5 element
  let R := NativeVectorAllResultComparison.weaken5 result
  let first := project (targetProjection direction) A R (.var 4) (.var 2)
    (mapped direction A R (.var 4) (.var 2) (.snd (.var 0)))
  let second := project (sourceProjection direction) A R (.var 4) (.var 2) (.snd (.var 0))
  let action := .lam (appSpine (.const `CumulativeTower.VecUpper.cons)
    [rename wk R, .var 5, .fst (.var 1), .var 0])
  let resultType := OriginalInputUniverses.upperVec R (succApp (.var 4))
  let firstResult := .app action first
  let equalityMotive := .lam (.lam (.id (NativeVectorAll.weaken2 resultType)
    (NativeVectorAll.weaken2 firstResult)
    (.app (NativeVectorAll.weaken2 action) (.var 1))))
  .lam (.lam (.lam (.lam (.lam
    (NativeIndexedFamilies.Intrinsic.identityEliminateApp
      (OriginalInputUniverses.upperVec R (.var 4)) first equalityMotive (.refl firstResult)
      second (.app (.var 1) (.snd (.var 0))))))))

def programme (direction : Direction) : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (.app (vecEliminateApp (.var 4) (motive direction (.var 4) (.var 3))
      (nilCase (.var 3)) (consCase direction (.var 4) (.var 3)) (.var 2) (.var 1)) (.var 0))))))

def programmeType (direction : Direction) : Tower.Tm 0 :=
  .pi (sortTm NativeVectorAllCommonRecursorProfile.dataLevel)
    (.pi (sortTm NativeVectorAllCommonRecursorProfile.resultLevel)
      (.pi natTm (.pi (vecApp (.var 2) (.var 0))
        (.pi (NativeVectorAllCommonRecursorProfile.Projection.inputType (source direction)
          (.var 3) (.var 2) (.var 1) (.var 0))
          (goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Comparison
