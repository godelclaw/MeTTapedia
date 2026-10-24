import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestMethodSpecialization
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeListResultChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation

/-!
# Registered List result projection and ordered native computation

The registered SearchTree List bundle is the actual input of the checked
projection. Its finite constructor readout retains one supplied result per
child occurrence, including equal children with distinct results. The raw
execution statement and the formation-sensitive input judgment are distinct
contracts. No decoding of arbitrary open List variables is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Declaration RussellTarski NativeIndexedFamilies

variable {n : Nat}

theorem registered_bundle_readback (element predicate children : Tower.Tm n) :
    NativeListResultView.bundleType element predicate children =
      PositiveInductiveSearchTreeGuest.bundleType element predicate children := rfl

private theorem list_root_inclusion {left right : Tower.Tm n}
    (step : (IntrinsicMaps.listRulesAt NativeListResultView.level).computation.step left right) :
    NativeListResultView.rules.computation.step left right := by
  cases step with
  | inherited impossible => exact impossible.elim
  | delta unfolding =>
    change (IntrinsicMaps.listSignatureAt NativeListResultView.level).valueOf? _ = some _ at unfolding
    simp only [IntrinsicMaps.listSignatureAt, Declaration.LevelInstance.signature,
      Signature.valueOf_instantiateLevels, Intrinsic.rawSignature_valueOf_none, Option.map_none] at unfolding
    cases unfolding
  | declared retained =>
    obtain ⟨evidence⟩ := retained
    exact .declared ⟨.list evidence⟩

private theorem list_step_inclusion {left right : Tower.Tm n}
    (step : StepCore (IntrinsicMaps.listRulesAt NativeListResultView.level).computation (fun _ _ => False) left right) :
    StepCore NativeListResultView.rules.computation NativeListResultView.rules.headEq left right := by
  have mapped := StepCore.mapHead (targetEq := NativeListResultView.rules.headEq)
    (targetRoot := NativeListResultView.rules.computation) (fun head => head) (fun impossible => impossible.elim)
    (fun previous => by simpa only [Tm.mapHead_id] using list_root_inclusion previous) step
  simpa only [Tm.mapHead_id] using mapped

theorem list_path_inclusion {left right : Tower.Tm n} (path : IntrinsicNativeListMapComputation.Reduces NativeListResultView.level left right) :
    TypedEquality.Reduces NativeListResultView.rules left right := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec
    (IntrinsicNativeListMapComputation.reduction NativeListResultView.level n)
    (fun left right _ => TypedEquality.Reduces NativeListResultView.rules left right)
    (fun _ => .refl)
    (fun {_ _ _} edge _ ih =>
      (.tail .refl (list_step_inclusion edge) : TypedEquality.Reduces NativeListResultView.rules _ _).trans ih)
    left right path

theorem project_map_readback (element result bundle : Tower.Tm n) :
    NativeListResultView.project element result bundle =
      IntrinsicNativeListMapComputation.mapped (NativeListResultView.packedType element (NativeListResultView.constantPredicate result)) result
        (.lam (.snd (.var 0))) (.fst bundle) := by
  simp [NativeListResultView.project, IntrinsicMaps.nativeMapBody, IntrinsicMaps.nativeMapMotive,
    IntrinsicMaps.nativeMapNilCase, IntrinsicMaps.nativeMapConsCase,
    IntrinsicNativeListMapComputation.mapped, IntrinsicNativeListMapComputation.motive, IntrinsicNativeListMapComputation.branch, Intrinsic.eliminateApp,
    Intrinsic.listApp, Intrinsic.nilApp, Intrinsic.consApp,
    subst, liftSub, Fin.cases, rename]
  dsimp [Fin.induction]
  simp [Fin.induction.go, rename_comp, rename]
  constructor
  · rfl
  · apply Fin.ext
    change 2 = 2 % (n + 3)
    exact (Nat.mod_eq_of_lt (by omega)).symm

def packedList (element result : Tower.Tm n) (pairs : List (Tower.Tm n × Tower.Tm n)) : Tower.Tm n :=
  IntrinsicNativeListMapComputation.encode (NativeListResultView.packedType element (NativeListResultView.constantPredicate result))
    (pairs.map (fun pair => .pair pair.1 pair.2))

theorem constructor_results (element result : Tower.Tm n)
    (pairs : List (Tower.Tm n × Tower.Tm n)) (relationEvidence : Tower.Tm n) :
    TypedEquality.Reduces NativeListResultView.rules
      (NativeListResultView.project element result (.pair (packedList element result pairs) relationEvidence))
      (IntrinsicNativeListMapComputation.encode result (pairs.map Prod.snd)) := by
  rw [project_map_readback]
  apply list_path_inclusion
  have selected : IntrinsicNativeListMapComputation.Reduces NativeListResultView.level
      (IntrinsicNativeListMapComputation.mapped (NativeListResultView.packedType element (NativeListResultView.constantPredicate result)) result
        (.lam (.snd (.var 0))) (.fst (.pair (packedList element result pairs) relationEvidence)))
      (IntrinsicNativeListMapComputation.mapped (NativeListResultView.packedType element (NativeListResultView.constantPredicate result)) result
        (.lam (.snd (.var 0))) (packedList element result pairs)) :=
    .step (.congAppArg (.betaSigmaFst _ _)) (.refl _)
  have mapped := IntrinsicNativeListMapComputation.mapped_encode NativeListResultView.level
    (NativeListResultView.packedType element (NativeListResultView.constantPredicate result)) result (.lam (.snd (.var 0)))
    (pairs.map (fun pair => .pair pair.1 pair.2))
  have read := IntrinsicNativeListMapComputation.encode_pointwise NativeListResultView.level result
    (fun term => .app (.lam (.snd (.var 0))) term) Tm.snd
    (pairs.map (fun pair => .pair pair.1 pair.2))
    (fun term _ => IntrinsicNativeListMapComputation.Reduces.beta NativeListResultView.level (.snd (.var 0)) term)
  let unpack : Tower.Tm n → Tower.Tm n := fun term => match term with
    | .pair _ second => second
    | other => other
  have projected := IntrinsicNativeListMapComputation.encode_pointwise NativeListResultView.level result Tm.snd unpack
    (pairs.map (fun pair => .pair pair.1 pair.2))
    (by
      intro term present
      obtain ⟨pair, _, rfl⟩ := List.mem_map.mp present
      exact .step (.betaSigmaSnd _ _) (.refl _))
  exact selected.trans (mapped.trans (by
    simpa only [packedList, List.map_map, Function.comp_def, unpack] using read.trans projected))

namespace Controls

def repeatedChildren : List (Tower.Tm 5 × Tower.Tm 5) :=
  [(.var 2, .var 1), (.var 2, .var 0)]

theorem independent_results : TypedEquality.Reduces NativeListResultView.rules
    (NativeListResultView.project (.var 4) (.var 3)
      (.pair (packedList (.var 4) (.var 3) repeatedChildren) (.var 0)))
    (IntrinsicNativeListMapComputation.encode (.var 3) [.var 1, .var 0]) :=
  constructor_results (.var 4) (.var 3) repeatedChildren (.var 0)

theorem exchanged_results_distinct :
    IntrinsicNativeListMapComputation.encode (.var 3 : Tower.Tm 5) [.var 1, .var 0] ≠
      IntrinsicNativeListMapComputation.encode (.var 3) [.var 0, .var 1] := by decide +kernel

/-- These are distinct raw receipt presentations; no typing judgment for
the deliberately unconstrained receipt variables is asserted here. -/
theorem distinct_receipt_presentations :
    Tm.pair (packedList (.var 4 : Tower.Tm 5) (.var 3) repeatedChildren) (.var 0) ≠
      Tm.pair (packedList (.var 4) (.var 3) repeatedChildren) (.var 1) := by decide +kernel

theorem other_receipt_same_results : TypedEquality.Reduces NativeListResultView.rules
    (NativeListResultView.project (.var 4) (.var 3)
      (.pair (packedList (.var 4) (.var 3) repeatedChildren) (.var 1)))
    (IntrinsicNativeListMapComputation.encode (.var 3) [.var 1, .var 0]) :=
  constructor_results (.var 4) (.var 3) repeatedChildren (.var 1)

end Controls

namespace Registered

open Mettapedia.TypeTheory.IndexedPositiveContainer
open FunctionArgumentAdapters
open IndexedInductive.Guest (TermEnv mapEnv)
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestResultArguments IndexedPositiveContainerGuestMethodSpecialization
open IndexedPositiveContainerGuestControls.Lists

/-- A dependent result retains its child alongside its motive witness.
The uniform-result program supplies the further second-projection readout. -/
def results : ResultSyntax I registry Tower.Head where
  viewType _ _ _ _ _ element predicate _ :=
    Intrinsic.listApp (NativeListResultView.packedType element predicate)
  projection _ _ _ _ _ _ _ _ := .lam (.fst (.var 0))
  viewType_substitute := by
    intros
    simp only [Intrinsic.listApp, subst, NativeListResultView.substitute_packedType]
  projection_substitute := by intros; rfl

abbrev code := branchCode

def algebraTypes {k : Nat} (element constructor : Tower.Tm k) : TypeSyntax I Tower.Head k where
  dataType _ := element
  family := element
  constructor _ := constructor

def sourceMethod : Tower.Tm 3 :=
  methodBody indexing (results.viewRegistry containers) code
    (algebraTypes (.var 2) (.var 0)) PUnit.unit (.var 1) (.var 0) []

def sourceMethodSpine : Tower.Tm 3 :=
  .pi (Intrinsic.listApp (.var 2))
    (.pi (Intrinsic.listApp (NativeListResultView.packedType (.var 3) (.var 2)))
      (.app (.var 3) (.app (.var 2) (.var 1))))

theorem source_method_exact : sourceMethod = sourceMethodSpine := by decide +kernel

def parameters : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (sortTm NativeListResultView.level))
    (.pi (.var 0) (sortTm NativeListResultView.level)))
    (.pi (Intrinsic.listApp (.var 1)) (.var 2))

def context : Tower.Ctx 5 :=
  .snoc (.snoc parameters sourceMethod) (Intrinsic.listApp (.var 3))

def types : TypeSyntax I Tower.Head 5 := algebraTypes (.var 4) (.var 2)
def fields : Fin (fieldCount code) → Tower.Tm 5 := fun _ => .var 0
def argumentSlots : List (Slot Tower.Head 5) :=
  slots indexing containers results code types PUnit.unit (.var 3) fields
def inputType : Tower.Tm 5 :=
  NativeListResultView.bundleType (.var 4) (.var 3) (.var 0)
def outputType : Tower.Tm 5 :=
  Intrinsic.listApp (NativeListResultView.packedType (.var 4) (.var 3))
def projection : Tower.Tm 5 := .lam (.fst (.var 0))
def resultType : Tower.Tm 5 := .app (.var 3) (.app (.var 2) (.var 0))
def methodType : Tower.Tm 5 :=
  methodBody indexing (results.viewRegistry containers) code types PUnit.unit (.var 3) (.var 2) []
def methodSpine : Tower.Tm 5 :=
  .pi (Intrinsic.listApp (.var 4))
    (.pi (Intrinsic.listApp (NativeListResultView.packedType (.var 5) (.var 4)))
      (.app (.var 5) (.app (.var 4) (.var 1))))
theorem method_spine_exact : methodType = methodSpine := by decide +kernel
def remainingType : Tower.Tm 5 := hypotheses [outputType] resultType

theorem slots_exact : argumentSlots = [⟨inputType, outputType, projection⟩] := rfl

def adapter : Tower.Tm 5 :=
  IndexedPositiveContainerGuestResultArguments.adapter indexing containers results code types
    PUnit.unit (.var 3) fields (applyFields code fields (.var 1))
def adapterType : Tower.Tm 5 := hypotheses [inputType] resultType
def programme : Tower.Tm 0 := TelescopeAbstraction.closeTerm context adapter
def programmeType : Tower.Tm 0 := TelescopeAbstraction.closeType context adapterType

end Registered

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter
