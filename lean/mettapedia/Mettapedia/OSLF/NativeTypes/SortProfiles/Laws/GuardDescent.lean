import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardControls

open Mettapedia.OSLF.Framework

/-!
# An actual provider query need not descend to sort readout

The finite provider accepts F(Zero) and rejects G(Zero), while their
independent two-sort interpretation agrees. A conditional source guard
cannot therefore be replaced automatically by a predicate of the sort.
This limits an added conditional interpretation; it does not refute the
unconditional equational-center definition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardDescent

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open ModalHypercube (HSort)

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.theory with
    terms := Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.declaredFormers ++
      [{label := "Zero", category := "Term", params := [], syntaxPattern := []}]}

def zero : Pattern := .apply "Zero" []
def first : Pattern := .apply "F" [zero]
def second : Pattern := .apply "G" [zero]

def rule : RewriteRule where
  name := "Question"
  typeContext := [("X", .base "Term")]
  premises := [.relationQuery "recognize" [.fvar "X"]]
  left := .fvar "X"
  right := .fvar "X"
  bindings := some ⟨[("X", [])], []⟩

def provider : ProviderSnapshot :=
  ⟨[⟨"recognize", [.base "Term"], [.input]⟩], [⟨"recognize", [first]⟩]⟩

def environment : Environment where
  language := language
  free := fun _ => none
  provider := provider
  specifications := []

def context : Context := ⟨0, rule, ⟨[("X", [])], []⟩, [], 0, 0⟩
def captured (body : Pattern) : Assignment := [("X", ⟨[], 0, body⟩)]

theorem first_capture_typed : TypedAssignment environment context (captured first) :=
  checkTypedAssignment_sound (by decide +kernel)

theorem second_capture_typed : TypedAssignment environment context (captured second) :=
  checkTypedAssignment_sound (by decide +kernel)

theorem actual_first_query :
    QueryHolds environment context "recognize" [.fvar "X"] (captured first) 0 (captured first) := by
  refine .row (row := ⟨"recognize", [first]⟩)
    (signature := ⟨"recognize", [.base "Term"], [.input]⟩) rfl (by decide +kernel)
    (checkRow_sound (by decide +kernel)) ?_ first_capture_typed
  exact .cons (.input (by decide +kernel)) .nil

theorem actual_second_query_impossible :
    ¬ ∃ index final, QueryHolds environment context "recognize" [.fvar "X"]
      (captured second) index final := by
  rintro ⟨index, final, held⟩
  cases held with
  | row found signature typed arguments _ =>
    cases index with
    | zero =>
      have rowEqual := Option.some.inj found
      subst_vars
      have signatureEqual := Option.some.inj signature
      subst_vars
      cases arguments with
      | cons head tail =>
        cases head with
        | input instantiated =>
          have actual : instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 (captured second) (.fvar "X") = some second := by
            decide +kernel
          have impossible : second = first := Option.some.inj (actual.symm.trans instantiated)
          have different : second ≠ first := by decide +kernel
          exact different impossible
    | succ index =>
      have absent : environment.provider.rows[index + 1]? = none := by
        simp [environment, provider]
      rw [absent] at found
      cases found

def sortModel : Mettapedia.UniversalAlgebra.Model (signature language) HSort :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.model _ (fun _ => .star)

def readout (body : Pattern) : Option HSort :=
  evaluate? language [] sortModel (fun _ => .star) body

theorem source_sorts_agree : readout first = some .star ∧ readout second = some .star := by
  decide +kernel

theorem actual_query_does_not_factor_through_sort :
    ¬ ∃ meaning : Option HSort → Prop, ∀ body,
      (∃ index final, QueryHolds environment context "recognize" [.fvar "X"]
        (captured body) index final) ↔ meaning (readout body) := by
  rintro ⟨meaning, factors⟩
  have accepted := (factors first).mp ⟨0, captured first, actual_first_query⟩
  have same : readout second = readout first := source_sorts_agree.2.trans source_sorts_agree.1.symm
  have rejected := (factors second).mpr (by rw [same]; exact accepted)
  exact actual_second_query_impossible rejected

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardDescent
