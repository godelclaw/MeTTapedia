import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Variants

/-!
# The variants of an equation side

`gslt:complete:variants` and `gslt:complete:variants-list` are `Complete.Inversion.variants` and
`variantsList`: under matching constructors, binders and closed collections the variants of the
parts are combined, a bag's elements in every order and a vector's in theirs; anywhere else the
instance stands for its display-erased self.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Inversion (perms variants variantsList)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

/-- An encoded pattern is an expression, so no symbol matches it. -/
theorem symbol_unmatched_pattern (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String)
    (pattern : Pattern) :
    SpaceSemantics.matchValue bindings (.symbol name) (CettaWireAtom.encode (encodePattern pattern)) = none := by
  cases pattern <;> simp [encodePattern, CettaWireAtom.encode, SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

/-- Walk a body that selects on data built from bound variables. -/
syntax "complete_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| complete_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call complete_checked; metta_eval [$facts,*] with complete_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, symbol_unmatched_pattern, $extra,*]))

/-- What `gslt:complete:variants` returns. -/
abbrev VariantsAt (state : State) (schema target : Pattern) : Prop :=
  PureReturns runtime [] state (apply "gslt:complete:variants" [patternValue schema, patternValue target]) state
    (patternsValue (variants schema target))

/-- What `gslt:complete:variants-list` returns. -/
abbrev VariantsListAt (state : State) (patterns targets : List Pattern) : Prop :=
  PureReturns runtime [] state (apply "gslt:complete:variants-list" [patternsValue patterns, patternsValue targets])
    state (rowsValue (variantsList patterns targets))

@[metta_head "gslt:complete:variants-list"]
theorem variants_list_of (state : State) : ∀ (patterns : List Pattern),
    (∀ pattern ∈ patterns, ∀ target, VariantsAt state pattern target) →
    ∀ targets, VariantsListAt state patterns targets
  | [], _, [] => by
    complete_eval unfolding [patternsValue, rowsValue, encodePatterns, variantsList]
  | [], _, target :: targets => by
    complete_eval unfolding [patternsValue, rowsValue, encodePatterns, variantsList]
  | pattern :: patterns, _, [] => by
    complete_eval unfolding [patternsValue, rowsValue, encodePatterns, variantsList]
  | pattern :: patterns, each, target :: targets => by
    have heads := each pattern (by simp) target
    have tails := variants_list_of state patterns (fun other member => each other (by simp [member])) targets
    have product := product_returns state (variantsList patterns targets) (variants pattern target)
    rw [VariantsListAt, variantsList]
    complete_eval [heads, tails, product]
      unfolding [patternsValue, rowsValue, encodePatterns, VariantsAt, VariantsListAt]

/-- The fallthrough: the instance, erased. -/
syntax "variant_other" term:max : tactic
macro_rules
  | `(tactic| variant_other $erased) => `(tactic|
      (simp only [VariantsAt, variants]
       complete_eval [$erased]
         unfolding [patternValue, patternsValue, encodePattern, encodePatterns, encodeBinder, encodeRest,
           InferenceCettaWire.encodeList]))

/-- **`gslt:complete:variants` is `Inversion.variants`.** -/
@[metta_head "gslt:complete:variants"]
theorem variants_returns (state : State) (schema : Pattern) : ∀ target, VariantsAt state schema target := by
  induction schema using Pattern.inductionOn with
  | hbvar index =>
    intro target
    have erased := erase_returns state target
    cases target with
    | collection actual targets other => cases other <;> variant_other erased
    | _ => variant_other erased
  | hfvar name =>
    intro target
    have erased := erase_returns state target
    cases target with
    | collection actual targets other => cases other <;> variant_other erased
    | _ => variant_other erased
  | hsubst body replacement bodyIH replacementIH =>
    intro target
    have erased := erase_returns state target
    cases target with
    | collection actual targets other => cases other <;> variant_other erased
    | _ => variant_other erased
  | happly label patterns ih =>
    intro target
    have erased := erase_returns state target
    cases target with
    | apply constructor targets =>
      have rows := variants_list_of state patterns ih targets
      have built := wrap_each_returns state (.apply constructor) (variantsList patterns targets)
      simp only [VariantsAt, variants]
      complete_eval [rows, built]
        unfolding [patternValue, patternsValue, encodePattern, encodePatterns, Shape.term, Shape.build, VariantsListAt]
    | collection actual targets other => cases other <;> variant_other erased
    | _ => variant_other erased
  | hlambda binder body ih =>
    intro target
    have erased := erase_returns state target
    cases target with
    | lambda other inner =>
      have each := lambda_each_returns state (variants body inner)
      simp only [VariantsAt, variants]
      complete_eval [ih inner, each]
        unfolding [patternValue, patternsValue, encodePattern, encodeBinder, VariantsAt]
    | collection actual targets other => cases other <;> variant_other erased
    | _ => variant_other erased
  | hmultiLambda arity binders body ih =>
    intro target
    have erased := erase_returns state target
    cases target with
    | multiLambda actual others inner =>
      have each := multi_lambda_each_returns state actual (variants body inner)
      simp only [VariantsAt, variants]
      complete_eval [ih inner, each]
        unfolding [patternValue, patternsValue, encodePattern, InferenceCettaWire.encodeList, VariantsAt]
    | collection actual targets other => cases other <;> variant_other erased
    | _ => variant_other erased
  | hcollection kind patterns rest ih =>
    intro target
    have erased := erase_returns state target
    cases rest with
    | some name =>
      cases target with
      | collection actual targets other =>
        cases other with
        | some other => variant_other erased
        | none =>
          have count : PureReturns runtime [] state (apply "gslt:automata:length" [patternsValue patterns]) state
              (number patterns.length) := by
            simpa only [patternsValue, encodePatterns_eq_encodeList] using
              complete_length_returns encodePattern state patterns
          have front := take_patterns_returns state patterns.length targets
          have remaining := drop_patterns_returns state patterns.length targets
          have back := erase_list_of state (targets.drop patterns.length) (fun pattern _ => erase_returns state pattern)
          have rows := variants_list_of state patterns ih (targets.take patterns.length)
          have joined := append_each_returns state ((targets.drop patterns.length).map Pattern.eraseBinderMetadata)
            (variantsList patterns (targets.take patterns.length))
          have orders := perms_all_returns state ((variantsList patterns (targets.take patterns.length)).map
            (· ++ (targets.drop patterns.length).map Pattern.eraseBinderMetadata))
          have plain := wrap_each_returns state (.collection actual)
            ((variantsList patterns (targets.take patterns.length)).map
              (· ++ (targets.drop patterns.length).map Pattern.eraseBinderMetadata))
          have ordered := wrap_each_returns state (.collection actual)
            (((variantsList patterns (targets.take patterns.length)).map
              (· ++ (targets.drop patterns.length).map Pattern.eraseBinderMetadata)).flatMap perms)
          cases kind with
          | vec =>
            have shape : variants (.collection .vec patterns (some name)) (.collection actual targets none) =
                ((variantsList patterns (targets.take patterns.length)).map
                  (· ++ (targets.drop patterns.length).map Pattern.eraseBinderMetadata)).map
                    (Shape.build (.collection actual)) := by
              simp only [variants, if_true, List.map_map]
              rfl
            rw [VariantsAt, shape]
            complete_eval [count, front, remaining, back, rows, joined, plain]
              unfolding [patternValue, patternsValue, encodePattern, encodePatterns, encodeRest, encodeCollectionType,
                Shape.term, VariantsListAt]
          | hashBag =>
            have shape : variants (.collection .hashBag patterns (some name)) (.collection actual targets none) =
                (((variantsList patterns (targets.take patterns.length)).map
                  (· ++ (targets.drop patterns.length).map Pattern.eraseBinderMetadata)).flatMap perms).map
                    (Shape.build (.collection actual)) := by
              simp only [variants, reduceCtorEq, if_false, List.flatMap_map]
              rfl
            rw [VariantsAt, shape]
            complete_eval [count, front, remaining, back, rows, joined, orders, ordered]
              unfolding [patternValue, patternsValue, encodePattern, encodePatterns, encodeRest, encodeCollectionType,
                Shape.term, VariantsListAt]
          | hashSet =>
            have shape : variants (.collection .hashSet patterns (some name)) (.collection actual targets none) =
                (((variantsList patterns (targets.take patterns.length)).map
                  (· ++ (targets.drop patterns.length).map Pattern.eraseBinderMetadata)).flatMap perms).map
                    (Shape.build (.collection actual)) := by
              simp only [variants, reduceCtorEq, if_false, List.flatMap_map]
              rfl
            rw [VariantsAt, shape]
            complete_eval [count, front, remaining, back, rows, joined, orders, ordered]
              unfolding [patternValue, patternsValue, encodePattern, encodePatterns, encodeRest, encodeCollectionType,
                Shape.term, VariantsListAt]
      | _ => variant_other erased
    | none =>
      cases target with
      | collection actual targets other =>
        cases other with
        | some name => variant_other erased
        | none =>
          have rows := variants_list_of state patterns ih targets
          have orders := perms_all_returns state (variantsList patterns targets)
          have plain := wrap_each_returns state (.collection actual) (variantsList patterns targets)
          have ordered := wrap_each_returns state (.collection actual) ((variantsList patterns targets).flatMap perms)
          cases kind <;>
          · simp only [VariantsAt, variants]
            complete_eval [rows, orders, plain, ordered]
              unfolding [patternValue, patternsValue, encodePattern, encodePatterns, encodeRest, encodeCollectionType,
                Shape.term, Shape.build, VariantsListAt]
      | _ => variant_other erased

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
