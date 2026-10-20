import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison
import Mettapedia.OSLF.SatisfactionUndecidable

open Mettapedia.OSLF.Framework

/-!
# Independent decision procedures agree on their shared Partrec fragment

The translator refuses unsupported formulas independently of semantic
refutation. The actual generated occurrence engine and the original machine
checker agree at their respective earned budgets, for every admitted open
configuration and every formula in the shared finite modal fragment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.SatisfactionUndecidable
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison
open GSLTTypeSynthesis

def fromLegacy? : OSLFFormula → Option (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty)
  | .top => some .top
  | .bot => some .bottom
  | .and first second => (fromLegacy? first).bind fun left =>
      (fromLegacy? second).map fun right => .conj left right
  | .or first second => (fromLegacy? first).bind fun left =>
      (fromLegacy? second).map fun right => .disj left right
  | .dia body => (fromLegacy? body).map .possibility
  | _ => none

def noLeaves (bound : List TypeExpr) : Empty → Test (theory bound) (Source bound) :=
  fun impossible => nomatch impossible

theorem translation_recognizes_fragment (formula : OSLFFormula) :
    (∃ generated, fromLegacy? formula = some generated) ↔ modalSearch formula = true := by
  induction formula with
  | top => simp [fromLegacy?, modalSearch]
  | bot => simp [fromLegacy?, modalSearch]
  | and first second firstIH secondIH =>
      simp only [fromLegacy?, modalSearch, Bool.and_eq_true, Option.bind_eq_some_iff,
        Option.map_eq_some_iff]
      aesop
  | or first second firstIH secondIH =>
      simp only [fromLegacy?, modalSearch, Bool.and_eq_true, Option.bind_eq_some_iff,
        Option.map_eq_some_iff]
      aesop
  | dia body ih =>
      simp only [fromLegacy?, modalSearch, Option.map_eq_some_iff]
      aesop
  | atom | imp | box | var | mu | emptyColl | cut | headed => simp [fromLegacy?, modalSearch]

theorem denotation_iff_original (bound : List TypeExpr) (interpretation : AtomSem)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (source : Pattern) (typed : Source bound source) :
    denotation (noLeaves bound) generated (.empty _) source ↔
      sem Mettapedia.Languages.PartrecMachine.Reduces interpretation formula source := by
  induction formula generalizing generated source with
  | top =>
      have same := Option.some.inj translated
      subst generated
      rfl
  | bot =>
      have same := Option.some.inj translated
      subst generated
      rfl
  | and first second firstIH secondIH =>
      simp only [fromLegacy?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
      obtain ⟨left, leftTranslated, right, rightTranslated, same⟩ := translated
      subst generated
      exact and_congr (firstIH leftTranslated source typed) (secondIH rightTranslated source typed)
  | or first second firstIH secondIH =>
      simp only [fromLegacy?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
      obtain ⟨left, leftTranslated, right, rightTranslated, same⟩ := translated
      subst generated
      exact or_congr (firstIH leftTranslated source typed) (secondIH rightTranslated source typed)
  | dia body ih =>
      obtain ⟨inner, innerTranslated, same⟩ := Option.map_eq_some_iff.mp translated
      subst generated
      rw [show denotation (noLeaves bound) (.possibility inner) (.empty _) source ↔
          ∃ target, (theory bound).Step source target ∧ denotation (noLeaves bound) inner (.empty _) target from
        gsltDiamond_spec (theory bound) (denotation (noLeaves bound) inner).1 source]
      change (∃ target, (theory bound).Step source target ∧ denotation (noLeaves bound) inner (.empty _) target) ↔
        ∃ target, Mettapedia.Languages.PartrecMachine.Reduces source target ∧
          sem Mettapedia.Languages.PartrecMachine.Reduces interpretation body target
      constructor
      · rintro ⟨target, step, holds⟩
        have original := (generated_step_iff_original bound typed).mp step
        exact ⟨target, original, (ih innerTranslated target (original_target_admitted bound typed original)).mp holds⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨target, (generated_step_iff_original bound typed).mpr step,
          (ih innerTranslated target (original_target_admitted bound typed step)).mpr holds⟩
  | atom | imp | box | var | mu | emptyColl | cut | headed =>
      simp [fromLegacy?] at translated

def run (bound : List TypeExpr) (generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty)
    (source : Pattern) (budget : Nat) : Option Bool :=
  (check (backend bound) (noLeaves bound) generated source budget).answer

def effectiveBound (bound : List TypeExpr) (generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty)
    (source : Pattern) : Nat :=
  workBound (backend bound) (noLeaves bound) generated source

theorem executable_answers_agree (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (source : Pattern) (typed : Source bound source) :
    run bound generated source (effectiveBound bound generated source) =
      some (decideModalSearch formula source) := by
  have supported := (translation_recognizes_fragment formula).mp ⟨generated, translated⟩
  have correct := denotation_iff_original bound (fun _ _ => False) translated source typed
  obtain ⟨answer, read⟩ := checked_complete (backend bound) (noLeaves bound) generated source typed
    (effectiveBound bound generated source) (Nat.le_refl _)
  change run bound generated source (effectiveBound bound generated source) = some answer at read
  rw [read]
  apply congrArg some
  cases answer with
  | true =>
      have positive := checked_positive (backend bound) (noLeaves bound) generated source _ read
      exact ((decideModalSearch_iff supported source).mpr (correct.mp positive)).symm
  | false =>
      have negative := checked_negative (backend bound) (noLeaves bound) generated source _ read
      cases actual : decideModalSearch formula source with
      | false => rfl
      | true => exact (negative (correct.mpr ((decideModalSearch_iff supported source).mp actual))).elim

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison
