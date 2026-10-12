import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SignatureGluing
import Mettapedia.GSLT.Dedukti.Interpretation

/-!
# Closed-term interpretations of module constant inventories

A module's exposed constants are interpreted by closed lambda-Pi terms.
The existing Dedukti interpretation extends these assignments to terms and
supplies its lifting, substitution and context-filling laws. Constants
outside the declared inventory retain their spelling. The scope predicate
records precisely where branch interpretations agree with the joined one.

This is an interpretation of constant inventories. Types, definitions and
rewrite rules need their independent preservation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ClosedTermGluing

open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.LanguageDef.LF

variable {Origin Body : Type} [DecidableEq Origin] [DecidableEq Body]

abbrev ClosedTerm := {term : LF.Term // Closed term}
abbrev Assignment (p : Presentation Origin String Body) :=
  DependentAssignment (fun _ : Entry Origin String Body => ClosedTerm) p

/-- Label uniqueness is proved by the existing origin-sensitive validity
law. The selection is mathematical; it makes no parser or runtime claim. -/
noncomputable def interpretation (p : Presentation Origin String Body)
    (assignment : Assignment p) : Interpretation where
  meaning name := if found : ∃ entry : Member p, entry.val.label = name
    then (assignment found.choose).val else .con name
  closed name := by
    split
    · exact (assignment _).property
    · exact .con

theorem interpretation_meaning (p : Presentation Origin String Body)
    (assignment : Assignment p) (entry : Member p) :
    (interpretation p assignment).meaning entry.val.label = (assignment entry).val := by
  have found : ∃ e : Member p, e.val.label = entry.val.label := ⟨entry, rfl⟩
  have same : found.choose = entry := Subtype.ext
    (p.property _ found.choose.property _ entry.property (.inr found.choose_spec))
  simp only [interpretation, dif_pos found]
  exact congrArg (fun e => (assignment e).val) same

theorem interpretation_outside (p : Presentation Origin String Body)
    (assignment : Assignment p) (name : String)
    (outside : ¬ ∃ entry : Member p, entry.val.label = name) :
    (interpretation p assignment).meaning name = .con name := by
  simp only [interpretation, dif_neg outside]

/-- All constants are declared locally; variables may still be open.
Scope through binders is retained by the existing lambda-Pi syntax. -/
inductive Supported (p : Presentation Origin String Body) : LF.Term → Prop where
  | var (index : Nat) : Supported p (.var index)
  | sort (level : LF.Srt) : Supported p (.srt level)
  | con (entry : Member p) : Supported p (.con entry.val.label)
  | pi {domain body : LF.Term} : Supported p domain → Supported p body →
      Supported p (.pi domain body)
  | lam {domain body : LF.Term} : Supported p domain → Supported p body →
      Supported p (.lam domain body)
  | app {function argument : LF.Term} : Supported p function → Supported p argument →
      Supported p (.app function argument)

theorem apply_eq_on_supported {p : Presentation Origin String Body}
    (first second : Interpretation)
    (agree : ∀ entry : Member p, first.meaning entry.val.label = second.meaning entry.val.label)
    {term : LF.Term} (supported : Supported p term) : first.apply term = second.apply term := by
  induction supported with
  | var _ => rfl
  | sort _ => rfl
  | con entry => exact agree entry
  | pi _ _ ihDomain ihBody => exact congrArg₂ LF.Term.pi ihDomain ihBody
  | lam _ _ ihDomain ihBody => exact congrArg₂ LF.Term.lam ihDomain ihBody
  | app _ _ ihFunction ihArgument => exact congrArg₂ LF.Term.app ihFunction ihArgument

theorem glued_meaning_left {p q r : Presentation Origin String Body}
    (joined : join p q = some r) (left : Assignment p) (right : Assignment q)
    (entry : Member p) :
    (interpretation r (glueDependent joined left right)).meaning entry.val.label =
      (interpretation p left).meaning entry.val.label := by
  have image := interpretation_meaning r (glueDependent joined left right)
    (includeLeft joined entry)
  exact image.trans ((congrArg Subtype.val (glueDependent_left joined left right entry)).trans
    (interpretation_meaning p left entry).symm)

theorem glued_meaning_right {p q r : Presentation Origin String Body}
    (joined : join p q = some r) (left : Assignment p) (right : Assignment q)
    (agree : ∀ entry hp hq, left ⟨entry, hp⟩ = right ⟨entry, hq⟩)
    (entry : Member q) :
    (interpretation r (glueDependent joined left right)).meaning entry.val.label =
      (interpretation q right).meaning entry.val.label := by
  have image := interpretation_meaning r (glueDependent joined left right)
    (includeRight joined entry)
  exact image.trans
    ((congrArg Subtype.val (glueDependent_right joined left right agree entry)).trans
      (interpretation_meaning q right entry).symm)

theorem glued_apply_left {p q r : Presentation Origin String Body}
    (joined : join p q = some r) (left : Assignment p) (right : Assignment q)
    {term : LF.Term} (supported : Supported p term) :
    (interpretation r (glueDependent joined left right)).apply term =
      (interpretation p left).apply term :=
  apply_eq_on_supported _ _ (glued_meaning_left joined left right) supported

theorem glued_apply_right {p q r : Presentation Origin String Body}
    (joined : join p q = some r) (left : Assignment p) (right : Assignment q)
    (agree : ∀ entry hp hq, left ⟨entry, hp⟩ = right ⟨entry, hq⟩)
    {term : LF.Term} (supported : Supported q term) :
    (interpretation r (glueDependent joined left right)).apply term =
      (interpretation q right).apply term :=
  apply_eq_on_supported _ _ (glued_meaning_right joined left right agree) supported

/-- This law applies to arbitrary terms, including substitutions whose
values mention constants outside either component's inventory. -/
theorem glued_subst0 {p q r : Presentation Origin String Body}
    (joined : join p q = some r) (left : Assignment p) (right : Assignment q)
    (argument body : LF.Term) :
    (interpretation r (glueDependent joined left right)).apply
        (LFTyping.subst0 argument body) =
      LFTyping.subst0
        ((interpretation r (glueDependent joined left right)).apply argument)
        ((interpretation r (glueDependent joined left right)).apply body) :=
  Interpretation.apply_subst0 _ argument body

/-- Rule instances are interpreted in the target assignment, so target
values need not belong to a component's source signature. -/
theorem glued_instantiate {p q r : Presentation Origin String Body}
    (joined : join p q = some r) (left : Assignment p) (right : Assignment q)
    (assignment : Nat → LF.Term) (template : LF.Term) (depth : Nat) :
    (interpretation r (glueDependent joined left right)).apply
        (Dedukti.instantiate assignment depth template) =
      Dedukti.instantiate
        (fun index => (interpretation r (glueDependent joined left right)).apply
          (assignment index)) depth
        ((interpretation r (glueDependent joined left right)).apply template) :=
  Interpretation.apply_instantiate _ assignment template depth

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ClosedTermGluing
