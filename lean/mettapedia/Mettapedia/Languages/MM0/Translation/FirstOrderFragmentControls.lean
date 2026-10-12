import Mettapedia.Languages.MM0.Translation.FirstOrderFragment
import Mettapedia.Languages.MM0.Translation.FirstOrderControls

/-!
# Controls for the first-order fragment

The propositional theory of the translation controls is generated, read
back from its MM0 tables, and compared with what was authored: the names,
the definitions in order, their bodies, the judgment sort and the rules.

Two developments lie outside the fragment. MM0 admits both. One declares a
quantifier with a bound variable, in the style of `set.mm0`. The other
declares a definition with a dummy variable. Neither has first-order
tables, so neither is the generated theory of a presentation of this class.
A third development tries to use its dummy variable, and MM0 refuses it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderFragmentControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Kernel FirstOrderSyntax FirstOrderRules FirstOrderAdmission
open FirstOrderNaming FirstOrderTheoryPresentations FirstOrderFragment
open FirstOrderControls.Definitions

/-! ## A generated theory, read back -/

/-- The MM0 tables generated from the authored propositional theory. -/
abbrev generated : Theory := chronological presentation

abbrev generatedNames : Names := presentationNames presentation

theorem constructors_read : generatedNames.terms = ["wi", "wn", "wb", "wa", "wo"] := by
  decide +kernel

theorem rules_read : generatedNames.rules = ["ax_1", "ax_2", "ax_3", "ax_mp"] := by
  decide +kernel

/-- The definitions come back in authored order. -/
theorem heads_read :
    (sourceRows generatedNames generated).map (·.head) = ["wb", "wa", "wo"] := by
  decide +kernel

/-- Each body comes back as the authored body over numbered formals. -/
theorem bodies_read :
    generated.definitions.reverse.map
        (fun entry => sourcePattern generatedNames entry.2.expression) =
      [wn (wi (wi p q) (wn (wi q p))), wn (wi p (wn q)), wi (wn p) q] := by
  decide +kernel

/-- The provable sort comes back as the judgment sort. -/
theorem judgments_read : judgmentNames generatedNames generated = ["wff"] := by
  decide +kernel

/-- The read presentation generates the authored definition of conjunction. -/
example :
    (readBack presentation).theory.definitionSignature 3 =
      some ⟨[], .app (.term 1) (.app (.app (.term 0) (.var 0)) (.app (.term 1) (.var 1)))⟩ :=
  (congrFun (read_generated presentation).2.1 3).trans conjunction_body

/-- A name is missing: the names do not fit. -/
example : ¬ (⟨["wff"], ["wi"], []⟩ : Names).Fit generated := by
  intro fit
  exact absurd ((fit.terms 1).mp (by decide +kernel)) (by decide)

/-! ## Two developments outside the fragment -/

/-- A provable sort of formulas, a sort of sets, and a universal quantifier
binding a set variable on which its formula may depend. -/
def quantifierDevelopment : List Admission :=
  [.sort 0 { provable := true }, .sort 1 {}, .term 0 ⟨[.bound 1, .regular 0 {0}], 0, ∅⟩]

/-- MM0 admits the quantifier. -/
theorem quantifier_admitted :
    (Theory.run? {} quantifierDevelopment).map (fun theory => theory.termSignature 0) =
      some (some ⟨[.bound 1, .regular 0 {0}], 0, ∅⟩) := by
  decide +kernel

/-- Its tables are not first-order. -/
theorem quantifier_outside {theory : Theory}
    (ran : Theory.run? {} quantifierDevelopment = some theory) : ¬ theory.FirstOrder := by
  have declared := quantifier_admitted
  rw [ran] at declared
  exact bound_formal_not_firstOrder (Option.some.inj declared)

/-- A constant, and a definition that declares a dummy variable it does
not use. -/
def unusedDummyDevelopment : List Admission :=
  [.sort 0 {}, .term 0 ⟨[], 0, ∅⟩, .definition 1 ⟨[], 0, ∅⟩ ⟨[0], .term 0⟩]

/-- MM0 admits it, dummy variable included. -/
theorem unusedDummy_admitted :
    (Theory.run? {} unusedDummyDevelopment).map
        (fun theory => theory.definitionSignature 1) = some (some ⟨[0], .term 0⟩) := by
  decide +kernel

/-- Its tables are not first-order. -/
theorem unusedDummy_outside {theory : Theory}
    (ran : Theory.run? {} unusedDummyDevelopment = some theory) : ¬ theory.FirstOrder := by
  have declared := unusedDummy_admitted
  rw [ran] at declared
  exact dummy_not_firstOrder (Option.some.inj declared) (by simp)

/-- A definition over a unary constructor whose body applies it to a dummy
variable. -/
def usedDummyDevelopment : List Admission :=
  [.sort 0 {}, .term 0 ⟨[.regular 0 ∅], 0, ∅⟩,
    .definition 1 ⟨[], 0, ∅⟩ ⟨[0], .app (.term 0) (.var 0)⟩]

/-- The body is well typed over the constructor and the dummy variable. -/
example :
    Preterm.infer (fun index => if index = 0 then some ⟨[.regular 0 ∅], 0, ∅⟩ else none)
      [.bound 0] (.app (.term 0) (.var 0)) = some ([], 0) := by
  decide +kernel

/-- MM0 refuses the development all the same. No constructor of a
first-order signature binds a variable, so the dummy variable occurs free
in the body. A dummy variable can be declared there and never used. -/
theorem usedDummy_refused : Theory.run? {} usedDummyDevelopment = none := by
  decide +kernel

end Mettapedia.Languages.MM0.Translation.FirstOrderFragmentControls
