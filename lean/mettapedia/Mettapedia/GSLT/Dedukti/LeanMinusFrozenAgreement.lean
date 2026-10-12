import Mettapedia.GSLT.Dedukti.LeanMinusPriority
import Mettapedia.GSLT.Dedukti.LeanMinusOneVariable

/-!
# The frozen strategy with the corrected rules agrees with the explicit substitution

On the translation of levels, the frozen strategy over the corrected rules
(`frozenTheoryCorrected`, `LeanMinusPriority`) and the theory with explicit
level substitution (`leanTheoryExplicit`) relate the same pairs, for every two
levels, with any level variables (`frozenCorrected_agrees_with_explicit`).

The frozen translation `paperLevel frzVar l` reduces to the code `|l|`
(`frozenCorrected_reduces_code`): the fallback turns `v (frz i) i` into the
code of the variable `i`.  The code reduces to `normalCode (normalSet l)` by
the rules of `ΣU` corrected (`code_reduces_normalSet`), which both theories
contain (`pureTheoryExplicit_extends_frozenCorrected`), and that code is normal
in both.  So in both theories conversion of the translations of two levels is
equality of their computed sets.  Inside a declaration, where the explicit
substitution reads a level as `sub x |l|` with the frame variable `x`, the
agreement holds as well (`frozenCorrected_agrees_in_declaration`).

Hence Theorems 2 and 3 of the paper hold for the frozen strategy with the
corrected rules wherever they hold for the explicit substitution: for the
levels in at most one variable, the closed levels among them
(`frozenCorrected_theorem2_one_variable`).  With the paper's rules they fail
(`frozen_disagrees_with_explicit`, `frozen_add_incomplete`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lookupType lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-- The level theory is contained in the frozen strategy over the corrected
rules. -/
theorem pureTheoryExplicit_extends_frozenCorrected : pureTheoryExplicit.Extends frozenTheoryCorrected where
  constType := fun name type declared => by
    have here : lookupType pureSig name = some type := declared
    show lookupType (pureSig ++ sigmaPoly ++ sigmaLean ++ sigmaFrozen) name = some type
    rw [List.append_assoc, List.append_assoc, lookupType_append, here]
    rfl
  body := fun name term defined => by
    have here : lookupBody pureSig name = some term := defined
    show lookupBody (pureSig ++ sigmaPoly ++ sigmaLean ++ sigmaFrozen) name = some term
    rw [List.append_assoc, List.append_assoc, lookupBody_append, here]
    rfl
  rule := fun rule member => List.mem_append_left _ (List.mem_append_left _ member)

/-- `v (frz i) i ⟶ |α_i|`: the fallback on the frozen parameter numbered `i`
gives the code of the variable, with its guard. -/
theorem frozenCorrected_fallback (index : Nat) :
    Reduces frozenTheoryCorrected (ap "v" [frzVar index, numeral index]) (varCode (numeral index)) := by
  have computed : evaluate frozenSig frozenRulesCorrected 1 (ap "v" [frzOf (.var 0), .var 0]) =
      varCode (.var 0) := by
    decide +kernel
  have closed : ∀ value ∈ [numeral index], Closed value := fun value member => by
    rw [List.mem_singleton.mp member]
    exact numeral_closed _
  have filled := Reduces.fill frozenTheoryCorrected_orthogonal.closedBodies [numeral index]
    (Reduces.of_evaluate frozenRulesCorrected_linear computed)
  rw [fill_eq_inst [numeral index] closed _ rfl, fill_eq_inst [numeral index] closed _ rfl] at filled
  simp only [frzVar, frzOf, varCode, guardOf, zeroN] at filled ⊢
  inst_simp at filled ⊢
  exact filled

/-- **The frozen translation of a level reduces to its code.** -/
theorem frozenCorrected_reduces_code :
    ∀ level : LeanLevel, Reduces frozenTheoryCorrected (paperLevel frzVar level) (code level)
  | .zero => .refl
  | .succ level => Reduces.app .refl (frozenCorrected_reduces_code level)
  | .max first second =>
      Reduces.app (Reduces.app .refl (frozenCorrected_reduces_code first))
        (frozenCorrected_reduces_code second)
  | .imax first second =>
      Reduces.app (Reduces.app .refl (frozenCorrected_reduces_code first))
        (frozenCorrected_reduces_code second)
  | .param index => frozenCorrected_fallback index

/-- **For the frozen strategy with the corrected rules, conversion of the
translations of two levels is equality of their computed sets.** -/
theorem frozenCorrected_conv_iff_normalSet {first second : LeanLevel} :
    Conv frozenTheoryCorrected (paperLevel frzVar first) (paperLevel frzVar second) ↔
      normalSet first = normalSet second := by
  have reduces (level : LeanLevel) :
      Reduces frozenTheoryCorrected (paperLevel frzVar level) (normalCode (normalSet level)) :=
    (frozenCorrected_reduces_code level).trans
      ((code_reduces_normalSet level).mono pureTheoryExplicit_extends_frozenCorrected)
  have rigid : ∀ name ∈ setConstructors, ¬ frozenTheoryCorrected.Defines name :=
    setConstructors_rigid (by decide +kernel)
  have headed : frozenTheoryCorrected.Headed := frozenTheoryCorrected_orthogonal.leftAlgebraic.headed
  constructor
  · intro convertible
    by_contra distinct
    exact not_conv_of_normal frozenTheoryCorrected_confluent (normalCode_normal headed rigid _)
      (normalCode_normal headed rigid _) (fun same => distinct (normalCode_injective same))
      (.trans _ _ _ (.symm _ _ (reduces first).conv) (.trans _ _ _ convertible (reduces second).conv))
  · intro same
    exact Joinable.conv ⟨_, reduces first, same ▸ reduces second⟩

/-- **Agreement on the translation of levels**: for every two levels, with any
level variables, the frozen strategy with the corrected rules converts their
frozen translations exactly when the explicit substitution converts their
codes. -/
theorem frozenCorrected_agrees_with_explicit {first second : LeanLevel} :
    Conv frozenTheoryCorrected (paperLevel frzVar first) (paperLevel frzVar second) ↔
      Conv leanTheoryExplicit (code first) (code second) :=
  frozenCorrected_conv_iff_normalSet.trans conv_code_iff_normalSet.symm

/-- **Agreement inside a declaration**: the frozen strategy with the corrected
rules converts the frozen translations of two levels exactly when the explicit
substitution converts their readings in the frame variable of the
declaration. -/
theorem frozenCorrected_agrees_in_declaration {index : Nat} {first second : LeanLevel} :
    Conv frozenTheoryCorrected (paperLevel frzVar first) (paperLevel frzVar second) ↔
      Conv leanTheoryExplicit (levelIn (.var index) first) (levelIn (.var index) second) :=
  frozenCorrected_agrees_with_explicit.trans conv_subVar_iff.symm

/-- **Theorems 2 and 3 for the frozen strategy with the corrected rules**, for
the levels in at most one variable, the closed levels among them. -/
theorem frozenCorrected_theorem2_one_variable {first second : LeanLevel}
    (firstOne : first.OneVariable = true) (secondOne : second.OneVariable = true) :
    Conv frozenTheoryCorrected (paperLevel frzVar first) (paperLevel frzVar second) ↔
      LeanLevel.Equiv first second :=
  frozenCorrected_agrees_with_explicit.trans (theorem2_one_variable firstOne secondOne)

#print axioms pureTheoryExplicit_extends_frozenCorrected
#print axioms frozenCorrected_reduces_code
#print axioms frozenCorrected_conv_iff_normalSet
#print axioms frozenCorrected_agrees_with_explicit
#print axioms frozenCorrected_agrees_in_declaration
#print axioms frozenCorrected_theorem2_one_variable

end Mettapedia.GSLT.Dedukti.LeanMinus
