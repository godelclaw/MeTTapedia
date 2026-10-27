import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Judgments
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
import Mettapedia.Logic.HOL.Soundness

/-!
# Entailment proved through higher-order logic

An entailment `φ ⊑ ψ` translates to the closed higher-order formula `∀ x. φ̂ x → ψ̂ x` (`entailmentFormula`), from the
translations of the two native types into higher-order logic over the generators. A derivation of it in the
natural-deduction calculus of higher-order logic proves the entailment in every native structure
(`sat_of_entailmentTheorem`), by the soundness of the calculus for Henkin models and the exactness of the translation
in the standard model of a native structure; so it proves the entailment at every type of every language
(`entails_of_entailmentTheorem`). A refuted entailment therefore has no derivation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern TypeExpr)
open Mettapedia.Logic.HOL (Derivation)

/-- **The higher-order formula of an entailment**: at every element, the premise's translation implies the
conclusion's. -/
def entailmentFormula (premise conclusion : Formula 0) : Mettapedia.Logic.HOL.ClosedFormula HigherOrder.Constant :=
  .all (.imp (.app (Mettapedia.Logic.HOL.weaken (HigherOrder.translate premise)) (.var .vz))
    (.app (Mettapedia.Logic.HOL.weaken (HigherOrder.translate conclusion)) (.var .vz)))

/-- **A derivation of the entailment's formula proves it in every native structure.** -/
theorem sat_of_entailmentTheorem {premise conclusion : Formula 0}
    (derived : Derivation.Theorem HigherOrder.Constant (entailmentFormula premise conclusion)) {Carrier : Type}
    (S : NativeStructure Carrier) (point : Carrier) (holds : S.sat Env.closed premise point) :
    S.sat Env.closed conclusion point := by
  have valid := Mettapedia.Logic.HOL.Soundness.derivation_sound derived (M := HigherOrder.standardModel S)
    (ρ := Mettapedia.OSLF.Framework.NativeBasis.nowhere (HigherOrder.presentation S)) (fun index => nomatch index)
    (fun _ member => nomatch member)
  have premiseDenotes := (HigherOrder.denote_translate_closed (S := S) premise point).mpr holds
  refine (HigherOrder.denote_translate_closed (S := S) conclusion point).mp ?_
  simp only [entailmentFormula, Mettapedia.Logic.HOL.PreModel.denote] at valid
  let state : Mettapedia.Logic.HOL.Ty.denote.{0, 0} (HigherOrder.standardModel S).Carrier
      (Mettapedia.OSLF.Framework.NativeBasis.stateTy ()) := ULift.up point
  let nowhere : (HigherOrder.standardModel S).Valuation [] :=
    Mettapedia.OSLF.Framework.NativeBasis.nowhere (HigherOrder.presentation S)
  have shift : ∀ formula : Formula 0,
      (HigherOrder.standardModel S).denote (Mettapedia.Logic.HOL.weaken (HigherOrder.translate formula))
          ((HigherOrder.standardModel S).extend nowhere state) =
        (HigherOrder.standardModel S).denote (HigherOrder.translate formula) nowhere :=
    fun formula => Mettapedia.Logic.HOL.Soundness.denote_weaken _ _ _ _
  have implies : ((HigherOrder.standardModel S).denote (Mettapedia.Logic.HOL.weaken (HigherOrder.translate premise))
        ((HigherOrder.standardModel S).extend nowhere state) state).down →
      ((HigherOrder.standardModel S).denote (Mettapedia.Logic.HOL.weaken (HigherOrder.translate conclusion))
        ((HigherOrder.standardModel S).extend nowhere state) state).down :=
    valid state (HigherOrder.full S _ _)
  rw [shift, shift] at implies
  exact implies premiseDenotes

/-- **A derivation proves the entailment at every type of every language.** -/
theorem entails_of_entailmentTheorem {premise conclusion : Formula 0}
    (derived : Derivation.Theorem HigherOrder.Constant (entailmentFormula premise conclusion)) (T : NativeStructure Pattern)
    (type : TypeExpr) : Entails T type premise conclusion :=
  fun value _ _ holds => sat_of_entailmentTheorem derived T value holds

/-- **Every native type entails itself**, by a derivation. -/
theorem entailmentFormula_refl (formula : Formula 0) :
    Derivation.Theorem HigherOrder.Constant (entailmentFormula formula formula) :=
  .allI (.impI (.hyp (List.mem_cons_self ..)))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
