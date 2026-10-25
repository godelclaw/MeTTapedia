import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Recovering telescope formation from its closed product type

Formation of the actual closed Pi telescope supplies formation of every
original domain and of the remaining body in that telescope. The result
retains the body universe supplied by Pi formation; it does not identify it
with the universe of the complete closed product. No normalization or
conversion-boundary premise is required for this syntactic inversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TelescopeAbstraction

open FormationSensitive

variable {Head : Type} {R : Rules Head} {n : Nat}

theorem formation_of_closeType (context : Ctx Head n) {type : Tm Head n} {level : Head}
    (isUniverse : R.isUniverse level)
    (formed : Typing R .nil (closeType context type) (.head level)) :
    ContextFormation R context ∧
      ∃ bodyLevel, R.isUniverse bodyLevel ∧ Typing R context type (.head bodyLevel) := by
  induction context generalizing level with
  | nil => exact ⟨.nil, level, isUniverse, formed⟩
  | snoc prior domain ih =>
      obtain ⟨priorFormed, productLevel, productUniverse, productFormed⟩ := ih isUniverse formed
      obtain ⟨domainLevel, bodyLevel, _, domainFormed, domainUniverse, bodyFormed, bodyUniverse, _⟩ :=
        productFormed.piFormation
      exact ⟨.snoc priorFormed domainFormed domainUniverse, bodyLevel, bodyUniverse, bodyFormed⟩

theorem closeTerm_mapHead {TargetHead : Type} (map : Head → TargetHead)
    (context : Ctx Head n) (term : Tm Head n) :
    (closeTerm context term).mapHead map = closeTerm (context.mapHead map) (term.mapHead map) := by
  induction context with
  | nil => rfl
  | snoc prior domain ih =>
      simpa only [closeTerm, Ctx.mapHead, Tm.mapHead] using ih (term := .lam term)

theorem closeType_mapHead {TargetHead : Type} (map : Head → TargetHead)
    (context : Ctx Head n) (type : Tm Head n) :
    (closeType context type).mapHead map = closeType (context.mapHead map) (type.mapHead map) := by
  induction context with
  | nil => rfl
  | snoc prior domain ih =>
      simpa only [closeType, Ctx.mapHead, Tm.mapHead] using ih (type := .pi domain type)

#print axioms formation_of_closeType
#print axioms closeTerm_mapHead
#print axioms closeType_mapHead

end TelescopeAbstraction
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
