import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantRenamingTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerLiteralConstants

/-!
# Formation-sensitive literal and user-constant renaming

The existing nonidentity String/Color and banana/red permutation preserves
and reflects every formation-sensitive judgment of its declared profile.
Both the source literal and its renamed user constant have actual formed
judgments. A value-name collapse fixing the distinct sort names cannot satisfy
the primitive declaration-preservation condition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace TypedEquality.TowerLiterals.FormationControls

theorem literal_formed : FormationSensitive.Judgment withLiteral .nil
    (.const banana) (.const String) := by
  have universeTyped : FormationSensitive.Typing withLiteral .nil universe0
      (.head (.sort (.succ Tower.zero))) := .headType (.sort Tower.zero)
  have stringKnown : withLiteral.constantType String = some universe0 := rfl
  have stringTyped : FormationSensitive.Typing withLiteral .nil (.const String) universe0 := by
    simpa only [Tm.liftClosed_at_zero] using
      (FormationSensitive.Typing.const (Γ := .nil) stringKnown universeTyped (.sort _))
  have literalKnown : withLiteral.constantType banana = some (.const String) := rfl
  refine ⟨.nil, ?_⟩
  simpa only [Tm.liftClosed_at_zero] using
    (FormationSensitive.Typing.const (Γ := .nil) literalKnown stringTyped (.sort _))

theorem renamed_literal_formed : FormationSensitive.Judgment withLiteral .nil
    (.const red) (.const Color) := by
  simpa only [Ctx.mapConst, Tm.mapConst, show swap banana = red by decide,
    show swap String = Color by decide] using literal_formed.mapConst swap_symmetry

theorem all_judgments_swap {n : Nat} {context : Ctx Tower.Head n}
    {term type : Tm Tower.Head n} :
    FormationSensitive.Judgment withLiteral context term type ↔
      FormationSensitive.Judgment withLiteral (context.mapConst swap)
        (term.mapConst swap) (type.mapConst swap) :=
  FormationSensitive.Judgment.mapConst_iff swap_symmetry swap_symmetry swap_involution

theorem literal_beta : Step withLiteral.headEq
    (.app (.lam (.var 0)) (.const banana) : Tm Tower.Head 0)
    (.const banana) withLiteral.computation := .betaPi _ _

theorem renamed_beta : Step withLiteral.headEq
    (.app (.lam (.var 0)) (.const red) : Tm Tower.Head 0)
    (.const red) withLiteral.computation := by
  simpa only [Tm.mapConst, show swap banana = red by decide] using literal_beta.mapConst swap_symmetry

def collapse (name : DeclName) : DeclName := if name = banana then red else name

theorem collapse_not_morphism : ¬ RulesRenaming withLiteral withLiteral collapse := by
  intro morphism
  have types := morphism.identified_types (left := banana) (right := red)
    (leftType := .const String) (rightType := .const Color) rfl rfl (by decide)
  have different : (Tm.const String : Tm Tower.Head 0) ≠ .const Color := by decide
  apply different
  simpa only [Tm.mapConst, collapse, show String ≠ banana by decide,
    show Color ≠ banana by decide, if_false] using types

#print axioms literal_formed
#print axioms renamed_literal_formed
#print axioms all_judgments_swap
#print axioms collapse_not_morphism

end TypedEquality.TowerLiterals.FormationControls

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
