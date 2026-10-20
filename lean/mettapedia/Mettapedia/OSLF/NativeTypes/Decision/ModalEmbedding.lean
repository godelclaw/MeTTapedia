import Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus
import Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula

/-!
# The shared modal fragment in the existing fixed-point language

The existing native formula's propositional and outgoing-modal fragment embeds
into the modal μ-calculus. Leaves become explicit environment slots. Spatial
separation is refused by this translation and continues to use its spatial
strategy; it is never interpreted as an opaque Boolean observation here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.ModalEmbedding

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus
open Reference.Core (Test denotation)

universe u w
variable {Leaf : Type w} {n : Nat}

def translate (index : Leaf → Fin n) : Reference.Core.Formula Leaf → Option (Formula Traversal n)
  | .atom leaf => some (.var (index leaf))
  | .top => some .tt
  | .bottom => some .ff
  | .neg inner => (.neg ·) <$> translate index inner
  | .conj left right => return .conj (← translate index left) (← translate index right)
  | .disj left right => return .disj (← translate index left) (← translate index right)
  | .imp left right => return .disj (.neg (← translate index left)) (← translate index right)
  | .possibility inner => (.diamond .future ·) <$> translate index inner
  | .outgoingUniversal inner => (.box .future ·) <$> translate index inner
  | .separating _ _ _ => none

theorem meaning {system : Mettapedia.GSLT.GSLT.{u}} {admitted : system.Term → Prop}
    (tests : Leaf → Test system admitted)
    (spatial : Spatial.SpatialTheory system) (index : Leaf → Fin n)
    (environment : Env system.Term n)
    (leaves : ∀ leaf state, state ∈ environment (index leaf) ↔ (tests leaf).predicate state)
    (formula : Reference.Core.Formula Leaf) (translated : Formula Traversal n)
    (success : translate index formula = some translated) (state : system.Term) :
    satisfies (transitionSystem (gsltSpan system)) environment translated state ↔
      denotation tests formula spatial state := by
  classical
  induction formula generalizing translated state with
  | atom leaf =>
      cases Option.some.inj success
      exact leaves leaf state
  | top | bottom => cases Option.some.inj success; rfl
  | separating _ _ _ => cases success
  | neg inner ih =>
      cases innerEq : translate index inner with
      | none => simp [translate, innerEq] at success
      | some child =>
        simp [translate, innerEq] at success
        subst translated
        exact not_congr (ih child innerEq state)
  | conj left right il ir =>
      cases leftEq : translate index left <;> cases rightEq : translate index right <;>
        simp [translate, leftEq, rightEq] at success
      subst translated
      exact and_congr (il _ leftEq state) (ir _ rightEq state)
  | disj left right il ir =>
      cases leftEq : translate index left <;> cases rightEq : translate index right <;>
        simp [translate, leftEq, rightEq] at success
      subst translated
      exact or_congr (il _ leftEq state) (ir _ rightEq state)
  | imp left right il ir =>
      cases leftEq : translate index left <;> cases rightEq : translate index right <;>
        simp [translate, leftEq, rightEq] at success
      subst translated
      change (¬ _ ∨ _) ↔ (_ → _)
      rw [il _ leftEq state, ir _ rightEq state]
      tauto
  | possibility inner ih =>
      cases innerEq : translate index inner with
      | none => simp [translate, innerEq] at success
      | some child =>
        simp [translate, innerEq] at success
        subst translated
        change (∃ target, (∃ event : (gsltSpan system).Edge, _ ∧ _) ∧ _) ↔
          gsltDiamond system (denotation tests inner spatial).val state
        rw [gsltDiamond_spec]
        simp only [gsltSpan_edge_iff_step, ih child innerEq]
  | outgoingUniversal inner ih =>
      cases innerEq : translate index inner with
      | none => simp [translate, innerEq] at success
      | some child =>
        simp [translate, innerEq] at success
        subst translated
        change (∀ target, (∃ event : (gsltSpan system).Edge, _ ∧ _) → _) ↔
          (∀ target, system.Step state target → denotation tests inner spatial target)
        simp only [gsltSpan_edge_iff_step, ih child innerEq]

theorem separation_refused (index : Leaf → Fin n) (former : Nat)
    (left right : Reference.Core.Formula Leaf) :
    translate index (.separating former left right) = none := rfl

open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary

theorem translated_positive (index : Leaf → Fin n) (formula : Reference.Core.Formula Leaf)
    (translated : Formula Traversal n) (success : translate index formula = some translated) :
    fixedPointsPositive translated = true := by
  induction formula generalizing translated with
  | atom _ | top | bottom => cases Option.some.inj success; rfl
  | separating _ _ _ => cases success
  | neg inner ih | possibility inner ih | outgoingUniversal inner ih =>
    cases innerEq : translate index inner with
    | none => simp [translate, innerEq] at success
    | some child =>
      simp [translate, innerEq] at success
      subst translated
      exact ih child innerEq
  | conj left right il ir | disj left right il ir | imp left right il ir =>
    cases leftEq : translate index left <;> cases rightEq : translate index right <;>
      simp [translate, leftEq, rightEq] at success
    all_goals subst translated
    all_goals simp only [fixedPointsPositive, Bool.and_eq_true]
    all_goals exact ⟨il _ leftEq, ir _ rightEq⟩

/-- The finite strategy checks the same native predicate as the original
shared modal checker on every successfully translated formula. -/
theorem evaluate_translated_iff {system : Mettapedia.GSLT.GSLT.{u}}
    [Fintype system.Term] [DecidableEq system.Term] {admitted : system.Term → Prop}
    (tests : Leaf → Test system admitted) (spatial : Spatial.SpatialTheory system)
    (model : FiniteMuCalculus.Model (transitionSystem (gsltSpan system)))
    (index : Leaf → Fin n) (environment : FiniteMuCalculus.Environment system.Term n)
    (leaves : ∀ leaf state, state ∈ environment (index leaf) ↔ (tests leaf).predicate state)
    (formula : Reference.Core.Formula Leaf) (translated : Formula Traversal n)
    (success : translate index formula = some translated) (state : system.Term) :
    state ∈ FiniteMuCalculus.evaluate model translated environment ↔
      denotation tests formula spatial state :=
  (FiniteMuCalculus.evaluate_correct model translated
    (translated_positive index formula translated success) environment state).trans
      (meaning tests spatial index environment.meaning leaves formula translated success state)

example : translate (fun _ : Unit => (0 : Fin 1))
    (.imp (.atom ()) (.possibility (.atom ()))) =
      some (.disj (.neg (.var 0)) (.diamond .future (.var 0))) := rfl

example : translate (fun _ : Unit => (0 : Fin 1))
    (.separating 0 (.atom ()) (.atom ())) = none := rfl

end Mettapedia.OSLF.NativeTypes.Decision.ModalEmbedding
