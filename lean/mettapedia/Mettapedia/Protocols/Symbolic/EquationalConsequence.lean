import Mettapedia.Protocols.Symbolic.Equational
import Mettapedia.UniversalAlgebra.FreeModel
import Mettapedia.UniversalAlgebra.Mathlib.FirstOrder

/-!
# Equality modulo a theory is equational consequence

The symbolic layer states its theories over Mathlib's first-order languages, and
`Mettapedia.UniversalAlgebra` states equational logic over its own signatures. For the
algebraic language of a signature `S`, the two meet exactly: a finite theory `es` is an
equation system of the library (`toEquationSystem`), and equality modulo `es` (`EqMod`) is
that system's generated equational consequence (`eqMod_iff_equationalConsequence`).

The library's completeness theorem then gives Birkhoff completeness for the symbolic layer:
two pattern terms are equal modulo a finite theory exactly when they are equal in every
algebra satisfying it (`eqMod_iff_forall_realize`). The forward direction is the existing
soundness theorem `EqMod.realize_eq`.
-/

namespace Mettapedia.Protocols.Symbolic

open FirstOrder FirstOrder.Language Mettapedia.UniversalAlgebra

variable {S : Signature.{0}}

/-- A finite theory over the algebraic language of `S`, read as an equation system of
`Mettapedia.UniversalAlgebra`. -/
def toEquationSystem
    (es : List (S.toFirstOrderLanguage.Term ℕ × S.toFirstOrderLanguage.Term ℕ)) :
    EquationSystem S :=
  ⟨es.map fun e => (Term.ofFirstOrder e.1, Term.ofFirstOrder e.2)⟩

/-- Reading a Mathlib term back commutes with substitution. -/
theorem ofFirstOrder_subst (t : S.toFirstOrderLanguage.Term ℕ)
    (σ : ℕ → S.toFirstOrderLanguage.Term ℕ) :
    Term.ofFirstOrder (t.subst σ) =
      (Term.ofFirstOrder t).subst fun i => Term.ofFirstOrder (σ i) := by
  apply (Term.firstOrderEquiv S).injective
  simp [Term.firstOrderEquiv, Term.toFirstOrder_subst]

theorem equationalConsequence_of_eqMod
    {es : List (S.toFirstOrderLanguage.Term ℕ × S.toFirstOrderLanguage.Term ℕ)}
    {t u : S.toFirstOrderLanguage.Term ℕ} (h : EqMod {e | e ∈ es} t u) :
    EquationalConsequence (toEquationSystem es) (Term.ofFirstOrder t, Term.ofFirstOrder u) := by
  induction h with
  | @inst l r member σ =>
      rw [ofFirstOrder_subst, ofFirstOrder_subst]
      have listed : (Term.ofFirstOrder l, Term.ofFirstOrder r) ∈ toEquationSystem es :=
        show _ ∈ (toEquationSystem es).equations from
          List.mem_map_of_mem (f := fun e => (Term.ofFirstOrder e.1, Term.ofFirstOrder e.2)) member
      exact (EquationalConsequence.of_mem listed).subst _
  | refl t => exact EquationalConsequence.refl _ _
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | congr f _ ih =>
      exact EquationalConsequence.operation f.1 _ _ fun i => ih (Fin.cast f.2 i)

theorem eqMod_of_equationalConsequence
    {es : List (S.toFirstOrderLanguage.Term ℕ × S.toFirstOrderLanguage.Term ℕ)}
    {equation : Equation S}
    (h : EquationalConsequence (toEquationSystem es) equation) :
    EqMod {e | e ∈ es} equation.1.toFirstOrder equation.2.toFirstOrder := by
  refine h.induction_on
    (P := fun equation => EqMod {e | e ∈ es} equation.1.toFirstOrder equation.2.toFirstOrder)
    ?_ ?_ ?_ ?_ ?_
  · intro equation member σ
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    simpa [Term.toFirstOrder_subst] using
      EqMod.inst (E := {e | e ∈ es}) (show (e.1, e.2) ∈ {e | e ∈ es} from listed)
        fun i => (σ i).toFirstOrder
  · intro term
    exact EqMod.refl _
  · intro _ _ ih
    exact ih.symm
  · intro _ _ _ first second
    exact first.trans second
  · intro symbol left right ih
    exact EqMod.congr (f := (⟨symbol, rfl⟩ : S.toFirstOrderLanguage.Functions (S.arity symbol))) ih

/-- Equality modulo a finite theory is the library's equational consequence of that theory. -/
theorem eqMod_iff_equationalConsequence
    (es : List (S.toFirstOrderLanguage.Term ℕ × S.toFirstOrderLanguage.Term ℕ))
    (t u : S.toFirstOrderLanguage.Term ℕ) :
    EqMod {e | e ∈ es} t u ↔
      EquationalConsequence (toEquationSystem es) (Term.ofFirstOrder t, Term.ofFirstOrder u) := by
  constructor
  · exact equationalConsequence_of_eqMod
  · intro h
    simpa using eqMod_of_equationalConsequence h

/-- **Birkhoff completeness** for finite symbolic theories, the converse of `EqMod.realize_eq`:
two pattern terms are equal modulo `es` exactly when they agree in every algebra satisfying
`es`, under every valuation. -/
theorem eqMod_iff_forall_realize
    (es : List (S.toFirstOrderLanguage.Term ℕ × S.toFirstOrderLanguage.Term ℕ))
    (t u : S.toFirstOrderLanguage.Term ℕ) :
    EqMod {e | e ∈ es} t u ↔
      ∀ (M : Type) [S.toFirstOrderLanguage.Structure M], Satisfies M {e | e ∈ es} →
        ∀ v : ℕ → M, t.realize v = u.realize v := by
  constructor
  · intro h M _ satisfies v
    exact h.realize_eq satisfies v
  · intro valid
    rw [eqMod_iff_equationalConsequence, equationalConsequence_iff_entails]
    intro Carrier model satisfiesModel valuation
    let _ : S.toFirstOrderLanguage.Structure Carrier := model.toFirstOrderStructure
    have satisfies : Satisfies Carrier {e | e ∈ es} := by
      intro e listed v
      have holds := satisfiesModel (Term.ofFirstOrder e.1, Term.ofFirstOrder e.2)
        (show _ ∈ (toEquationSystem es).equations from
          List.mem_map_of_mem (f := fun e => (Term.ofFirstOrder e.1, Term.ofFirstOrder e.2)) listed) v
      rw [← Model.realize_toFirstOrder, ← Model.realize_toFirstOrder] at holds
      simpa using holds
    have agree := valid Carrier satisfies valuation
    show (Term.ofFirstOrder t).evaluate model valuation = (Term.ofFirstOrder u).evaluate model valuation
    rw [← Model.realize_toFirstOrder, ← Model.realize_toFirstOrder]
    simpa using agree

end Mettapedia.Protocols.Symbolic
