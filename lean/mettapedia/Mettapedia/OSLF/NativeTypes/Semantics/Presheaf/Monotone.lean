import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Logic
import Mettapedia.GSLT.Topos.NativeFixedPointEncodings

/-!
# Checked variance and derived monotone native predicates

The finite checker derives variance from formula syntax. Implication reverses
variance in its antecedent. Its correctness theorem constructs the actual
monotone operator, whose least/greatest meanings are the independently
qualified corrected encodings. Context substitution commutes with the whole
construction, including fixed points, rather than merely with pointwise
Boolean approximations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Monotone

open _root_.CategoryTheory Logic Mettapedia.GSLT.Topos.NativeFixedPointEncodings

universe u v w z

variable {Atom : Type z}

/-- `true` requests monotonicity; `false` requests antitonicity.
The right-hand atom is the bound predicate variable. -/
def variance (positive : Bool) : Formula (Sum Atom Unit) → Bool
  | .atom (.inl _) => true
  | .atom (.inr _) => positive
  | .top => true
  | .bot => true
  | .conj left right => variance positive left && variance positive right
  | .disj left right => variance positive left && variance positive right
  | .impl left right => variance (!positive) left && variance positive right

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w}

def environment (atoms : Atom → Subfunctor P) (candidate : Subfunctor P) :
    Sum Atom Unit → Subfunctor P
  | .inl atom => atoms atom
  | .inr _ => candidate

theorem variance_sound (atoms : Atom → Subfunctor P)
    (body : Formula (Sum Atom Unit)) (positive : Bool)
    (checked : variance positive body = true) (first second : Subfunctor P)
    (below : first ≤ second) :
    if positive then denote (environment atoms first) body ≤ denote (environment atoms second) body
    else denote (environment atoms second) body ≤ denote (environment atoms first) body := by
  induction body generalizing positive with
  | atom name =>
      cases name with
      | inl name => cases positive <;> exact le_rfl
      | inr name =>
          cases positive with
          | false => simp [variance] at checked
          | true => exact below
  | top => cases positive <;> exact le_rfl
  | bot => cases positive <;> exact le_rfl
  | conj left right leftSound rightSound =>
      have both : variance positive left = true ∧ variance positive right = true := by
        simpa only [variance, Bool.and_eq_true] using checked
      have leftProof := leftSound positive both.1
      have rightProof := rightSound positive both.2
      cases positive <;> exact inf_le_inf leftProof rightProof
  | disj left right leftSound rightSound =>
      have both : variance positive left = true ∧ variance positive right = true := by
        simpa only [variance, Bool.and_eq_true] using checked
      have leftProof := leftSound positive both.1
      have rightProof := rightSound positive both.2
      cases positive <;> exact sup_le_sup leftProof rightProof
  | impl left right leftSound rightSound =>
      have both : variance (!positive) left = true ∧ variance positive right = true := by
        simpa only [variance, Bool.and_eq_true] using checked
      have leftProof := leftSound (!positive) both.1
      have rightProof := rightSound positive both.2
      cases positive <;> exact himp_le_himp leftProof rightProof

/-- The operator contains the syntactic formula evaluation and the checker-
derived monotonicity proof; admissibility is not supplied as a semantic field. -/
noncomputable def operator (atoms : Atom → Subfunctor P)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) :
    Subfunctor P →o Subfunctor P where
  toFun candidate := denote (environment atoms candidate) body
  monotone' := by
    intro first second below
    exact variance_sound atoms body true checked first second below

/-- A failed positive-variance check yields an explicit refusal. -/
noncomputable def install (atoms : Atom → Subfunctor P) (body : Formula (Sum Atom Unit)) :
    Option (Subfunctor P →o Subfunctor P) :=
  if checked : variance true body = true then some (operator atoms body checked) else none

theorem install_none_iff (atoms : Atom → Subfunctor P) (body : Formula (Sum Atom Unit)) :
    install atoms body = none ↔ variance true body = false := by
  unfold install
  split <;> simp_all

theorem operator_reindex (atoms : Atom → Subfunctor Q) (σ : P ⟶ Q)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true)
    (candidate : Subfunctor Q) :
    (operator atoms body checked candidate).preimage σ =
      operator (fun atom => (atoms atom).preimage σ) body checked (candidate.preimage σ) := by
  change (denote (environment atoms candidate) body).preimage σ =
    denote (environment (fun atom => (atoms atom).preimage σ) (candidate.preimage σ)) body
  rw [reindex_denote]
  apply congrArg (fun meaning => denote meaning body)
  funext name
  cases name <;> rfl

/-- Derived inductive native predicate from the admitted formula. -/
noncomputable def inductiveMeaning (atoms : Atom → Subfunctor P)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) : Subfunctor P :=
  leastEncoding (operator atoms body checked)

/-- Derived coinductive native predicate from the same admitted formula. -/
noncomputable def coinductiveMeaning (atoms : Atom → Subfunctor P)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) : Subfunctor P :=
  greatestEncoding (operator atoms body checked)

theorem inductive_substitution (atoms : Atom → Subfunctor Q) (σ : P ⟶ Q)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) :
    (inductiveMeaning atoms body checked).preimage σ =
      inductiveMeaning (fun atom => (atoms atom).preimage σ) body checked :=
  least_preimage σ _ _ (operator_reindex atoms σ body checked)

theorem coinductive_substitution (atoms : Atom → Subfunctor Q) (σ : P ⟶ Q)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) :
    (coinductiveMeaning atoms body checked).preimage σ =
      coinductiveMeaning (fun atom => (atoms atom).preimage σ) body checked :=
  greatest_preimage σ _ _ (operator_reindex atoms σ body checked)

theorem inductive_unfold (atoms : Atom → Subfunctor P)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) :
    denote (environment atoms (inductiveMeaning atoms body checked)) body =
      inductiveMeaning atoms body checked := by
  exact least_unfold (operator atoms body checked)

theorem coinductive_unfold (atoms : Atom → Subfunctor P)
    (body : Formula (Sum Atom Unit)) (checked : variance true body = true) :
    denote (environment atoms (coinductiveMeaning atoms body checked)) body =
      coinductiveMeaning atoms body checked := by
  exact greatest_unfold (operator atoms body checked)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Monotone
