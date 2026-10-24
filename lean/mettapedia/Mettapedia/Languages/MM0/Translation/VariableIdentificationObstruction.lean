import Mettapedia.Languages.MM0.Kernel.SubstitutionStability
import Mettapedia.Computability.ComputationalTrinityBaseChange

/-!
# Targets closed under every renaming cannot reflect MM0 derivability

An MM0 bound variable is a name. Derivability is stable under admissible
substitutions (`Kernel.Substitution.Admissible.derives`), which send distinct
bound variables to distinct bound variables, and not under a substitution that
identifies two of them (`SubstitutionStabilityControls.independence_required`).

A target in which derivability is closed under every renaming of variables does
not have that boundary. A Π-quantified constant applied to one variable twice is
the typical case: LF signatures, higher-order abstract syntax and other
Π-binding readings of a theory are closed in this way.

* `renameVars ρ` renames the variables of a preterm. It is MM0's own
  simultaneous substitution by variables (`renameVars_substitutes`).
* **Obstruction** (`not_reflects_of_unstable`). Suppose an MM0 judgment is
  derivable and one of its renamings is not. Then no encoding into a target
  closed under renaming, that preserves derivability and commutes with
  renaming, also reflects derivability. This is the base-change law for one
  change of context (`Computability.ComputationalTrinity.stable_of_lossless_of_natural`)
  read contrapositively; its form for faces on context categories is
  `Computability.ComputationalTrinity.stable_of_lossless`.
* **Instance** (`distinct_not_reflected`). In the theory of
  `SubstitutionStabilityControls`, whose one axiom is `distinct x y` for two
  bound variables, every such encoding makes the underivable `distinct 0 0`
  derivable.

Controls:
* The target that derives every `distinct l r`, as one Π-quantified constant
  does, is closed under renaming and preserves derivability (`allPairs_preserves`),
  and it derives `distinct 0 0` (`allPairs_derives_coincident`).
* MM0 derivability read as its own target reflects trivially, and is not closed
  under renaming (`mm0_not_renaming_closed`). So the closure hypothesis is what
  the obstruction rests on.

An adequate target for MM0 with bound formals must therefore restrict its
closure to admissible renamings, for instance through an explicit apartness
judgment for bound variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.VariableIdentificationObstruction

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.MM0.Kernel.SubstitutionStabilityControls

/-- Rename the variables of a preterm. -/
def renameVars (ρ : Nat → Nat) : Preterm → Preterm
  | .var index => .var (ρ index)
  | .term index => .term index
  | .app function argument => .app (renameVars ρ function) (renameVars ρ argument)

/-- **Renaming is MM0's substitution by variables.** -/
theorem renameVars_substitutes (ρ : Nat → Nat) :
    ∀ source : Preterm, Preterm.Substitutes (fun index => some (.var (ρ index))) source (renameVars ρ source)
  | .var _ => .var rfl
  | .term index => .term index
  | .app function argument =>
      .app (renameVars_substitutes ρ function) (renameVars_substitutes ρ argument)

/-- A target judgment system whose derivability is closed under every renaming
of variables. -/
structure RenamingClosedTarget where
  Judgment : Type
  Derivable : Judgment → Prop
  rename : (Nat → Nat) → Judgment → Judgment
  closed : ∀ (ρ : Nat → Nat) (judgment : Judgment), Derivable judgment → Derivable (rename ρ judgment)

/-- **No renaming-closed target reflects an unstable MM0 judgment.** If `e` is
derivable and its renaming along `ρ` is not, then an encoding that preserves
derivability and commutes with renaming does not reflect derivability. -/
theorem not_reflects_of_unstable {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {Γ : Context} {e : Preterm} (ρ : Nat → Nat)
    (derived : Derives signature definitions theorems Γ [] e)
    (unstable : ¬ Derives signature definitions theorems Γ [] (renameVars ρ e))
    (T : RenamingClosedTarget) (encode : Preterm → T.Judgment)
    (commutes : ∀ ρ e, encode (renameVars ρ e) = T.rename ρ (encode e))
    (preserves : ∀ e, Derives signature definitions theorems Γ [] e → T.Derivable (encode e)) :
    ¬ ∀ e, T.Derivable (encode e) → Derives signature definitions theorems Γ [] e := by
  intro reflects
  exact unstable (Mettapedia.Computability.ComputationalTrinity.stable_of_lossless_of_natural
    encode (fun e => ⟨preserves e, reflects e⟩) (commutes ρ) (T.closed ρ) e derived)

/-- Identifying the two variables of `distinct 0 1`. -/
theorem renameVars_distinct : renameVars (fun _ => 0) (distinct 0 1) = distinct 0 0 := rfl

/-- **The axiom `distinct x y` is unstable**: derivable, while its identifying
renaming is not. -/
theorem distinct_unstable :
    Derives signature noDefinitions theorems twoBound [] (distinct 0 1) ∧
      ¬ Derives signature noDefinitions theorems twoBound [] (renameVars (fun _ => 0) (distinct 0 1)) := by
  refine ⟨distinct_derivable, ?_⟩
  rw [renameVars_distinct]
  exact independence_required.2.2.2.1

/-- **The instance**: every preserving, renaming-commuting encoding of this theory
into a renaming-closed target derives an encoding of the underivable
`distinct 0 0`. -/
theorem distinct_not_reflected (T : RenamingClosedTarget) (encode : Preterm → T.Judgment)
    (commutes : ∀ ρ e, encode (renameVars ρ e) = T.rename ρ (encode e))
    (preserves : ∀ e, Derives signature noDefinitions theorems twoBound [] e → T.Derivable (encode e)) :
    T.Derivable (encode (distinct 0 0)) ∧
      ¬ Derives signature noDefinitions theorems twoBound [] (distinct 0 0) := by
  refine ⟨?_, independence_required.2.2.2.1⟩
  rw [← renameVars_distinct, commutes]
  exact T.closed _ _ (preserves _ distinct_derivable)

/-! ## Controls -/

/-- The target deriving every `distinct l r`, as a constant quantified over two
variables does. -/
def allPairs : RenamingClosedTarget where
  Judgment := Preterm
  Derivable judgment := ∃ left right, judgment = distinct left right
  rename := renameVars
  closed := by
    rintro ρ _ ⟨left, right, rfl⟩
    exact ⟨ρ left, ρ right, rfl⟩

/-- **The all-pairs target preserves derivability.** -/
theorem allPairs_preserves (e : Preterm)
    (derived : Derives signature noDefinitions theorems twoBound [] e) : allPairs.Derivable e := by
  obtain ⟨left, right, rfl, -⟩ := derivable_distinct derived
  exact ⟨left, right, rfl⟩

/-- **The all-pairs target derives the coincident instance**, which MM0 does not. -/
theorem allPairs_derives_coincident :
    allPairs.Derivable (distinct 0 0) ∧
      ¬ Derives signature noDefinitions theorems twoBound [] (distinct 0 0) :=
  distinct_not_reflected allPairs id (fun _ _ => rfl) allPairs_preserves

/-- **MM0 derivability is not closed under renaming**, so it is no renaming-closed
target although, as its own target, it reflects. -/
theorem mm0_not_renaming_closed :
    ¬ ∀ (ρ : Nat → Nat) (e : Preterm), Derives signature noDefinitions theorems twoBound [] e →
        Derives signature noDefinitions theorems twoBound [] (renameVars ρ e) :=
  fun closed => distinct_unstable.2 (closed _ _ distinct_unstable.1)

#print axioms not_reflects_of_unstable
#print axioms distinct_not_reflected
#print axioms allPairs_derives_coincident
#print axioms mm0_not_renaming_closed

end Mettapedia.Languages.MM0.Translation.VariableIdentificationObstruction
