import Mettapedia.Logic.LP.IndependentOutputUnification

/-!
# Private variable names and public solution families

Changing private names must preserve the same public values, including open
values and their correlations with later constraints. Witness transport here
changes the coordinates at which a substitution is consulted, without renaming
the terms in its range. This gives equality of projected solution families,
not just equality of satisfiability verdicts.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.PrivateVariableRenaming

open UnificationRenaming IndependentOutputUnification

variable {σ : LPSignature}

def reindex (f : σ.vars → σ.vars) (witness : Subst σ) : Subst σ :=
  fun slot => witness (f slot)

theorem reindex_apply (f : σ.vars → σ.vars) (witness : Subst σ) (term : Term σ) :
    (reindex f witness).applyTerm term = witness.applyTerm (rename f term) := by
  induction term with
  | var slot => rfl
  | const constant => rfl
  | app head children ih => simp only [Subst.applyTerm,rename_app,ih]

theorem reindex_renamed (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (witness : Subst σ) (term : Term σ) :
    (reindex g witness).applyTerm (rename f term) = witness.applyTerm term := by
  rw [reindex_apply,rename_leftInverse f g inverse]

theorem reindex_unifies (f : σ.vars → σ.vars) (witness : Subst σ)
    (constraints : List (Term σ × Term σ))
    (solves : Unifies witness (equations f constraints)) :
    Unifies (reindex f witness) constraints := by
  intro pair member
  simpa only [reindex_apply] using solves _ (List.mem_map.mpr ⟨pair,member,rfl⟩)

theorem reindex_unifies_renamed (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (witness : Subst σ)
    (constraints : List (Term σ × Term σ)) (solves : Unifies witness constraints) :
    Unifies (reindex g witness) (equations f constraints) := by
  intro pair member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  simpa only [reindex_renamed f g inverse] using solves original present

/-- Renaming the problem and observation coordinates preserves the actual
projected values. The witness ranges are not renamed. -/
theorem solutions_renamed (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (constraints : List (Term σ × Term σ)) (observations : List (Term σ)) :
    solutions (equations f constraints) (observations.map (rename f)) =
      solutions constraints observations := by
  ext values
  constructor
  · rintro ⟨witness,solves,published⟩
    refine ⟨reindex f witness,reindex_unifies f witness constraints solves,?_⟩
    rw [published,List.map_map]
    exact List.map_congr_left fun term _ => (reindex_apply f witness term).symm
  · rintro ⟨witness,solves,published⟩
    refine ⟨reindex g witness,reindex_unifies_renamed f g inverse witness constraints solves,?_⟩
    rw [published,List.map_map]
    exact List.map_congr_left fun term _ => (reindex_renamed f g inverse witness term).symm

/-- The caller's coordinates and future equations remain untouched. -/
theorem solutions_private_renaming (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f)
    (constraints later : List (Term σ × Term σ)) (observations : List (Term σ))
    (laterFixed : equations f later = later)
    (observationsFixed : observations.map (rename f) = observations) :
    solutions (equations f constraints ++ later) observations =
      solutions (constraints ++ later) observations := by
  have same := solutions_renamed f g inverse (constraints ++ later) observations
  have append : equations f (constraints ++ later) =
      equations f constraints ++ equations f later := List.map_append
  simpa only [append,laterFixed,observationsFixed] using same


end Mettapedia.Logic.LP.PrivateVariableRenaming
