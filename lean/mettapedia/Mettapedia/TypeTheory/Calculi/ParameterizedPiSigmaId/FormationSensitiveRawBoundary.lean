import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity

/-!
# Raw typing does not supply formation-sensitive authorization

The legacy lambda rule omits domain formation. An identity at an undeclared
domain is consequently a raw derivation, including in the empty context.
The formation-sensitive judgment rejects that same displayed function type.

This is an intentional distinction between two specified judgments. It is
not a consistency or strength separation about dependent type theories.
In particular, forgetting formation-sensitive proofs cannot turn preservation
for that judgment into the legacy signature's uniform raw preservation law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head}

theorem raw_identity_at_any_domain (domain : Tm Head 0) :
    HasType R .nil (.lam (.var 0)) (.pi domain (rename wk domain)) :=
  .lamIntro (.var 0)

theorem judgment_identity_domain_declared (universes : UniverseRegularity R)
    {name : DeclName}
    (judgment : Judgment R .nil (.lam (.var 0))
      (.pi (.const name) (.const name))) :
    ∃ type, R.constantType name = some type := by
  obtain ⟨_, _, formed⟩ := judgment.regularity universes
  obtain ⟨_, _, _, domain, _, _, _, _⟩ := formed.typing.piFormation
  obtain ⟨type, _, known, _, _⟩ := domain.constFormation
  exact ⟨type, known⟩

theorem raw_identity_missing_domain (universes : UniverseRegularity R)
    {name : DeclName} (missing : R.constantType name = none) :
    HasType R .nil (.lam (.var 0)) (.pi (.const name) (.const name)) ∧
      ¬ Judgment R .nil (.lam (.var 0)) (.pi (.const name) (.const name)) := by
  refine ⟨raw_identity_at_any_domain (.const name), ?_⟩
  intro judgment
  obtain ⟨_, known⟩ := judgment_identity_domain_declared universes judgment
  rw [missing] at known
  cases known

/-- Even supplying a formed ambient context cannot upgrade every legacy
derivation. Preserving only the refined judgment needs its own authorization. -/
theorem no_uniform_raw_upgrade (universes : UniverseRegularity R)
    {name : DeclName} (missing : R.constantType name = none) :
    ¬ (∀ {n : Nat} {context : Ctx Head n} {term type : Tm Head n},
      ContextFormation R context → HasType R context term type →
        Judgment R context term type) := by
  intro upgrade
  have witness := raw_identity_missing_domain universes missing
  exact witness.2 (upgrade .nil witness.1)

end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
