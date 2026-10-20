import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical.Support

/-!
# Canonical Kripke-Henkin packaging

Final content layer for the supported canonical construction: the supported
membership consequence interface and its completeness theorems
(`intuitionisticHOL_supported_completeness_param_free` needs only a
`SchedulerProvider`, and providers exist for every countable signature), and
three hypothesis packages for a constant-domain canonical `KripkeHenkin`
structure, `LocalMembershipClauses`, `LevelLocalMembershipClauses` and
`FullPresentedUpgrade`, with the conversions between them.  The membership,
frame, recursive forcing and support towers are imported from content modules
under `KripkeHenkinCanonical/`.

The three packages are empty over every countable signature with a base type
(`isEmpty_localMembershipClauses`, `isEmpty_levelLocalMembershipClauses` and
`isEmpty_fullPresentedUpgrade` in `KripkeHenkinCanonicalObstruction`).  With a
scheduler provider, each would make the supported presented worlds a
constant-domain `KripkeHenkin` structure.  Such a structure forces the
constant-domain sentence at every world, and some supported presented world
omits that sentence, because it is not derivable.  Kripke completeness holds
for varying domains instead (`KripkeVarying.Canonical.provable_iff_consequence`).

## Removed: the conditional constant-domain package family

This module used to contain canonical `KripkeHenkin` instances and
completeness corollaries assuming a `SchedulerProvider` together with one of
the three packages.  That family was pursued as the route to Kripke-Henkin
completeness.  No signature with a base type satisfies its hypotheses
(`not_schedulerProvider_and_localMembershipClauses`,
`not_schedulerProvider_and_levelLocalMembershipClauses` and
`not_schedulerProvider_and_fullPresentedUpgrade`), so every member was vacuous.
The family was removed on 2026-10-20: 54 declarations (4 definitions and 50
theorems), all in `KripkeHenkin.SupportedCanonicalFrame`.

* With `LocalMembershipClauses` (12): `canonicalKripkeHenkin`,
  `canonicalKripkeHenkin_forces_iff_mem`,
  `not_consequence_of_canonical_countermodel`,
  `not_consequence_of_not_supportedMembershipConsequence`,
  `not_consequence_of_supported_countermodel_at_bound`,
  `provable_iff_consequence_param_free_supported`,
  `provable_iff_consequence_supported_at_bound`,
  `provable_of_consequence_param_free_supported`,
  `provable_of_consequence_supported_at_bound`,
  `provable_of_consequence_with_canonical_countermodels`,
  `supportedMembershipConsequence_iff_canonicalKripkeHenkin`,
  `supportedMembershipConsequence_of_consequence`.
* With `LevelLocalMembershipClauses` (17): `canonicalLevelKripkeHenkin`,
  `canonicalLevelKripkeHenkin_forcesAt_empty_iff_mem`,
  `canonicalLevelKripkeHenkin_forces_iff_mem`,
  `intuitionisticHOL_level_kripke_completeness_param_free`,
  `intuitionisticHOL_level_kripke_countermodel_at_bound`,
  `not_consequence_of_canonical_countermodel_level`,
  `not_consequence_of_not_supportedMembershipConsequence_level`,
  `not_consequence_of_supported_countermodel_at_bound_level`,
  `provable_iff_canonicalLevelKripkeHenkin_param_free_supported`,
  `provable_iff_canonicalLevelKripkeHenkin_supported_at_bound`,
  `provable_iff_consequence_param_free_supported_level`,
  `provable_iff_consequence_supported_at_bound_level`,
  `provable_of_consequence_param_free_supported_level`,
  `provable_of_consequence_supported_at_bound_level`,
  `provable_of_consequence_with_canonical_countermodels_level`,
  `supportedMembershipConsequence_iff_canonicalLevelKripkeHenkin`,
  `supportedMembershipConsequence_of_consequence_level`.
* With `FullPresentedUpgrade` (25): `canonicalKripkeHenkinOfUpgrade`,
  `canonicalLevelKripkeHenkinOfUpgrade`,
  `canonicalLevelKripkeHenkinOfUpgrade_forcesAt_empty_iff_mem`,
  `canonicalLevelKripkeHenkinOfUpgrade_forces_iff_mem`,
  `intuitionisticHOL_full_kripke_completeness_param_free_of_upgrade`,
  `not_consequence_of_canonical_countermodel_level_of_upgrade`,
  `not_consequence_of_canonical_countermodel_of_upgrade`,
  `not_consequence_of_not_supportedMembershipConsequence_level_of_upgrade`,
  `not_consequence_of_not_supportedMembershipConsequence_of_upgrade`,
  `not_consequence_of_supported_countermodel_at_bound_level_of_upgrade`,
  `not_consequence_of_supported_countermodel_at_bound_of_upgrade`,
  `provable_iff_canonicalLevelKripkeHenkin_param_free_supported_of_upgrade`,
  `provable_iff_canonicalLevelKripkeHenkin_supported_at_bound_of_upgrade`,
  `provable_iff_consequence_param_free_supported_level_of_upgrade`,
  `provable_iff_consequence_param_free_supported_of_upgrade`,
  `provable_iff_consequence_supported_at_bound_level_of_upgrade`,
  `provable_iff_consequence_supported_at_bound_of_upgrade`,
  `provable_of_consequence_param_free_supported_level_of_upgrade`,
  `provable_of_consequence_param_free_supported_of_upgrade`,
  `provable_of_consequence_supported_at_bound_level_of_upgrade`,
  `provable_of_consequence_supported_at_bound_of_upgrade`,
  `provable_of_consequence_with_canonical_countermodels_level_of_upgrade`,
  `provable_of_consequence_with_canonical_countermodels_of_upgrade`,
  `supportedMembershipConsequence_of_consequence_level_of_upgrade`,
  `supportedMembershipConsequence_of_consequence_of_upgrade`.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin

namespace SupportedCanonicalFrame

open ClosedTheorySet

/-- Local membership clauses: disjunction primeness and Kripke-style existential
witnesses for the carrier of every supported presented world, with no support
condition.  Together with a `SchedulerProvider`, which supplies the
implication, negation and universal clauses, they would make the supported
presented worlds a substitutional `KripkeHenkin` structure.  The package is
empty over every countable signature with a base type
(`isEmpty_localMembershipClauses`). -/
structure LocalMembershipClauses (Const : Ty Base → Type v) where
  or_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {φ ψ : ClosedFormula (WithParams Const)},
      Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
        Forces (Base := Base) (Const := Const) W φ ∨
          Forces (Base := Base) (Const := Const) W ψ
  ex_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            Le (Base := Base) (Const := Const) W V →
              Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ)

/-- The local membership clauses are exactly a global-strength upgrade for each
supported presented world: they supply unrestricted disjunction primeness and
unrestricted existential witnesses for its deductive-closure carrier. -/
def LocalMembershipClauses.toFullPresented
    (L : LocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    ClosedTheorySet.FullPresentedIntuitionisticWorld (Base := Base) Const :=
  { level := W.level
    raw := W.raw
    raw_avoids_future := W.raw_avoids_future
    consistent := W.consistent
    prime_or := by
      intro φ ψ hOr
      have hForces :
          Forces (Base := Base) (Const := Const) W (.or φ ψ) := by
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hOr
      rcases (L.or_clause (W := W) (φ := φ) (ψ := ψ)).mp hForces with hφ | hψ
      · left
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hφ
      · right
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hψ
    exists_witness := by
      intro σ φ hEx
      have hForces :
          Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) := by
        simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using hEx
      obtain ⟨t, ht⟩ := (L.ex_clause (W := W) (σ := σ) (φ := φ)).mp hForces
      refine ⟨t, ?_⟩
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier] using
        ht W (le_refl (Base := Base) (Const := Const) W) }

/-- Upgrading a supported world through the local clauses and then forgetting
back to the supported interface preserves the underlying world. -/
@[simp] theorem LocalMembershipClauses.toFullPresented_toSupported
    (L : LocalMembershipClauses (Base := Base) Const)
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    (L.toFullPresented (Base := Base) W).toSupported = W := by
  cases W
  simp [LocalMembershipClauses.toFullPresented,
    ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported]

/-- An equivalent way to state the local canonical gap: every supported
presented world can be upgraded to a full presented world without changing its
raw presentation or support level.

**Do not attempt to discharge this for arbitrary supported worlds.**  Global
disjunction primeness of a fixed level-bounded closure over pairs mentioning
future-layer parameters is disjunction-property strength (normalization-route
work), and `FormulaPairFairAfter.incompatible_with_avoids_layers` refutes the
one-enumeration fairness route.  The viable completeness interface is the
support-bounded one (`provable_iff_supportedMembershipConsequence_*`).  This
package is empty over every countable signature with a base type
(`isEmpty_fullPresentedUpgrade`); the conditional `KripkeHenkin` instances once
built from it were removed (see the module docstring). -/
structure FullPresentedUpgrade (Const : Ty Base → Type v) where
  full :
    ∀ _ : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      ClosedTheorySet.FullPresentedIntuitionisticWorld (Base := Base) Const
  forget :
    ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      (full W).toSupported = W

/-- Local membership clauses determine a full-presented upgrade for every
supported world. -/
def LocalMembershipClauses.toFullPresentedUpgrade
    (L : LocalMembershipClauses (Base := Base) Const) :
    FullPresentedUpgrade (Base := Base) Const where
  full := L.toFullPresented (Base := Base)
  forget := L.toFullPresented_toSupported (Base := Base)

theorem fullPresented_or_clause
    (W : ClosedTheorySet.FullPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)} :
    Forces (Base := Base) (Const := Const) W.toSupported (.or φ ψ) ↔
      Forces (Base := Base) (Const := Const) W.toSupported φ ∨
        Forces (Base := Base) (Const := Const) W.toSupported ψ := by
  constructor
  · intro hOr
    have hOr' : (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw := by
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hOr
    rcases W.prime_or hOr' with hφ | hψ
    · left
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hφ
    · right
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hψ
  · intro hOr
    rcases hOr with hφ | hψ
    · exact SupportedCanonicalMembership.or_left_mem (W := W.toSupported) hφ
    · exact SupportedCanonicalMembership.or_right_mem (W := W.toSupported) hψ

theorem fullPresented_ex_clause
    (W : ClosedTheorySet.FullPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    Forces (Base := Base) (Const := Const) W.toSupported (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        Forces (Base := Base) (Const := Const) W.toSupported (instantiate (Base := Base) t φ) := by
  constructor
  · intro hEx
    have hEx' : (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw := by
      simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
        ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using hEx
    obtain ⟨t, ht⟩ := W.exists_witness hEx'
    refine ⟨t, ?_⟩
    simpa [Forces, ClosedTheorySet.SupportedPresentedIntuitionisticWorld.carrier,
      ClosedTheorySet.FullPresentedIntuitionisticWorld.toSupported] using ht
  · intro hEx
    rcases hEx with ⟨t, ht⟩
    exact SupportedCanonicalMembership.ex_intro_mem (W := W.toSupported) t ht

theorem fullPresented_ex_kripke_clause
    (W : ClosedTheorySet.FullPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    Forces (Base := Base) (Const := Const) W.toSupported (.ex φ : ClosedFormula (WithParams Const)) ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
          Le (Base := Base) (Const := Const) W.toSupported V →
            Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ) := by
  constructor
  · intro hEx
    obtain ⟨t, ht⟩ :=
      (fullPresented_ex_clause (Base := Base) (Const := Const) W).mp hEx
    refine ⟨t, ?_⟩
    intro V hWV
    exact forces_mono (Base := Base) (Const := Const) hWV ht
  · intro hEx
    rcases hEx with ⟨t, ht⟩
    exact (fullPresented_ex_clause (Base := Base) (Const := Const) W).mpr
      ⟨t, ht W.toSupported (le_refl (Base := Base) (Const := Const) W.toSupported)⟩

/-- A full-presented upgrade supplies the local membership clauses. -/
theorem FullPresentedUpgrade.toLocalMembershipClauses
    (U : FullPresentedUpgrade (Base := Base) Const) :
    LocalMembershipClauses (Base := Base) Const where
  or_clause := by
    intro W φ ψ
    have hClause := fullPresented_or_clause (Base := Base) (Const := Const)
      (U.full W) (φ := φ) (ψ := ψ)
    simpa [U.forget W] using hClause
  ex_clause := by
    intro W σ φ
    have hClause := fullPresented_ex_kripke_clause (Base := Base) (Const := Const)
      (U.full W) (σ := σ) (φ := φ)
    simpa [U.forget W] using hClause

/-- Level-aware local membership clauses for the canonical membership frame
whose preorder is `LevelLe`.  The package is empty over every countable
signature with a base type (`isEmpty_levelLocalMembershipClauses`). -/
structure LevelLocalMembershipClauses (Const : Ty Base → Type v) where
  or_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {φ ψ : ClosedFormula (WithParams Const)},
      Forces (Base := Base) (Const := Const) W (.or φ ψ) ↔
        Forces (Base := Base) (Const := Const) W φ ∨
          Forces (Base := Base) (Const := Const) W ψ
  ex_clause :
    ∀ {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}
      {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      Forces (Base := Base) (Const := Const) W (.ex φ : ClosedFormula (WithParams Const)) ↔
        ∃ t : ClosedTerm (WithParams Const) σ,
          ∀ V : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
            LevelLe (Base := Base) (Const := Const) W V →
              Forces (Base := Base) (Const := Const) V (instantiate (Base := Base) t φ)

/-- Ordinary local membership clauses also supply the level-aware version by
forgetting the level component of accessibility. -/
theorem LocalMembershipClauses.toLevelLocalMembershipClauses
    (L : LocalMembershipClauses (Base := Base) Const) :
    LevelLocalMembershipClauses (Base := Base) Const where
  or_clause := L.or_clause
  ex_clause := by
    intro W σ φ
    constructor
    · intro hEx
      obtain ⟨t, ht⟩ := (L.ex_clause (W := W) (σ := σ) (φ := φ)).mp hEx
      exact ⟨t, fun V hWV => ht V hWV.2⟩
    · intro hEx
      obtain ⟨t, ht⟩ := hEx
      exact SupportedCanonicalMembership.ex_intro_mem (Base := Base) (Const := Const)
        (W := W) t (ht W (levelLe_refl (Base := Base) (Const := Const) W))

/-- A full-presented upgrade supplies level-aware local membership clauses. -/
theorem FullPresentedUpgrade.toLevelLocalMembershipClauses
    (U : FullPresentedUpgrade (Base := Base) Const) :
    LevelLocalMembershipClauses (Base := Base) Const :=
  (U.toLocalMembershipClauses (Base := Base)).toLevelLocalMembershipClauses (Base := Base)

end SupportedCanonicalFrame

namespace SupportedCanonicalFrame

/-- Semantic consequence over the canonical supported-membership frame.  This is
an intermediate canonical countermodel interface, not the final independent
`KripkeHenkin` model class: worlds still carry raw presentations and forcing is
carrier membership. -/
def SupportedMembershipConsequence
    (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
    (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
      Forces (Base := Base) (Const := Const) W ψ) →
        Forces (Base := Base) (Const := Const) W θ

/-- EM-free provability is sound for the supported-membership consequence
interface by deductive closure of every supported presented carrier. -/
theorem supportedMembershipConsequence_of_provable
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hθ : ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  intro W hT
  exact W.closed
    (ClosedTheorySet.provable_mono (Const := WithParams Const)
      (T := T) (U := W.carrier) hT hθ)

/-- A supported canonical counterworld refutes supported-membership
consequence directly, without the full `KripkeHenkin` upgrade obligation. -/
theorem not_supportedMembershipConsequence_of_canonical_countermodel
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const)
    (hT : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier)
    (hθ : θ ∉ W.carrier) :
    ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  intro hSem
  exact hθ (hSem W hT)

/-- If the supported raw construction supplies counterworlds for every
non-derivation, supported-membership semantic consequence implies provability. -/
theorem provable_of_supportedMembershipConsequence_with_canonical_countermodels
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hCounter :
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ →
        ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const,
          (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
            θ ∉ W.carrier)
    (hSem : SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  obtain ⟨W, hT, hθ⟩ := hCounter hNot
  exact (not_supportedMembershipConsequence_of_canonical_countermodel
    (Base := Base) (Const := Const) W hT hθ) hSem

/-- A supported raw alternating countermodel refutes supported-membership
consequence at a fixed parameter bound. -/
theorem not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  obtain ⟨W, _hLevel, hT, hθ⟩ :=
    ClosedTheorySet.exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := m) (T := T)
      (P.scheduler m) hLayer hStage hθStage hNot
  exact not_supportedMembershipConsequence_of_canonical_countermodel
    (Base := Base) (Const := Const) W hT hθ

/-- Completeness at a fixed parameter bound for the supported canonical
membership interface, given a scheduler provider. -/
theorem provable_of_supportedMembershipConsequence_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hSem : SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  by_contra hNot
  exact (not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage hNot) hSem

/-- At a fixed parameter bound, the supported canonical membership interface is
complete for the EM-free calculus.  This is an intermediate equivalence for the
raw presented-world semantics, not yet the final independent `KripkeHenkin`
consequence theorem. -/
theorem provable_iff_supportedMembershipConsequence_supported_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  constructor
  · exact supportedMembershipConsequence_of_provable (Base := Base) (Const := Const)
  · exact provable_of_supportedMembershipConsequence_supported_at_bound
      (Base := Base) (Const := Const) P hLayer hStage hθStage

/-- Param-free completeness for the supported canonical membership interface,
given a scheduler provider.  It needs no `KripkeHenkin` upgrade obligation. -/
theorem provable_of_supportedMembershipConsequence_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ)
    (hSem : SupportedMembershipConsequence (Base := Base) (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  refine provable_of_supportedMembershipConsequence_supported_at_bound
    (Base := Base) (Const := Const) P (m := 0) ?_ ?_ ?_ hSem
  · intro ψ hψ σ m k _hm
    exact hT0 ψ hψ σ (Nat.pair m k)
  · intro ψ hψ σ r k _hr
    exact hT0 ψ hψ σ (Nat.pair 0 (Nat.pair r k))
  · intro σ r k _hr
    exact hθ0 σ (Nat.pair 0 (Nat.pair r k))

/-- Param-free equivalence for the supported canonical membership interface.  The
remaining assumptions are exactly the scheduler data for the raw alternating
construction; the theorem deliberately does not claim the final model-class
`Consequence` result. -/
theorem provable_iff_supportedMembershipConsequence_param_free_supported
    (P : SchedulerProvider (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ := by
  constructor
  · exact supportedMembershipConsequence_of_provable (Base := Base) (Const := Const)
  · exact provable_of_supportedMembershipConsequence_param_free_supported
      (Base := Base) (Const := Const) P hT0 hθ0

/-! ## Intuitionistic HOL supported completeness interface -/

/-- Positive supported example: EM-free derivability is valid in every
supported canonical membership world. -/
theorem intuitionisticHOL_supported_soundness
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hθ : ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  supportedMembershipConsequence_of_provable
    (Base := Base) (Const := Const) hθ

/-- Negative supported example: the raw alternating construction supplies a
counterworld for every fixed-bound non-derivation. -/
theorem intuitionisticHOL_supported_countermodel_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  not_supportedMembershipConsequence_of_supported_countermodel_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage hNot

/-- Fixed-bound completeness for the supported canonical membership semantics. -/
theorem intuitionisticHOL_supported_completeness_at_bound
    (P : SchedulerProvider (Base := Base) Const)
    {m : Nat} {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : ClosedTheorySet.AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) T)
    (hStage : ClosedTheorySet.AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 T)
    (hθStage : ClosedTheorySet.FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  provable_iff_supportedMembershipConsequence_supported_at_bound
    (Base := Base) (Const := Const) P hLayer hStage hθStage

/-- Param-free completeness for the supported canonical membership semantics. -/
theorem intuitionisticHOL_supported_completeness_param_free
    (P : SchedulerProvider (Base := Base) Const)
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hθ0 : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      SupportedMembershipConsequence (Base := Base) (Const := Const) T θ :=
  provable_iff_supportedMembershipConsequence_param_free_supported
    (Base := Base) (Const := Const) P hT0 hθ0

end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
