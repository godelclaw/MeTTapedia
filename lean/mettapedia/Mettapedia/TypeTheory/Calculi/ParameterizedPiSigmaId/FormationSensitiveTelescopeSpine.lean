import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDeclarationSpine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Typed argument recovery for an arbitrary declaration telescope

Closing an existing context with Pi and applying the declaration to one
simultaneous substitution describe the same dependent argument order. A
formed observed application recovers the whole typed substitution, its
principal result and the original result-adjustment replay. The construction
works for every finite arity rather than a separately unrolled eliminator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head} {n k : Nat}

/-- An observed closed-telescope application retains a typing derivation
for its actual head, including beneath conversion and cumulativity tails. -/
theorem Typing.applyClosed_head {Γ : Ctx Head n} (telescope : Ctx Head k) :
    ∀ (assignment : Sub Head k n) {function displayed : Tm Head n},
      Typing R Γ (TelescopeAbstraction.applyClosed telescope assignment function) displayed →
        ∃ headType, Typing R Γ function headType := by
  induction telescope with
  | nil => intro assignment function displayed observed; exact ⟨displayed, observed⟩
  | snoc prior domain ih =>
      intro assignment function displayed observed
      obtain ⟨_, _, previous, _, _, _⟩ := observed.appGeneration
      exact ih (fun index => assignment index.succ) previous

theorem CtxMor.extend {Γ : Ctx Head k} {Δ : Ctx Head n}
    {substitution : Sub Head k n} {type : Tm Head k} {term : Tm Head n}
    (typed : CtxMor R Γ Δ substitution)
    (termTyped : Typing R Δ term (subst substitution type)) :
    CtxMor R (.snoc Γ type) Δ (consSub term substitution) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [consSub_zero, Ctx.lookup_snoc_zero,
      subst_consSub_rename_wk] using termTyped
  · intro prior
    simpa only [consSub_succ, Ctx.lookup_snoc_succ,
      subst_consSub_rename_wk] using typed prior

theorem CtxMor.dropNewest {Γ : Ctx Head k} {Δ : Ctx Head n} {type : Tm Head k}
    {substitution : Sub Head (k + 1) n}
    (typed : CtxMor R (.snoc Γ type) Δ substitution) :
    CtxMor R Γ Δ (fun i => substitution i.succ) := by
  intro index
  simpa only [Ctx.lookup_snoc_succ, subst_rename, wk] using typed index.succ

namespace DeclarationSpine

open TelescopeAbstraction

/-- The declaration head of an observed telescope application supplies its
original closed formation certificate. Its declared type is checked by the
lookup, rather than inferred from the shape of an arbitrary function. -/
theorem ofObservedTelescope {Γ : Ctx Head n} (telescope : Ctx Head k)
    (result : Tm Head k) (assignment : Sub Head k n) {name : DeclName}
    {displayed : Tm Head n}
    (lookup : R.constantType name = some (closeType telescope result))
    (observed : Typing R Γ (applyClosed telescope assignment (.const name)) displayed) :
    DeclarationSpine R Γ (.const name) (liftClosed (closeType telescope result)) := by
  obtain ⟨_, head⟩ := observed.applyClosed_head telescope assignment
  obtain ⟨declared, level, known, formed, universeWitness⟩ := head.constFormation
  have same : declared = closeType telescope result :=
    Option.some.inj (known.symm.trans lookup)
  subst declared
  exact .constant lookup formed universeWitness

theorem constant_formed {Γ : Ctx Head n} {name : DeclName} {declared : Tm Head 0}
    {displayed : Tm Head n} (spine : DeclarationSpine R Γ (.const name) displayed)
    (lookup : R.constantType name = some declared) :
    ∃ level, Typing R .nil declared (.head level) ∧ R.isUniverse level := by
  cases spine with
  | constant known formed universeWitness =>
      have same := Option.some.inj (known.symm.trans lookup)
      subst declared
      exact ⟨_, formed, universeWitness⟩

/-- Applying a declaration along an independently typed simultaneous
substitution constructs its principal dependent spine. -/
theorem applyTelescope {Γ : Ctx Head n} (telescope : Ctx Head k) :
    ∀ (result : Tm Head k) (substitution : Sub Head k n) {function : Tm Head n},
      DeclarationSpine R Γ function (liftClosed (closeType telescope result)) →
      CtxMor R telescope Γ substitution →
      DeclarationSpine R Γ (applyClosed telescope substitution function)
        (subst substitution result) := by
  induction telescope with
  | nil =>
      intro result substitution function spine _
      rw [subst_empty substitution result]
      exact spine
  | @snoc k telescope domain ih =>
      intro result substitution function spine typed
      have previous := ih (.pi domain result) (fun i => substitution i.succ) spine typed.dropNewest
      have argument : Typing R Γ (substitution 0)
          (subst (fun i => substitution i.succ) domain) := by
        simpa only [Ctx.lookup_snoc_zero, subst_rename, wk] using typed 0
      have current := DeclarationSpine.app previous argument
      have opened : inst0 (substitution 0)
          (subst (liftSub (fun i => substitution i.succ)) result) =
          subst substitution result := by
        rw [← subst_consSub, consSub_eta]
      rw [opened] at current
      exact current

/-- An arbitrary observed declaration application supplies a typed
substitution for every declared parameter, plus replay at its exact displayed
result. The Pi boundary is a conversion obligation, not an assumed typing
inversion or a replacement typing judgment. -/
theorem recoverTelescope
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} (context : ContextFormation R Γ)
    (telescope : Ctx Head k) :
    ∀ (result : Tm Head k) (substitution : Sub Head k n)
      {function displayed : Tm Head n},
      DeclarationSpine R Γ function (liftClosed (closeType telescope result)) →
      Typing R Γ (applyClosed telescope substitution function) displayed →
      CtxMor R telescope Γ substitution ∧
        DeclarationSpine R Γ (applyClosed telescope substitution function)
          (subst substitution result) ∧
        TypeAdjustment R (subst substitution result) displayed ∧
        (∀ {replacement}, Typing R Γ replacement (subst substitution result) →
          Typing R Γ replacement displayed) := by
  induction telescope with
  | nil =>
      intro result substitution function displayed spine observed
      rw [subst_empty substitution result]
      exact ⟨(fun i => Fin.elim0 i), spine, spine.adjustment boundary observed,
        fun replacement => spine.replay universes boundary context observed replacement⟩
  | @snoc k telescope domain ih =>
      intro result substitution function displayed spine observed
      obtain ⟨_, _, previousObserved, _, _, _⟩ := observed.appGeneration
      obtain ⟨previousTyped, previousSpine, _, _⟩ :=
        ih (.pi domain result) (fun i => substitution i.succ) spine previousObserved
      obtain ⟨argumentTyped, nextSpine, adjustment, replay⟩ :=
        previousSpine.recoverApplication universes boundary context observed
      have opened : inst0 (substitution 0)
          (subst (liftSub (fun i => substitution i.succ)) result) =
          subst substitution result := by
        rw [← subst_consSub, consSub_eta]
      rw [opened] at nextSpine adjustment replay
      have typed := previousTyped.extend argumentTyped
      rw [consSub_eta] at typed
      exact ⟨typed, nextSpine, adjustment, replay⟩

#print axioms recoverTelescope
#print axioms applyTelescope
#print axioms ofObservedTelescope
#print axioms constant_formed

end DeclarationSpine

#print axioms CtxMor.extend
#print axioms CtxMor.dropNewest
#print axioms Typing.applyClosed_head

end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
