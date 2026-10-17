import Mettapedia.Languages.Megalodon.NativeSupport
import Mettapedia.Languages.Megalodon.ProofJudgment
import Mettapedia.Languages.Megalodon.SourcePublicationNormalization

/-!
# Definition-normal results and avoiding repeated expansion

A completed delta traversal leaves no expandable name. Beta/eta reduction and
both substitutions cannot introduce a new named declaration. This establishes
the invariant needed to skip repeated delta expansion in local proof rules;
the optimization is justified by retained meaning, not a pointer-equality
heuristic or a claim that one proof row has constant cost.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.DeltaNormalInvariant
open MathdataKernel NativeSupport ProofJudgment

def Normal (environment : Environment) (body : Tm) : Prop :=
  ∀ name declaration, Dependency.termName name ∈ termSupport body →
    environment.lookupTerm? name = some declaration → declaration.definition = none

theorem mono {environment : Environment} {body result : Tm} (normal : Normal environment body)
    (support : termSupport result ⊆ termSupport body) : Normal environment result :=
  fun name declaration member found => normal name declaration (support member) found

theorem pair {environment : Environment} {first second : Tm}
    (one : Normal environment first) (two : Normal environment second) :
    ∀ name declaration, Dependency.termName name ∈ termSupport first ∪ termSupport second →
      environment.lookupTerm? name = some declaration → declaration.definition = none := by
  intro name declaration member found
  rcases Finset.mem_union.mp member with left | right
  · exact one name declaration left found
  · exact two name declaration right found

theorem fixed {environment : Environment} {body : Tm} (normal : Normal environment body) (fuel : Nat) :
    deltaNormalize environment fuel body = some body := by
  induction body with
  | db | prim => cases fuel <;> simp [deltaNormalize]
  | named name =>
      cases found : environment.lookupTerm? name with
      | none => cases fuel <;> simp [deltaNormalize, found]
      | some declaration =>
          have noDefinition := normal name declaration (by simp [termSupport]) found
          rcases declaration with ⟨declaredName, type, definition⟩
          cases definition with
          | none => cases fuel <;> simp [deltaNormalize, found]
          | some body => cases noDefinition
  | app first second ihf iha | imp first second ihf iha =>
      have one := ihf (mono normal (by exact Finset.subset_union_left))
      have two := iha (mono normal (by exact Finset.subset_union_right))
      simp [deltaNormalize, one, two]
  | lam _ _ ih | all _ _ ih | typeApp _ _ ih | typeLam _ ih | typeAll _ ih =>
      simp [deltaNormalize, ih normal]

theorem delta_result (environment : Environment) :
    ∀ (fuel : Nat) (body result : Tm), deltaNormalize environment fuel body = some result → Normal environment result
  | fuel, .named name, result, normalized => by
      cases found : environment.lookupTerm? name with
      | none =>
          cases fuel <;> simp only [deltaNormalize, found, Option.some.injEq] at normalized <;> subst result
          all_goals
            intro other declaration member lookup
            have same : other = name := by simpa [termSupport] using member
            subst other
            rw [found] at lookup
            cases lookup
      | some declaration =>
          rcases declaration with ⟨declaredName, type, definition⟩
          cases definition with
          | none =>
              cases fuel <;> simp only [deltaNormalize, found, Option.some.injEq] at normalized <;> subst result
              all_goals
                intro other declaration member lookup
                have same : other = name := by simpa [termSupport] using member
                subst other
                rw [found] at lookup
                cases Option.some.inj lookup
                rfl
          | some body =>
              cases fuel with
              | zero => simp [deltaNormalize, found] at normalized
              | succ fuel =>
                  exact delta_result environment fuel body result (by simpa [deltaNormalize, found] using normalized)
  | fuel, .app first second, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨one, oneExpanded, two, twoExpanded, rfl⟩ := normalized
      exact pair (delta_result environment fuel first one oneExpanded) (delta_result environment fuel second two twoExpanded)
  | fuel, .imp first second, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨one, oneExpanded, two, twoExpanded, rfl⟩ := normalized
      exact pair (delta_result environment fuel first one oneExpanded) (delta_result environment fuel second two twoExpanded)
  | fuel, .lam type body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      exact delta_result environment fuel body next expanded
  | fuel, .all type body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      exact delta_result environment fuel body next expanded
  | fuel, .typeApp body type, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      exact delta_result environment fuel body next expanded
  | fuel, .typeLam body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      exact delta_result environment fuel body next expanded
  | fuel, .typeAll body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      exact delta_result environment fuel body next expanded
  | fuel, .db index, result, normalized => by
      cases fuel <;> simp only [deltaNormalize, Option.some.injEq] at normalized <;> subst result
      all_goals simp [Normal, termSupport]
  | fuel, .prim index, result, normalized => by
      cases fuel <;> simp only [deltaNormalize, Option.some.injEq] at normalized <;> subst result
      all_goals simp [Normal, termSupport]
termination_by fuel body _ _ => (fuel, sizeOf body)

theorem normalize_result {environment : Environment} {fuel : Nat} {body result : Tm}
    (normalized : MathdataKernel.normalize environment fuel body = some result) : Normal environment result := by
  obtain ⟨expanded, delta, beta⟩ := Option.bind_eq_some_iff.mp normalized
  exact mono (delta_result environment fuel body expanded delta) (termSupport_normalize_subset beta)

theorem instantiate {environment : Environment} {body argument : Tm}
    (bodyNormal : Normal environment body) (argumentNormal : Normal environment argument) :
    Normal environment (Tm.instantiate argument body) := by
  intro name declaration member found
  exact pair argumentNormal bodyNormal name declaration (termSupport_instantiate_subset argument body member) found

def ContextNormal (environment : Environment) (context : Context) : Prop :=
  ∀ proposition ∈ context.hypotheses, Normal environment proposition

theorem inferred_normal {environment : Environment} {fuel : Nat} {context : Context} {proof : Pf} {proposition : Tm}
    (proved : Proves environment fuel context proof proposition) (hypotheses : ContextNormal environment context) :
    Normal environment proposition := by
  induction proved with
  | hyp found => exact hypotheses _ (List.mem_of_getElem? found)
  | known _ normalized | termApp _ _ _ normalized _ => exact normalize_result normalized
  | proofApp _ _ ihf _ => exact mono (ihf hypotheses) Finset.subset_union_right
  | termLam _ _ ih =>
      apply ih
      intro proposition member
      change proposition ∈ List.map (Tm.shift 0 1) _ at member
      obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp member
      subst proposition
      simpa only [Normal, termSupport_shift] using hypotheses source sourceMember
  | proofLam _ normalized _ ih =>
      refine pair (normalize_result normalized) (ih ?_)
      intro proposition member
      rcases List.mem_cons.mp member with rfl | old
      · exact normalize_result normalized
      · exact hypotheses proposition old
  | typeApp _ ih => simpa only [Normal, termSupport_typeInstantiate, termSupport] using ih hypotheses
  | typeLam _ _ _ ih => exact ih (by intro proposition member; cases member)

/-- The publication proof rule normalizes beta/eta after substitution.
The native reference's extra delta phase is provably redundant here. -/
theorem application_normalization (environment : Environment) (fuel : Nat) {body argument expanded : Tm}
    (bodyNormal : Normal environment body) (unfolded : deltaNormalize environment fuel argument = some expanded) :
    MathdataKernel.normalize environment fuel (Tm.instantiate expanded body) =
      Tm.normalize fuel (Tm.instantiate expanded body) := by
  have normal := instantiate bodyNormal (delta_result environment fuel argument expanded unfolded)
  simp [MathdataKernel.normalize, fixed normal fuel]

end Mettapedia.Languages.Megalodon.DeltaNormalInvariant
