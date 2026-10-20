import Mettapedia.GSLT.Dedukti.HOLHubTransport
import Mettapedia.Logic.HOL.EtaConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingFacts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingPointedTyping

/-!
# The HOL hub of Dedukti and the HOL fiber of a code package

Two readings of higher-order logic start from the same source, the
intrinsically typed HOL terms of `Logic.HOL`:

* the **hub**: a theory of an encoding in the λΠ-calculus modulo
  (`HOLHub.HubTheory`, instantiated by Holide's theory and by the STTfa hub),
  which reads a term as its shallow embedding (`HOLHub.Encoding.translate`);
* the **fiber**: a reading of the signature in a package of proposition codes
  (`HOLReading`), which reads a term of the core (variables, interpreted
  constants, application, abstraction, `⇒`, `∀` and `=`) as a term of the
  package, typed at its carrier (`HOLReading.term`, `Laws.term_typed`).

On the terms that the fiber reads, this module compares the definitional
equalities of the two.

* **Read terms are closed under β-reduction** (`read_step`), and a β-step from
  a read term is a definitional step of the reading's compiler, so a reduction
  from a read term is a conversion article inside the read terms
  (`repConversion_of_reduces`).
* **Preservation.**  β-convertible read terms have equal reads in the fiber of
  every lawful reading (`fiber_equal_of_betaConv`): by confluence they have a
  common reduct, which is read, and the compiler sends the two reductions to
  typed equality (`Laws.conversion_equal`, with no defining equation).  Read
  terms whose translations are convertible in a hub are β-convertible, by the
  end-to-end theorem of the hub (`HubTheory.translate_conv_iff`), so they too
  have equal reads (`fiber_equal_of_conv`).
* **No conservativity.**  The fiber has η: in every lawful reading the reads
  of `λ x. f x` and `f` are equal (`fiber_eta_equal`), while their translations
  are not convertible in any hub (`HubTheory.eta_not_conv`).  The fiber's
  equality on read terms therefore strictly contains the conversion of every
  hub (`fiber_not_conservative`).

* **βη inside the read terms.**  An η-step between read terms is typed
  equality (`etaStep_equal`, by `Derivable.etaPi`), and so is a βη-conversion
  that stays inside the read terms (`readBetaEta_equal`).

**Scope.**  The comparison is on read terms: the fiber leaves `⊤ ⊥ ∧ ∨ ¬ ∃`
and the constants a reading does not interpret unread.  The fiber's equality on
read terms is not βη-conversion in general: a reading whose package computes
with an interpreted constant equates more (`SetProfile.DeduktiHubFiber`, at
`add x zero` and `x`).  Whether it is exactly βη for readings whose package
adds no equation between read terms is not decided here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHubFiber

open Mettapedia.Logic
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.Dedukti.HOLHub
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic.HOL.ContextualTrinity (BetaStep)

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-! ## Read terms under β-reduction -/

section Reading

variable (ρ : HOLReading Head Base Const)

/-- **Read terms are closed under β-reduction**, and a β-step from a read term
is a definitional step of the reading's source. -/
theorem read_step {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    (step : BetaStep s t) : (ρ.term s).isSome → (ρ.term t).isSome ∧ HOL.SourceStep [] s t := by
  induction step with
  | beta body argument =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, a', hf, ha, -⟩ := HOLReading.term_app hs
      obtain ⟨b', hb, -⟩ := HOLReading.term_lam hf
      refine ⟨?_, .beta body argument⟩
      rw [ρ.term_instantiate ha, hb]
      rfl
  | appFun argument _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, _, hf, ha, -⟩ := HOLReading.term_app hs
      obtain ⟨readNext, source⟩ := ih (by rw [hf]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, HOLReading.both, hNext, ha], .appFun argument source⟩
  | appArg function _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, _, hf, ha, -⟩ := HOLReading.term_app hs
      obtain ⟨readNext, source⟩ := ih (by rw [ha]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, HOLReading.both, hNext, hf], .appArg function source⟩
  | lam _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, hb, -⟩ := HOLReading.term_lam hs
      obtain ⟨readNext, source⟩ := ih (by rw [hb]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, hNext], .lam source⟩
  | andLeft _ _ _ => intro read; simp [HOLReading.term] at read
  | andRight _ _ _ => intro read; simp [HOLReading.term] at read
  | orLeft _ _ _ => intro read; simp [HOLReading.term] at read
  | orRight _ _ _ => intro read; simp [HOLReading.term] at read
  | impLeft right _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, _, hp, hq, -⟩ := HOLReading.term_imp hs
      obtain ⟨readNext, source⟩ := ih (by rw [hp]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, HOLReading.both, hNext, hq], .impLeft right source⟩
  | impRight left _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, _, hp, hq, -⟩ := HOLReading.term_imp hs
      obtain ⟨readNext, source⟩ := ih (by rw [hq]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, HOLReading.both, hNext, hp], .impRight left source⟩
  | not _ _ => intro read; simp [HOLReading.term] at read
  | eqLeft right _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, _, hl, hr, -⟩ := HOLReading.term_eq hs
      obtain ⟨readNext, source⟩ := ih (by rw [hl]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, HOLReading.both, hNext, hr], .eqLeft right source⟩
  | eqRight left _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, _, hl, hr, -⟩ := HOLReading.term_eq hs
      obtain ⟨readNext, source⟩ := ih (by rw [hr]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, HOLReading.both, hNext, hl], .eqRight left source⟩
  | all _ ih =>
      intro read
      obtain ⟨_, hs⟩ := Option.isSome_iff_exists.mp read
      obtain ⟨_, hb, -⟩ := HOLReading.term_all hs
      obtain ⟨readNext, source⟩ := ih (by rw [hb]; rfl)
      obtain ⟨_, hNext⟩ := Option.isSome_iff_exists.mp readNext
      exact ⟨by simp [HOLReading.term, hNext], .all source⟩
  | ex _ _ => intro read; simp [HOLReading.term] at read

/-- **A reduction from a read term is a conversion article inside the read
terms**, ending at a read term. -/
theorem repConversion_of_reduces {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s n : HOL.Term Const Γ τ}
    (reduces : HOL.BetaNormalization.ReducesStar s n) (read : (ρ.term s).isSome) :
    ρ.RepConversion [] s n ∧ (ρ.term n).isSome := by
  induction reduces with
  | refl => exact ⟨.refl _, read⟩
  | tail _ step ih =>
      obtain ⟨conversion, readMiddle⟩ := ih
      obtain ⟨one⟩ := step
      obtain ⟨readNext, source⟩ := read_step ρ one readMiddle
      exact ⟨.trans _ _ _ conversion (.rel _ _ ⟨readMiddle, readNext, source⟩), readNext⟩

/-- Every reading realizes the empty list of defining equations. -/
theorem realizes_nil : ρ.Realizes [] := fun _ member => nomatch member

/-- The read of `λ x. f x`. -/
theorem term_etaExpanded (σ τ : HOL.Ty Base) :
    ρ.term (etaExpanded (Const := Const) σ τ) = some (.lam (.app (.var 1) (.var 0))) := rfl

/-- The read of `f`. -/
theorem term_etaContracted (σ τ : HOL.Ty Base) :
    ρ.term (etaContracted (Const := Const) σ τ) = some (.var 0) := rfl

end Reading

/-! ## The comparison -/

section Laws

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

/-- **β-convertible read terms are equal in the fiber**, at their carrier. -/
theorem fiber_equal_of_betaConv {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    {s' t' : Tm Head Γ.length} (hs : ρ.term s = some s') (ht : ρ.term t = some t')
    (converted : BetaConv s t) :
    Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) := by
  obtain ⟨_, toMeetS, toMeetT⟩ := sourceConfluent.eqvGen_iff_join.mp converted
  obtain ⟨sMeet, _⟩ := repConversion_of_reduces ρ toMeetS (by rw [hs]; rfl)
  obtain ⟨tMeet, _⟩ := repConversion_of_reduces ρ toMeetT (by rw [ht]; rfl)
  exact L.conversion_equal (realizes_nil ρ) (.trans _ _ _ sMeet (.symm _ _ tMeet)) hs ht

/-- **Preservation**: read terms whose translations are convertible in a hub
have equal reads in the fiber, at their carrier. -/
theorem fiber_equal_of_conv {e : Encoding Base Const} (h : HubTheory e) {Γ : HOL.Ctx Base}
    {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ} {s' t' : Tm Head Γ.length}
    (hs : ρ.term s = some s') (ht : ρ.term t = some t')
    (converted : Conv h.theory (e.translate s) (e.translate t)) :
    Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) :=
  fiber_equal_of_betaConv L hs ht ((h.translate_conv_iff s t).mp converted)

/-- **The fiber has η**: the reads of `λ x. f x` and `f` are equal at the
carrier of `σ ⇒ τ`, in the context `f : σ ⇒ τ`. -/
theorem fiber_eta_equal (σ τ : HOL.Ty Base) :
    Equal ρ.rules (ρ.objCtx [.arr σ τ]) (.lam (.app (.var 1) (.var 0))) (.var 0)
      (ρ.carrierAt 1 (.arr σ τ)) := by
  let Γ1 : Ctx Head 1 := .snoc .nil (ρ.carrierAt 0 (.arr σ τ))
  have f1 : Typed ρ.rules Γ1 (.var 0) (ρ.carrierAt 1 (.arr σ τ)) := ρ.var_carrier (.arr σ τ)
  have f2 : Typed ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ)) (.var 1) (ρ.carrierAt 2 (.arr σ τ)) :=
    HOLReading.var_weaken_carrier ρ f1
  have x2 : Typed ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ)) (.var 0) (ρ.carrierAt 2 σ) :=
    ρ.var_carrier σ
  have app2 : Typed ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ)) (.app (.var 1) (.var 0))
      (ρ.carrierAt 2 τ) := HOLReading.app_carrier f2 x2
  have expanded : Typed ρ.rules Γ1 (.lam (.app (.var 1) (.var 0))) (ρ.carrierAt 1 (.arr σ τ)) :=
    L.lam_carrier app2
  have lifted : Typed ρ.rules (.snoc (.snoc Γ1 (ρ.carrierAt 1 σ)) (ρ.carrierAt 2 σ))
      (.app (.var 2) (.var 0)) (ρ.carrierAt 3 τ) :=
    HOLReading.app_carrier (HOLReading.var_weaken_carrier ρ f2) (ρ.var_carrier σ)
  have beta : Equal ρ.rules (.snoc Γ1 (ρ.carrierAt 1 σ))
      (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.app (.var 1) (.var 0))
      (ρ.carrierAt 2 τ) := by
    have e := Derivable.betaPi (L.carrierAt_typed (.arr σ τ)) L.proofs_universe lifted x2
    simp only [HOLReading.inst0_carrierAt] at e
    exact e
  exact Derivable.etaPi expanded f1 beta

/-- **The fiber is not conservative over a hub**: the reads of `λ x. f x` and
`f` are equal in the fiber, while their translations are not convertible in
the hub. -/
theorem fiber_not_conservative {e : Encoding Base Const} (h : HubTheory e) (σ τ : HOL.Ty Base) :
    ρ.term (etaExpanded (Const := Const) σ τ) = some (.lam (.app (.var 1) (.var 0))) ∧
      ρ.term (etaContracted (Const := Const) σ τ) = some (.var 0) ∧
      Equal ρ.rules (ρ.objCtx [.arr σ τ]) (.lam (.app (.var 1) (.var 0))) (.var 0)
        (ρ.carrierAt 1 (.arr σ τ)) ∧
      ¬ Conv h.theory (e.translate (etaExpanded (Const := Const) σ τ))
        (e.translate (etaContracted (Const := Const) σ τ)) :=
  ⟨term_etaExpanded ρ σ τ, term_etaContracted ρ σ τ, fiber_eta_equal L σ τ, h.eta_not_conv σ τ⟩

end Laws

/-! ## βη inside the read terms -/

section Eta

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

/-- **An η-step between read terms is typed equality**, at their carrier. -/
theorem etaStep_equal {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    (step : HOL.EtaConversion.EtaStep s t) :
    ∀ {s' t' : Tm Head Γ.length}, ρ.term s = some s' → ρ.term t = some t' →
      Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) := by
  induction step with
  | @eta Γ σ τ function =>
      intro s' t' hs ht
      obtain ⟨b', hb, rfl⟩ := HOLReading.term_lam hs
      obtain ⟨g', x', hg, hx, rfl⟩ := HOLReading.term_app hb
      rw [ρ.term_weaken, ht] at hg
      cases hg
      cases hx
      have fTyped := L.term_typed ht
      have fWeak : Typed ρ.rules (.snoc (ρ.objCtx Γ) (ρ.carrierAt Γ.length σ))
          (Presentation.rename wk t') (ρ.carrierAt (Γ.length + 1) (.arr σ τ)) := by
        simpa only [HOLReading.rename_carrierAt] using
          fTyped.weaken (extension := ρ.carrierAt Γ.length σ)
      have bodyTyped := HOLReading.app_carrier fWeak (ρ.var_carrier σ)
      exact Derivable.etaPi (L.lam_carrier bodyTyped) fTyped (L.equal_app_wk_lam bodyTyped)
  | appFun argument _ ih =>
      intro s' t' hs ht
      obtain ⟨f', a', hf, ha, rfl⟩ := HOLReading.term_app hs
      obtain ⟨g', a'', hg, ha', rfl⟩ := HOLReading.term_app ht
      rw [ha] at ha'
      cases ha'
      have e := Derivable.appCong (ih hf hg) (.refl (L.term_typed ha))
      rwa [ρ.inst0_carrierAt] at e
  | appArg function _ ih =>
      intro s' t' hs ht
      obtain ⟨f', a', hf, ha, rfl⟩ := HOLReading.term_app hs
      obtain ⟨f'', b', hf', hb, rfl⟩ := HOLReading.term_app ht
      rw [hf] at hf'
      cases hf'
      have e := Derivable.appCong (.refl (L.term_typed hf)) (ih ha hb)
      rwa [ρ.inst0_carrierAt] at e
  | lam _ ih =>
      intro s' t' hs ht
      obtain ⟨b', hb, rfl⟩ := HOLReading.term_lam hs
      obtain ⟨c', hc, rfl⟩ := HOLReading.term_lam ht
      exact .lamCong (L.carrierAt_typed (.arr _ _)) L.proofs_universe (ih hb hc)
  | andLeft _ _ _ => intro s' t' hs; simp [HOLReading.term] at hs
  | andRight _ _ _ => intro s' t' hs; simp [HOLReading.term] at hs
  | orLeft _ _ _ => intro s' t' hs; simp [HOLReading.term] at hs
  | orRight _ _ _ => intro s' t' hs; simp [HOLReading.term] at hs
  | impLeft right _ ih =>
      intro s' t' hs ht
      obtain ⟨p', q', hp, hq, rfl⟩ := HOLReading.term_imp hs
      obtain ⟨p'', q'', hp', hq', rfl⟩ := HOLReading.term_imp ht
      rw [hq] at hq'
      cases hq'
      exact L.equal_impOf (ih hp hp') (.refl (L.term_typed hq))
  | impRight left _ ih =>
      intro s' t' hs ht
      obtain ⟨p', q', hp, hq, rfl⟩ := HOLReading.term_imp hs
      obtain ⟨p'', q'', hp', hq', rfl⟩ := HOLReading.term_imp ht
      rw [hp] at hp'
      cases hp'
      exact L.equal_impOf (.refl (L.term_typed hp)) (ih hq hq')
  | not _ _ => intro s' t' hs; simp [HOLReading.term] at hs
  | eqLeft right _ ih =>
      intro s' t' hs ht
      obtain ⟨l', r', hl, hr, rfl⟩ := HOLReading.term_eq hs
      obtain ⟨l'', r'', hl', hr', rfl⟩ := HOLReading.term_eq ht
      rw [hr] at hr'
      cases hr'
      exact L.equal_eqOf (ih hl hl') (.refl (L.term_typed hr))
  | eqRight left _ ih =>
      intro s' t' hs ht
      obtain ⟨l', r', hl, hr, rfl⟩ := HOLReading.term_eq hs
      obtain ⟨l'', r'', hl', hr', rfl⟩ := HOLReading.term_eq ht
      rw [hl] at hl'
      cases hl'
      exact L.equal_eqOf (.refl (L.term_typed hl)) (ih hr hr')
  | all _ ih =>
      intro s' t' hs ht
      obtain ⟨b', hb, rfl⟩ := HOLReading.term_all hs
      obtain ⟨c', hc, rfl⟩ := HOLReading.term_all ht
      exact L.equal_allOf_lam (ih hb hc)
  | ex _ _ => intro s' t' hs; simp [HOLReading.term] at hs

end Eta

/-- A βη-step between two read terms. -/
def ReadBetaEtaStep (ρ : HOLReading Head Base Const) {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
    (s t : HOL.Term Const Γ τ) : Prop :=
  (ρ.term s).isSome ∧ (ρ.term t).isSome ∧ HOL.EtaConversion.BetaEtaStep s t

/-- Related terms are equal, or both read. -/
theorem ReadBetaEtaConv.eq_or_read {ρ : HOLReading Head Base Const} {Γ : HOL.Ctx Base}
    {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    (conversion : Relation.EqvGen (ReadBetaEtaStep ρ) s t) :
    s = t ∨ ((ρ.term s).isSome ∧ (ρ.term t).isSome) := by
  induction conversion with
  | rel _ _ step => exact Or.inr ⟨step.1, step.2.1⟩
  | refl => exact Or.inl rfl
  | symm _ _ _ ih =>
      rcases ih with same | ⟨readS, readT⟩
      · exact Or.inl same.symm
      · exact Or.inr ⟨readT, readS⟩
  | trans _ _ _ _ _ first second =>
      rcases first with same | ⟨readS, readM⟩
      · rcases second with same' | ⟨readM', readT⟩
        · exact Or.inl (same.trans same')
        · subst same
          exact Or.inr ⟨readM', readT⟩
      · rcases second with same' | ⟨_, readT⟩
        · subst same'
          exact Or.inr ⟨readS, readM⟩
        · exact Or.inr ⟨readS, readT⟩

section ReadBetaEta

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

/-- **βη-conversion inside the read terms is typed equality**, at their
carrier. -/
theorem readBetaEta_equal {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {s t : HOL.Term Const Γ τ}
    (conversion : Relation.EqvGen (ReadBetaEtaStep ρ) s t) :
    ∀ {s' t' : Tm Head Γ.length}, ρ.term s = some s' → ρ.term t = some t' →
      Equal ρ.rules (ρ.objCtx Γ) s' t' (ρ.carrierAt Γ.length τ) := by
  induction conversion with
  | rel _ _ step =>
      intro s' t' hs ht
      obtain ⟨readS, _, stepped⟩ := step
      rcases stepped with beta | eta
      · obtain ⟨one⟩ := beta
        exact L.sourceStep_equal (realizes_nil ρ) (read_step ρ one readS).2 hs ht
      · exact etaStep_equal L eta hs ht
  | refl =>
      intro s' t' hs ht
      rw [hs] at ht
      cases ht
      exact .refl (L.term_typed hs)
  | symm _ _ _ ih =>
      intro s' t' hs ht
      exact .symm (ih ht hs)
  | trans _ _ _ first _ ihFirst ihSecond =>
      intro s' t' hs ht
      rcases ReadBetaEtaConv.eq_or_read first with same | ⟨_, middleRead⟩
      · subst same
        exact ihSecond hs ht
      · obtain ⟨m', hm⟩ := Option.isSome_iff_exists.mp middleRead
        exact .trans (ihFirst hs hm) (ihSecond hm ht)

end ReadBetaEta

#print axioms read_step
#print axioms repConversion_of_reduces
#print axioms fiber_equal_of_betaConv
#print axioms fiber_equal_of_conv
#print axioms fiber_eta_equal
#print axioms fiber_not_conservative
#print axioms etaStep_equal
#print axioms readBetaEta_equal

end Mettapedia.GSLT.Dedukti.HOLHubFiber
