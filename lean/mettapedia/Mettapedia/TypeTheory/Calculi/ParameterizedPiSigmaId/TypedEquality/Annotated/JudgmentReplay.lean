import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.JudgmentCode
import Mettapedia.Logic.DerivationGraph

/-!
# Replay of annotated typing, equality and subtyping derivations

Finite local codes implement exactly the independently defined forty-rule
annotated judgment. Complete derivations keep the original premise lists,
including declared-root obligations. The source judgment does not require
context formation at every rule; formation remains a separate checked input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Annotated.Checking

open Mettapedia.Logic
variable {Head : Type} {R : Rules Head} (P : ChurchRules R) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]

theorem decode_sound (decoder : RootDecoder P.computation) {statement : CStatement Head}
    (code : Code Head decoder.Code statement) {premises : List (CStatement Head)}
    (accepted : decode P decoder code = some premises)
    (children : ∀ premise ∈ premises, CDerivable P premise) : CDerivable P statement := by
  cases code with
  | @headType _n _Γ _h _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.headType h0
  | @var _n _Γ i =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.var i
  | @const _n _Γ _name _type _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1
      cases accepted
      exact CDerivable.const h0 (children (.typing .nil _type (.head _u)) (by simp)) h1
  | @piForm _n _Γ _A _B _u _v _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1 h2
      cases accepted
      exact CDerivable.piForm (children (.typing _Γ _A (.head _u)) (by simp)) h0 (children (.typing (.snoc _Γ _A) _B (.head _v)) (by simp)) h1 h2
  | @sigmaForm _n _Γ _A _B _u _v _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1 h2
      cases accepted
      exact CDerivable.sigmaForm (children (.typing _Γ _A (.head _u)) (by simp)) h0 (children (.typing (.snoc _Γ _A) _B (.head _v)) (by simp)) h1 h2
  | @lamIntro _n _Γ _A _body _B _u _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1
      cases accepted
      exact CDerivable.lamIntro (children (.typing _Γ _A (.head _w)) (by simp)) h0 (children (.typing _Γ (.pi _A _B) (.head _u)) (by simp)) h1 (children (.typing (.snoc _Γ _A) _body _B) (by simp))
  | @appElim _n _Γ _g _a _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.appElim (children (.typing _Γ _g (.pi _A _B)) (by simp)) (children (.typing _Γ _a _A) (by simp))
  | @pairIntro _n _Γ _a _b _A _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.pairIntro (children (.typing _Γ (.sigma _A _B) (.head _u)) (by simp)) h0 (children (.typing _Γ _a _A) (by simp)) (children (.typing _Γ _b (CTm.inst0 _a _B)) (by simp))
  | @fstElim _n _Γ _p _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.fstElim (children (.typing _Γ _p (.sigma _A _B)) (by simp))
  | @sndElim _n _Γ _p _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.sndElim (children (.typing _Γ _p (.sigma _A _B)) (by simp))
  | @idForm _n _Γ _A _a _b _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.idForm (children (.typing _Γ _A (.head _u)) (by simp)) h0 (children (.typing _Γ _a _A) (by simp)) (children (.typing _Γ _b _A) (by simp))
  | @reflIntro _n _Γ _a _A =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.reflIntro (children (.typing _Γ _a _A) (by simp))
  | @sub _n _Γ _t _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.sub (children (.typing _Γ _t _A) (by simp)) (children (.sub _Γ _A _B) (by simp))
  | @conv _n _Γ _t _A _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.conv (children (.typing _Γ _t _A) (by simp)) (children (.equality _Γ _A _B (.head _u)) (by simp)) h0
  | @refl _n _Γ _a _A =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.refl (children (.typing _Γ _a _A) (by simp))
  | @symm _n _Γ _a _b _A =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.symm (children (.equality _Γ _a _b _A) (by simp))
  | @trans _n _Γ _a _b _c _A =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.trans (children (.equality _Γ _a _b _A) (by simp)) (children (.equality _Γ _b _c _A) (by simp))
  | @convEq _n _Γ _a _b _A _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.convEq (children (.equality _Γ _a _b _A) (by simp)) (children (.equality _Γ _A _B (.head _u)) (by simp)) h0
  | @subEq _n _Γ _a _b _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.subEq (children (.equality _Γ _a _b _A) (by simp)) (children (.sub _Γ _A _B) (by simp))
  | @headEq _n _Γ _h _h' _A =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.headEq h0 (children (.typing _Γ (.head _h) _A) (by simp)) (children (.typing _Γ (.head _h') _A) (by simp))
  | @piCong _n _Γ _A _A' _B _B' _u _v _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1 h2
      cases accepted
      exact CDerivable.piCong (children (.equality _Γ _A _A' (.head _u)) (by simp)) h0 (children (.equality (.snoc _Γ _A) _B _B' (.head _v)) (by simp)) h1 h2
  | @sigmaCong _n _Γ _A _A' _B _B' _u _v _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1 h2
      cases accepted
      exact CDerivable.sigmaCong (children (.equality _Γ _A _A' (.head _u)) (by simp)) h0 (children (.equality (.snoc _Γ _A) _B _B' (.head _v)) (by simp)) h1 h2
  | @idCong _n _Γ _A _A' _a _a' _b _b' _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.idCong (children (.equality _Γ _A _A' (.head _u)) (by simp)) h0 (children (.equality _Γ _a _a' _A) (by simp)) (children (.equality _Γ _b _b' _A) (by simp))
  | @lamCong _n _Γ _A _A' _body _body' _B _u _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1
      cases accepted
      exact CDerivable.lamCong (children (.equality _Γ _A _A' (.head _w)) (by simp)) h0 (children (.typing _Γ (.pi _A _B) (.head _u)) (by simp)) h1 (children (.equality (.snoc _Γ _A) _body _body' _B) (by simp))
  | @appCong _n _Γ _f _g _a _b _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.appCong (children (.equality _Γ _f _g (.pi _A _B)) (by simp)) (children (.equality _Γ _a _b _A) (by simp))
  | @pairCong _n _Γ _a _a' _b _b' _A _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.pairCong (children (.typing _Γ (.sigma _A _B) (.head _u)) (by simp)) h0 (children (.equality _Γ _a _a' _A) (by simp)) (children (.equality _Γ _b _b' (CTm.inst0 _a _B)) (by simp))
  | @fstCong _n _Γ _p _q _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.fstCong (children (.equality _Γ _p _q (.sigma _A _B)) (by simp))
  | @sndCong _n _Γ _p _q _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.sndCong (children (.equality _Γ _p _q (.sigma _A _B)) (by simp))
  | @reflCong _n _Γ _a _b _A =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.reflCong (children (.equality _Γ _a _b _A) (by simp))
  | @betaPi _n _Γ _A _a _body _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.betaPi (children (.typing _Γ (.pi _A _B) (.head _u)) (by simp)) h0 (children (.typing (.snoc _Γ _A) _body _B) (by simp)) (children (.typing _Γ _a _A) (by simp))
  | @betaFst _n _Γ _A _a _b _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.betaFst (children (.typing _Γ (.sigma _A _B) (.head _u)) (by simp)) h0 (children (.typing _Γ _a _A) (by simp)) (children (.typing _Γ _b (CTm.inst0 _a _B)) (by simp))
  | @betaSnd _n _Γ _A _a _b _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.betaSnd (children (.typing _Γ (.sigma _A _B) (.head _u)) (by simp)) h0 (children (.typing _Γ _a _A) (by simp)) (children (.typing _Γ _b (CTm.inst0 _a _B)) (by simp))
  | @root n Γ left right A code =>
      cases decoded : decoder.decode code with
      | none => simp only [decode, decoded, reduceCtorEq] at accepted
      | some result =>
          simp only [decode, decoded] at accepted
          split_ifs at accepted with same
          · cases accepted
            obtain ⟨leftSame, rightSame⟩ := same
            subst left right
            obtain ⟨step, required⟩ := decoder.sound decoded
            exact .root step required
              (fun premise member => children _ (List.mem_append_right _ (List.mem_map.mpr ⟨premise, member, rfl⟩)))
              (children _ (by simp)) (children _ (by simp))
  | @etaPi _n _Γ _f _g _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.etaPi (children (.typing _Γ _f (.pi _A _B)) (by simp)) (children (.typing _Γ _g (.pi _A _B)) (by simp)) (children (.equality (.snoc _Γ _A)
        (.app (_f.rename wk) (.var 0)) (.app (_g.rename wk) (.var 0)) _B) (by simp))
  | @etaSigma _n _Γ _p _q _A _B =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.etaSigma (children (.typing _Γ _p (.sigma _A _B)) (by simp)) (children (.typing _Γ _q (.sigma _A _B)) (by simp)) (children (.equality _Γ (.fst _p) (.fst _q) _A) (by simp)) (children (.equality _Γ (.snd _p) (.snd _q) (CTm.inst0 (.fst _p) _B)) (by simp))
  | @subEqual _n _Γ _A _B _u =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.subEqual (children (.equality _Γ _A _B (.head _u)) (by simp)) h0
  | @subUniv _n _Γ _u _v =>
      simp only [decode] at accepted
      split_ifs at accepted with h0
      cases accepted
      exact CDerivable.subUniv h0
  | @subPi _n _Γ _A _A' _B _B' _u _u' _w =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1 h2
      cases accepted
      exact CDerivable.subPi (children (.typing _Γ (.pi _A _B) (.head _u)) (by simp)) h0 (children (.typing _Γ (.pi _A' _B') (.head _u')) (by simp)) h1 (children (.equality _Γ _A _A' (.head _w)) (by simp)) h2 (children (.sub (.snoc _Γ _A) _B _B') (by simp))
  | @subSigma _n _Γ _A _A' _B _B' _u _u' =>
      simp only [decode] at accepted
      split_ifs at accepted with h0 h1
      cases accepted
      exact CDerivable.subSigma (children (.typing _Γ (.sigma _A _B) (.head _u)) (by simp)) h0 (children (.typing _Γ (.sigma _A' _B') (.head _u')) (by simp)) h1 (children (.sub _Γ _A _A') (by simp)) (children (.sub (.snoc _Γ _A) _B _B') (by simp))
  | @subTrans _n _Γ _A _B _C =>
      simp only [decode] at accepted
      cases accepted
      exact CDerivable.subTrans (children (.sub _Γ _A _B) (by simp)) (children (.sub _Γ _B _C) (by simp))

/-- The local relation is the accepted primitive code and its actual ordered
premises. Soundness above relates it to the independent declarative rules. -/
def rules (decoder : RootDecoder P.computation) (premises : List (CStatement Head))
    (conclusion : CStatement Head) : Prop :=
  ∃ code : Code Head decoder.Code conclusion, decode P decoder code = some premises

theorem derives_sound (decoder : RootDecoder P.computation) {statement : CStatement Head}
    (derived : Derives (rules P decoder) statement) : CDerivable P statement := by
  induction derived with
  | node premises conclusion rule _ ih =>
      obtain ⟨code, accepted⟩ := rule
      exact decode_sound P decoder code accepted ih

#print axioms decode_sound
#print axioms derives_sound

end TypedEquality.Annotated.Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
