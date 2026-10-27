import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.JudgmentReplay

/-!
# Complete finite evidence for the annotated declarative judgment

Every existing typing, equality or subtyping derivation has a finite accepted
certificate. Primitive root completeness is supplied by the selected root
decoder; no conversion search or normalization is assumed.
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

theorem derives_complete (decoder : RootDecoder P.computation) {statement : CStatement Head}
    (derived : CDerivable P statement) : Derives (rules P decoder) statement := by
  induction derived with
  | @headType n Γ h u h0 =>
      refine .node [] _
        ⟨(@Code.headType Head decoder.Code n Γ h u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        cases member
  | @var n Γ i =>
      refine .node [] _
        ⟨(@Code.var Head decoder.Code n Γ i), ?_⟩ ?_
      · rfl
      · intro premise member
        cases member
  | @const n Γ name type u h0 _ h1 ih0 =>
      refine .node [(.typing .nil type (.head u))] _
        ⟨(@Code.const Head decoder.Code n Γ name type u), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @piForm n Γ A B u v w _ h0 _ h1 h2 ih0 ih1 =>
      refine .node [(.typing Γ A (.head u)), (.typing (.snoc Γ A) B (.head v))] _
        ⟨(@Code.piForm Head decoder.Code n Γ A B u v w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1, if_pos h2]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @sigmaForm n Γ A B u v w _ h0 _ h1 h2 ih0 ih1 =>
      refine .node [(.typing Γ A (.head u)), (.typing (.snoc Γ A) B (.head v))] _
        ⟨(@Code.sigmaForm Head decoder.Code n Γ A B u v w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1, if_pos h2]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @lamIntro n Γ A body B u w _ h0 _ h1 _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ A (.head w)), (.typing Γ (.pi A B) (.head u)), (.typing (.snoc Γ A) body B)] _
        ⟨(@Code.lamIntro Head decoder.Code n Γ A body B u w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @appElim n Γ g a A B _ _ ih0 ih1 =>
      refine .node [(.typing Γ g (.pi A B)), (.typing Γ a A)] _
        ⟨(@Code.appElim Head decoder.Code n Γ g a A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @pairIntro n Γ a b A B u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ (.sigma A B) (.head u)), (.typing Γ a A), (.typing Γ b (CTm.inst0 a B))] _
        ⟨(@Code.pairIntro Head decoder.Code n Γ a b A B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @fstElim n Γ p A B _ ih0 =>
      refine .node [(.typing Γ p (.sigma A B))] _
        ⟨(@Code.fstElim Head decoder.Code n Γ p A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @sndElim n Γ p A B _ ih0 =>
      refine .node [(.typing Γ p (.sigma A B))] _
        ⟨(@Code.sndElim Head decoder.Code n Γ p A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @idForm n Γ A a b u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ A (.head u)), (.typing Γ a A), (.typing Γ b A)] _
        ⟨(@Code.idForm Head decoder.Code n Γ A a b u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @reflIntro n Γ a A _ ih0 =>
      refine .node [(.typing Γ a A)] _
        ⟨(@Code.reflIntro Head decoder.Code n Γ a A), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @sub n Γ t A B _ _ ih0 ih1 =>
      refine .node [(.typing Γ t A), (.sub Γ A B)] _
        ⟨(@Code.sub Head decoder.Code n Γ t A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @conv n Γ t A B u _ _ h0 ih0 ih1 =>
      refine .node [(.typing Γ t A), (.equality Γ A B (.head u))] _
        ⟨(@Code.conv Head decoder.Code n Γ t A B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @refl n Γ a A _ ih0 =>
      refine .node [(.typing Γ a A)] _
        ⟨(@Code.refl Head decoder.Code n Γ a A), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @symm n Γ a b A _ ih0 =>
      refine .node [(.equality Γ a b A)] _
        ⟨(@Code.symm Head decoder.Code n Γ a b A), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @trans n Γ a b c A _ _ ih0 ih1 =>
      refine .node [(.equality Γ a b A), (.equality Γ b c A)] _
        ⟨(@Code.trans Head decoder.Code n Γ a b c A), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @convEq n Γ a b A B u _ _ h0 ih0 ih1 =>
      refine .node [(.equality Γ a b A), (.equality Γ A B (.head u))] _
        ⟨(@Code.convEq Head decoder.Code n Γ a b A B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @subEq n Γ a b A B _ _ ih0 ih1 =>
      refine .node [(.equality Γ a b A), (.sub Γ A B)] _
        ⟨(@Code.subEq Head decoder.Code n Γ a b A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @headEq n Γ h h' A h0 _ _ ih0 ih1 =>
      refine .node [(.typing Γ (.head h) A), (.typing Γ (.head h') A)] _
        ⟨(@Code.headEq Head decoder.Code n Γ h h' A), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @piCong n Γ A A' B B' u v w _ h0 _ h1 h2 ih0 ih1 =>
      refine .node [(.equality Γ A A' (.head u)), (.equality (.snoc Γ A) B B' (.head v))] _
        ⟨(@Code.piCong Head decoder.Code n Γ A A' B B' u v w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1, if_pos h2]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @sigmaCong n Γ A A' B B' u v w _ h0 _ h1 h2 ih0 ih1 =>
      refine .node [(.equality Γ A A' (.head u)), (.equality (.snoc Γ A) B B' (.head v))] _
        ⟨(@Code.sigmaCong Head decoder.Code n Γ A A' B B' u v w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1, if_pos h2]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @idCong n Γ A A' a a' b b' u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.equality Γ A A' (.head u)), (.equality Γ a a' A), (.equality Γ b b' A)] _
        ⟨(@Code.idCong Head decoder.Code n Γ A A' a a' b b' u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @lamCong n Γ A A' body body' B u w _ h0 _ h1 _ ih0 ih1 ih2 =>
      refine .node [(.equality Γ A A' (.head w)), (.typing Γ (.pi A B) (.head u)), (.equality (.snoc Γ A) body body' B)] _
        ⟨(@Code.lamCong Head decoder.Code n Γ A A' body body' B u w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @appCong n Γ f g a b A B _ _ ih0 ih1 =>
      refine .node [(.equality Γ f g (.pi A B)), (.equality Γ a b A)] _
        ⟨(@Code.appCong Head decoder.Code n Γ f g a b A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1
  | @pairCong n Γ a a' b b' A B u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ (.sigma A B) (.head u)), (.equality Γ a a' A), (.equality Γ b b' (CTm.inst0 a B))] _
        ⟨(@Code.pairCong Head decoder.Code n Γ a a' b b' A B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @fstCong n Γ p q A B _ ih0 =>
      refine .node [(.equality Γ p q (.sigma A B))] _
        ⟨(@Code.fstCong Head decoder.Code n Γ p q A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @sndCong n Γ p q A B _ ih0 =>
      refine .node [(.equality Γ p q (.sigma A B))] _
        ⟨(@Code.sndCong Head decoder.Code n Γ p q A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @reflCong n Γ a b A _ ih0 =>
      refine .node [(.equality Γ a b A)] _
        ⟨(@Code.reflCong Head decoder.Code n Γ a b A), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @betaPi n Γ A a body B u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ (.pi A B) (.head u)), (.typing (.snoc Γ A) body B), (.typing Γ a A)] _
        ⟨(@Code.betaPi Head decoder.Code n Γ A a body B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @betaFst n Γ A a b B u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ (.sigma A B) (.head u)), (.typing Γ a A), (.typing Γ b (CTm.inst0 a B))] _
        ⟨(@Code.betaFst Head decoder.Code n Γ A a b B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @betaSnd n Γ A a b B u _ h0 _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ (.sigma A B) (.head u)), (.typing Γ a A), (.typing Γ b (CTm.inst0 a B))] _
        ⟨(@Code.betaSnd Head decoder.Code n Γ A a b B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @root n Γ left right A premises step required _ _ _ ihPremises ihLeft ihRight =>
      obtain ⟨code, decoded⟩ := decoder.complete step required
      refine .node ([.typing Γ left A, .typing Γ right A] ++ premises.map (CPremise.statement Γ)) _
        ⟨.root code, ?_⟩ ?_
      · simp only [decode, decoded, and_self, if_true]
      · intro premise member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at member
        rcases member with (rfl | rfl) | ⟨original, member, rfl⟩
        · exact ihLeft
        · exact ihRight
        · exact ihPremises original member
  | @etaPi n Γ f g A B _ _ _ ih0 ih1 ih2 =>
      refine .node [(.typing Γ f (.pi A B)), (.typing Γ g (.pi A B)), (.equality (.snoc Γ A)
        (.app (f.rename wk) (.var 0)) (.app (g.rename wk) (.var 0)) B)] _
        ⟨(@Code.etaPi Head decoder.Code n Γ f g A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
  | @etaSigma n Γ p q A B _ _ _ _ ih0 ih1 ih2 ih3 =>
      refine .node [(.typing Γ p (.sigma A B)), (.typing Γ q (.sigma A B)), (.equality Γ (.fst p) (.fst q) A), (.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B))] _
        ⟨(@Code.etaSigma Head decoder.Code n Γ p q A B), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
        · exact ih3
  | @subEqual n Γ A B u _ h0 ih0 =>
      refine .node [(.equality Γ A B (.head u))] _
        ⟨(@Code.subEqual Head decoder.Code n Γ A B u), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact ih0
  | @subUniv n Γ u v h0 =>
      refine .node [] _
        ⟨(@Code.subUniv Head decoder.Code n Γ u v), ?_⟩ ?_
      · simp only [decode, if_pos h0]
      · intro premise member
        cases member
  | @subPi n Γ A A' B B' u u' w _ h0 _ h1 _ h2 _ ih0 ih1 ih2 ih3 =>
      refine .node [(.typing Γ (.pi A B) (.head u)), (.typing Γ (.pi A' B') (.head u')), (.equality Γ A A' (.head w)), (.sub (.snoc Γ A) B B')] _
        ⟨(@Code.subPi Head decoder.Code n Γ A A' B B' u u' w), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1, if_pos h2]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
        · exact ih3
  | @subSigma n Γ A A' B B' u u' _ h0 _ h1 _ _ ih0 ih1 ih2 ih3 =>
      refine .node [(.typing Γ (.sigma A B) (.head u)), (.typing Γ (.sigma A' B') (.head u')), (.sub Γ A A'), (.sub (.snoc Γ A) B B')] _
        ⟨(@Code.subSigma Head decoder.Code n Γ A A' B B' u u'), ?_⟩ ?_
      · simp only [decode, if_pos h0, if_pos h1]
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact ih0
        · exact ih1
        · exact ih2
        · exact ih3
  | @subTrans n Γ A B C _ _ ih0 ih1 =>
      refine .node [(.sub Γ A B), (.sub Γ B C)] _
        ⟨(@Code.subTrans Head decoder.Code n Γ A B C), ?_⟩ ?_
      · rfl
      · intro premise member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ih0
        · exact ih1

theorem derivable_iff (decoder : RootDecoder P.computation) (statement : CStatement Head) :
    CDerivable P statement ↔ Derives (rules P decoder) statement :=
  ⟨derives_complete P decoder, derives_sound P decoder⟩

/-- The common checker compares both conclusion and every ordered premise. -/
def interface (decoder : RootDecoder P.computation) : RuleWitness (rules P decoder) where
  W := (statement : CStatement Head) × Code Head decoder.Code statement
  isInstance witness premises conclusion :=
    match decode P decoder witness.2 with
    | none => false
    | some required => decide (conclusion = witness.1 ∧ premises = required)
  sound := by
    intro ⟨statement, code⟩ premises conclusion accepted
    cases decoded : decode P decoder code with
    | none => simp [decoded] at accepted
    | some required =>
        simp only [decoded, decide_eq_true_eq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨code, decoded⟩
  complete := by
    rintro premises conclusion ⟨code, decoded⟩
    exact ⟨⟨conclusion, code⟩, by simp [decoded]⟩

theorem derivable_iff_checked_tree (decoder : RootDecoder P.computation) (statement : CStatement Head) :
    CDerivable P statement ↔
      ∃ certificate : Logic.Derivation (CStatement Head) (interface P decoder).W,
        certificate.valid (interface P decoder) = true ∧ certificate.concl = statement := by
  rw [derivable_iff P decoder]
  exact ⟨Derives.exists_derivation (interface P decoder), by
    rintro ⟨certificate, accepted, rfl⟩
    exact certificate.valid_sound (interface P decoder) accepted⟩

/-- Shared graphs replay the same annotated judgments and preserve the
ordered parent references of each local rule. -/
theorem derivable_iff_checked_graph (decoder : RootDecoder P.computation) (statement : CStatement Head) :
    CDerivable P statement ↔
      ∃ (nodes : List (DerivationGraph.Node (CStatement Head) (interface P decoder).W Unit))
        (cache : Array (CStatement Head)) (root : Nat),
        DerivationGraph.replay (interface P decoder) nodes = some cache ∧ cache[root]? = some statement :=
  (derivable_iff P decoder statement).trans
    (DerivationGraph.derives_iff_checked_graph (interface P decoder) () statement)

#print axioms derives_complete
#print axioms derivable_iff_checked_tree
#print axioms derivable_iff_checked_graph

end TypedEquality.Annotated.Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
