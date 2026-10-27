import Mettapedia.OSLF.Syntax.SignatureMorphismMetas

/-!
# What a signature morphism keeps of a rule

A morphism of binding signatures (`SigMor`) carries a positioned rewrite to a positioned rewrite (`SigMor.onRewrite`),
because it keeps occurrence counts (`countVar_mapTerm`). The same counts decide the slots of the generated modality, so
the slots are carried too, and the inclusion of a signature in its free extension commutes with carrying.

- **The slots are carried**: a rule variable is a rely parameter exactly when its image is one
  (`SigMor.relyParameter_onRewrite`), and a local parameter exactly when its image is one
  (`SigMor.localParameter_onRewrite`).
- **Embedding the base signature is natural** (`mapTerm_withMetas_embed`): a base term embedded in the free extension
  and carried along the extended morphism (`SigMor.withMetas`) is the carried term, embedded.

The controls are in `RhoSortErasure`.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S T : Signature}

/-- **A rule variable is a rely parameter exactly when its image is one.** -/
theorem SigMor.relyParameter_onRewrite (F : SigMor S T) (P : PositionedRewrite S) {s : S.Srt} (x : Var P.ctx s) :
    (F.onRewrite P).RelyParameter (mapVar F.sortMap s x) ↔ P.RelyParameter x := by
  change 0 < countVar (mapVar F.sortMap s (Var.succ x)) (F.onTerm P.position.ctxt) ∧
      countVar (mapVar F.sortMap s x) (F.onTerm P.position.redex) = 0 ↔ _
  rw [countVar_mapTerm F (mapVar F.sortMap) (Var.succ x) (fun _ y => sameVar_mapVar F _ y),
    countVar_mapTerm F (mapVar F.sortMap) x (fun _ y => sameVar_mapVar F _ y)]
  rfl

/-- **A rule variable is a local parameter exactly when its image is one.** -/
theorem SigMor.localParameter_onRewrite (F : SigMor S T) (P : PositionedRewrite S) {s : S.Srt} (x : Var P.ctx s) :
    (F.onRewrite P).LocalParameter (mapVar F.sortMap s x) ↔ P.LocalParameter x := by
  change countVar (mapVar F.sortMap s (Var.succ x)) (F.onTerm P.position.ctxt) = 0 ∧
      0 < countVar (mapVar F.sortMap s x) (F.onTerm P.position.redex) ↔ _
  rw [countVar_mapTerm F (mapVar F.sortMap) (Var.succ x) (fun _ y => sameVar_mapVar F _ y),
    countVar_mapTerm F (mapVar F.sortMap) x (fun _ y => sameVar_mapVar F _ y)]
  rfl

theorem embedArgs_castArgsArity (M : List (MetaArity T)) {as bs : List (List T.Srt × T.Srt)} (same : as = bs)
    {Δ : Ctx T} (args : Args T as Δ) :
    embedArgs (M := M) (castArgsArity same args) =
      castArgsArity (T := Binding.withMetas T M) same (embedArgs (M := M) args) := by
  subst same
  rfl

mutual
/-- **Embedding the base signature is natural**: embedding and then carrying along the extended morphism is carrying
and then embedding. -/
theorem mapTerm_withMetas_embed (F : SigMor S T) (M : List (MetaArity S)) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ) {s : S.Srt} (t : Term S Γ s),
      mapTerm (F.withMetas M) ν (embed (M := M) t) = embed (M := F.mapMetas M) (mapTerm F ν t)
  | _, _, _, _, .var _ => rfl
  | _, _, ν, _, .op o args =>
    congrArg (Term.op (S := Binding.withMetas T (F.mapMetas M)) (Sum.inl (F.opMap o)))
      ((congrArg (castArgsArity (T := Binding.withMetas T (F.mapMetas M)) _) (mapArgs_withMetas_embedArgs F M ν args)).trans
        (embedArgs_castArgsArity (F.mapMetas M) (F.carriesArity o).symm (mapArgs F ν args)).symm)

theorem mapArgs_withMetas_embedArgs (F : SigMor S T) (M : List (MetaArity S)) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ) (args : Args S as Γ),
      mapArgs (F.withMetas M) ν (embedArgs (M := M) args) = embedArgs (M := F.mapMetas M) (mapArgs F ν args)
  | _, _, _, _, .nil => rfl
  | _, _, _, ν, .cons (bs := bs) head tail =>
    congrArg₂ (fun head tail => Args.cons head tail) (mapTerm_withMetas_embed F M (liftVarMap F.sortMap ν bs) head)
      (mapArgs_withMetas_embedArgs F M ν tail)
end

end Mettapedia.OSLF.Binding
