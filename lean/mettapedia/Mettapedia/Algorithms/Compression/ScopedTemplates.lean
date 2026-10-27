import Mettapedia.OSLF.Syntax.ScopedMatching

/-!
# Scoped template reconstruction from partial captures

The term algebra, binding signatures, typed argument-spine recognizer and
matcher are the existing shared ones. This layer expands only the captures a
matched template actually requests. It supplies no default inhabitants for
unused rule variables or metavariables, whose sorts may have none.

Contextual holes support the matcher's injective bound-variable profile,
including subsets and permutations. Repeated or nonvariable spines may be
declined; that is not a claim of general higher-order unsolvability.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ScopedTemplates

open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)}
variable [DecidableEq S.Srt]

/-- Apply a stored contextual body at the template's actual argument spine.
The recognized renaming fixes the identity of each selected binder. -/
def applyBody {dependencies bound ordinary : Ctx S} {sort : S.Srt}
    (arguments : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bound ++ ordinary))
    (body : Term S dependencies sort) : Option (Term S (bound ++ []) sort) := do
  let projected ← strengthenA (Strengthener.boundPrefix (S := withMetas S M) bound ordinary) arguments
  let selected ← recognizeVariableArguments projected
  pure (rename (fun s v => injPrefix (Γ := []) bound (selected.rho s v)) body)

omit [DecidableEq S.Srt] in
private theorem rescope_unScopeVar : ∀ (bound : Ctx S) {sort : S.Srt}
    (position : Var (bound ++ []) sort),
    injPrefix (Γ := []) bound (unScopeVar bound position) = position
  | [], _, position => nomatch position
  | _ :: _, _, .zero => rfl
  | _ :: rest, _, .succ position => congrArg Var.succ (rescope_unScopeVar rest position)

omit [DecidableEq S.Srt] in
private theorem rescope_unScope (bound : Ctx S) {sort : S.Srt}
    (source : Term S (bound ++ []) sort) :
    rename (fun _ v => injPrefix (Γ := []) bound v) (unScope bound source) = source := by
  simp only [unScope, rename_comp, rescope_unScopeVar, rename_id]

/-- Recovery and application use the same checked spine, not only the same
spine length. Local binders inside the captured body remain local. -/
theorem applyBody_recovered {dependencies bound ordinary : Ctx S} {sort : S.Srt}
    (arguments : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bound ++ ordinary))
    (source : Term S (bound ++ []) sort) (body : Term S dependencies sort)
    (found : recoverBoundVariableBody arguments source = some body) :
    applyBody arguments body = some source := by
  unfold recoverBoundVariableBody at found
  cases projected : strengthenA (Strengthener.boundPrefix (S := withMetas S M) bound ordinary) arguments with
  | none => simp [projected] at found
  | some spine =>
      simp only [projected, recoverVariableArgumentBody] at found
      cases recognized : recognizeVariableArguments spine with
      | none => simp [recognized] at found
      | some selected =>
          simp only [recognized] at found
          have restored := rename_strengthenT selected.baseInverse (unScope bound source) body found
          simp only [applyBody, projected, Bind.bind, Option.bind, recognized]
          rw [← rename_comp, restored, rescope_unScope]
          rfl

mutual
/-- Independently expand a template using partial captures. A missing used
capture is a refusal, rather than an invented value or an unevaluated hole. -/
def expandAtT {ordinary : Ctx S} (bound : Ctx S) {sort : S.Srt}
    (captures : MAcc S M ordinary) :
    Term (withMetas S M) (bound ++ ordinary) sort → Option (Term S (bound ++ []) sort)
  | .var position =>
      match splitVar bound position with
      | .inl boundVar => some (.var (injPrefix (Γ := []) bound boundVar))
      | .inr ruleVar => (captures.vars _ ruleVar).map (rename (fun _ v => weakenVar bound v))
  | .op (.inr (.mk index)) arguments => do
      let body ← captures.metas index
      applyBody arguments body
  | .op (.inl constructor) arguments => (expandAtA bound captures arguments).map (.op constructor)
termination_by pattern => 2 * termSize pattern
decreasing_by all_goals simp only [termSize]; omega

/-- Each constructor field opens exactly its declared binder prefix. -/
def expandAtA {ordinary : Ctx S} (bound : Ctx S)
    {arity : List (List S.Srt × S.Srt)} (captures : MAcc S M ordinary) :
    Args (withMetas S M) arity (bound ++ ordinary) → Option (Args S arity (bound ++ []))
  | .nil => some .nil
  | .cons (bs := binders) head tail => do
      let value ← expandAtT (binders ++ bound) captures
        (castTermCtx (T := withMetas S M) (List.append_assoc binders bound ordinary).symm head)
      let rest ← expandAtA bound captures tail
      pure (.cons (castTermCtx (T := S) (List.append_assoc binders bound []) value) rest)
termination_by arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

variable [opDec : ∀ sort : S.Srt, DecidableEq (S.Op sort)]

omit [DecidableEq S.Srt] opDec in
private theorem cast_roundtrip {first second : Ctx S} (same : first = second)
    {sort : S.Srt} (value : Term S second sort) :
    castTermCtx same (castTermCtx same.symm value) = value := by cases same; rfl

mutual
/-- Successful matching supplies all captures used by its own template.
Later agreeing captures may be retained from other components of the rule. -/
theorem matched_expandsAtT : ∀ {ordinary : Ctx S} (bound : Ctx S) {sort : S.Srt}
    (before matched final : MAcc S M ordinary)
    (pattern : Term (withMetas S M) (bound ++ ordinary) sort)
    (source : Term S (bound ++ []) sort),
    smatchAtT bound before pattern source = some matched →
    MAccLe matched final → expandAtT bound final pattern = some source
  | _, bound, _, before, matched, final, .var position, source, found, retained => by
      rw [smatchAtT] at found
      cases split : splitVar bound position with
      | inl boundVar =>
          simp only [split] at found
          split at found
          · rename_i same
            simp [expandAtT, split, same]
          · cases found
      | inr ruleVar =>
          simp only [split] at found
          cases recovered : strengthenT (Strengthener.ofWeakenPrefix S (Γ := []) bound) source with
          | none => simp [recovered] at found
          | some body =>
              simp only [recovered] at found
              have stored : final.vars _ ruleVar = some body := by
                cases previous : before.vars _ ruleVar with
                | none =>
                    simp only [previous, Option.some.injEq] at found
                    subst matched
                    exact retained.1 _ ruleVar body (updatePSub_self before.vars ruleVar body)
                | some old =>
                    simp only [previous] at found
                    split at found
                    · rename_i same
                      cases Option.some.inj found
                      simpa only [same] using retained.1 _ ruleVar old previous
                    · cases found
              have restored := rename_strengthenT
                (Strengthener.ofWeakenPrefix S (Γ := []) bound) source body recovered
              simpa only [expandAtT, split, stored, Option.map_some] using congrArg some restored
  | _, bound, _, before, matched, final, .op (.inr (.mk index)) arguments, source, found, retained => by
      rw [smatchAtT] at found
      cases recovered : recoverBoundVariableBody arguments source with
      | none => simp [recovered] at found
      | some body =>
          simp only [recovered] at found
          have stored : final.metas index = some body := by
            cases previous : before.metas index with
            | none =>
                simp only [previous, Option.some.injEq] at found
                subst matched
                exact retained.2 index body (setMeta_self before index body)
            | some old =>
                simp only [previous] at found
                split at found
                · rename_i same
                  cases Option.some.inj found
                  simpa only [same] using retained.2 index old previous
                · cases found
          simpa only [expandAtT, stored, Bind.bind, Option.bind] using
            applyBody_recovered arguments source body recovered
  | _, bound, _, before, matched, final, .op (.inl constructor) arguments,
      .op actual values, found, retained => by
      rw [smatchAtT] at found
      split at found
      · rename_i same
        subst actual
        simp only [expandAtT, matched_expandsAtA bound before matched final arguments values found retained,
          Option.map_some]
      · cases found
  | _, bound, _, before, matched, final, .op (.inl constructor) arguments,
      .var position, found, _ => by
      rw [smatchAtT] at found
      cases found
termination_by _ _ _ _ _ _ pattern _ _ _ => 2 * termSize pattern
decreasing_by all_goals simp only [termSize]; omega

theorem matched_expandsAtA : ∀ {ordinary : Ctx S} (bound : Ctx S)
    {arity : List (List S.Srt × S.Srt)} (before matched final : MAcc S M ordinary)
    (patterns : Args (withMetas S M) arity (bound ++ ordinary))
    (sources : Args S arity (bound ++ [])),
    smatchAtA bound before patterns sources = some matched →
    MAccLe matched final → expandAtA bound final patterns = some sources
  | _, _, _, _, _, _, .nil, .nil, _, _ => by rw [expandAtA]
  | ordinary, bound, _, before, matched, final, .cons (bs := binders) head tail,
      .cons value rest, found, retained => by
      rw [smatchAtA] at found
      split at found
      · cases found
      · rename_i middle headMatch
        have headRetained := (smatchAtA_mono bound middle matched tail rest found).trans retained
        have first := matched_expandsAtT (binders ++ bound) before middle final _ _ headMatch headRetained
        have later := matched_expandsAtA bound middle matched final tail rest found retained
        simp only [expandAtA, first, Bind.bind, Option.bind, later]
        rw [cast_roundtrip]
        rfl
termination_by _ _ _ _ _ _ patterns _ _ _ => 2 * argsSize patterns + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

/-- No total completion or closed inhabitant for an unused parameter is
needed to reconstruct the source accepted by the actual scoped matcher. -/
theorem matched_expands {ordinary : Ctx S} {sort : S.Srt}
    (pattern : Term (withMetas S M) ordinary sort) (source : Term S [] sort)
    (captures : MAcc S M ordinary)
    (found : smatchT emptyMAcc pattern source = some captures) :
    expandAtT [] captures pattern = some source :=
  matched_expandsAtT [] emptyMAcc captures captures pattern source found (MAccLe.refl captures)

end Mettapedia.Algorithms.Compression.ScopedTemplates
