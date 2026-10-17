import Mettapedia.Languages.Megalodon.SourceTermFragment
import Mettapedia.Languages.Megalodon.SourceDefinitionInvariant
import Mettapedia.Languages.Megalodon.SortedABTRefinement
import Mettapedia.GSLT.LanguageDef.SortedABTSubstitution
import Mathlib.Tactic.SplitIfs

/-!
# Source substitution through the shared all-sort binder machinery

The common ABT operation weakens every free variable sort beneath a binder.
On the Megalodon source term fragment it agrees with native term substitution,
at every depth and for arbitrary replacements. This connects the source
compatibility boundary to the general capture-avoiding operation rather than
identifying the old selected-axis operation with that stronger operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceBinderRefinement
open MathdataKernel SortedABTRefinement
open Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT

private def shiftMap (cutoff amount : Nat) : Term.Renaming VarSort :=
  fun sort index => if sort = .term then if index < cutoff then index else index + amount else index

private theorem lift_shiftMap (binders : List VarSort) (cutoff amount : Nat) :
    Term.liftRenaming binders (shiftMap cutoff amount) =
      shiftMap (cutoff + Term.binderCount .term binders) amount := by
  funext sort index
  cases sort <;> simp only [Term.liftRenaming, Term.liftIndex, shiftMap]
  all_goals split_ifs <;> simp_all <;> omega

mutual
private theorem rename_shift (term : ABT) (cutoff amount : Nat) :
    Term.parallelRename (shiftMap cutoff amount) term = Term.lift .term cutoff amount term := by
  cases term with
  | idx sort index =>
      cases sort <;> simp [Term.parallelRename, shiftMap, Term.lift]
      split_ifs <;> rfl
  | node head fields =>
      exact congrArg (Term.node head) (fields_rename_shift fields cutoff amount)

private theorem fields_rename_shift (fields : ABTFields) (cutoff amount : Nat) :
    Term.Fields.parallelRename (shiftMap cutoff amount) fields = Term.Fields.lift .term cutoff amount fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Term.Fields.parallelRename, Term.Fields.lift, lift_shiftMap,
        rename_shift, fields_rename_shift rest]
end

private theorem weaken_encode (term : Tm) :
    Term.parallelRename (Term.weakenRenaming [VarSort.term]) (encode term) = encode (Tm.shift 0 1 term) := by
  have same : Term.weakenRenaming [VarSort.term] = shiftMap 0 1 := by
    funext sort index
    cases sort <;> simp [Term.weakenRenaming, Term.binderCount, shiftMap, Nat.add_comm]
  rw [same, rename_shift, ← encode_shift]

private theorem shift_add (term : Tm) (cutoff first second : Nat) :
    Tm.shift cutoff first (Tm.shift cutoff second term) = Tm.shift cutoff (second + first) term := by
  induction term generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff
      · simp [Tm.shift, below]
      · simp [Tm.shift, below, show ¬ index + second < cutoff by omega, Nat.add_assoc]
  | named | prim => rfl
  | app _ _ ihf iha | imp _ _ ihf iha => simp [Tm.shift, ihf, iha]
  | lam _ _ ih | all _ _ ih => simp [Tm.shift, ih]
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => simp [Tm.shift, ih]

private theorem shift_zero (term : Tm) (cutoff : Nat) : Tm.shift cutoff 0 term = term := by
  induction term generalizing cutoff <;> simp_all [Tm.shift]

private def substitution (depth : Nat) (replacement : Tm) : Term.Substitution VarSort Head
  | .type, index => .idx .type index
  | .term, index => if index < depth then .idx .term index else
      if index = depth then encode (Tm.shift 0 depth replacement) else .idx .term (index - 1)

private theorem lift_nil (σ : Term.Substitution VarSort Head) : Term.liftSubstitution [] σ = σ := by
  funext sort index
  simp [Term.liftSubstitution, Term.binderCount]

private theorem lift_substitution (depth : Nat) (replacement : Tm) :
    Term.liftSubstitution [VarSort.term] (substitution depth replacement) =
      substitution (depth + 1) replacement := by
  funext sort index
  cases sort with
  | type => simp [Term.liftSubstitution, Term.binderCount, substitution, Term.parallelRename, Term.weakenRenaming]
  | term =>
      cases index with
      | zero => simp [Term.liftSubstitution, Term.binderCount, substitution]
      | succ index =>
          by_cases below : index < depth
          · simp [Term.liftSubstitution, Term.binderCount, substitution, below,
              show index + 1 < depth + 1 by omega, Term.parallelRename, Term.weakenRenaming, Nat.add_comm]
          · by_cases same : index = depth
            · subst index
              simp [Term.liftSubstitution, Term.binderCount, substitution, weaken_encode, shift_add]
            · have above : ¬ index + 1 < depth + 1 := by omega
              simp [Term.liftSubstitution, Term.binderCount, substitution, below, same, above,
                Term.parallelRename, Term.weakenRenaming, show 1 + (index - 1) = index by omega]

private theorem lift_keeps_types (binders : List VarSort) (σ : Term.Substitution VarSort Head)
    (same : ∀ index, σ .type index = .idx .type index) (index : Nat) :
    Term.liftSubstitution binders σ .type index = .idx .type index := by
  by_cases below : index < Term.binderCount .type binders
  · simp [Term.liftSubstitution, below]
  · simp [Term.liftSubstitution, below, same, Term.parallelRename, Term.weakenRenaming,
      Nat.add_sub_of_le (Nat.le_of_not_gt below)]

private theorem types_unchanged (σ : Term.Substitution VarSort Head)
    (same : ∀ index, σ .type index = .idx .type index) (type : Tp) :
    Term.parallelSubstitute σ (encodeType type) = encodeType type := by
  induction type generalizing σ with
  | var index => exact same index
  | prop | base => rfl
  | arr domain codomain ihd ihc =>
      change Term.parallelSubstitute σ
        (.node .typeArr (.cons [] (encodeType domain) (.cons [] (encodeType codomain) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil, ihd σ same, ihc σ same]
      rfl
  | all body ih =>
      change Term.parallelSubstitute σ (.node .typeAll (.cons [.type] (encodeType body) .nil)) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute,
        ih _ (lift_keeps_types [.type] σ same)]
      rfl

private theorem head_unchanged {head : Tm} (admitted : SourceTermFragment.Head head)
    (depth : Nat) (replacement : Tm) :
    Term.parallelSubstitute (substitution depth replacement) (encode head) = encode head := by
  induction admitted with
  | named | prim => rfl
  | @typeApp head type _ ih =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node .termTypeApp (.cons [] (encode head) (.cons [] (encodeType type) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil, ih,
        types_unchanged (substitution depth replacement) (fun _ => rfl) type]
      rfl

theorem source_substitution {body : Tm} (admitted : SourceTermFragment.Term body)
    (depth : Nat) (replacement : Tm) :
    Term.parallelSubstitute (substitution depth replacement) (encode body) =
      encode (Tm.instantiateAt depth replacement body) := by
  induction admitted generalizing depth with
  | db index =>
      simp [encode, Term.parallelSubstitute, substitution, Tm.instantiateAt]
      split_ifs <;> rfl
  | head head => rw [head_unchanged head, head.instantiate]
  | @app function argument _ _ ihf iha =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node .termApp (.cons [] (encode function) (.cons [] (encode argument) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil, ihf, iha]
      rfl
  | @imp domain codomain _ _ ihd ihc =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node .termImp (.cons [] (encode domain) (.cons [] (encode codomain) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil, ihd, ihc]
      rfl
  | @lam type body _ ih =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node .termLam (.cons [] (encodeType type) (.cons [.term] (encode body) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        lift_substitution, ih, types_unchanged (substitution depth replacement) (fun _ => rfl) type]
      rfl
  | @all type body _ ih =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node .termAll (.cons [] (encodeType type) (.cons [.term] (encode body) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        lift_substitution, ih, types_unchanged (substitution depth replacement) (fun _ => rfl) type]
      rfl

/-- The shared capture-avoiding substitution and the independent publication
traversal coincide on the entire source fragment, not only closed examples. -/
theorem publication_uses_all_sorts {body : Tm} (admitted : SourceTermFragment.Term body) (replacement : Tm) :
    Term.substituteTop .term (encode replacement) (encode body) =
      encode (SourceTermFragment.publicationSubstitute 0 replacement body) := by
  have same : Term.topSubstitution .term (encode replacement) = substitution 0 replacement := by
    funext sort index
    cases sort <;> cases index <;> simp [Term.topSubstitution, substitution, shift_zero]
  rw [Term.substituteTop, same, source_substitution admitted, SourceTermFragment.substitution_agrees admitted]

private theorem lift_keeps_terms (binders : List VarSort) (σ : Term.Substitution VarSort Head)
    (bound : Nat) (same : ∀ index, index < bound → σ .term index = .idx .term index)
    (index : Nat) (inside : index < bound + Term.binderCount .term binders) :
    Term.liftSubstitution binders σ .term index = .idx .term index := by
  by_cases below : index < Term.binderCount .term binders
  · simp [Term.liftSubstitution, below]
  · have available : index - Term.binderCount .term binders < bound := by omega
    simp [Term.liftSubstitution, below, same _ available, Term.parallelRename,
      Term.weakenRenaming, Nat.add_sub_of_le (Nat.le_of_not_gt below)]

/-- A substitution that fixes all variables occurring in a term leaves that
term unchanged, including beneath either sort of binder. -/
private theorem scoped_unchanged {body : Tm} {bound : Nat}
    (scope : SourceScopeInvariant.Scoped bound body) (σ : Term.Substitution VarSort Head)
    (sameTypes : ∀ index, σ .type index = .idx .type index)
    (sameTerms : ∀ index, index < bound → σ .term index = .idx .term index) :
    Term.parallelSubstitute σ (encode body) = encode body := by
  induction body generalizing bound σ with
  | db index => exact sameTerms index scope
  | named | prim => rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      change Term.parallelSubstitute σ
        (.node _ (.cons [] (encode function) (.cons [] (encode argument) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        ihf scope.1 σ sameTypes sameTerms, iha scope.2 σ sameTypes sameTerms]
      rfl
  | lam type body ih | all type body ih =>
      change Term.parallelSubstitute σ
        (.node _ (.cons [] (encodeType type) (.cons [.term] (encode body) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        types_unchanged σ sameTypes type,
        ih scope _ (lift_keeps_types [.term] σ sameTypes) (lift_keeps_terms [.term] σ bound sameTerms)]
      rfl
  | typeApp body type ih =>
      change Term.parallelSubstitute σ
        (.node .termTypeApp (.cons [] (encode body) (.cons [] (encodeType type) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        ih scope σ sameTypes sameTerms, types_unchanged σ sameTypes type]
      rfl
  | typeLam body ih | typeAll body ih =>
      change Term.parallelSubstitute σ (.node _ (.cons [.type] (encode body) .nil)) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute,
        ih scope _ (lift_keeps_types [.type] σ sameTypes) (lift_keeps_terms [.type] σ bound sameTerms)]
      rfl

/-- The all-sort operation also agrees after definition expansion. The
invariant concerns term closure of polymorphic regions, not their absence. -/
theorem protected_substitution {body : Tm} (safe : SourceScopeInvariant.Protected body)
    (depth : Nat) (replacement : Tm) :
    Term.parallelSubstitute (substitution depth replacement) (encode body) =
      encode (Tm.instantiateAt depth replacement body) := by
  induction body generalizing depth with
  | db index =>
      simp [encode, Term.parallelSubstitute, substitution, Tm.instantiateAt]
      split_ifs <;> rfl
  | named | prim => rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node _ (.cons [] (encode function) (.cons [] (encode argument) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        ihf safe.1, iha safe.2]
      rfl
  | lam type body ih | all type body ih =>
      change Term.parallelSubstitute (substitution depth replacement)
        (.node _ (.cons [] (encodeType type) (.cons [.term] (encode body) .nil))) = _
      simp only [Term.parallelSubstitute, Term.Fields.parallelSubstitute, lift_nil,
        lift_substitution, ih safe,
        types_unchanged (substitution depth replacement) (fun _ => rfl) type]
      rfl
  | typeApp body type _ =>
      have region : SourceScopeInvariant.Scoped 0 (.typeApp body type) := safe.1
      rw [scoped_unchanged region (substitution depth replacement) (fun _ => rfl) (fun index inside => by omega),
        SourceScopeInvariant.instantiate_eq region depth replacement (Nat.zero_le depth)]
  | typeLam body _ =>
      have region : SourceScopeInvariant.Scoped 0 (.typeLam body) := safe.1
      rw [scoped_unchanged region (substitution depth replacement) (fun _ => rfl) (fun index inside => by omega),
        SourceScopeInvariant.instantiate_eq region depth replacement (Nat.zero_le depth)]
  | typeAll body _ =>
      have region : SourceScopeInvariant.Scoped 0 (.typeAll body) := safe.1
      rw [scoped_unchanged region (substitution depth replacement) (fun _ => rfl) (fun index inside => by omega),
        SourceScopeInvariant.instantiate_eq region depth replacement (Nat.zero_le depth)]

theorem protected_publication_uses_all_sorts {body : Tm}
    (safe : SourceScopeInvariant.Protected body) (replacement : Tm) :
    Term.substituteTop .term (encode replacement) (encode body) =
      encode (SourceTermFragment.publicationSubstitute 0 replacement body) := by
  have same : Term.topSubstitution .term (encode replacement) = substitution 0 replacement := by
    funext sort index
    cases sort <;> cases index <;> simp [Term.topSubstitution, substitution, shift_zero]
  rw [Term.substituteTop, same, protected_substitution safe,
    SourceScopeInvariant.publication_substitution_agrees safe]

theorem normalized_publication_uses_all_sorts {environment : Environment}
    (definitions : SourceScopeInvariant.Definitions environment) {body result : Tm}
    (safe : SourceScopeInvariant.Protected body) (fuel : Nat)
    (normalized : MathdataKernel.normalize environment fuel body = some result) (replacement : Tm) :
    Term.substituteTop .term (encode replacement) (encode result) =
      encode (SourceTermFragment.publicationSubstitute 0 replacement result) :=
  protected_publication_uses_all_sorts
    ((SourceScopeInvariant.full_normalize_invariants definitions fuel normalized).2 safe) replacement

end Mettapedia.Languages.Megalodon.SourceBinderRefinement
