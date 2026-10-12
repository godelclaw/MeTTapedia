import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginView

/-! # Separating controls for origin-coherent and origin-view composition -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginViewControls

open Mettapedia.GSLT.LanguageDef.Extension

private abbrev Spec := Nat × Nat
private abbrev Coherent := ModuleAlgebra.Presentation Nat String Spec
private abbrev View := OriginView.Presentation Nat String Spec

private def source : Entry Nat String Spec := ⟨1, "Foo", (0, 1)⟩
private def renamedSource : Entry Nat String Spec := ⟨1, "Bar", (0, 1)⟩
private def independentlyCopied : Entry Nat String Spec := ⟨2, "Foo", (0, 1)⟩
private def independentRule : Entry Nat String Spec := ⟨2, "Other", (1, 2)⟩

private def original : Coherent := ⟨{source}, by decide⟩
private def renamed : Coherent := ⟨{renamedSource}, by decide⟩
private def copied : Coherent := ⟨{independentlyCopied}, by decide⟩
private def independent : Coherent := ⟨{independentRule}, by decide⟩
private def mixed : View := ⟨{source, renamedSource}, by decide⟩

/-- This is a real origin-preserving replacement of the existing coherent algebra. -/
theorem replacement_builds_renamed : ModuleAlgebra.replace original 1 "Bar" (0, 1) = some renamed := by
  apply ModuleAlgebra.check_eq_some_iff.mpr
  decide

theorem same_origin : source.origin = renamedSource.origin := rfl
theorem same_behavior_body : source.body = renamedSource.body := rfl
theorem distinct_structural_views : OriginView.viewKey source ≠ OriginView.viewKey renamedSource := by
  decide

theorem coherent_rename_join_rejected : ModuleAlgebra.join original renamed = none := by decide

theorem view_rename_join_retains_both :
    OriginView.join (OriginView.ofCoherent original) (OriginView.ofCoherent renamed) = some mixed := by
  apply OriginView.join_eq_some_iff.mpr
  decide

theorem view_rename_join_cardinality : mixed.val.card = 2 := by decide

theorem shared_origin_is_retained : ModuleAlgebra.origins mixed.val = {1} := by decide

theorem coherent_rename_meet_retains_left : ModuleAlgebra.meet original renamed = original := by
  apply Subtype.ext
  decide

theorem coherent_rename_meet_reverse_retains_right : ModuleAlgebra.meet renamed original = renamed := by
  apply Subtype.ext
  decide

theorem coherent_rename_meet_not_commutative :
    ModuleAlgebra.meet original renamed ≠ ModuleAlgebra.meet renamed original := by
  intro same
  have values := congrArg (fun p : Coherent => p.val) same
  have different : (ModuleAlgebra.meet original renamed).val ≠
      (ModuleAlgebra.meet renamed original).val := by decide
  exact different values

theorem view_rename_meet_empty :
    OriginView.meet (OriginView.ofCoherent original) (OriginView.ofCoherent renamed) = OriginView.empty := by
  apply Subtype.ext
  decide

theorem coherent_rename_difference_empty : ModuleAlgebra.diff original renamed = ModuleAlgebra.empty := by
  apply Subtype.ext
  decide

theorem view_rename_difference_retains_left :
    OriginView.diff (OriginView.ofCoherent original) (OriginView.ofCoherent renamed) =
      OriginView.ofCoherent original := by
  apply Subtype.ext
  decide

theorem each_operand_has_one_representative :
    OriginView.OneRepresentativePerOrigin original.val ∧
      OriginView.OneRepresentativePerOrigin renamed.val := by decide

theorem operand_union_has_divergent_representatives :
    ¬ OriginView.OneRepresentativePerOrigin (original.val ∪ renamed.val) := by decide

theorem mixed_views_cannot_recover_coherence : OriginView.coherentOfView? mixed = none := by decide

theorem successful_single_view_recovers_coherence :
    OriginView.coherentOfView? (OriginView.ofCoherent original) = some original :=
  OriginView.coherentOfView_ofCoherent original

/-- Same bodies do not make independently created declarations share an identity. -/
theorem independent_same_label_view_join_rejected :
    OriginView.join (OriginView.ofCoherent original) (OriginView.ofCoherent copied) = none := by decide

theorem independent_same_label_coherent_join_rejected : ModuleAlgebra.join original copied = none := by
  decide

private def originalOccurrence : OriginView.Member mixed :=
  OriginView.includeLeft view_rename_join_retains_both ⟨source, by decide⟩

private def renamedOccurrence : OriginView.Member mixed :=
  OriginView.includeRight view_rename_join_retains_both ⟨renamedSource, by decide⟩

/-- Both occurrences survive despite having identical origin and semantic body. -/
theorem renamed_occurrences_remain_distinct : originalOccurrence ≠ renamedOccurrence := by
  intro same
  have labels := congrArg (fun occurrence : OriginView.Member mixed => occurrence.val.label) same
  have different : source.label ≠ renamedSource.label := by decide
  exact different labels

theorem same_origin_occurrences : originalOccurrence.val.origin = renamedOccurrence.val.origin := rfl
theorem same_body_occurrences : originalOccurrence.val.body = renamedOccurrence.val.body := rfl

private def independentWhole : Coherent := ⟨{source, independentRule}, by decide⟩

theorem independent_union_single :
    OriginView.OneRepresentativePerOrigin (original.val ∪ independent.val) := by decide

theorem independent_coherent_join : ModuleAlgebra.join original independent = some independentWhole := by
  apply ModuleAlgebra.join_eq_some_iff.mpr
  decide

theorem independent_view_join :
    OriginView.join (OriginView.ofCoherent original) (OriginView.ofCoherent independent) =
      some (OriginView.ofCoherent independentWhole) := by
  rw [← OriginView.join_agreement_of_union_single original independent independent_union_single,
    independent_coherent_join]
  rfl

theorem independent_meet_agrees :
    OriginView.ofCoherent (ModuleAlgebra.meet original independent) =
      OriginView.meet (OriginView.ofCoherent original) (OriginView.ofCoherent independent) :=
  OriginView.meet_agreement_of_union_single original independent independent_union_single

theorem independent_difference_agrees :
    OriginView.ofCoherent (ModuleAlgebra.diff original independent) =
      OriginView.diff (OriginView.ofCoherent original) (OriginView.ofCoherent independent) :=
  OriginView.diff_agreement_of_union_single original independent independent_union_single

theorem explicit_recovery_matches_coherent_rejection :
    (OriginView.join (OriginView.ofCoherent original) (OriginView.ofCoherent renamed)).bind
      OriginView.coherentOfView? = none := by
  rw [OriginView.join_coherent_through_view, coherent_rename_join_rejected]

/-- Repeated authored views share one declaration; divergent views both survive. -/
theorem nested_authoring_retains_views :
    OriginView.elaborate
      (.bundle [OriginView.quote (OriginView.ofCoherent original),
        .bundle [OriginView.quote (OriginView.ofCoherent renamed),
          OriginView.quote (OriginView.ofCoherent original)]]) = some mixed := by
  apply OriginView.check_eq_some_iff.mpr
  simp only [OriginView.quote, DeclarationDocument.values, DeclarationDocument.valuesList,
    ModuleAlgebra.unionFragments, List.foldr_cons, List.foldr_nil, List.append_nil,
    List.cons_append, List.nil_append, Finset.union_empty]
  decide

theorem conflicting_authoring_rejected :
    OriginView.elaborate
      (.bundle [OriginView.quote (OriginView.ofCoherent original),
        OriginView.quote (OriginView.ofCoherent copied)]) = none := by
  change OriginView.check (ModuleAlgebra.unionFragments _) = none
  simp only [OriginView.quote, DeclarationDocument.values, DeclarationDocument.valuesList,
    ModuleAlgebra.unionFragments, List.foldr_cons, List.foldr_nil, List.append_nil,
    List.cons_append, List.nil_append, Finset.union_empty]
  decide

theorem view_failure_associativity :
    (OriginView.join (OriginView.ofCoherent original) (OriginView.ofCoherent renamed)).bind
        (fun p => OriginView.join p (OriginView.ofCoherent copied)) =
      (OriginView.join (OriginView.ofCoherent renamed) (OriginView.ofCoherent copied)).bind
        (fun p => OriginView.join (OriginView.ofCoherent original) p) :=
  OriginView.join_assoc _ _ _

theorem view_partition_recovers_all_views :
    OriginView.join (OriginView.meet mixed (OriginView.ofCoherent renamed))
      (OriginView.diff mixed (OriginView.ofCoherent renamed)) = some mixed :=
  OriginView.join_meet_diff _ _

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginViewControls
