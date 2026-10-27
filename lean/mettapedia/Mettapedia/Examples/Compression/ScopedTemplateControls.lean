import Mettapedia.Algorithms.Compression.ScopedTemplateWire
import Mettapedia.GSLT.LanguageDef.ScopedMatchingControls

/-!
Scoped reconstruction controls reuse the authored binding-language examples.
The separate finite control has a genuinely uninhabited unused sort: completing
every parameter is impossible, yet matching and reconstructing the used syntax
must still work.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.ScopedTemplateControls

open Mettapedia.OSLF.Binding
open Mettapedia.Algorithms.Compression

namespace Authored

open Mettapedia.GSLT.LanguageDef
open ScopedMatchingControls MetaDependencyControls ScopedMatcherDependencyBoundary
open PartialRenamingControls PartialRenamingInstantiationControls
open VariableArgumentRecognitionControls BoundPrefixProjectionControls
open WellSorted.OccurrenceControls (a b)

noncomputable local instance operatorEquality (sort : signature.Srt) :
    DecidableEq (signature.Op sort) := Classical.decEq _

theorem subset_reconstructs :
    ScopedTemplates.expandAtA []
      (setMeta (emptyMAcc : MAcc signature nestedDeclarations [a, b]) nestedIndex nestedBody)
      nestedSlot = some nestedSlotTarget :=
  ScopedTemplates.matched_expandsAtA [] emptyMAcc _ _ nestedSlot nestedSlotTarget
    nested_slot_records_actual_body (MAccLe.refl _)

theorem repeated_depths_reconstruct :
    ScopedTemplates.expandAtA []
      (setMeta (emptyMAcc : MAcc signature declarations []) dependentIndex (.var .zero))
      repeatedMetaDepths =
      some (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)) :=
  ScopedTemplates.matched_expandsAtA [] emptyMAcc _ _ repeatedMetaDepths _
    repeated_meta_at_different_depths (MAccLe.refl _)

end Authored

namespace Unused

abbrev rows : List (ScopedTemplateWire.Declaration String) := [⟨"constant", "T", []⟩]
abbrev signature := ScopedTemplateWire.signature rows
abbrev parameters : List (MetaArity signature) := [([], "absent")]

def constant : signature.Op "T" := ⟨⟨0, by decide⟩, rfl⟩
def pattern : Term (withMetas signature parameters) ["absent"] "T" := .op (.inl constant) .nil
def source : Term signature [] "T" := .op constant .nil
def requested : Term (withMetas signature parameters) ["absent"] "absent" :=
  .op (.inr (.mk ⟨0, by decide⟩)) .nil

theorem missing_sort_uninhabited : ¬ Nonempty (Term signature [] "absent") := by
  rintro ⟨term⟩
  cases term with
  | var position => nomatch position
  | op operator arguments =>
      rcases operator with ⟨⟨index, below⟩, correctSort⟩
      have zero : index = 0 := by
        change index < 1 at below
        omega
      subst index
      simp [rows] at correctSort

theorem no_total_ordinary_assignment : ¬ Nonempty (Sub signature ["absent"] []) := by
  rintro ⟨assignment⟩
  exact missing_sort_uninhabited ⟨assignment _ .zero⟩

theorem no_total_meta_assignment :
    ¬ Nonempty ((index : Fin parameters.length) →
      Term signature (parameters.get index).1 (parameters.get index).2) := by
  rintro ⟨assignment⟩
  exact missing_sort_uninhabited ⟨assignment ⟨0, by decide⟩⟩

theorem actual_match :
    smatchT (emptyMAcc : MAcc signature parameters ["absent"]) pattern source = some emptyMAcc := by
  unfold smatchT pattern source constant
  rw [smatchAtT.eq_3 (S := signature), dif_pos rfl]
  exact smatchAtA_nil [] emptyMAcc

theorem actual_reconstruction :
    ScopedTemplates.expandAtT [] (emptyMAcc : MAcc signature parameters ["absent"]) pattern =
      some source :=
  ScopedTemplates.matched_expands pattern source emptyMAcc actual_match

theorem actual_wire_reconstruction :
    ScopedTemplateWire.matchExpand rows parameters ["absent"] "T"
      ((ScopedTemplateWire.schemaCodec rows parameters ["absent"] "T").put pattern)
      ((ScopedTemplateWire.sourceCodec rows [] "T").put source) =
        some ((ScopedTemplateWire.sourceCodec rows [] "T").put source) :=
  ScopedTemplateWire.matchExpand_reconstructs rows parameters ["absent"] "T"
    pattern source emptyMAcc actual_match

theorem missing_used_capture_refused :
    ScopedTemplates.expandAtT [] (emptyMAcc : MAcc signature parameters ["absent"]) requested = none := by
  unfold requested
  rw [ScopedTemplates.expandAtT.eq_2 (S := signature)]
  rfl

theorem wrong_sort_wire_refused :
    (ScopedTemplateWire.sourceCodec rows [] "absent").get
      ((ScopedTemplateWire.sourceCodec rows [] "T").put source) = none := by rfl

end Unused

end Mettapedia.Examples.Compression.ScopedTemplateControls
