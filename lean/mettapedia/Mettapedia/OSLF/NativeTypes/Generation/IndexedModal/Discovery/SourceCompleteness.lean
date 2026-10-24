import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Source

/-!
# Every independently specified contextual response has its computed source

The generated index/rely partition covers exactly the variables read by
the enclosing context. Completed assignments may contain additional focus
captures and premise outputs; neither can alter contextual reconstruction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Source

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.NativeTypes.Modal Instantiation NativeBindingMatchInstantiation
open FocusMeaning FiniteFocusChecking

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

def site (installed : Joined.Installed) (index : installed.Index) : Occurrences.Site :=
  (Occurrences.generate (NativeCubeProfile.language installed.indexed.operational))[
    installed.indexed.headers[index].site]

theorem site_selected (installed : Joined.Installed) (index : installed.Index) :
    Selects (site installed index).focus (site installed index).context
      (installed.indexed.schema index).declaration.rule.left := by
  let schema := installed.indexed.schema index
  let operational := installed.indexed.operational
  let raw := site installed index
  have generated : raw ∈ Occurrences.generate (NativeCubeProfile.language operational) :=
    List.getElem_mem installed.indexed.headers[index].site.isLt
  have source := (Occurrences.generate_spec _ raw).mp generated
  have compiledMember : schema.declaration ∈
      (GeneralExecutionAdmission.compile operational.generated.snapshot
        operational.generated.languageFragment.operational).rules := by
    have declared := List.fst_mem_of_mem_zipIdx schema.declared
    simpa only [BindingPipeline.plan, Generated.plan, StructuralDescent.Plan.rules_preserved]
      using declared
  obtain ⟨authored, ordinal, origin, _, compiled⟩ :=
    GeneralExecutionAdmission.compiled_rule_origin compiledMember
  have read := GeneralExecutionAdmission.rulePlan_readout compiled
  have snapshot : NativeCubeProfile.language operational = operational.generated.snapshot.language :=
    NativeCubeProfile.language_preserved operational
  have rawAt : operational.generated.snapshot.language.rewrites[raw.declaration]? = some raw.rule := by
    simpa only [snapshot] using List.mk_mem_zipIdx_iff_getElem?.mp source.1
  have authoredAt := List.mk_mem_zipIdx_iff_getElem?.mp origin
  have sameIndex : raw.declaration = ordinal :=
    installed.indexed.headers[index].matching.1.trans read.1
  rw [sameIndex] at rawAt
  have sameRule : raw.rule = authored := Option.some.inj (rawAt.symm.trans authoredAt)
  have sameLeft : raw.rule.left = schema.declaration.rule.left := by
    rw [sameRule, ← read.2.1]
    rfl
  exact sameLeft ▸ source.2

theorem site_position (installed : Joined.Installed) (index : installed.Index) :
    contextAddress (site installed index).context = (installed.indexed.schema index).position :=
  installed.indexed.headers[index].matching.2.1

private theorem lookup_agrees (entries completed : ScopedRuleMatching.Assignment)
    (valid : ∀ entry ∈ entries, lookup completed entry.1 = some entry.2)
    (name : String) (present : name ∈ entries.map Prod.fst) :
    lookup entries name = lookup completed name := by
  induction entries with
  | nil => cases present
  | cons entry rest ih =>
      rcases entry with ⟨head, value⟩
      by_cases same : head = name
      · subst head
        have stored := valid (name, value) List.mem_cons_self
        simp only [lookup, List.find?_cons, beq_self_eq_true, Option.map_some]
        exact stored.symm
      · have different : (head == name) = false := by simpa using same
        have tailPresent : name ∈ rest.map Prod.fst := by
          simpa only [List.map_cons, List.mem_cons, Prod.fst] using
            (show name ≠ head ∧ name ∈ rest.map Prod.fst from
              ⟨Ne.symm same, (List.mem_cons.mp present).resolve_left (Ne.symm same)⟩).2
        have tail := ih (fun entry member => valid entry (List.mem_cons_of_mem _ member)) tailPresent
        simpa only [lookup, List.find?_cons, different, ↓reduceIte] using tail

theorem context_parameter_names (operational : BindingPipeline.Installed)
    (header : SourceInterfaces.Header operational) (name : String)
    (present : name ∈ Occurrences.contextNames
      (Occurrences.generate (NativeCubeProfile.language operational))[header.site].context) :
    name ∈ header.indices.map (fun parameter => parameter.slot.name) ∨
      name ∈ operational.modal[header.origin].rely.map (fun parameter => parameter.slot.name) := by
  let raw : Occurrences.Site := (Occurrences.generate (NativeCubeProfile.language operational)).get header.site
  by_cases shared : name ∈ fvarNames raw.focus
  · apply Or.inl
    rw [header.index_names]
    exact (SortProfiles.DisplayedGraph.index_names_exact _ _).mpr ⟨present, shared⟩
  · apply Or.inr
    apply header.matching.2.2.mem_iff.mp
    exact (Occurrences.rely_names_spec _ _).mpr ⟨present, shared⟩

theorem seed_agrees (parameters : Parameters installed index ambient)
    (values : RelyValues installed index ambient) (payload : NativeReceiptRechecking.Payload)
    (indices : IndexMatches parameters.meaning payload) (relies : RelyMatches values payload) :
    ∀ name ∈ Occurrences.contextNames (site installed index).context,
      lookup (seed parameters values) name = lookup payload.completed name := by
  have all : ∀ entry ∈ seed parameters values, lookup payload.completed entry.1 = some entry.2 := by
    intro entry present
    rcases List.mem_append.mp present with left | right
    · obtain ⟨position, _, rfl⟩ := List.mem_map.mp left
      exact indices position
    · obtain ⟨position, _, rfl⟩ := List.mem_map.mp right
      exact relies position
  intro name present
  apply lookup_agrees (seed parameters values) payload.completed all name
  rcases context_parameter_names installed.indexed.operational (installed.indexed.headers.get index)
      name present with indexed | decoded
  ·
    obtain ⟨parameter, member, named⟩ := List.mem_map.mp indexed
    obtain ⟨position, located⟩ := List.mem_iff_get.mp member
    apply List.mem_map.mpr
    refine ⟨(parameter.slot.name, (parameters.indices position).value.val), ?_, ?_⟩
    · apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨position, List.mem_finRange _, ?_⟩
      congr 1
      exact congrArg (fun item => item.slot.name) located
    · exact named
  ·
    obtain ⟨parameter, member, named⟩ := List.mem_map.mp decoded
    obtain ⟨position, located⟩ := List.mem_iff_get.mp member
    apply List.mem_map.mpr
    refine ⟨(parameter.slot.name, (values position).val), ?_, ?_⟩
    · apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨position, List.mem_finRange _, ?_⟩
      congr 1
      exact congrArg (fun item => item.slot.name) located
    · exact named

set_option maxHeartbeats 800000 in
/-- Every independent selected firing reconstructs its canonical authored
left-hand side even after premises add further completed captures. -/
theorem response_instantiates (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern)
    (payload : NativeReceiptRechecking.Payload)
    (valid : SourceResponse parameters.meaning focus values source payload) :
    (instantiateAt? (installed.indexed.schema index).declaration.rule
      (installed.indexed.schema index).declaration.binding.spec ambient.length
      .left [] 0 payload.completed (installed.indexed.schema index).declaration.rule.left).map
        Pattern.eraseBinderMetadata = some source := by
  let plan := BindingPipeline.plan installed.indexed.operational.generated
  let schema := installed.indexed.schema index
  have shape := NativeBindingTreeAdmission.schema_tree
    ((NativeBindingTreeAdmission.check_exact plan).mp installed.semantic.sourceTrees) schema
  have selectedRule := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have selectedSpec := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  rw [← valid.2.1] at selectedRule selectedSpec
  cases valid.1 with
  | fire ruleLookup specLookup _ sorted matching _ premises _ _ =>
      cases Option.some.inj (ruleLookup.symm.trans selectedRule)
      cases Option.some.inj (specLookup.symm.trans selectedSpec)
      obtain ⟨rawSource, instantiated, erased⟩ := matching_reconstructs
        (operation := Substitution.instantiateBVar)
        (rule := schema.declaration.rule) (spec := schema.declaration.binding.spec)
        (ambient := (NativeBindingEventAction.bound ambient).length)
        (site := .left) (path := []) (depth := 0)
        (completed := payload.completed) (pattern := schema.declaration.rule.left)
        matching.matching shape premises.extension
      have interpreted : instantiateAt? schema.declaration.rule schema.declaration.binding.spec
          ambient.length .left [] 0 payload.completed schema.declaration.rule.left = some rawSource := by
        simpa only [NativeBindingEventAction.bound,
          Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map, instantiateAt?] using instantiated
      rw [interpreted]
      exact congrArg some (erased.trans
        (Pattern.eraseBinderMetadata_eq_self_of_canonical sorted.2.1))

/-- No independent response can require an ungenerated source. The computed
source uses only the request, while the response may retain arbitrarily many
additional matched values and ordered premise outputs. -/
theorem response_source_mem (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern)
    (payload : NativeReceiptRechecking.Payload)
    (valid : SourceResponse parameters.meaning focus values source payload) :
    source ∈ sources parameters focus values := by
  let plan := BindingPipeline.plan installed.indexed.operational.generated
  let schema := installed.indexed.schema index
  obtain ⟨rawFocus, selected, erased⟩ := valid.2.2.1
  have shape := NativeBindingTreeAdmission.schema_tree
    ((NativeBindingTreeAdmission.check_exact plan).mp installed.semantic.sourceTrees) schema
  have holes : focus.eraseBinderMetadata = rawFocus.eraseBinderMetadata := by
    rw [← erased, Pattern.eraseBinderMetadata_idempotent]
  have equality := SourceFilling.fill_congr (site_selected installed index) shape
    schema.declaration.rule schema.declaration.binding.spec ambient.length .left [] 0
    (seed parameters values) payload.completed focus rawFocus holes
    (seed_agrees parameters values payload valid.2.2.2.1 valid.2.2.2.2.1)
  rw [site_position installed index, fill_authored selected] at equality
  have reconstructed := response_instantiates parameters focus values source payload valid
  change source? parameters focus values =
    (instantiateAt? schema.declaration.rule schema.declaration.binding.spec ambient.length .left [] 0
      payload.completed schema.declaration.rule.left).map Pattern.eraseBinderMetadata at equality
  rw [reconstructed] at equality
  exact Option.mem_toList.mpr equality

/-- Any two independent responses to the same request start from the same
program, while their complete event payloads may still differ. -/
theorem response_source_unique (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (first second : Pattern)
    (left right : NativeReceiptRechecking.Payload)
    (firstResponse : SourceResponse parameters.meaning focus values first left)
    (secondResponse : SourceResponse parameters.meaning focus values second right) :
    first = second := by
  have firstMember := response_source_mem parameters focus values first left firstResponse
  have secondMember := response_source_mem parameters focus values second right secondResponse
  have firstFound : source? parameters focus values = some first := Option.mem_toList.mp firstMember
  have secondFound : source? parameters focus values = some second := Option.mem_toList.mp secondMember
  exact Option.some.inj (firstFound.symm.trans secondFound)

theorem missing_source_no_response (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (missing : source? parameters focus values = none) :
    ¬ ∃ source payload, SourceResponse parameters.meaning focus values source payload := by
  rintro ⟨source, payload, valid⟩
  have member := response_source_mem parameters focus values source payload valid
  simp only [sources, missing, Option.toList_none, List.not_mem_nil] at member

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Source
