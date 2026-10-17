import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission

/-!
# Representation flow of independently justified premise results

Provider output refinements follow actual row positions. Successful matches
retain previous values, and quantified bodies restore their lexical parameter.
The refinements justify later freshness and finite-collection observations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

theorem AtomicCaptureNames.append {assignment : Assignment} {left right : List String}
    (front : AtomicCaptureNames assignment left) (back : AtomicCaptureNames assignment right) :
    AtomicCaptureNames assignment (left ++ right) := by
  intro name member
  rcases List.mem_append.mp member with member | member
  · exact front name member
  · exact back name member

theorem FiniteCaptureNames.empty (assignment : Assignment) : FiniteCaptureNames assignment [] :=
  by intro name member; simp at member

theorem AtomicCaptureNames.empty (assignment : Assignment) : AtomicCaptureNames assignment [] :=
  by intro name member; simp at member

namespace Static

def RowSuffix (row : ProviderRow) (index : Nat) (values : List Pattern) : Prop :=
  ∀ ordinal, values[ordinal]? = row.values[index + ordinal]?

theorem RowSuffix.initial (row : ProviderRow) : RowSuffix row 0 row.values := by
  intro ordinal
  simp only [Nat.zero_add]

theorem RowSuffix.head {row : ProviderRow} {index : Nat} {value : Pattern} {values : List Pattern}
    (suffix : RowSuffix row index (value :: values)) : row.values[index]? = some value := by
  simpa only [List.getElem?_cons_zero, Nat.add_zero] using (suffix 0).symm

theorem RowSuffix.tail {row : ProviderRow} {index : Nat} {value : Pattern} {values : List Pattern}
    (suffix : RowSuffix row index (value :: values)) : RowSuffix row (index + 1) values := by
  intro ordinal
  simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 ordinal]
    using suffix (ordinal + 1)

theorem matching_finite_value {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name : String} {kind : CollType} {elements : List Pattern}
    (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial
      (.fvar name) (.collection kind elements none) final) : FiniteCaptureNames final [name] := by
  cases matching with
  | capture captured =>
    exact captureRest_finite (by simpa only [captureRest?] using captured)

theorem matching_atomic_value {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name atom : String}
    (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial
      (.fvar name) (.fvar atom) final) : AtomicCaptureNames final [name] := by
  cases matching with
  | capture captured => exact capture_atom captured

theorem output_finite {provider : ProviderSnapshot} {relation : String}
    {row : ProviderRow} (rowMember : row ∈ provider.rows) (rowRelation : row.relation = relation)
    {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    (suffix : RowSuffix row index values)
    (held : ArgumentsHold context index initial schemas values modes final) :
    FiniteCaptureNames final
      (representedOutputNames provider relation checkFiniteValue index schemas modes) := by
  induction held with
  | nil => exact .empty _
  | @cons index initial middle final schema value schemas values mode modes head tail ih =>
    have remaining := ih suffix.tail
    cases head with
    | input _ =>
      simpa only [representedOutputNames, List.nil_append] using remaining
    | output matching =>
      cases schema with
      | fvar name =>
        simp only [representedOutputNames]
        split
        · rename_i checked
          obtain ⟨actual, found, finite⟩ := checkProviderRepresentation_sound checked row rowMember rowRelation
          have same := Option.some.inj (found.symm.trans suffix.head)
          obtain ⟨kind, elements, shape⟩ := checkFiniteValue_sound finite
          subst actual
          rw [shape] at matching
          exact ((matching_finite_value matching).extension tail.extension).append remaining
        · simpa only [List.nil_append] using remaining
      | bvar index => simpa only [representedOutputNames, List.nil_append] using remaining
      | apply name arguments => simpa only [representedOutputNames, List.nil_append] using remaining
      | lambda name body => simpa only [representedOutputNames, List.nil_append] using remaining
      | multiLambda arity names body => simpa only [representedOutputNames, List.nil_append] using remaining
      | subst body replacement => simpa only [representedOutputNames, List.nil_append] using remaining
      | collection kind elements rest => simpa only [representedOutputNames, List.nil_append] using remaining

theorem output_atomic {provider : ProviderSnapshot} {relation : String}
    {row : ProviderRow} (rowMember : row ∈ provider.rows) (rowRelation : row.relation = relation)
    {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    (suffix : RowSuffix row index values)
    (held : ArgumentsHold context index initial schemas values modes final) :
    AtomicCaptureNames final
      (representedOutputNames provider relation checkAtomicValue index schemas modes) := by
  induction held with
  | nil => exact .empty _
  | @cons index initial middle final schema value schemas values mode modes head tail ih =>
    have remaining := ih suffix.tail
    cases head with
    | input _ =>
      simpa only [representedOutputNames, List.nil_append] using remaining
    | output matching =>
      cases schema with
      | fvar name =>
        simp only [representedOutputNames]
        split
        · rename_i checked
          obtain ⟨actual, found, atomic⟩ := checkProviderRepresentation_sound checked row rowMember rowRelation
          have same := Option.some.inj (found.symm.trans suffix.head)
          obtain ⟨atom, shape⟩ := checkAtomicValue_sound atomic
          subst actual
          rw [shape] at matching
          exact ((matching_atomic_value matching).extension tail.extension).append remaining
        · simpa only [List.nil_append] using remaining
      | bvar index => simpa only [representedOutputNames, List.nil_append] using remaining
      | apply name arguments => simpa only [representedOutputNames, List.nil_append] using remaining
      | lambda name body => simpa only [representedOutputNames, List.nil_append] using remaining
      | multiLambda arity names body => simpa only [representedOutputNames, List.nil_append] using remaining
      | subst body replacement => simpa only [representedOutputNames, List.nil_append] using remaining
      | collection kind elements rest => simpa only [representedOutputNames, List.nil_append] using remaining

theorem output_rest {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    (held : ArgumentsHold context index initial schemas values modes final) :
    FiniteCaptureNames final (outputRestNames schemas modes) := by
  induction held with
  | nil => exact .empty _
  | cons head tail ih =>
    cases head with
    | input _ => simpa only [outputRestNames, List.nil_append] using ih
    | output matching =>
      simpa only [outputRestNames] using
        ((matching_finite_restCaptures matching).extension tail.extension).append ih

theorem Refinement.Holds.extension {initial final : Assignment} {refinement : Refinement}
    (held : refinement.Holds initial) (extension : Extension initial final) : refinement.Holds final :=
  ⟨held.1.extension extension, held.2.1.extension extension, held.2.2.extension extension⟩

/-- A finite static row inventory does not establish an output-shape
invariant for a registered dynamic relation. -/
theorem representedOutputNames_dynamic {provider : ProviderSnapshot} {relation : String}
    (registered : relation ∈ provider.dynamicRelations) (check : Pattern → Bool) :
    ∀ (index : Nat) (schemas : List Pattern) (modes : List RelationArgMode),
      representedOutputNames provider relation check index schemas modes = [] := by
  intro index schemas
  induction schemas generalizing index with
  | nil => intro modes; cases modes <;> rfl
  | cons schema schemas ih =>
      intro modes
      cases modes with
      | nil => rfl
      | cons mode modes =>
          cases mode <;> cases schema <;>
            simp [representedOutputNames, checkProviderRepresentation_dynamic registered, ih]

theorem premiseFlow_holds {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event} {refinement : Refinement}
    (before : refinement.Holds initial)
    (held : PremiseHolds environment context premise initial final event) :
    (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement premise).refinement.Holds final := by
  cases held with
  | query query =>
    cases query with
    | row selected declared rowTyped arguments finalTyped =>
      have member := List.mem_of_getElem? selected
      have relation := rowTyped.1.trans
        (signature?_readout environment.provider _ _ _ declared).2.1
      have preserved := before.extension arguments.readout.extension
      simp only [premiseFlow, declared, Refinement.Holds]
      exact ⟨arguments.readout.produces.append preserved.1,
        ((output_rest arguments.readout).append
          (output_finite member relation (.initial _) arguments.readout)).append preserved.2.1,
        (output_atomic member relation (.initial _) arguments.readout).append preserved.2.2⟩
    | dynamicRow registered declared _ _ _ _ arguments _ =>
      have preserved := before.extension arguments.readout.extension
      simp only [premiseFlow, declared, Refinement.Holds,
        representedOutputNames_dynamic registered, List.nil_append, List.append_nil]
      exact ⟨arguments.readout.produces.append preserved.1,
        (output_rest arguments.readout).append preserved.2.1, preserved.2.2⟩
  | freshness _ _ => exact before
  | step _ _ _ matching _ =>
      have preserved := before.extension matching.matching.extends
      exact ⟨(matching_bound_names matching.matching).append preserved.1,
        (matching_finite_restCaptures matching.matching).append preserved.2.1, preserved.2.2⟩
  | scopedStep _ _ matching _ =>
      have preserved := before.extension matching.matching.extends
      exact ⟨(matching_bound_names matching.matching).append preserved.1,
        (matching_finite_restCaptures matching.matching).append preserved.2.1, preserved.2.2⟩
  | quantified read elements =>
      exact before.extension (PremiseHolds.quantified read elements).extension

theorem premisesFlow_holds {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List Event}
    {refinement : Refinement} (depthZero : context.quantifierDepth = 0)
    (before : refinement.Holds initial)
    (held : PremisesHold environment context premises initial final events) :
    (premisesFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex refinement premises).refinement.Holds final :=
  match held with
  | .nil => before
  | @PremisesHold.cons _ _ premise premises _ middle _ event events head tail => by
      have produced := premiseFlow_holds before head
      rw [depthZero] at produced
      exact premisesFlow_holds (context := context.next) (premises := premises)
        (refinement := (premiseFlow environment.language environment.provider context.rule
          context.spec context.premiseIndex 0 refinement premise).refinement) rfl produced tail
termination_by premises.length

end Static
end Mettapedia.OSLF.MeTTaIL.GeneralPremise
