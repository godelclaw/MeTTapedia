import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.Spec.Match.ModelTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Finite scope at equation selection

The scope contains every variable in the query, retained atoms, stored binding
values, assigned keys and equality endpoints. Its structural scan has no
evaluation-fuel parameter. Membership realizes the independent evaluator's
`QueryVisibleName` relation at every atom depth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Spec.Match.Merge
open Spec.Match.ModelTheory
open Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement

/-- Ordered support of a binding presentation, including nested values. -/
def bindingNames (bindings : Bindings) : List String :=
  bindings.assignments.flatMap (fun entry =>
    entry.1 :: (encodeModelAtom entry.2).vars) ++
  bindings.equalities.flatMap (fun edge => [edge.1, edge.2])

/-- Names forbidden to a fresh equation instance. -/
def visibleNames (live : List Atom) (query : Atom) (incoming : Bindings) : List String :=
  (encodeModelAtom query).vars ++
    live.flatMap (fun atom => (encodeModelAtom atom).vars) ++ bindingNames incoming

theorem bindingNames_toFinset (bindings : Bindings) :
    (bindingNames bindings).toFinset = bindingSupport bindings := rfl

/-- The complete finite scope is exactly the declarative visible-name scope. -/
theorem mem_visibleNames_iff (live : List Atom) (query : Atom) (incoming : Bindings)
    (name : String) :
    name ∈ visibleNames live query incoming ↔ QueryVisibleName live query incoming name := by
  simp only [visibleNames, bindingNames, List.mem_append, List.mem_flatMap]
  constructor
  · rintro ((queryMember | liveMember) | bindingMember)
    · exact Or.inl (atomOccurs_iff_mem_translated_vars.mpr queryMember)
    · obtain ⟨atom, member, occurrence⟩ := liveMember
      exact Or.inr (Or.inl ⟨atom, member, atomOccurs_iff_mem_translated_vars.mpr occurrence⟩)
    · rcases bindingMember with assigned | equality
      · obtain ⟨⟨key, value⟩, member, occurrence⟩ := assigned
        simp only [List.mem_cons] at occurrence
        rcases occurrence with rfl | occurrence
        · exact Or.inr (Or.inr (Or.inl ⟨value, member⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨key, value, member, atomOccurs_iff_mem_translated_vars.mpr occurrence⟩)))
      · obtain ⟨⟨left, right⟩, member, occurrence⟩ := equality
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, occurrence⟩)))
  · rintro (queryOccurs | liveOccurs | assigned | storedOccurs | equality)
    · exact Or.inl (Or.inl (atomOccurs_iff_mem_translated_vars.mp queryOccurs))
    · obtain ⟨atom, member, occurrence⟩ := liveOccurs
      exact Or.inl (Or.inr ⟨atom, member, atomOccurs_iff_mem_translated_vars.mp occurrence⟩)
    · obtain ⟨value, member⟩ := assigned
      exact Or.inr (Or.inl ⟨(name, value), member, by simp⟩)
    · obtain ⟨key, value, member, occurrence⟩ := storedOccurs
      exact Or.inr (Or.inl ⟨(key, value), member,
        List.mem_cons_of_mem _ (atomOccurs_iff_mem_translated_vars.mp occurrence)⟩)
    · obtain ⟨left, right, member, occurrence⟩ := equality
      exact Or.inr (Or.inr ⟨(left, right), member, by simpa using occurrence⟩)

theorem query_occurrence_mem {live : List Atom} {query : Atom} {incoming : Bindings}
    {name : String} (occurrence : AtomOccurs query name) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr (Or.inl occurrence)

theorem retained_occurrence_mem {live : List Atom} {query atom : Atom} {incoming : Bindings}
    {name : String} (member : atom ∈ live) (occurrence : AtomOccurs atom name) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr
    (Or.inr (Or.inl ⟨atom, member, occurrence⟩))

theorem assignment_key_mem {live : List Atom} {query value : Atom} {incoming : Bindings}
    {name : String} (member : (name, value) ∈ incoming.assignments) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr
    (Or.inr (Or.inr (Or.inl ⟨value, member⟩)))

theorem assignment_value_occurrence_mem {live : List Atom} {query value : Atom}
    {incoming : Bindings} {key name : String} (member : (key, value) ∈ incoming.assignments)
    (occurrence : AtomOccurs value name) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨key, value, member, occurrence⟩))))

theorem equality_left_mem {live : List Atom} {query : Atom} {incoming : Bindings}
    {left right : String} (member : (left, right) ∈ incoming.equalities) :
    left ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming left).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, Or.inl rfl⟩))))

theorem equality_right_mem {live : List Atom} {query : Atom} {incoming : Bindings}
    {left right : String} (member : (left, right) ∈ incoming.equalities) :
    right ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming right).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, Or.inr rfl⟩))))

/-- Every name mentioned by the incoming constraint theory is protected by
the equation-selection scope. -/
theorem binding_var_visible {live : List Atom} {query : Atom} {incoming : Bindings}
    {name : String} (member : name ∈ Spec.Bindings.ScopeObservation.specBindingVars incoming) :
    QueryVisibleName live query incoming name := by
  simp only [Spec.Bindings.ScopeObservation.specBindingVars, List.mem_append,
    List.mem_flatMap] at member
  rcases member with assigned | equality
  · obtain ⟨⟨key,value⟩, stored, occurs⟩ := assigned
    rcases List.mem_cons.mp occurs with rfl | occurs
    · exact Or.inr (Or.inr (Or.inl ⟨value,stored⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨key,value,stored,(atomOccurs_iff_mem_typeVars value name).mpr occurs⟩)))
  · obtain ⟨⟨left,right⟩, stored, occurs⟩ := equality
    simp only [List.mem_cons,List.not_mem_nil,or_false] at occurs
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨left,right,stored,occurs⟩)))

/-- Visible query names consist exactly of current syntax, retained syntax and
complete incoming constraint support. -/
theorem queryVisible_support_iff (live : List Atom) (query : Atom)
    (bindings : Bindings) (name : String) :
    Spec.Eval.Steps.QueryVisibleName live query bindings name ↔
      Spec.Match.Merge.AtomOccurs query name ∨
        (∃ atom∈live,Spec.Match.Merge.AtomOccurs atom name) ∨ name∈Spec.Bindings.ScopeObservation.specBindingVars bindings := by
  have occurs : ∀ atom, Spec.Match.Merge.AtomOccurs atom name ↔ name∈TypeSubst.typeVars atom := by
    intro atom
    exact Spec.Eval.Steps.atomOccurs_iff_mem_typeVars atom name
  simp only [Spec.Eval.Steps.QueryVisibleName,Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap,
    List.mem_cons,List.not_mem_nil,or_false]
  simp only [occurs]
  constructor
  · rintro (queryOccurs | liveOccurs | ⟨value,stored⟩ | ⟨key,value,stored,inside⟩ |
        ⟨left,right,stored,inside⟩)
    · exact Or.inl queryOccurs
    · exact Or.inr (Or.inl liveOccurs)
    · exact Or.inr (Or.inr (Or.inl ⟨(name,value),stored,Or.inl rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨(key,value),stored,Or.inr inside⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨(left,right),stored,inside⟩))
  · rintro (queryOccurs | liveOccurs | ⟨⟨key,value⟩,stored,same | inside⟩ |
        ⟨⟨left,right⟩,stored,inside⟩)
    · exact Or.inl queryOccurs
    · exact Or.inr (Or.inl liveOccurs)
    · change name=key at same
      subst key
      exact Or.inr (Or.inr (Or.inl ⟨value,stored⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨key,value,stored,inside⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨left,right,stored,inside⟩)))


/-- A closed current query leaves precisely the retained syntax and complete
incoming binding support observable at equation selection. -/
theorem visible_closed_iff {live : List Atom} {query : Atom} {incoming : Bindings}
    (closed : TypeSubst.typeVars query = []) (name : String) :
    name ∈ visibleNames live query incoming ↔
      name ∈ live.flatMap TypeSubst.typeVars ∨ name ∈ Spec.Bindings.ScopeObservation.specBindingVars incoming := by
  rw [mem_visibleNames_iff]
  constructor
  · rintro (queryOccurs | liveOccurs | assigned | storedOccurs | equality)
    · have present := atomOccurs_mem_typeVars queryOccurs
      rw [closed] at present
      cases present
    · obtain ⟨atom,member,occurs⟩ := liveOccurs
      exact Or.inl (List.mem_flatMap.mpr ⟨atom,member,atomOccurs_mem_typeVars occurs⟩)
    · obtain ⟨value,member⟩ := assigned
      exact Or.inr (by
        simp only [Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
        exact Or.inl ⟨(name,value),member,by simp⟩)
    · obtain ⟨key,value,member,occurs⟩ := storedOccurs
      exact Or.inr (by
        simp only [Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
        exact Or.inl ⟨(key,value),member,List.mem_cons_of_mem _ (atomOccurs_mem_typeVars occurs)⟩)
    · obtain ⟨left,right,member,same⟩ := equality
      exact Or.inr (by
        simp only [Spec.Bindings.ScopeObservation.specBindingVars,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨(left,right),member,by simpa using same⟩)
  · rintro (retained | bindings)
    · obtain ⟨atom,member,occurs⟩ := List.mem_flatMap.mp retained
      exact Or.inr (Or.inl ⟨atom,member,(atomOccurs_iff_mem_typeVars atom name).mpr occurs⟩)
    · exact binding_var_visible bindings

/-- A private rule model can be combined with any caller model. Only names
in the fresh pattern are changed; the query, live continuation and complete
incoming constraint support keep the caller's interpretation. -/
theorem fresh_pattern_model
    {live : List Atom} {query rawPattern rawBody pattern body : Atom} {incoming : Bindings}
    (variant : AlphaVariantRel live query incoming rawPattern rawBody pattern body)
    (caller rule : String → Atom)
    (satisfied : TypeBindingSatisfied caller incoming) :
    ∃ combined,
      TypeBindingSatisfied combined incoming ∧
      applyTypeValuation combined pattern = applyTypeValuation rule rawPattern ∧
      Spec.Bindings.ScopeObservation.ValuationsAgreeOn
        (visibleNames live query incoming) caller combined := by
  classical
  obtain ⟨rename,injective,renamed,_body,fresh⟩ := variant
  have shape := EquationFreshening.alphaRename_eq renamed
  let transported := Function.extend rename rule caller
  let combined : String → Atom := fun name =>
    if name ∈ TypeSubst.typeVars pattern then transported name else caller name
  have avoids {name : String} (member : name ∈ TypeSubst.typeVars pattern) :
      ¬QueryVisibleName live query incoming name := by
    rw [shape,ScopeObservation.typeVars_renameTypeVars] at member
    obtain ⟨original,occurs,rfl⟩ := List.mem_map.mp member
    exact fresh original (Or.inl ((atomOccurs_iff_mem_typeVars rawPattern original).mpr occurs))
  have agrees : Spec.Bindings.ScopeObservation.ValuationsAgreeOn
      (visibleNames live query incoming) caller combined := by
    intro name member
    have absent : name ∉ TypeSubst.typeVars pattern :=
      fun present => avoids present ((mem_visibleNames_iff live query incoming name).mp member)
    simp only [combined,if_neg absent]
  refine ⟨combined,
    (Spec.Bindings.ScopeObservation.specTypeBindingSatisfied_congr_of_bindingVars
      (fun name member => agrees name ((mem_visibleNames_iff live query incoming name).mpr
        (binding_var_visible member)))).mp satisfied,
    ?_,agrees⟩
  calc
    applyTypeValuation combined pattern = applyTypeValuation transported pattern :=
      (applyTypeValuation_eq_iff_on_typeVars combined transported pattern).mpr (by
        intro name member
        simp only [combined,if_pos member])
    _ = applyTypeValuation (transported ∘ rename) rawPattern := by
      rw [shape,ApplicationEquivariance.applyTypeValuation_renameTypeVars]
    _ = applyTypeValuation rule rawPattern := by
      congr 1
      exact Function.extend_comp injective rule caller

/-- Fixing the declared caller scope leaves both its query and its complete
binding presentation unchanged, including names nested in stored values. -/
theorem caller_fixed {live : List Atom} {query : Atom} {incoming : Bindings}
    (rename : String → String)
    (fixed : ∀ name, QueryVisibleName live query incoming name → rename name = name) :
    Spec.Type.RuntimeRefinement.renameTypeVars rename query = query ∧
      Spec.Bindings.ScopeObservation.renameBindings rename incoming = incoming := by
  have atom_fixed (atom : Atom)
      (covered : ∀ name, AtomOccurs atom name → QueryVisibleName live query incoming name) :
      renameTypeVars rename atom = atom := by
    calc
      _ = renameTypeVars id atom :=
        ScopeObservation.renameTypeVars_congr_on_typeVars atom (fun name member =>
          fixed name (covered name ((atomOccurs_iff_mem_typeVars atom name).mpr member)))
      _ = atom := ScopeObservation.renameTypeVars_id atom
  refine ⟨atom_fixed query (fun _ occurrence => Or.inl occurrence),?_⟩
  apply congrArg₂ Bindings.mk
  · calc
      _ = incoming.assignments.map id := by
        apply List.map_congr_left
        rintro ⟨name,value⟩ member
        have keyFixed := fixed name (Or.inr (Or.inr (Or.inl ⟨value,member⟩)))
        have valueFixed := atom_fixed value (fun _ occurs =>
          Or.inr (Or.inr (Or.inr (Or.inl ⟨name,value,member,occurs⟩))))
        simp only [keyFixed,valueFixed,id_eq]
      _ = incoming.assignments := List.map_id _
  · calc
      _ = incoming.equalities.map id := by
        apply List.map_congr_left
        rintro ⟨left,right⟩ member
        have leftFixed := fixed left (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨left,right,member,Or.inl rfl⟩))))
        have rightFixed := fixed right (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨left,right,member,Or.inr rfl⟩))))
        simp only [leftFixed,rightFixed,id_eq]
      _ = incoming.equalities := List.map_id _

end Mettapedia.Languages.MeTTa.HE.EquationScope


namespace Mettapedia.Languages.MeTTa.HE.EquationFreshening

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval.Steps Spec.Match.Merge Spec.Type.Presentation Spec.Type.RuntimeRefinement

/-- Two legal fresh variants of an equation differ by one constructed
permutation fixing the complete caller-visible scope. The same map transports
both the pattern and body. -/
theorem alphaVariants_public_fixed_permutation
    {live : List Atom} {query lhs rhs leftPattern leftRhs rightPattern rightRhs : Atom}
    {incoming : Bindings}
    (left : AlphaVariantRel live query incoming lhs rhs leftPattern leftRhs)
    (right : AlphaVariantRel live query incoming lhs rhs rightPattern rightRhs) :
    ∃ permutation : Equiv.Perm String,
      (∀ name, QueryVisibleName live query incoming name → permutation name = name) ∧
      rightPattern = renameTypeVars permutation leftPattern ∧
      rightRhs = renameTypeVars permutation leftRhs := by
  obtain ⟨leftRename,leftInjective,leftPatternRenamed,leftBodyRenamed,leftFresh⟩ := left
  obtain ⟨rightRename,rightInjective,rightPatternRenamed,rightBodyRenamed,rightFresh⟩ := right
  let names := TypeSubst.typeVars lhs ++ TypeSubst.typeVars rhs
  have occurs (name : String) (member : name ∈ names) :
      AtomOccurs lhs name ∨ AtomOccurs rhs name := by
    exact (List.mem_append.mp member).imp
      ((atomOccurs_iff_mem_typeVars lhs name).mpr)
      ((atomOccurs_iff_mem_typeVars rhs name).mpr)
  obtain ⟨permutation,fixed,mapped⟩ :=
    Mettapedia.Logic.HostingStyles.NameEquality.exists_perm_of_same_pattern
      {name | QueryVisibleName live query incoming name}
      (fun index : Fin names.length => leftRename names[index])
      (fun index => rightRename names[index])
      (fun index => leftFresh _ (occurs _ (List.getElem_mem index.isLt)))
      (fun index => rightFresh _ (occurs _ (List.getElem_mem index.isLt)))
      (by
        intro first second
        exact ⟨fun same => congrArg rightRename (leftInjective same),
          fun same => congrArg leftRename (rightInjective same)⟩)
  have agrees (name : String) (member : name ∈ names) :
      permutation (leftRename name) = rightRename name := by
    obtain ⟨index,bound,same⟩ := List.getElem_of_mem member
    simpa only [Fin.getElem_fin,same] using mapped ⟨index,bound⟩
  refine ⟨permutation,fixed,?_,?_⟩
  · rw [alphaRename_eq leftPatternRenamed,alphaRename_eq rightPatternRenamed,
      ScopeObservation.renameTypeVars_comp]
    exact (ScopeObservation.renameTypeVars_congr_on_typeVars lhs
      (fun name member => agrees name (List.mem_append_left _ member))).symm
  · rw [alphaRename_eq leftBodyRenamed,alphaRename_eq rightBodyRenamed,
      ScopeObservation.renameTypeVars_comp]
    exact (ScopeObservation.renameTypeVars_congr_on_typeVars rhs
      (fun name member => agrees name (List.mem_append_right _ member))).symm

/-- Matching is viable at one legal fresh equation instance exactly when it
is viable at another. Caller equations are fixed, and the same permutation
transports the entire selected binding theory. -/
theorem alphaVariants_candidate_exists_iff
    {live : List Atom} {query lhs rhs leftPattern leftRhs rightPattern rightRhs : Atom}
    {incoming : Bindings}
    (left : AlphaVariantRel live query incoming lhs rhs leftPattern leftRhs)
    (right : AlphaVariantRel live query incoming lhs rhs rightPattern rightRhs) :
    (∃ output, UnifyCandidateRel query leftPattern incoming output) ↔
      ∃ output, UnifyCandidateRel query rightPattern incoming output := by
  obtain ⟨permutation,fixed,patternEquation,_bodyEquation⟩ :=
    alphaVariants_public_fixed_permutation left right
  obtain ⟨queryFixed,bindingsFixed⟩ := EquationScope.caller_fixed permutation fixed
  have inverseFixed : ∀ name, QueryVisibleName live query incoming name →
      permutation.symm name = name := by
    intro name visible
    apply permutation.injective
    simp only [Equiv.apply_symm_apply,fixed name visible]
  obtain ⟨inverseQuery,inverseBindings⟩ := EquationScope.caller_fixed permutation.symm inverseFixed
  constructor
  · rintro ⟨output,candidate⟩
    refine ⟨Spec.Bindings.ScopeObservation.renameBindings permutation output,?_⟩
    simpa only [queryFixed,bindingsFixed,← patternEquation] using
      Spec.Eval.Renaming.unify_candidate permutation candidate
  · rintro ⟨output,candidate⟩
    refine ⟨Spec.Bindings.ScopeObservation.renameBindings permutation.symm output,?_⟩
    simpa only [inverseQuery,inverseBindings,patternEquation,
      Spec.Bindings.ScopeObservation.renameTypeVars_perm_inverse] using
      Spec.Eval.Renaming.unify_candidate permutation.symm candidate

end Mettapedia.Languages.MeTTa.HE.EquationFreshening
