import Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport
import Mettapedia.Util.LinearHash
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.HE.Spec.Match.StructuralModel
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
import Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
import Batteries.Tactic.OpenPrivate
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Logical presentations of HE query bindings

The actual HE matching and binding operations preserve their complete source
constraint theories. Successful local operations construct independent source
derivations and binding presentations, including open incoming aliases. Logical
endpoints are related by their full solution theories and variable support;
neither relation order nor a chosen residual representative defines that
agreement.

The actual HE resolver has its own canonical principal-readout theorem under
semantic loop freedom, non-variable assignments and structural class
coherence. The existing executable coverage bound supplies sufficient depth.
Scoped-equivalent theories give one residual-name permutation for an entire
observed tuple, preserving correlations while retaining concrete checkpoints.
The model-language encoding used here is a structural syntax map, not an
interpreter comparison.

The executable LeaTTa projection and its materialization/invocation
comparisons live in the separate runtime conformance owner.
-/

set_option autoImplicit false

/-! ## Actual binding support and protected private components -/

namespace Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (vars)
open Spec.Type.Presentation Spec.Bindings.ScopeObservation

theorem readFrame_of_fresh {keys : String → Prop} {bindings : Bindings}
    (fresh : ∀ key, keys key → key ∉ specBindingVars bindings) :
    ReadFrame keys (fun _ => none) bindings := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value member key occurs owned
    apply fresh key owned
    simp only [specBindingVars, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨(name,value), member, by
      simp only [List.mem_cons]
      exact Or.inr ((TypeSubst.typeVars_eq_vars value).symm ▸ occurs)⟩
  · intro left right member
    constructor
    · intro owned
      apply fresh left owned
      simp only [specBindingVars, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(left,right), member, by simp⟩
    · intro owned
      apply fresh right owned
      simp only [specBindingVars, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(left,right), member, by simp⟩
  · intro key owned
    apply List.lookup_eq_none_iff.mpr
    intro entry member
    apply bne_iff_ne.mpr
    intro same
    apply fresh key owned
    simp only [specBindingVars, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨entry, member, by simp [same]⟩

/-- An equality key with no incident stored edge has exactly its singleton
ordered class, even when unrelated classes contain duplicate edges. -/
theorem orderedClass_of_no_edge {bindings : Bindings} {key : String}
    (noEdges : ∀ left right, (left,right)∈bindings.equalities → left≠key ∧ right≠key) :
    bindings.eqClassOrdered key = [key] := by
  have absent : key ∉ bindings.eqVarsInOrder := by
    rw [EqualityClosure.mem_eqVarsInOrder_iff]
    intro member
    obtain ⟨⟨left,right⟩, stored, which⟩ := List.mem_flatMap.mp member
    rcases (show key=left ∨ key=right by simpa using which) with same | same
    · exact (noEdges left right stored).1 same.symm
    · exact (noEdges left right stored).2 same.symm
  have filtered : bindings.eqVarsInOrder.filter
      (fun name => (bindings.eqClass key).contains name) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    obtain ⟨ordered, reachable⟩ := List.mem_filter.mp member
    have walk := EqualityClosure.mem_eqClass_iff_reachable.mp (List.contains_iff_mem.mp reachable)
    obtain ⟨walk⟩ := walk
    cases walk with
    | nil => exact absent ordered
    | @cons first next last edge tail =>
      rcases edge.2 with forward | backward
      · exact (noEdges key next forward).1 rfl
      · exact (noEdges next key backward).2 rfl
  simp only [Bindings.eqClassOrdered, filtered]

theorem ReadFrame.orderedClass {keys : String → Prop} {saved : String → Option Atom}
    {bindings : Bindings} (frame : ReadFrame keys saved bindings)
    {key : String} (owned : keys key) : bindings.eqClassOrdered key = [key] := by
  apply orderedClass_of_no_edge
  intro left right stored
  obtain ⟨leftOutside,rightOutside⟩ := frame.equalities left right stored
  exact ⟨fun same => leftOutside (same ▸ owned), fun same => rightOutside (same ▸ owned)⟩

theorem hasResolvableVarAux_closed (bindings : Bindings) (fuel : Nat) (atom : Atom)
    (closed : TypeSubst.typeVars atom = []) : bindings.hasResolvableVarAux fuel atom = false := by
  induction fuel generalizing atom with
  | zero => rfl
  | succ fuel ih =>
    cases atom with
    | var name => simp [TypeSubst.typeVars] at closed
    | symbol | grounded => rfl
    | expression atoms =>
      simp only [Bindings.hasResolvableVarAux]
      apply List.any_eq_false.mpr
      intro atom present
      have allClosed : ∀ item ∈ atoms, TypeSubst.typeVars item = [] := by
        intro item member
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro key occurs
        have whole := Freshness.typeVars_mem_typeVarsList_of_mem member key occurs
        change TypeSubst.typeVarsList atoms = [] at closed
        simp only [closed, List.not_mem_nil] at whole
      simp only [ih atom (allClosed atom present), Bool.false_eq_true, not_false_eq_true]

theorem hasResolvableVar_closed (bindings : Bindings) (atom : Atom)
    (closed : TypeSubst.typeVars atom = []) : bindings.hasResolvableVar atom = false :=
  hasResolvableVarAux_closed bindings _ atom closed

theorem resolveFull_eq_of_closed_singleton {first second : Bindings} {key : String}
    (firstClass : first.eqClassOrdered key = [key])
    (secondClass : second.eqClassOrdered key = [key])
    (same : second.lookup key = first.lookup key)
    (closed : ∀ value, first.lookup key = some value → TypeSubst.typeVars value = [])
    (fuel : Nat) : second.resolveFull key fuel = first.resolveFull key fuel := by
  cases found : first.lookup key with
  | none => simp [Bindings.resolveFull, firstClass, secondClass, same, found]
  | some value =>
    have valueClosed := closed value found
    cases fuel with
    | zero => simp [Bindings.resolveFull, firstClass, secondClass, same, found,
        Bindings.resolveAtomFullAux]
    | succ fuel =>
      cases value with
      | var name => simp [TypeSubst.typeVars] at valueClosed
      | symbol name =>
        simp [Bindings.resolveFull, firstClass, secondClass, same, found,
          Bindings.resolveAtomFullAux, hasResolvableVar_closed _ _ valueClosed]
      | grounded value =>
        simp [Bindings.resolveFull, firstClass, secondClass, same, found,
          Bindings.resolveAtomFullAux, hasResolvableVar_closed _ _ valueClosed]
      | expression atoms =>
        simp [Bindings.resolveFull, firstClass, secondClass, same, found,
          Bindings.resolveAtomFullAux, hasResolvableVar_closed _ _ valueClosed]

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Bindings.ScopeObservation Spec.Match.ModelTheory

/-- The actual merger never removes a relation already in its accumulator.
This uses the executable-tracking merge relation only as induction evidence,
not as an independent source judgment. -/
theorem mergeRel_left_subrecord {left right out : Bindings}
    (relation : DeclMergeSpec.MergeRel left right out) : BindingSubrecord left out := by
  apply DeclMergeSpec.MergeRel.rec
    (motive_1 := fun before _ _ after _ => BindingSubrecord before after)
    (motive_2 := fun before _ _ after _ => BindingSubrecord before after)
    (motive_3 := fun before _ after _ => BindingSubrecord before after)
    (motive_4 := fun before _ after _ => BindingSubrecord before after)
    (motive_5 := fun before _ after _ => BindingSubrecord before after)
    (t:=relation)
  next =>
    intro before key value empty
    exact bindingSubrecord_assign_of_not_isBound _ _ _
      (EqualityClosure.isBound_eq_false_of_classValues_nil empty)
  next => intros; exact BindingSubrecord.refl _
  next => intros; assumption
  next => intros; assumption
  next => intros; exact bindingSubrecord_addEquality _ _ _
  next => intros; rename_i ih; exact (bindingSubrecord_addEquality _ _ _).trans ih
  next => intros; rename_i ih; exact (bindingSubrecord_addEquality _ _ _).trans ih
  next => intros; exact BindingSubrecord.refl _
  next => intros; rename_i first rest; exact first.trans rest
  next => intros; exact BindingSubrecord.refl _
  next => intros; rename_i first rest; exact first.trans rest
  next => intros; rename_i first rest; exact first.trans rest

theorem addBindingRel_seed_subrecord {before out : Bindings} {key : String} {value : Atom}
    (relation : DeclMergeSpec.AddVarBindingRel before key value out) :
    BindingSubrecord before out := by
  cases relation with
  | fresh empty =>
      exact bindingSubrecord_assign_of_not_isBound _ _ _
        (EqualityClosure.isBound_eq_false_of_classValues_nil empty)
  | same => exact BindingSubrecord.refl _
  | conflict _ _ _ _ merged => exact mergeRel_left_subrecord merged
  | reconcile _ _ _ merged => exact mergeRel_left_subrecord merged

theorem addEqualityRel_candidate_subrecord {before out : Bindings} {left right : String}
    (relation : DeclMergeSpec.AddVarEqualityRel before left right out) :
    BindingSubrecord (before.addEquality left right) out := by
  cases relation with
  | consistent => exact BindingSubrecord.refl _
  | pairConflict _ _ _ merged => exact mergeRel_left_subrecord merged
  | classConflict _ _ _ merged => exact mergeRel_left_subrecord merged

theorem mergeAssignsRel_seed_subrecord {before out : Bindings} {rows : List (String × Atom)}
    (relation : DeclMergeSpec.MergeAssignsRel before rows out) :
    BindingSubrecord before out := by
  induction rows generalizing before with
  | nil => cases relation; exact BindingSubrecord.refl _
  | cons head tail ih =>
      cases relation with
      | cons first rest => exact (addBindingRel_seed_subrecord first).trans (ih rest)

theorem mergeEqsRel_seed_subrecord {before out : Bindings} {rows : List (String × String)}
    (relation : DeclMergeSpec.MergeEqsRel before rows out) :
    BindingSubrecord before out := by
  induction rows generalizing before with
  | nil => cases relation; exact BindingSubrecord.refl _
  | cons head tail ih =>
      cases relation with
      | cons first rest =>
          exact ((bindingSubrecord_addEquality _ _ _).trans
            (addEqualityRel_candidate_subrecord first)).trans (ih rest)

theorem merge_left_subrecord {left right out : Bindings} {fuel : Nat}
    (member : out∈mergeBindings left right fuel) : BindingSubrecord left out :=
  mergeRel_left_subrecord (DeclMergeSpec.mergeBindings_sound member)

theorem subrecord_support {before after : Bindings} (rows : BindingSubrecord before after)
    {name : String} (present : name∈specBindingVars before) : name∈specBindingVars after := by
  simp only [specBindingVars,List.mem_append,List.mem_flatMap] at present ⊢
  rcases present with ⟨entry,stored,inside⟩ | ⟨edge,stored,inside⟩
  · exact Or.inl ⟨entry,rows.1 entry stored,inside⟩
  · exact Or.inr ⟨edge,rows.2 edge stored,inside⟩

theorem ReadFrame.absent {keys : String → Prop} {bindings : Bindings}
    (frame : ReadFrame keys (fun _=>none) bindings) {name : String} (owned : keys name) :
    name∉specBindingVars bindings := by
  intro present
  simp only [specBindingVars,List.mem_append,List.mem_flatMap] at present
  rcases present with ⟨⟨key,value⟩,stored,inside⟩ | ⟨⟨left,right⟩,stored,inside⟩
  · rcases List.mem_cons.mp inside with same | inside
    · exact frame.none_key stored (by simpa only [same] using owned)
    · exact frame.values key value stored name
        (TypeSubst.typeVars_eq_vars value ▸ inside) owned
  · rcases (show name=left ∨ name=right by simpa using inside) with same | same
    · exact (frame.equalities left right stored).1 (same ▸ owned)
    · exact (frame.equalities left right stored).2 (same ▸ owned)

/-- Recursive reconciliation introduces no variable absent from both inputs. -/
theorem merge_support_subset {left right out : Bindings} {fuel : Nat}
    (member : out∈mergeBindings left right fuel) {name : String}
    (present : name∈specBindingVars out) :
    name∈specBindingVars left ∨ name∈specBindingVars right := by
  by_contra absent
  have leftAbsent : name∉specBindingVars left := fun old => absent (Or.inl old)
  have rightAbsent : name∉specBindingVars right := fun old => absent (Or.inr old)
  have frame := (frame_family (fun key=>key=name) fuel).2.2.1
    (fun _=>none) left right out
    (readFrame_of_fresh (fun key same => same ▸ leftAbsent))
    (readFrame_of_fresh (fun key same => same ▸ rightAbsent)) member
  exact frame.absent rfl present

theorem match_support_subset {left right : Atom} {out : Bindings} {fuel : Nat}
    (member : out∈matchAtoms left right fuel) {name : String}
    (present : name∈specBindingVars out) :
    name∈TypeSubst.typeVars left ∨ name∈TypeSubst.typeVars right := by
  by_contra absent
  have leftAbsent : name∉TypeSubst.typeVars left := fun old => absent (Or.inl old)
  have rightAbsent : name∉TypeSubst.typeVars right := fun old => absent (Or.inr old)
  have frame := (frame_family (fun key=>key=name) fuel).1 left right out
    (fun key occurs same => leftAbsent
      ((TypeSubst.typeVars_eq_vars left).symm ▸ (same ▸ occurs)))
    (fun key occurs same => rightAbsent
      ((TypeSubst.typeVars_eq_vars right).symm ▸ (same ▸ occurs))) member
  exact frame.absent rfl present

theorem matchList_support_subset {left right : List Atom} {seeds : List Bindings}
    {out : Bindings} {fuel : Nat} (member : out∈matchAtomsList left right seeds fuel)
    {name : String} (present : name∈specBindingVars out) :
    (∃ seed∈seeds,name∈specBindingVars seed) ∨
      name∈TypeSubst.typeVarsList left ∨ name∈TypeSubst.typeVarsList right := by
  by_contra absent
  have seedAbsent : ∀ seed∈seeds,name∉specBindingVars seed := by
    intro seed stored old
    exact absent (Or.inl ⟨seed,stored,old⟩)
  have leftAbsent : name∉TypeSubst.typeVarsList left := fun old => absent (Or.inr (Or.inl old))
  have rightAbsent : name∉TypeSubst.typeVarsList right := fun old => absent (Or.inr (Or.inr old))
  have frame := (frame_family (fun key=>key=name) fuel).2.1 left right seeds out
    (fun atom stored key occurs same => leftAbsent
      (Freshness.typeVars_mem_typeVarsList_of_mem stored name
        ((TypeSubst.typeVars_eq_vars atom).symm ▸ (same ▸ occurs))))
    (fun atom stored key occurs same => rightAbsent
      (Freshness.typeVars_mem_typeVarsList_of_mem stored name
        ((TypeSubst.typeVars_eq_vars atom).symm ▸ (same ▸ occurs))))
    (fun seed stored => readFrame_of_fresh (fun key same=>same ▸ seedAbsent seed stored)) member
  exact frame.absent rfl present

private theorem fold_flatMap_support {α : Type} (itemVars : α → List String)
    (step : Bindings → α → List Bindings) (items : List α) (seeds : List Bindings)
    (preserves : ∀ item∈items,∀ seed out,out∈step seed item→BindingSubrecord seed out)
    (covers : ∀ item∈items,∀ seed out,out∈step seed item→
      ∀ name∈itemVars item,name∈specBindingVars out)
    {out : Bindings} (member : out∈items.foldl (fun acc item=>acc.flatMap (step · item)) seeds) :
    ∃ seed∈seeds,BindingSubrecord seed out ∧
      ∀ item∈items,∀ name∈itemVars item,name∈specBindingVars out := by
  induction items generalizing seeds with
  | nil => exact ⟨out,member,BindingSubrecord.refl _,by simp⟩
  | cons item rest ih =>
    obtain ⟨next,present,rows,covered⟩ := ih _
      (fun a ha=>preserves a (by simp [ha]))
      (fun a ha=>covers a (by simp [ha])) member
    obtain ⟨seed,initial,stepMember⟩ := List.mem_flatMap.mp present
    refine ⟨seed,initial,(preserves item (by simp) seed next stepMember).trans rows,?_⟩
    intro a stored name occurs
    rcases List.mem_cons.mp stored with same | later
    · subst a
      exact subrecord_support rows (covers item (by simp) seed next stepMember name occurs)
    · exact covered a later name occurs

private theorem equality_support {before out : Bindings} {left right name : String} {fuel : Nat}
    (member : out∈addVarEquality before left right fuel) (occurs : name=left ∨ name=right) :
    name∈specBindingVars out := by
  apply subrecord_support (addEqualityRel_candidate_subrecord
    (DeclMergeSpec.addVarEquality_sound member))
  simp [specBindingVars,Bindings.addEquality,occurs]

private theorem fresh_assignment_support {before : Bindings} {key name : String} {value : Atom}
    (unbound : before.isBound key=false) (occurs : name=key ∨ name∈TypeSubst.typeVars value) :
    name∈specBindingVars (before.assign key value) := by
  simp only [specBindingVars,Bindings.assign,unbound,Bool.false_eq_true,↓reduceIte]
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨(key,value),by simp,by simpa using occurs⟩

/-- Every successful actual matcher retains all syntactic variable support;
list matching also retains the exact selected accumulator as a subrecord. -/
theorem support_cover_family (fuel : Nat) :
    (∀ left right out,out∈matchAtoms left right fuel→∀ name,
      name∈TypeSubst.typeVars left ∨ name∈TypeSubst.typeVars right→name∈specBindingVars out) ∧
    (∀ left right seeds out,out∈matchAtomsList left right seeds fuel→
      ∃ seed∈seeds,BindingSubrecord seed out ∧ ∀ name,
        name∈TypeSubst.typeVarsList left ∨ name∈TypeSubst.typeVarsList right→
        name∈specBindingVars out) ∧
    (∀ left right out,out∈mergeBindings left right fuel→∀ name,
      name∈specBindingVars right→name∈specBindingVars out) ∧
    (∀ before key value out,out∈addVarBinding before key value fuel→∀ name,
      name=key ∨ name∈TypeSubst.typeVars value→name∈specBindingVars out) := by
  induction fuel with
  | zero => simp [matchAtoms,matchAtomsList,mergeBindings,addVarBinding]
  | succ fuel ih =>
    obtain ⟨matched,listed,merged,assigned⟩ := ih
    refine ⟨?_,?_,?_,?_⟩
    · intro left right out member name occurs
      cases left with
      | var key =>
        cases right with
        | var other =>
          have stored : out=Bindings.empty.addEquality key other :=
            (show out=Bindings.empty.addEquality key other ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType] using member).1
          subst out
          simpa [specBindingVars,Bindings.empty,Bindings.addEquality,TypeSubst.typeVars] using occurs
        | symbol value =>
          have stored : out=Bindings.empty.assign key (.symbol value) :=
            (show out=Bindings.empty.assign key (.symbol value) ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType,Atom.symbolType] using member).1
          subst out
          apply fresh_assignment_support rfl
          simpa [TypeSubst.typeVars] using occurs
        | grounded value =>
          have stored : out=Bindings.empty.assign key (.grounded value) :=
            (show out=Bindings.empty.assign key (.grounded value) ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType,Atom.groundedType] using member).1
          subst out
          apply fresh_assignment_support rfl
          simpa [TypeSubst.typeVars] using occurs
        | expression values =>
          have stored : out=Bindings.empty.assign key (.expression values) :=
            (show out=Bindings.empty.assign key (.expression values) ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType,Atom.expressionType] using member).1
          subst out
          apply fresh_assignment_support rfl
          simpa [TypeSubst.typeVars] using occurs
      | symbol symbol =>
        cases right with
        | var key =>
          have stored : out=Bindings.empty.assign key (.symbol symbol) :=
            (show out=Bindings.empty.assign key (.symbol symbol) ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType,Atom.symbolType] using member).1
          subst out
          apply fresh_assignment_support rfl
          simpa [TypeSubst.typeVars] using occurs
        | symbol | grounded => all_goals simp [TypeSubst.typeVars] at occurs
        | expression => simp [matchAtoms,getMetaType,Atom.symbolType,Atom.expressionType] at member
      | grounded value =>
        cases right with
        | var key =>
          have stored : out=Bindings.empty.assign key (.grounded value) :=
            (show out=Bindings.empty.assign key (.grounded value) ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType,Atom.groundedType] using member).1
          subst out
          apply fresh_assignment_support rfl
          simpa [TypeSubst.typeVars] using occurs
        | symbol | grounded => all_goals simp [TypeSubst.typeVars] at occurs
        | expression => simp [matchAtoms,getMetaType,Atom.groundedType,Atom.expressionType] at member
      | expression values =>
        cases right with
        | var key =>
          have stored : out=Bindings.empty.assign key (.expression values) :=
            (show out=Bindings.empty.assign key (.expression values) ∧ out.hasLoop=false from
              by simpa [matchAtoms,getMetaType,Atom.variableType,Atom.expressionType] using member).1
          subst out
          apply fresh_assignment_support rfl
          simpa [TypeSubst.typeVars,or_comm] using occurs
        | expression others =>
          have raw := (show out∈(if values.length=others.length then
              matchAtomsList values others [Bindings.empty] fuel else []) ∧ out.hasLoop=false from
            by simpa [matchAtoms,getMetaType,Atom.expressionType] using member).1
          split at raw
          · exact (listed values others [Bindings.empty] out raw).choose_spec.2.2 name occurs
          · simp at raw
        | symbol | grounded => all_goals
            simp [matchAtoms,getMetaType,Atom.symbolType,Atom.groundedType,Atom.expressionType] at member
    · intro left right seeds out member
      cases left with
      | nil =>
        cases right with
        | nil => exact ⟨out,member,BindingSubrecord.refl _,by simp [TypeSubst.typeVarsList]⟩
        | cons => simp [matchAtomsList] at member
      | cons first rest =>
        cases right with
        | nil => simp [matchAtomsList] at member
        | cons second others =>
          obtain ⟨next,present,rows,covered⟩ := listed rest others _ out member
          obtain ⟨seed,initial,found⟩ := List.mem_flatMap.mp present
          obtain ⟨head,headMatch,headMerge⟩ := List.mem_flatMap.mp found
          refine ⟨seed,initial,(merge_left_subrecord headMerge).trans rows,?_⟩
          intro name occurs
          simp only [TypeSubst.typeVarsList,List.mem_append] at occurs
          rcases occurs with (headLeft | tailLeft) | (headRight | tailRight)
          · exact subrecord_support rows (merged seed head next headMerge name
              (matched first second head headMatch name (Or.inl headLeft)))
          · exact covered name (Or.inl tailLeft)
          · exact subrecord_support rows (merged seed head next headMerge name
              (matched first second head headMatch name (Or.inr headRight)))
          · exact covered name (Or.inr tailRight)
    · intro left right out member name occurs
      change out∈right.equalities.foldl
        (fun acc edge=>acc.flatMap (fun seed=>addVarEquality seed edge.1 edge.2 fuel))
        (right.assignments.foldl
          (fun acc entry=>acc.flatMap (fun seed=>addVarBinding seed entry.1 entry.2 fuel)) [left]) at member
      obtain ⟨mid,midMember,midRows,eqs⟩ := fold_flatMap_support
        (fun edge : String×String=>[edge.1,edge.2])
        (fun seed edge=>addVarEquality seed edge.1 edge.2 fuel)
        right.equalities _
        (fun edge _ seed next found=>(bindingSubrecord_addEquality seed edge.1 edge.2).trans
          (addEqualityRel_candidate_subrecord (DeclMergeSpec.addVarEquality_sound found)))
        (by intro edge _ seed next found key present
            exact equality_support found (by simpa using present)) member
      obtain ⟨_,_,_,assigns⟩ := fold_flatMap_support
        (fun entry : String×Atom=>entry.1::TypeSubst.typeVars entry.2)
        (fun seed entry=>addVarBinding seed entry.1 entry.2 fuel)
        right.assignments [left]
        (fun _ _ _ _ found=>addBindingRel_seed_subrecord (DeclMergeSpec.addVarBinding_sound found))
        (by intro entry _ seed next found key present
            exact assigned seed entry.1 entry.2 next found key (by simpa using present)) midMember
      simp only [specBindingVars,List.mem_append,List.mem_flatMap] at occurs
      rcases occurs with ⟨entry,stored,present⟩ | ⟨edge,stored,present⟩
      · exact subrecord_support midRows (assigns entry stored name present)
      · exact eqs edge stored name present
    · intro before key value out member name occurs
      have beforeRows := addBindingRel_seed_subrecord (DeclMergeSpec.addVarBinding_sound member)
      simp only [addVarBinding] at member
      cases values : before.classValues key with
      | nil =>
        simp only [values,List.mem_singleton] at member
        subst out
        exact fresh_assignment_support (EqualityClosure.isBound_eq_false_of_classValues_nil values) occurs
      | cons first rest =>
        have keyCovered : key∈specBindingVars out := subrecord_support beforeRows
          (class_key_support (key:=key) (value:=first) (by rw [values]; simp))
        rcases occurs with same | occurs
        · exact same ▸ keyCovered
        · simp only [values] at member
          split at member
          · split at member
            · rename_i equal
              have same : first=value := by simpa using equal
              have stored : value∈before.classValues key := by rw [values, same]; simp
              exact subrecord_support beforeRows (class_value_support stored occurs)
            · obtain ⟨result,selected,joined⟩ := List.mem_flatMap.mp member
              exact merged before result out joined name
                (matched first value result selected name (Or.inr occurs))
          · obtain ⟨result,selected,joined⟩ := List.mem_flatMap.mp member
            obtain ⟨_,_,_,covered⟩ := listed _ _ [Bindings.empty] result selected
            apply merged before result out joined name
            apply covered name (Or.inr ?_)
            exact Freshness.typeVars_mem_typeVarsList_of_mem (by simp) name occurs

/-- Complete support of an actual successful merge, with no caller invariant. -/
theorem merge_support_iff {left right out : Bindings} {fuel : Nat}
    (member : out∈mergeBindings left right fuel) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars left ∨ name∈specBindingVars right := by
  refine ⟨merge_support_subset member, ?_⟩
  intro present
  rcases present with old | added
  · exact subrecord_support (merge_left_subrecord member) old
  · exact (support_cover_family fuel).2.2.1 left right out member name added

/-- Variable support records both sides of a successful actual match, including
self-equalities and repeated input names. -/
theorem match_support_iff {left right : Atom} {out : Bindings} {fuel : Nat}
    (member : out∈matchAtoms left right fuel) (name : String) :
    name∈specBindingVars out ↔
      name∈TypeSubst.typeVars left ∨ name∈TypeSubst.typeVars right :=
  ⟨match_support_subset member,(support_cover_family fuel).1 left right out member name⟩

theorem addBinding_support_iff {before out : Bindings} {key : String} {value : Atom} {fuel : Nat}
    (member : out∈addVarBinding before key value fuel) (name : String) :
    name∈specBindingVars out ↔
      name∈specBindingVars before ∨ name=key ∨ name∈TypeSubst.typeVars value := by
  refine ⟨?_, ?_⟩
  · intro present
    by_contra absent
    have beforeAbsent : name∉specBindingVars before := fun old=>absent (Or.inl old)
    have keyAbsent : name≠key := fun same=>absent (Or.inr (Or.inl same))
    have valueAbsent : name∉TypeSubst.typeVars value := fun old=>absent (Or.inr (Or.inr old))
    have frame := (frame_family (fun k=>k=name) fuel).2.2.2.1
      (fun _=>none) before key value out
      (readFrame_of_fresh (fun k same=>same ▸ beforeAbsent)) (Ne.symm keyAbsent)
      (fun k occurs same=>valueAbsent
        ((TypeSubst.typeVars_eq_vars value).symm ▸ (same ▸ occurs))) member
    exact frame.absent rfl present
  · intro present
    rcases present with old | added
    · exact subrecord_support (addBindingRel_seed_subrecord
        (DeclMergeSpec.addVarBinding_sound member)) old
    · exact (support_cover_family fuel).2.2.2 before key value out member name added

theorem addEquality_support_iff {before out : Bindings} {left right : String} {fuel : Nat}
    (member : out∈addVarEquality before left right fuel) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars before ∨ name=left ∨ name=right := by
  refine ⟨?_, ?_⟩
  · intro present
    by_contra absent
    have beforeAbsent : name∉specBindingVars before := fun old=>absent (Or.inl old)
    have leftAbsent : name≠left := fun same=>absent (Or.inr (Or.inl same))
    have rightAbsent : name≠right := fun same=>absent (Or.inr (Or.inr same))
    have frame := (frame_family (fun k=>k=name) fuel).2.2.2.2
      (fun _=>none) before left right out
      (readFrame_of_fresh (fun k same=>same ▸ beforeAbsent))
      (Ne.symm leftAbsent) (Ne.symm rightAbsent) member
    exact frame.absent rfl present
  · intro present
    rcases present with old | added
    · exact subrecord_support ((bindingSubrecord_addEquality before left right).trans
        (addEqualityRel_candidate_subrecord (DeclMergeSpec.addVarEquality_sound member))) old
    · exact equality_support member added

namespace SupportControls
/-- A self-alias carries a freshness name even though it adds no model constraint. -/
example : mergeBindings Bindings.empty ⟨[],[("hole","hole")]⟩ 3 =
    [⟨[],[("hole","hole")]⟩] := by decide

/-- Reconciliation retains the variable introduced by the caller's conflicting
structured values instead of forgetting it after the values agree. -/
example : mergeBindings
    ⟨[("x",.expression [.symbol "F",.var "y"])],[]⟩
    ⟨[("x",.expression [.symbol "F",.symbol "A"])],[]⟩ 20 =
    [⟨[("x",.expression [.symbol "F",.var "y"]),("y",.symbol "A")],[]⟩] := by decide

/-- Failure has no endpoint support theorem: incompatible input values refuse. -/
example : mergeBindings ⟨[("x",.symbol "A")],[]⟩
    ⟨[("x",.symbol "B")],[]⟩ 6=[] := by decide
end SupportControls


/-- Fresh closed rows have an independent source merge even when the caller
has aliases, duplicate edges or open values. -/
theorem closed_constraints_source (rows : List (String × Atom))
    (unique : (rows.map Prod.fst).Nodup)
    (closed : ∀ key value, (key,value)∈rows → TypeSubst.typeVars value=[])
    (initial : Bindings)
    (fresh : ∀ key ∈ rows.map Prod.fst, key∉specBindingVars initial) :
    Spec.Match.Merge.MergeConstraintsRel Spec.Match.Merge.equalityGroundedSemantic initial
      (rows.map (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2))
      ⟨initial.assignments ++ rows, initial.equalities⟩ := by
  induction rows generalizing initial with
  | nil =>
    have same : (⟨initial.assignments ++ [], initial.equalities⟩ : Bindings) = initial := by
      cases initial; simp
    rw [same]
    exact .nil
  | cons entry rows ih =>
    rcases entry with ⟨key,value⟩
    have uniqueParts := List.nodup_cons.mp unique
    have emptyFrame := readFrame_of_fresh (keys := fun name => name=key)
      (fun name same => same ▸ fresh key (by simp))
    have absent := emptyFrame.reads key rfl
    have emptyClass : initial.classValues key=[] := by
      simp [Bindings.classValues, emptyFrame.orderedClass rfl, absent]
    have assigned : initial.assign key value =
        (⟨initial.assignments ++ [(key,value)], initial.equalities⟩ : Bindings) := by
      simp [Bindings.assign, Bindings.isBound, absent]
    have remainingFresh : ∀ name ∈ rows.map Prod.fst,
        name ∉ specBindingVars (initial.assign key value) := by
      intro name member present
      have notInitial := fresh name (by simp [member])
      have notKey : name≠key := by
        intro same
        exact uniqueParts.1 (same ▸ member)
      rw [assigned] at present
      simp only [specBindingVars, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, closed key value (by simp),
        List.mem_append, List.mem_singleton] at present
      rcases present with (old | added) | old
      · exact notInitial (List.mem_append_left _ old)
      · exact notKey added
      · exact notInitial (List.mem_append_right _ old)
    have tail := ih uniqueParts.2
      (fun name atom member => closed name atom (by simp [member]))
      (initial.assign key value) remainingFresh
    simpa only [List.map_cons, assigned, List.append_assoc, List.singleton_append] using
      Spec.Match.Merge.MergeConstraintsRel.value (.fresh emptyClass) tail

end Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Eval.Steps
open Spec.Type.Presentation (TypeSubst)
open Spec.Type.Presentation.BindingTheory (BindingMaterializationRel)

/-! ## Operational application under the projected solution theory -/

private theorem class_observation {bindings : Bindings} {valuation : String → Metta.Atom}
    (satisfied : HEBindingSatisfied valuation bindings) {name other : String}
    (member : other ∈ bindings.eqClassOrdered name) : valuation name = valuation other :=
  satisfied.eq_of_mem_eqClass (EqualityClosure.mem_eqClassOrdered_iff.mp member)

private theorem representative_observation {bindings : Bindings} {valuation : String → Metta.Atom}
    (satisfied : HEBindingSatisfied valuation bindings) (name : String) :
    valuation (bindings.eqRepresentative name) = valuation name := by
  unfold Bindings.eqRepresentative
  cases selected : bindings.eqClassOrdered name with
  | nil => simp
  | cons first rest =>
      simp only [List.headD_cons]
      exact (class_observation satisfied (by rw [selected]; exact List.mem_cons_self)).symm

private theorem selected_value_observation {bindings : Bindings} {valuation : String → Metta.Atom}
    (satisfied : HEBindingSatisfied valuation bindings) {name : String} {value : Atom}
    (selected : (bindings.eqClassOrdered name).findSome? bindings.lookup = some value) :
    valuation name = applyClassSolution valuation (encodeModelAtom value) := by
  obtain ⟨key, member, lookup⟩ := List.exists_of_findSome?_eq_some selected
  obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp lookup
  have stored : (key, value) ∈ bindings.assignments := by rw [entries]; simp
  exact (class_observation satisfied member).trans (satisfied.1 key value stored)

/-- A successful actual resolver walk preserves the observed atom at every
fuel, including equality representatives and nested assignment dependencies.
Failure and cycle rejection are not converted into successful resolutions. -/
theorem resolveAtomFullAux_semantically_inert {bindings : Bindings}
    {valuation : String → Metta.Atom} (satisfied : HEBindingSatisfied valuation bindings) :
    ∀ fuel visited atom resolved,
      bindings.resolveAtomFullAux fuel visited atom = some resolved →
      applyClassSolution valuation (encodeModelAtom resolved) =
        applyClassSolution valuation (encodeModelAtom atom) := by
  intro fuel
  induction fuel with
  | zero => intro visited atom resolved ran; simp [Bindings.resolveAtomFullAux] at ran
  | succ fuel ih =>
      intro visited atom resolved ran
      cases atom with
      | symbol name => simp only [Bindings.resolveAtomFullAux, Option.some.injEq] at ran; subst resolved; rfl
      | grounded value => simp only [Bindings.resolveAtomFullAux, Option.some.injEq] at ran; subst resolved; rfl
      | expression atoms =>
          simp only [Bindings.resolveAtomFullAux] at ran
          cases mapped : atoms.mapM (bindings.resolveAtomFullAux fuel visited) with
          | none => simp [mapped] at ran
          | some values =>
              rw [mapped] at ran
              cases ran
              have observed : ∀ xs ys : List Atom,
                  xs.mapM (bindings.resolveAtomFullAux fuel visited) = some ys →
                  (encodeModelAtoms ys).map (applyClassSolution valuation) =
                    (encodeModelAtoms xs).map (applyClassSolution valuation) := by
                intro xs
                induction xs with
                | nil => intro ys mapped; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at mapped; subst ys; rfl
                | cons first rest tail =>
                    intro ys mapped
                    cases firstRun : bindings.resolveAtomFullAux fuel visited first with
                    | none => simp [List.mapM_cons, firstRun] at mapped
                    | some value =>
                        cases restRun : rest.mapM (bindings.resolveAtomFullAux fuel visited) with
                        | none => simp [List.mapM_cons, firstRun, restRun] at mapped
                        | some values =>
                            have same : value :: values = ys := by simpa [List.mapM_cons, firstRun, restRun] using mapped
                            subst ys
                            simpa only [encodeModelAtoms, List.map_cons] using
                              congrArg₂ List.cons (ih visited first value firstRun) (tail values restRun)
              simpa only [encodeModelAtom, applyClassSolution, Metta.Atom.expr.injEq] using observed atoms values mapped
      | var name =>
          rw [show applyClassSolution valuation (encodeModelAtom (.var name)) = valuation name by
            simp only [encodeModelAtom, applyClassSolution]]
          simp only [Bindings.resolveAtomFullAux] at ran
          split at ran
          · cases ran
          · cases selected : (bindings.eqClassOrdered name).findSome? bindings.lookup with
            | none =>
                simp only [selected] at ran
                split at ran
                · cases ran; simp only [encodeModelAtom, applyClassSolution]
                · cases ran
                  simpa only [encodeModelAtom, applyClassSolution] using representative_observation satisfied name
            | some value =>
                simp only [selected] at ran
                have valueObserved := (selected_value_observation satisfied selected).symm
                cases value with
                | var other =>
                    dsimp only at ran
                    split at ran
                    · split at ran
                      · cases ran
                      · cases ran; simpa only [encodeModelAtom, applyClassSolution] using representative_observation satisfied name
                    · split at ran
                      · exact (ih _ _ _ ran).trans valueObserved
                      · cases ran; exact valueObserved
                | symbol other =>
                    dsimp only at ran
                    split at ran
                    · exact (ih _ _ _ ran).trans valueObserved
                    · cases ran; exact valueObserved
                | grounded other =>
                    dsimp only at ran
                    split at ran
                    · exact (ih _ _ _ ran).trans valueObserved
                    · cases ran; exact valueObserved
                | expression values =>
                    dsimp only at ran
                    split at ran
                    · exact (ih _ _ _ ran).trans valueObserved
                    · cases ran; exact valueObserved

/-- Successful public root resolution has the same model observation as the
original variable; the open/failed branch remains the resolver's own `none`. -/
theorem resolveFull_semantically_inert {bindings : Bindings} {valuation : String → Metta.Atom}
    (satisfied : HEBindingSatisfied valuation bindings) {name : String} {fuel : Nat} {resolved : Atom}
    (ran : bindings.resolveFull name fuel = some resolved) :
    applyClassSolution valuation (encodeModelAtom resolved) = valuation name := by
  unfold Bindings.resolveFull at ran
  dsimp only at ran
  split at ran
  · cases ran
  · simpa only [encodeModelAtom, applyClassSolution] using
      resolveAtomFullAux_semantically_inert satisfied fuel [] (.var name) resolved ran

/-- Bounded HE application preserves meaning even when its fuel is too small
for complete syntactic materialization. This law does not identify such a
partial value with native fully instantiated syntax. -/
theorem applyFull_semantically_inert {bindings : Bindings} {valuation : String → Metta.Atom}
    (satisfied : HEBindingSatisfied valuation bindings) (atom : Atom) (fuel : Nat) :
    applyClassSolution valuation (encodeModelAtom (bindings.applyFull atom fuel)) =
      applyClassSolution valuation (encodeModelAtom atom) := by
  induction fuel generalizing atom with
  | zero => rfl
  | succ fuel ih =>
      cases atom with
      | symbol | grounded => rfl
      | var name =>
          simp only [Bindings.applyFull]
          cases resolved : bindings.resolveFull name fuel with
          | none => rfl
          | some value =>
              simpa only [encodeModelAtom, applyClassSolution] using
                resolveFull_semantically_inert satisfied resolved
      | expression atoms =>
          simp only [Bindings.applyFull, encodeModelAtom, applyClassSolution, Metta.Atom.expr.injEq]
          have mapped : ∀ xs : List Atom,
              (encodeModelAtoms (xs.map fun atom => bindings.applyFull atom fuel)).map
                  (applyClassSolution valuation) =
                (encodeModelAtoms xs).map (applyClassSolution valuation) := by
            intro xs
            induction xs with
            | nil => rfl
            | cons first rest tail =>
                simpa only [List.map_cons, encodeModelAtoms] using congrArg₂ List.cons (ih first) tail
          exact mapped atoms

/-! ## Principal readout of the actual HE resolver -/

section PrincipalReadout

open Spec.Match.ModelTheory
open Spec.Match.Merge (AtomOccurs)

private theorem selected_stored {bindings : Bindings} {name : String} {value : Atom}
    (selected : (bindings.eqClassOrdered name).findSome? bindings.lookup = some value) :
    ∃ key, (key,value) ∈ bindings.assignments ∧ key ∈ bindings.eqClass name := by
  obtain ⟨key, member, lookup⟩ := List.exists_of_findSome?_eq_some selected
  obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp lookup
  exact ⟨key, by rw [entries]; simp, EqualityClosure.mem_eqClassOrdered_iff.mp member⟩

private theorem class_member_eq_of_outside {bindings : Bindings} {name other : String}
    (outside : name ∉ bindingSupport bindings) (member : other ∈ bindings.eqClass name) :
    other = name := by
  by_contra different
  obtain ⟨walk⟩ := EqualityClosure.mem_eqClass_iff_reachable.mp member
  have support := EqualityClosure.walk_support_subset_start_edgeNodes walk walk.end_mem_support
  have edgeMember : other ∈ EqualityClosure.edgeNodes bindings.equalities := by
    simpa only [List.mem_cons, different, false_or] using support
  have otherSupport : other ∈ bindingSupport bindings := by
    simp only [EqualityClosure.edgeNodes, List.mem_flatMap] at edgeMember
    obtain ⟨⟨left,right⟩, stored, endpoint⟩ := edgeMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at endpoint
    rcases endpoint with rfl | rfl
    · exact equality_left_mem_bindingSupport stored
    · exact equality_right_mem_bindingSupport stored
  exact outside (mem_bindingSupport_of_mem_eqClass otherSupport (mem_eqClass_symm member))

private theorem canonical_of_no_class_value {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings) (name : String)
    (missing : (bindings.eqClassOrdered name).findSome? bindings.lookup = none) :
    canonicalValuation bindings loopFree nonvariable name =
      .var (bindings.eqRepresentative name) := by
  classical
  by_cases supported : name ∈ bindingSupport bindings
  · apply canonicalValuation_eq_var_representative_of_no_classAssignment loopFree nonvariable supported
    rintro ⟨⟨⟨key,value⟩, stored, classMember⟩⟩
    have representativeClass := EqualityClosure.eqClassOrdered_eq_of_reachable
      (EqualityClosure.mem_eqClass_iff_reachable.mp (eqRepresentative_mem_eqClass bindings name))
    have keyMember : key ∈ bindings.eqClassOrdered name := by
      rw [representativeClass]
      exact EqualityClosure.mem_eqClassOrdered_iff.mpr classMember
    have noLookup := (List.findSome?_eq_none_iff.mp missing) key keyMember
    have noKey := (List.lookup_eq_none_iff.mp noLookup) (key,value) stored
    simp at noKey
  · have representative : bindings.eqRepresentative name = name :=
      class_member_eq_of_outside supported (eqRepresentative_mem_eqClass bindings name)
    simp only [canonicalValuation, dif_neg supported, representative]

private theorem unresolvable_occurrence (bindings : Bindings) :
    ∀ depth atom, Bindings.atomScanFuel atom ≤ depth →
      bindings.hasResolvableVarAux depth atom = false →
      ∀ name, AtomOccurs atom name →
        bindings.eqClassOrdered name = [name] ∧ bindings.lookup name = none := by
  intro depth
  induction depth with
  | zero =>
      intro atom bounded
      cases atom <;> simp [Bindings.atomScanFuel] at bounded
  | succ depth ih =>
      intro atom bounded unresolvable name occurrence
      cases occurrence with
      | var =>
          by_cases singleton : bindings.eqClassOrdered name = [name]
          · refine ⟨singleton, ?_⟩
            simpa [Bindings.hasResolvableVarAux, singleton, Bindings.isBound] using unresolvable
          · simp [Bindings.hasResolvableVarAux, singleton] at unresolvable
      | @expression atoms atom name member occurrence =>
          have atomBound := Bindings.atomScanFuel_mem atoms atom member
          apply ih atom (by omega) _ name occurrence
          have allFalse := List.any_eq_false.mp unresolvable
          exact Bool.eq_false_iff.mpr (allFalse atom member)

private theorem canonical_fixes_unresolvable {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings) {atom : Atom}
    (unresolvable : bindings.hasResolvableVar atom = false) :
    applyClassSolution (canonicalValuation bindings loopFree nonvariable)
      (encodeModelAtom atom) = encodeModelAtom atom := by
  refine (applyClassSolution_congr_of_eq_on_vars
    (canonicalValuation bindings loopFree nonvariable) (fun name => .var name)
    (encodeModelAtom atom) ?_).trans (applyClassSolution_identity _)
  intro name member
  have occurrence := atomOccurs_iff_mem_translated_vars.mpr member
  obtain ⟨singleton, lookup⟩ := unresolvable_occurrence bindings _ _ (Nat.le_refl _)
    unresolvable name occurrence
  have missing : (bindings.eqClassOrdered name).findSome? bindings.lookup = none := by
    simp [singleton, lookup]
  rw [canonical_of_no_class_value loopFree nonvariable name missing]
  simp [Bindings.eqRepresentative, singleton]


private def readoutRank (valuation : String → Metta.Atom) (atom : Atom) : Nat :=
  2 * (applyClassSolution valuation (encodeModelAtom atom)).size +
    if Spec.Match.Merge.isVariableB atom then 1 else 0

private theorem readoutRank_child (valuation : String → Metta.Atom)
    {atoms : List Atom} {atom : Atom} (member : atom ∈ atoms) :
    readoutRank valuation atom < readoutRank valuation (.expression atoms) := by
  have encoded : encodeModelAtom atom ∈ encodeModelAtoms atoms := by
    have maps : encodeModelAtoms atoms = atoms.map encodeModelAtom := by
      clear member
      induction atoms with
      | nil => rfl
      | cons first rest ih => simp only [encodeModelAtoms, List.map_cons, ih]
    rw [maps]
    exact List.mem_map.mpr ⟨atom, member, rfl⟩
  have sizes : (applyClassSolution valuation (encodeModelAtom atom)).size ∈
      ((encodeModelAtoms atoms).map (applyClassSolution valuation)).map Metta.Atom.size :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_,encoded,rfl⟩,rfl⟩
  have smaller := List.single_le_sum (by intro _ _; omega) _ sizes
  have extra : (if Spec.Match.Merge.isVariableB atom then 1 else 0) ≤ 1 := by
    split <;> omega
  have parent : readoutRank valuation (.expression atoms) =
      2 * ((((encodeModelAtoms atoms).map (applyClassSolution valuation)).map Metta.Atom.size).sum + 1) := by
    simp [readoutRank,encodeModelAtom,applyClassSolution,Metta.Atom.size,Spec.Match.Merge.isVariableB,Nat.add_comm]
  rw [parent]
  unfold readoutRank
  omega

private def AncestorBound (valuation : String → Metta.Atom)
    (visited : List String) (atom : Atom) : Prop :=
  ∀ name, AtomOccurs atom name → ∀ seen ∈ visited,
    (valuation name).size < (valuation seen).size

private theorem resolver_principal_of_rank {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable) :
    ∀ fuel visited atom,
      readoutRank (canonicalValuation bindings loopFree nonvariable) atom < fuel →
      AncestorBound (canonicalValuation bindings loopFree nonvariable) visited atom →
      ∃ resolved, bindings.resolveAtomFullAux fuel visited atom = some resolved ∧
        encodeModelAtom resolved =
          applyClassSolution (canonicalValuation bindings loopFree nonvariable)
            (encodeModelAtom atom) := by
  let valuation := canonicalValuation bindings loopFree nonvariable
  have satisfied : HEBindingSatisfied valuation bindings :=
    canonicalValuation_satisfies_of_classCoherent loopFree nonvariable coherent
  intro fuel
  induction fuel with
  | zero => intro visited atom bounded; omega
  | succ fuel ih =>
      intro visited atom bounded ancestors
      cases atom with
      | symbol name => exact ⟨.symbol name,rfl,by simp [encodeModelAtom,applyClassSolution]⟩
      | grounded value => exact ⟨.grounded value,rfl,by simp [encodeModelAtom,applyClassSolution]⟩
      | expression atoms =>
          have each : ∀ atom ∈ atoms, ∃ resolved,
              bindings.resolveAtomFullAux fuel visited atom = some resolved ∧
              encodeModelAtom resolved = applyClassSolution valuation (encodeModelAtom atom) := by
            intro atom member
            apply ih visited atom
            · have smaller := readoutRank_child valuation member
              change readoutRank valuation (.expression atoms) < fuel + 1 at bounded
              change readoutRank valuation atom < fuel
              omega
            · intro name occurrence seen inVisited
              exact ancestors name (.expression member occurrence) seen inVisited
          have many : ∀ xs : List Atom, (∀ x ∈ xs, x ∈ atoms) →
              ∃ ys, xs.mapM (bindings.resolveAtomFullAux fuel visited) = some ys ∧
                encodeModelAtoms ys = (encodeModelAtoms xs).map (applyClassSolution valuation) := by
            intro xs
            induction xs with
            | nil => intro _; exact ⟨[],rfl,rfl⟩
            | cons first rest tail =>
                intro subset
                obtain ⟨value,firstRun,firstValue⟩ := each first (subset first (by simp))
                obtain ⟨values,restRun,restValues⟩ := tail (fun x member => subset x (by simp [member]))
                refine ⟨value::values, ?_, ?_⟩
                · simp [List.mapM_cons,firstRun,restRun]
                · simp only [encodeModelAtoms,List.map_cons,firstValue,restValues]
          obtain ⟨resolved,mapped,readout⟩ := many atoms (fun _ member => member)
          refine ⟨.expression resolved, ?_, ?_⟩
          · simp [Bindings.resolveAtomFullAux,mapped]
          · simpa only [encodeModelAtom,applyClassSolution] using congrArg Metta.Atom.expr readout
      | var name =>
          have notVisited : (bindings.eqClassOrdered name).any visited.contains = false := by
            apply List.any_eq_false.mpr
            intro seen inClass inVisited
            have same := class_observation satisfied inClass
            have strict := ancestors name (.var name) seen (by simpa using inVisited)
            change (valuation name).size < (valuation seen).size at strict
            rw [same] at strict
            exact (Nat.lt_irrefl _) strict
          cases selected : (bindings.eqClassOrdered name).findSome? bindings.lookup with
          | none =>
              have observed := canonical_of_no_class_value loopFree nonvariable name selected
              by_cases singleton : bindings.eqClassOrdered name = [name]
              · refine ⟨.var name, ?_, ?_⟩
                · simp only [Bindings.resolveAtomFullAux,notVisited,Bool.false_eq_true,↓reduceIte,selected]
                  rw [if_pos singleton]
                · simpa only [encodeModelAtom,applyClassSolution,Bindings.eqRepresentative,singleton,
                    List.headD_cons] using observed.symm
              · refine ⟨.var (bindings.eqRepresentative name), ?_, ?_⟩
                · simp only [Bindings.resolveAtomFullAux,notVisited,Bool.false_eq_true,↓reduceIte,selected]
                  rw [if_neg singleton]
                · simpa only [encodeModelAtom,applyClassSolution] using observed.symm
          | some value =>
              obtain ⟨key,stored,inClass⟩ := selected_stored selected
              have valueNonvar := nonvariable key value stored
              have observed : valuation name = applyClassSolution valuation (encodeModelAtom value) :=
                selected_value_observation satisfied selected
              have unfoldResolver : bindings.resolveAtomFullAux (fuel+1) visited (.var name) =
                  if bindings.hasResolvableVar value then
                    bindings.resolveAtomFullAux fuel (bindings.eqClassOrdered name ++ visited) value
                  else some value := by
                cases value <;> simp_all [Bindings.resolveAtomFullAux,Spec.Match.Merge.isVariableB]
              rw [unfoldResolver]
              by_cases resolvable : bindings.hasResolvableVar value = true
              · rw [if_pos resolvable]
                have smaller : readoutRank valuation value < readoutRank valuation (.var name) := by
                  have left : readoutRank valuation value =
                      2 * (applyClassSolution valuation (encodeModelAtom value)).size := by
                    simp only [readoutRank,valueNonvar,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
                  have right : readoutRank valuation (.var name) = 2 * (valuation name).size + 1 := by
                    simp only [readoutRank,Spec.Match.Merge.isVariableB,encodeModelAtom,applyClassSolution,↓reduceIte]
                  rw [left,right,observed]
                  omega
                obtain ⟨resolved,ran,readout⟩ := ih (bindings.eqClassOrdered name ++ visited) value
                  (by
                    change readoutRank valuation (.var name) < fuel + 1 at bounded
                    change readoutRank valuation value < fuel
                    omega) (by
                    intro dependency occurrence seen inVisited
                    have smaller := size_valuation_lt_apply_of_atomOccurs_nonvariable valuation
                      valueNonvar occurrence
                    rw [← observed] at smaller
                    rcases List.mem_append.mp inVisited with inClass | inOld
                    · have same := class_observation satisfied inClass
                      change (valuation dependency).size < (valuation seen).size
                      rw [← same]
                      exact smaller
                    · exact smaller.trans (ancestors name (.var name) seen inOld))
                refine ⟨resolved,ran,?_⟩
                simpa only [encodeModelAtom,applyClassSolution] using readout.trans observed.symm
              · rw [if_neg resolvable]
                refine ⟨value,rfl,?_⟩
                simpa only [encodeModelAtom,applyClassSolution] using
                  (canonical_fixes_unresolvable loopFree nonvariable
                    (by simpa using resolvable)).symm.trans observed.symm


private theorem application_principal_of_rank {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable) :
    ∀ fuel atom,
      readoutRank (canonicalValuation bindings loopFree nonvariable) atom + 1 < fuel →
      encodeModelAtom (bindings.applyFull atom fuel) =
        applyClassSolution (canonicalValuation bindings loopFree nonvariable)
          (encodeModelAtom atom) := by
  let valuation := canonicalValuation bindings loopFree nonvariable
  intro fuel
  induction fuel with
  | zero => intro atom bounded; omega
  | succ fuel ih =>
      intro atom bounded
      cases atom with
      | symbol name => simp [Bindings.applyFull,encodeModelAtom,applyClassSolution]
      | grounded value => simp [Bindings.applyFull,encodeModelAtom,applyClassSolution]
      | expression atoms =>
          have each : ∀ atom ∈ atoms,
              encodeModelAtom (bindings.applyFull atom fuel) =
                applyClassSolution valuation (encodeModelAtom atom) := by
            intro atom member
            apply ih atom
            have smaller := readoutRank_child valuation member
            change readoutRank valuation (.expression atoms) + 1 < fuel + 1 at bounded
            change readoutRank valuation atom + 1 < fuel
            omega
          have many : ∀ xs : List Atom, (∀ x ∈ xs, x ∈ atoms) →
              encodeModelAtoms (xs.map (fun atom => bindings.applyFull atom fuel)) =
                (encodeModelAtoms xs).map (applyClassSolution valuation) := by
            intro xs
            induction xs with
            | nil => intro _; rfl
            | cons first rest tail =>
                intro subset
                simp only [List.map_cons,encodeModelAtoms]
                exact congrArg₂ List.cons (each first (subset first (by simp)))
                  (tail (fun atom member => subset atom (by simp [member])))
          simpa only [Bindings.applyFull,encodeModelAtom,applyClassSolution] using
            congrArg Metta.Atom.expr (many atoms (fun _ member => member))
      | var name =>
          by_cases missing :
              (bindings.eqClassOrdered name = [name] &&
                ((bindings.eqClassOrdered name).findSome? bindings.lookup).isNone) = true
          · have pair : bindings.eqClassOrdered name = [name] ∧
                (bindings.eqClassOrdered name).findSome? bindings.lookup = none := by
              simpa using missing
            obtain ⟨singleton,empty⟩ := pair
            have observed := canonical_of_no_class_value loopFree nonvariable name empty
            have unchanged : bindings.applyFull (.var name) (fuel+1) = .var name := by
              simp only [Bindings.applyFull,Bindings.resolveFull,missing,↓reduceIte]
            rw [unchanged]
            simpa only [encodeModelAtom,applyClassSolution,Bindings.eqRepresentative,
              singleton,List.headD_cons] using observed.symm
          · obtain ⟨resolved,ran,readout⟩ := resolver_principal_of_rank loopFree nonvariable coherent
              fuel [] (.var name) (by omega) (by intro _ _ _ member; cases member)
            have executed : bindings.applyFull (.var name) (fuel+1) = resolved := by
              simp [Bindings.applyFull,Bindings.resolveFull,missing,ran]
            rw [executed]
            exact readout

/-- Complete materialization by the actual HE resolver is the independent
canonical valuation. Coverage is the actual dependency certificate; class
coherence and acyclicity are properties of the input binding theory. -/
theorem applyFull_eq_canonical_of_covered {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable)
    (atom : Atom) (depth : Nat) (covered : bindings.applyFullCovered atom depth = true) :
    encodeModelAtom (bindings.applyFull atom depth) =
      applyClassSolution (canonicalValuation bindings loopFree nonvariable) (encodeModelAtom atom) := by
  let extra := readoutRank (canonicalValuation bindings loopFree nonvariable) atom + 2
  have actual := application_principal_of_rank loopFree nonvariable coherent (depth+extra) atom
    (by dsimp [extra]; omega)
  rw [bindings.applyFullCovered_stable atom depth extra covered] at actual
  exact actual

/-- The existing executable structural bound supplies coverage for every atom;
the proof-only model rank is absent from this runtime-facing statement. -/
theorem applyFull_eq_canonical_of_resolutionFuel {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable)
    (atom : Atom) (extra : Nat := 0) :
    encodeModelAtom (bindings.applyFull atom (bindings.resolutionFuel atom + extra)) =
      applyClassSolution (canonicalValuation bindings loopFree nonvariable) (encodeModelAtom atom) := by
  rw [bindings.applyFullCovered_stable atom (bindings.resolutionFuel atom) extra
    (bindings.applyFullCovered_resolutionFuel atom)]
  exact applyFull_eq_canonical_of_covered loopFree nonvariable coherent atom _
    (bindings.applyFullCovered_resolutionFuel atom)

/-- Simultaneously reading variables through the actual HE implementation
constructs a principal solution of its coherent acyclic binding record. The
encoding here is only the existing injective syntax map. -/
theorem applyFull_mostGeneralSolution {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable) :
    MostGeneralSolution bindings (fun name =>
      encodeModelAtom (bindings.applyFull (.var name) (bindings.resolutionFuel (.var name)))) := by
  have same : (fun name =>
      encodeModelAtom (bindings.applyFull (.var name) (bindings.resolutionFuel (.var name)))) =
      canonicalValuation bindings loopFree nonvariable := by
    funext name
    simpa only [Nat.add_zero,encodeModelAtom,applyClassSolution] using
      applyFull_eq_canonical_of_resolutionFuel loopFree nonvariable coherent (.var name)
  rw [same]
  exact canonicalValuation_mostGeneralSolution_of_classCoherent loopFree nonvariable coherent

/-- The executable HE binding syntax obtains the same model; no evaluator from the model
language participates in this transport. -/
theorem applyFull_typeBindingSatisfied {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable) :
    Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => bindings.applyFull (.var name) (bindings.resolutionFuel (.var name))) bindings :=
  (Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated _ _).mpr
    (applyFull_mostGeneralSolution loopFree nonvariable coherent).1

/-- One sufficient-depth executable HE readout acts homomorphically on an arbitrary
observed atom, including all of its correlated residual variable occurrences. -/
theorem applyFull_eq_readoutValuation_of_covered {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable)
    (atom : Atom) (depth : Nat) (covered : bindings.applyFullCovered atom depth = true) :
    bindings.applyFull atom depth = Spec.Type.RuntimeRefinement.applyTypeValuation
      (fun name => bindings.applyFull (.var name) (bindings.resolutionFuel (.var name))) atom := by
  apply encodeModelAtom_injective
  rw [applyFull_eq_canonical_of_covered loopFree nonvariable coherent atom depth covered,
    Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation]
  apply applyClassSolution_congr_of_eq_on_vars
  intro name _
  simpa only [Nat.add_zero,encodeModelAtom,applyClassSolution] using
    (applyFull_eq_canonical_of_resolutionFuel loopFree nonvariable coherent (.var name)).symm


/-- The existing model-preservation law stated entirely in the executable HE binding syntax.
It holds even below complete materialization depth. -/
theorem applyFull_type_semantically_inert {bindings : Bindings} {valuation : String → Atom}
    (satisfied : Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings)
    (atom : Atom) (depth : Nat) :
    Spec.Type.RuntimeRefinement.applyTypeValuation valuation (bindings.applyFull atom depth) =
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation atom := by
  apply encodeModelAtom_injective
  simp only [Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation]
  exact applyFull_semantically_inert
    (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied satisfied) atom depth

/-- Scoped-equivalent binding theories yield alpha-equivalent actual HE
readouts. Private model extensions are taken from the existing scoped
observer, and principality is earned from the real resolver. -/
theorem applyFull_observedTypeAlpha_of_scoped_solution_equiv
    {scope : List String} {left right : Bindings}
    (leftLoopFree : Spec.Match.Merge.SemanticLoopFree left)
    (rightLoopFree : Spec.Match.Merge.SemanticLoopFree right)
    (leftNonvariable : AssignmentsNonVariable left)
    (rightNonvariable : AssignmentsNonVariable right)
    (leftCoherent : CanonicalClassCoherent left leftLoopFree leftNonvariable)
    (rightCoherent : CanonicalClassCoherent right rightLoopFree rightNonvariable)
    (equiv : Spec.Bindings.ScopeObservation.BindingTheoryEquivAt scope left right)
    (atom : Atom)
    (atomCovered : ∀ name, name ∈ Spec.Type.Presentation.TypeSubst.typeVars atom → name ∈ scope)
    (leftDepth rightDepth : Nat)
    (leftCovered : left.applyFullCovered atom leftDepth = true)
    (rightCovered : right.applyFullCovered atom rightDepth = true) :
    Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel
      (left.applyFull atom leftDepth) (right.applyFull atom rightDepth) := by
  let leftModel := fun name => left.applyFull (.var name) (left.resolutionFuel (.var name))
  let rightModel := fun name => right.applyFull (.var name) (right.resolutionFuel (.var name))
  have leftSatisfied := applyFull_typeBindingSatisfied leftLoopFree leftNonvariable leftCoherent
  have rightSatisfied := applyFull_typeBindingSatisfied rightLoopFree rightNonvariable rightCoherent
  apply Spec.Type.Presentation.PrincipalAlpha.observedTypeAlpha_of_mutual_instances
  · obtain ⟨extension, satisfied, agrees⟩ := equiv.rightToLeft rightModel rightSatisfied
    refine ⟨extension, ?_⟩
    rw [applyFull_type_semantically_inert satisfied]
    rw [Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars atom
      (fun name member => agrees name (atomCovered name member))]
    exact (applyFull_eq_readoutValuation_of_covered rightLoopFree rightNonvariable rightCoherent
      atom rightDepth rightCovered).symm
  · obtain ⟨extension, satisfied, agrees⟩ := equiv.leftToRight leftModel leftSatisfied
    refine ⟨extension, ?_⟩
    rw [applyFull_type_semantically_inert satisfied]
    rw [Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars atom
      (fun name member => (agrees name (atomCovered name member)).symm)]
    exact (applyFull_eq_readoutValuation_of_covered leftLoopFree leftNonvariable leftCoherent
      atom leftDepth leftCovered).symm

/-- Reading an entire live tuple uses one residual permutation, including
observations spanning several public variables and private-frame extensions. -/
theorem applyFull_joint_permutation_of_scoped_solution_equiv
    {scope : List String} {left right : Bindings}
    (leftLoopFree : Spec.Match.Merge.SemanticLoopFree left)
    (rightLoopFree : Spec.Match.Merge.SemanticLoopFree right)
    (leftNonvariable : AssignmentsNonVariable left)
    (rightNonvariable : AssignmentsNonVariable right)
    (leftCoherent : CanonicalClassCoherent left leftLoopFree leftNonvariable)
    (rightCoherent : CanonicalClassCoherent right rightLoopFree rightNonvariable)
    (equiv : Spec.Bindings.ScopeObservation.BindingTheoryEquivAt scope left right)
    (observations : List Atom)
    (observationsCovered : ∀ name,
      name ∈ Spec.Type.Presentation.TypeSubst.typeVars (.expression observations) → name ∈ scope)
    (leftDepth rightDepth : Nat)
    (leftCovered : left.applyFullCovered (.expression observations) leftDepth = true)
    (rightCovered : right.applyFullCovered (.expression observations) rightDepth = true) :
    ∃ permutation : Equiv.Perm String,
      right.applyFull (.expression observations) rightDepth =
        Spec.Type.RuntimeRefinement.renameTypeVars permutation
          (left.applyFull (.expression observations) leftDepth) := by
  exact Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.exists_permutation
    (applyFull_observedTypeAlpha_of_scoped_solution_equiv leftLoopFree rightLoopFree
      leftNonvariable rightNonvariable leftCoherent rightCoherent equiv
      (.expression observations) observationsCovered leftDepth rightDepth leftCovered rightCovered)

/-- Coherent complete HE readouts of the same binding theory are alpha
variants. This follows from the two principal factorizations, not from
permuting the physical assignment or equality records. -/
theorem applyFull_observedTypeAlpha_of_solution_equiv
    {left right : Bindings}
    (leftLoopFree : Spec.Match.Merge.SemanticLoopFree left)
    (rightLoopFree : Spec.Match.Merge.SemanticLoopFree right)
    (leftNonvariable : AssignmentsNonVariable left)
    (rightNonvariable : AssignmentsNonVariable right)
    (leftCoherent : CanonicalClassCoherent left leftLoopFree leftNonvariable)
    (rightCoherent : CanonicalClassCoherent right rightLoopFree rightNonvariable)
    (sameSolutions : ∀ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation left ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation right)
    (atom : Atom) (leftDepth rightDepth : Nat)
    (leftCovered : left.applyFullCovered atom leftDepth = true)
    (rightCovered : right.applyFullCovered atom rightDepth = true) :
    Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel
      (left.applyFull atom leftDepth) (right.applyFull atom rightDepth) := by
  apply applyFull_observedTypeAlpha_of_scoped_solution_equiv leftLoopFree rightLoopFree
    leftNonvariable rightNonvariable leftCoherent rightCoherent
    (scope := Spec.Type.Presentation.TypeSubst.typeVars atom)
    (atom := atom) (leftDepth := leftDepth) (rightDepth := rightDepth)
  · exact Spec.Bindings.ScopeObservation.BindingTheoryEquivAt.of_solution_iff sameSolutions _
  · exact fun _ member => member
  · exact leftCovered
  · exact rightCovered

/-- Reading all live observations as one expression yields ONE global
permutation of residual names. Repeated occurrences and cross-observation
sharing are therefore preserved jointly. Actual checkpoint records are not
identified by this semantic comparison. -/
theorem applyFull_joint_permutation_of_solution_equiv
    {left right : Bindings}
    (leftLoopFree : Spec.Match.Merge.SemanticLoopFree left)
    (rightLoopFree : Spec.Match.Merge.SemanticLoopFree right)
    (leftNonvariable : AssignmentsNonVariable left)
    (rightNonvariable : AssignmentsNonVariable right)
    (leftCoherent : CanonicalClassCoherent left leftLoopFree leftNonvariable)
    (rightCoherent : CanonicalClassCoherent right rightLoopFree rightNonvariable)
    (sameSolutions : ∀ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation left ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation right)
    (observations : List Atom) (leftDepth rightDepth : Nat)
    (leftCovered : left.applyFullCovered (.expression observations) leftDepth = true)
    (rightCovered : right.applyFullCovered (.expression observations) rightDepth = true) :
    ∃ permutation : Equiv.Perm String,
      right.applyFull (.expression observations) rightDepth =
        Spec.Type.RuntimeRefinement.renameTypeVars permutation
          (left.applyFull (.expression observations) leftDepth) := by
  exact Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.exists_permutation
    (applyFull_observedTypeAlpha_of_solution_equiv leftLoopFree rightLoopFree
      leftNonvariable rightNonvariable leftCoherent rightCoherent sameSolutions
      (.expression observations) leftDepth rightDepth leftCovered rightCovered)

open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation
open Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation

/-- The independent equation fold and the actual covered HE readout are
alpha variants on the declared scope. The source record need not be a
coherent input to the executable resolver: its fold earns a normal exact
presentation instead. -/
theorem applyFull_observedTypeAlpha_of_bindingMaterialization
    {scope : List String} {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (equiv : BindingTheoryEquivAt scope native independent)
    (atom : Atom)
    (atomCovered : ∀ name, name ∈ TypeSubst.typeVars atom → name ∈ scope)
    (depth : Nat) (covered : native.applyFullCovered atom depth = true)
    {normalized : Atom}
    (materialized : BindingMaterializationRel independent atom normalized) :
    Alpha.ObservedTypeAlphaRel (native.applyFull atom depth) normalized := by
  obtain ⟨presentation, _fold, normal, solutions, output⟩ := materialized.presentation
  let independentModel := Theory.presentedValuation presentation
  have independentSatisfied : TypeBindingSatisfied independentModel independent :=
    (solutions independentModel).mp (Theory.normal_presentedValuation_satisfied normal)
  let nativeModel := fun name => native.applyFull (.var name)
    (native.resolutionFuel (.var name))
  have nativeSatisfied := applyFull_typeBindingSatisfied loopFree nonvariable coherent
  apply PrincipalAlpha.observedTypeAlpha_of_mutual_instances
  · obtain ⟨extension, satisfied, agrees⟩ :=
      equiv.rightToLeft independentModel independentSatisfied
    refine ⟨extension, ?_⟩
    rw [applyFull_type_semantically_inert satisfied]
    rw [applyTypeValuation_congr_of_typeVars atom
      (fun name member => agrees name (atomCovered name member))]
    exact (Theory.applyTypeValuation_presented_eq_apply presentation atom).trans output.symm
  · obtain ⟨extension, satisfied, agrees⟩ :=
      equiv.leftToRight nativeModel nativeSatisfied
    refine ⟨extension, ?_⟩
    rw [materialized.preserves_model extension satisfied]
    rw [applyTypeValuation_congr_of_typeVars atom
      (fun name member => (agrees name (atomCovered name member)).symm)]
    exact (applyFull_eq_readoutValuation_of_covered loopFree nonvariable coherent
      atom depth covered).symm

/-- Materialize all observations together; one residual permutation preserves
sharing between observations and repeated uses inside each observation. -/
theorem applyFull_joint_permutation_of_bindingMaterialization
    {scope : List String} {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (equiv : BindingTheoryEquivAt scope native independent)
    (observations : List Atom)
    (observationsCovered : ∀ name,
      name ∈ TypeSubst.typeVars (.expression observations) → name ∈ scope)
    (depth : Nat)
    (covered : native.applyFullCovered (.expression observations) depth = true)
    {normalized : Atom}
    (materialized : BindingMaterializationRel independent (.expression observations) normalized) :
    ∃ permutation : Equiv.Perm String,
      normalized = renameTypeVars permutation
        (native.applyFull (.expression observations) depth) :=
  ScopeObservation.ObservedTypeAlphaRel.exists_permutation
    (applyFull_observedTypeAlpha_of_bindingMaterialization loopFree nonvariable coherent
      equiv (.expression observations) observationsCovered depth covered materialized)

/-- The source materialization exists from the actual native principal model
and scoped equivalence. Neither satisfiability nor output correspondence is
an extra caller premise. -/
theorem exists_joint_bindingMaterialization_of_scoped_solution_equiv
    {scope : List String} {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (equiv : BindingTheoryEquivAt scope native independent)
    (observations : List Atom)
    (observationsCovered : ∀ name,
      name ∈ TypeSubst.typeVars (.expression observations) → name ∈ scope)
    (depth : Nat)
    (covered : native.applyFullCovered (.expression observations) depth = true) :
    ∃ normalized,
      BindingMaterializationRel independent (.expression observations) normalized ∧
        ∃ permutation : Equiv.Perm String,
          normalized = renameTypeVars permutation
            (native.applyFull (.expression observations) depth) := by
  obtain ⟨independentModel, independentSatisfied, _⟩ := equiv.leftToRight _
    (applyFull_typeBindingSatisfied loopFree nonvariable coherent)
  obtain ⟨normalized, materialized⟩ := BindingMaterializationRel.exists_of_satisfiable
    ⟨independentModel, independentSatisfied⟩ (.expression observations)
  exact ⟨normalized, materialized,
    applyFull_joint_permutation_of_bindingMaterialization loopFree nonvariable coherent
      equiv observations observationsCovered depth covered materialized⟩

/-- Full solution equality strengthens joint alpha readout to one residual
permutation fixing every source model. The permutation is supported only on
the two observed residual supports and preserves the source binding theory.
Scoped equivalence alone is deliberately not the premise of this theorem. -/
theorem applyFull_joint_model_fixed_permutation_of_bindingMaterialization
    {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (sameSolutions : ∀ valuation : String → Atom,
      TypeBindingSatisfied valuation native ↔ TypeBindingSatisfied valuation independent)
    (observations : List Atom) (depth : Nat)
    (covered : native.applyFullCovered (.expression observations) depth = true)
    {normalized : Atom}
    (materialized : BindingMaterializationRel independent (.expression observations) normalized) :
    ∃ permutation : Equiv.Perm String,
      normalized = renameTypeVars permutation
        (native.applyFull (.expression observations) depth) ∧
      (∀ valuation, TypeBindingSatisfied valuation independent →
        ∀ name, valuation (permutation name) = valuation name) ∧
      (∀ name,
        name ∉ TypeSubst.typeVars (native.applyFull (.expression observations) depth) →
        name ∉ TypeSubst.typeVars normalized → permutation name = name) ∧
      (∀ valuation,
        TypeBindingSatisfied valuation (renameBindings permutation independent) ↔
          TypeBindingSatisfied valuation independent) := by
  have alpha := applyFull_observedTypeAlpha_of_bindingMaterialization loopFree nonvariable coherent
    (BindingTheoryEquivAt.of_solution_iff sameSolutions
      (TypeSubst.typeVars (.expression observations)))
    (.expression observations) (fun _ member => member) depth covered materialized
  let Model := {valuation : String → Atom // TypeBindingSatisfied valuation independent}
  obtain ⟨permutation, equation, fixedModels, outside⟩ :=
    PrincipalAlpha.observedTypeAlpha_exists_model_fixed_permutation alpha
      (fun model : Model => model.1)
      (fun model =>
        (applyFull_type_semantically_inert ((sameSolutions model.1).mpr model.2)
          (.expression observations) depth).trans
        (materialized.preserves_model model.1 model.2).symm)
  have fixed : ∀ valuation, TypeBindingSatisfied valuation independent →
      ∀ name, valuation (permutation name) = valuation name := by
    intro valuation satisfied name
    exact fixedModels ⟨valuation, satisfied⟩ name
  exact ⟨permutation, equation, fixed, outside,
    renameBindings_theory_of_model_fixed independent permutation fixed⟩

end PrincipalReadout

/-! ## Canonical coherence earned by actual reconciliation -/

section ActualMergePrincipality

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Spec.Match.ModelTheory Spec.Match.StructuralModel
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation

open private map_replicate_append_singleton_last
  from Mettapedia.Languages.MeTTa.HE.Spec.Match.StructuralModel

private theorem occurs_iff_typeVars {atom : Atom} {name : String} :
    Spec.Match.Merge.AtomOccurs atom name ↔ name ∈ TypeSubst.typeVars atom := by
  rw [atomOccurs_iff_mem_translated_vars, Spec.Type.Presentation.encodeModelAtom_vars_eq_typeVars]

private theorem dependenciesBelow_of_support {target out : Bindings}
    {source : DependencyNode target}
    (supported : ∀ name ∈ specBindingVars out,
      ∃ member : name ∈ bindingSupport target,
        DependencyOrder target (representativeNode ⟨name,member⟩) source) :
    BindingDependenciesBelow target source out := by
  constructor
  · intro key value stored
    constructor
    · intro name occurs
      cases occurs
      apply supported key
      exact List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨(key,value), stored, by simp⟩)
    · intro name occurs
      apply supported name
      exact List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨(key,value), stored, List.mem_cons_of_mem _ (occurs_iff_typeVars.mp occurs)⟩)
  · intro left right stored
    constructor
    · intro name occurs
      cases occurs
      apply supported left
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨(left,right), stored, by simp⟩)
    · intro name occurs
      cases occurs
      apply supported right
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨(left,right), stored, by simp⟩)

/-- The executable-tracking match witness introduces no dependency outside its
input atoms. It is used as recursion evidence, not as independent semantics. -/
theorem declMatch_dependenciesBelow {target : Bindings} {source : DependencyNode target}
    {left right : Atom} {out : Bindings}
    (matched : DeclMatchSpec.MatchRel left right out)
    (leftBelow : AtomDependenciesBelow target source left)
    (rightBelow : AtomDependenciesBelow target source right) :
    BindingDependenciesBelow target source out := by
  obtain ⟨fuel, member⟩ := DeclMatchSpec.matchAtoms_complete matched
  apply dependenciesBelow_of_support
  intro name present
  rcases FreshPrivateMerge.match_support_subset member present with inside | inside
  · exact leftBelow name (occurs_iff_typeVars.mpr inside)
  · exact rightBelow name (occurs_iff_typeVars.mpr inside)

/-- Empty-seed list matching also preserves the strict input dependency scope. -/
theorem declMatchList_dependenciesBelow {target : Bindings} {source : DependencyNode target}
    {left right : List Atom} {out : Bindings}
    (matched : DeclMatchSpec.MatchListRel left right out)
    (leftBelow : AtomsDependenciesBelow target source left)
    (rightBelow : AtomsDependenciesBelow target source right) :
    BindingDependenciesBelow target source out := by
  obtain ⟨fuel, member⟩ := DeclMatchSpec.matchAtomsList_complete matched
  apply dependenciesBelow_of_support
  intro name present
  rcases FreshPrivateMerge.matchList_support_subset member present with
    ⟨seed, selected, inside⟩ | inside | inside
  · have same : seed = Bindings.empty := List.mem_singleton.mp selected
    simp [same, specBindingVars, Bindings.empty] at inside
  · obtain ⟨atom, stored, occurs⟩ :=
      Spec.Type.Presentation.Freshness.exists_mem_of_mem_typeVarsList inside
    exact leftBelow atom stored name (occurs_iff_typeVars.mpr occurs)
  · obtain ⟨atom, stored, occurs⟩ :=
      Spec.Type.Presentation.Freshness.exists_mem_of_mem_typeVarsList inside
    exact rightBelow atom stored name (occurs_iff_typeVars.mpr occurs)

/-- The Boolean check has exactly the structural agreement meaning used by the
independent class-coherence algebra. -/
theorem valuesConsistent_iff_valuesAgree (values : List Atom) :
    Bindings.valuesConsistent values = true ↔ Spec.Match.Merge.ValuesAgree values := by
  cases values <;> simp [Bindings.valuesConsistent, Spec.Match.Merge.ValuesAgree]

/-- Replaying every actual right-hand row makes it true below the current
canonical dependency frontier. Duplicate rows are retained by the derivation;
no deduplicated independent merge endpoint is asserted. -/
theorem declMerge_right_satisfied_of_dependenciesBelow
    {target : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree target)
    (nonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (smaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target loopFree nonvariable node =
          applyClassSolution (canonicalValuation target loopFree nonvariable)
            (encodeModelAtom assignment.1.2))
    {left right out : Bindings}
    (merged : DeclMergeSpec.MergeRel left right out)
    (included : BindingSubrecord out target)
    (below : BindingDependenciesBelow target source right) :
    HEBindingSatisfied (canonicalValuation target loopFree nonvariable) right := by
  let valuation := canonicalValuation target loopFree nonvariable
  have replay : BindingSubrecord out target →
      BindingDependenciesBelow target source right → HEBindingSatisfied valuation right := by
    apply DeclMergeSpec.MergeRel.rec
      (motive_1 := fun _ key value result _ =>
        BindingSubrecord result target →
        AtomDependenciesBelow target source (.var key) →
        AtomDependenciesBelow target source value →
        valuation key = applyClassSolution valuation (encodeModelAtom value))
      (motive_2 := fun _ first second result _ =>
        BindingSubrecord result target → valuation first = valuation second)
      (motive_3 := fun _ assignments result _ =>
        BindingSubrecord result target →
        (∀ key value, (key,value) ∈ assignments →
          AtomDependenciesBelow target source (.var key) ∧
          AtomDependenciesBelow target source value) →
        ∀ key value, (key,value) ∈ assignments →
          valuation key = applyClassSolution valuation (encodeModelAtom value))
      (motive_4 := fun _ equalities result _ =>
        BindingSubrecord result target →
        ∀ first second, (first,second) ∈ equalities →
          valuation first = valuation second)
      (motive_5 := fun _ rhs result _ =>
        BindingSubrecord result target →
        BindingDependenciesBelow target source rhs → HEBindingSatisfied valuation rhs)
      (t := merged)
    next =>
      intro seed key value empty contained keyBelow _valueBelow
      have free := EqualityClosure.isBound_eq_false_of_classValues_nil empty
      have stored : (key,value) ∈ (seed.assign key value).assignments := by
        simp [Bindings.assign, free]
      exact canonical_assignment_eq_of_key_below loopFree nonvariable smaller
        (contained.1 _ stored) keyBelow
    next =>
      intro seed key value first rest values _agree same contained keyBelow _valueBelow
      subst value
      apply canonical_eq_classValue_of_subrecord_below
        loopFree nonvariable smaller contained keyBelow
      simp [values]
    next =>
      intro seed key value first rest matched result values _agree _different
        matchedProof mergeProof mergeIH contained keyBelow valueBelow
      have firstMem : first ∈ seed.classValues key := by simp [values]
      have seedTarget := (FreshPrivateMerge.mergeRel_left_subrecord mergeProof).trans contained
      have firstBelow := classValue_dependenciesBelow_of_subrecord
        nonvariable seedTarget keyBelow firstMem
      have matchedBelow := declMatch_dependenciesBelow matchedProof firstBelow valueBelow
      have matchedSatisfied := mergeIH contained matchedBelow
      obtain ⟨fuel, member⟩ := DeclMatchSpec.matchAtoms_complete matchedProof
      have firstValue := (matchAtoms_solution_iff member valuation).mp matchedSatisfied
      exact (canonical_eq_classValue_of_subrecord_below
        loopFree nonvariable smaller seedTarget keyBelow firstMem).trans firstValue
    next =>
      intro seed key value first rest matched result values _disagree
        listProof mergeProof mergeIH contained keyBelow valueBelow
      have firstMem : first ∈ seed.classValues key := by simp [values]
      have seedTarget := (FreshPrivateMerge.mergeRel_left_subrecord mergeProof).trans contained
      have allBelow : ∀ atom ∈ first :: rest, AtomDependenciesBelow target source atom := by
        intro atom member
        exact classValue_dependenciesBelow_of_subrecord nonvariable seedTarget keyBelow
          (by simpa only [values] using member)
      have matchedBelow := declMatchList_dependenciesBelow listProof
        (by
          intro atom member
          obtain ⟨_, same⟩ := List.mem_replicate.mp member
          subst atom
          exact allBelow first (by simp))
        (by
          intro atom member
          rcases List.mem_append.mp member with member | member
          · exact allBelow atom (by simp [member])
          · have same := List.mem_singleton.mp member
            exact same ▸ valueBelow)
      have matchedSatisfied := mergeIH contained matchedBelow
      obtain ⟨fuel, member⟩ := DeclMatchSpec.matchAtomsList_complete listProof
      have listValues := (matchAtomsList_singleton_solution_iff member valuation).mp
        matchedSatisfied |>.2
      have firstValue : applyClassSolution valuation (encodeModelAtom first) =
          applyClassSolution valuation (encodeModelAtom value) := by
        apply map_replicate_append_singleton_last
          (fun atom => applyClassSolution valuation (encodeModelAtom atom)) first value rest
        simpa [MettaAtomListsSatisfied, solutionTheory_encodeModelAtoms_eq_map,
          List.map_map, Function.comp_def] using listValues
      exact (canonical_eq_classValue_of_subrecord_below
        loopFree nonvariable smaller seedTarget keyBelow firstMem).trans firstValue
    next =>
      intro seed first second _agree contained
      apply canonicalValuation_satisfies_equalities loopFree nonvariable first second
      apply contained.2
      simp [Bindings.addEquality]
    next =>
      intro seed first second _pivot _other _matched _result _values _disagree
        _matchedProof mergeProof _mergeIH contained
      apply canonicalValuation_satisfies_equalities loopFree nonvariable first second
      apply ((FreshPrivateMerge.mergeRel_left_subrecord mergeProof).trans contained).2
      simp [Bindings.addEquality]
    next =>
      intro seed first second _pivot _other _third _rest _matched _result _values _disagree
        _matchedProof mergeProof _mergeIH contained
      apply canonicalValuation_satisfies_equalities loopFree nonvariable first second
      apply ((FreshPrivateMerge.mergeRel_left_subrecord mergeProof).trans contained).2
      simp [Bindings.addEquality]
    next =>
      intro seed _contained _below key value member
      simp at member
    next =>
      intro seed key value rest next result _added tail headIH tailIH contained allBelow
        observedKey observedValue member
      rcases List.mem_cons.mp member with same | member
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        have headBelow := allBelow observedKey observedValue (by simp)
        exact headIH
          ((FreshPrivateMerge.mergeAssignsRel_seed_subrecord tail).trans contained)
          headBelow.1 headBelow.2
      · exact tailIH contained (fun key value member => allBelow key value (by simp [member]))
          observedKey observedValue member
    next =>
      intro seed _contained first second member
      simp at member
    next =>
      intro seed first second rest next result _added tail headIH tailIH contained
        observedFirst observedSecond member
      rcases List.mem_cons.mp member with same | member
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        exact headIH ((FreshPrivateMerge.mergeEqsRel_seed_subrecord tail).trans contained)
      · exact tailIH contained observedFirst observedSecond member
    next =>
      intro seed rhs middle result _assignments equalities assignmentsIH equalitiesIH
        contained rhsBelow
      exact ⟨assignmentsIH
          ((FreshPrivateMerge.mergeEqsRel_seed_subrecord equalities).trans contained)
          rhsBelow.assignments,
        equalitiesIH contained⟩
  exact replay included below

/-- The existing actual matcher shape law in the independent model's vocabulary. -/
theorem matchAtoms_assignmentsNonVariable_model
    {left right : Atom} {out : Bindings} {fuel : Nat}
    (member : out ∈ matchAtoms left right fuel) : AssignmentsNonVariable out := by
  intro key value stored
  exact DeclMatchSpec.matchAtoms_assignmentValue_isVarB_false member stored

/-- List matching preserves the shape of each actual incoming seed. -/
theorem matchAtomsList_assignmentsNonVariable_model
    {left right : List Atom} {seeds : List Bindings} {out : Bindings} {fuel : Nat}
    (member : out ∈ matchAtomsList left right seeds fuel)
    (seedShape : ∀ seed ∈ seeds, AssignmentsNonVariable seed) :
    AssignmentsNonVariable out := by
  intro key value stored
  exact DeclMatchSpec.matchAtomsList_assignmentValue_isVarB_false member seedShape stored

/-- Actual recursive merge preserves the structural assignment invariant. -/
theorem mergeBindings_assignmentsNonVariable_model
    {left right out : Bindings} {fuel : Nat}
    (member : out ∈ mergeBindings left right fuel)
    (leftShape : AssignmentsNonVariable left)
    (rightShape : AssignmentsNonVariable right) : AssignmentsNonVariable out := by
  intro key value stored
  exact DeclMatchSpec.mergeBindings_assignmentValue_isVarB_false member leftShape rightShape stored

/-- A common finite-term input model survives actual reconciliation and rules
out every semantic dependency cycle in its returned binding record. -/
theorem mergeBindings_semanticLoopFree_of_common_model
    {left right out : Bindings} {fuel : Nat} {valuation : String → Metta.Atom}
    (member : out ∈ mergeBindings left right fuel)
    (leftShape : AssignmentsNonVariable left)
    (rightShape : AssignmentsNonVariable right)
    (leftModel : HEBindingSatisfied valuation left)
    (rightModel : HEBindingSatisfied valuation right) :
    Spec.Match.Merge.SemanticLoopFree out :=
  semanticLoopFree_of_satisfied_nonvariable
    ((mergeBindings_solution_iff member valuation).mpr ⟨leftModel, rightModel⟩)
    (mergeBindings_assignmentsNonVariable_model member leftShape rightShape)

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.ModelTheory Spec.Match.StructuralModel
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

open private assignmentsNodup_assign lookup_eq_some_of_mem_nodup map_replicate_eq_each
  from Mettapedia.Languages.MeTTa.HE.Spec.Match.StructuralModel

/-- The actual merge folds preserve coherence in a fixed eventual canonical
valuation. Raw relation occurrences, including repeated equality rows, remain
in the endpoint; this is not an embedding into the unordered source merge. -/
theorem declMerge_evalCoherentAt
    {target : Bindings} (loopFree : Spec.Match.Merge.SemanticLoopFree target)
    (nonvariable : AssignmentsNonVariable target) (source : DependencyNode target)
    (smaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target loopFree nonvariable node =
          applyClassSolution (canonicalValuation target loopFree nonvariable)
            (encodeModelAtom assignment.1.2))
    {left right out : Bindings} (merged : DeclMergeSpec.MergeRel left right out)
    (included : BindingSubrecord out target) (unique : AssignmentsNodup left)
    (seedCoherent : ClassAssignmentsEvalCoherentIn target left
      (canonicalValuation target loopFree nonvariable) source) :
    ClassAssignmentsEvalCoherentIn target out
        (canonicalValuation target loopFree nonvariable) source ∧
      AssignmentsNodup out := by
  let valuation := canonicalValuation target loopFree nonvariable
  apply DeclMergeSpec.MergeRel.rec
    (motive_1 := fun seed _ _ result _ =>
      BindingSubrecord result target → AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn target seed valuation source →
        ClassAssignmentsEvalCoherentIn target result valuation source ∧ AssignmentsNodup result)
    (motive_2 := fun seed _ _ result _ =>
      BindingSubrecord result target → AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn target seed valuation source →
        ClassAssignmentsEvalCoherentIn target result valuation source ∧ AssignmentsNodup result)
    (motive_3 := fun seed _ result _ =>
      BindingSubrecord result target → AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn target seed valuation source →
        ClassAssignmentsEvalCoherentIn target result valuation source ∧ AssignmentsNodup result)
    (motive_4 := fun seed _ result _ =>
      BindingSubrecord result target → AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn target seed valuation source →
        ClassAssignmentsEvalCoherentIn target result valuation source ∧ AssignmentsNodup result)
    (motive_5 := fun seed _ result _ =>
      BindingSubrecord result target → AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn target seed valuation source →
        ClassAssignmentsEvalCoherentIn target result valuation source ∧ AssignmentsNodup result)
    (t := merged)
  next =>
    intro seed key value empty resultIncluded seedUnique coherent
    exact ⟨evalCoherentIn_assign_of_classValues_nil coherent seedUnique empty resultIncluded,
      assignmentsNodup_assign seedUnique⟩
  next =>
    intro seed key value first rest values agree same resultIncluded seedUnique coherent
    exact ⟨coherent, seedUnique⟩
  next =>
    intro seed key value first rest matched result values agree different matchProof mergeProof
      ihMerge resultIncluded seedUnique coherent
    exact ihMerge resultIncluded seedUnique coherent
  next =>
    intro seed key value first rest matched result values disagree matchProof mergeProof
      ihMerge resultIncluded seedUnique coherent
    exact ihMerge resultIncluded seedUnique coherent
  next =>
    intro seed addedLeft addedRight agree resultIncluded seedUnique coherent
    exact ⟨evalCoherentIn_addEquality_of_valuesAgree coherent seedUnique
      ((valuesConsistent_iff_valuesAgree _).mp agree) resultIncluded,
      by simpa [AssignmentsNodup, Bindings.addEquality] using seedUnique⟩
  next =>
    intro seed addedLeft addedRight first second matched result values disagree
      matchProof mergeProof ihMerge resultIncluded seedUnique coherent
    let candidate := seed.addEquality addedLeft addedRight
    have candidateUnique : AssignmentsNodup candidate := by
      simpa [candidate, AssignmentsNodup, Bindings.addEquality] using seedUnique
    have candidateIncluded :=
      (FreshPrivateMerge.mergeRel_left_subrecord mergeProof).trans resultIncluded
    have valuePermutation : ([first, second] : List Atom).Perm
        (candidate.classValues addedLeft) := by
      rw [values]
    by_cases joined : source.1 ∈ target.eqClass addedLeft
    · have allBelow : ∀ value ∈ [first, second], AtomDependenciesBelow target source value := by
        intro value present
        exact addEquality_classValue_dependenciesBelow seedUnique valuePermutation
          candidateIncluded nonvariable source joined present
      have matchedBelow := declMatch_dependenciesBelow matchProof
        (allBelow first (by simp)) (allBelow second (by simp))
      have matchedSatisfied := declMerge_right_satisfied_of_dependenciesBelow loopFree nonvariable
        smaller mergeProof resultIncluded matchedBelow
      obtain ⟨fuel, ran⟩ := DeclMatchSpec.matchAtoms_complete matchProof
      have equation := (matchAtoms_solution_iff ran valuation).mp matchedSatisfied
      have pivot : ∀ value ∈ [first, second],
          applyClassSolution valuation (encodeModelAtom first) =
            applyClassSolution valuation (encodeModelAtom value) := by
        intro value present
        rcases List.mem_cons.mp present with same | present
        · subst value; rfl
        · have same := List.mem_singleton.mp present
          subst value
          exact equation
      exact ihMerge resultIncluded candidateUnique
        (evalCoherentIn_addEquality_of_pivot coherent seedUnique valuePermutation candidateIncluded pivot)
    · exact ihMerge resultIncluded candidateUnique
        (evalCoherentIn_addEquality_of_ambient_outside coherent candidateIncluded joined)
  next =>
    intro seed addedLeft addedRight first second third rest matched result values disagree
      matchProof mergeProof ihMerge resultIncluded seedUnique coherent
    let candidate := seed.addEquality addedLeft addedRight
    have candidateUnique : AssignmentsNodup candidate := by
      simpa [candidate, AssignmentsNodup, Bindings.addEquality] using seedUnique
    have candidateIncluded :=
      (FreshPrivateMerge.mergeRel_left_subrecord mergeProof).trans resultIncluded
    have valuePermutation : (first :: second :: third :: rest).Perm
        (candidate.classValues addedLeft) := by
      rw [values]
    by_cases joined : source.1 ∈ target.eqClass addedLeft
    · have allBelow : ∀ value ∈ first :: second :: third :: rest,
          AtomDependenciesBelow target source value := by
        intro value present
        exact addEquality_classValue_dependenciesBelow seedUnique valuePermutation
          candidateIncluded nonvariable source joined present
      have matchedBelow := declMatchList_dependenciesBelow matchProof
        (by
          intro value member
          obtain ⟨_, same⟩ := List.mem_replicate.mp member
          subst value
          exact allBelow first (by simp))
        (by intro value member; exact allBelow value (by simp [member]))
      have matchedSatisfied := declMerge_right_satisfied_of_dependenciesBelow loopFree nonvariable
        smaller mergeProof resultIncluded matchedBelow
      obtain ⟨fuel, ran⟩ := DeclMatchSpec.matchAtomsList_complete matchProof
      have items := (matchAtomsList_singleton_solution_iff ran valuation).mp matchedSatisfied |>.2
      have pivot : ∀ value ∈ first :: second :: third :: rest,
          applyClassSolution valuation (encodeModelAtom first) =
            applyClassSolution valuation (encodeModelAtom value) := by
        apply map_replicate_eq_each (fun atom => applyClassSolution valuation (encodeModelAtom atom))
          first (second :: third :: rest)
        simpa [MettaAtomListsSatisfied, solutionTheory_encodeModelAtoms_eq_map,
          List.map_map, Function.comp_def, Nat.add_assoc] using items
      exact ihMerge resultIncluded candidateUnique
        (evalCoherentIn_addEquality_of_pivot coherent seedUnique valuePermutation candidateIncluded pivot)
    · exact ihMerge resultIncluded candidateUnique
        (evalCoherentIn_addEquality_of_ambient_outside coherent candidateIncluded joined)
  next =>
    intro seed resultIncluded seedUnique coherent
    exact ⟨coherent, seedUnique⟩
  next =>
    intro seed key value rest next result inserted tail ihInsert ihTail
      resultIncluded seedUnique coherent
    have nextIncluded := (FreshPrivateMerge.mergeAssignsRel_seed_subrecord tail).trans resultIncluded
    obtain ⟨nextCoherent, nextUnique⟩ := ihInsert nextIncluded seedUnique coherent
    exact ihTail resultIncluded nextUnique nextCoherent
  next =>
    intro seed resultIncluded seedUnique coherent
    exact ⟨coherent, seedUnique⟩
  next =>
    intro seed addedLeft addedRight rest next result inserted tail ihInsert ihTail
      resultIncluded seedUnique coherent
    have nextIncluded := (FreshPrivateMerge.mergeEqsRel_seed_subrecord tail).trans resultIncluded
    obtain ⟨nextCoherent, nextUnique⟩ := ihInsert nextIncluded seedUnique coherent
    exact ihTail resultIncluded nextUnique nextCoherent
  next =>
    intro seed other middle result assignments equalities ihAssignments ihEqualities
      resultIncluded seedUnique coherent
    have middleIncluded :=
      (FreshPrivateMerge.mergeEqsRel_seed_subrecord equalities).trans resultIncluded
    obtain ⟨middleCoherent, middleUnique⟩ := ihAssignments middleIncluded seedUnique coherent
    exact ihEqualities resultIncluded middleUnique middleCoherent
  · exact included
  · exact unique
  · exact seedCoherent

/-- An equality-free unique seed has pairwise-equal values in each of its
own classes under every valuation, without assuming the valuation models it. -/
theorem evalCoherentIn_of_no_equalities {target seed : Bindings}
    (valuation : String → Metta.Atom) (source : DependencyNode target)
    (included : BindingSubrecord seed target)
    (unique : AssignmentsNodup seed) (noEqualities : seed.equalities = []) :
    ClassAssignmentsEvalCoherentIn target seed valuation source := by
  refine ⟨included, ?_⟩
  intro leftKey rightKey leftValue rightValue leftPresent rightPresent sameClass inAmbient
  have sameKey : rightKey = leftKey := by
    have ordered := EqualityClosure.mem_eqClassOrdered_iff.mpr sameClass
    simpa only [Bindings.eqClassOrdered_no_equalities noEqualities, List.mem_singleton] using ordered
  subst rightKey
  have sameValue : leftValue = rightValue := Option.some.inj
    ((lookup_eq_some_of_mem_nodup unique leftPresent).symm.trans
      (lookup_eq_some_of_mem_nodup unique rightPresent))
  exact congrArg (fun value => applyClassSolution valuation (encodeModelAtom value)) sameValue

/-- Starting from a unique equality-free seed, an actual successful merge
earns canonical coherence by replaying every conflict. Caller coherence is
not an assumed field; final acyclicity and assignment shape are explicit. -/
theorem declMerge_canonicalClassCoherent_of_no_equalities
    {left right out : Bindings} (merged : DeclMergeSpec.MergeRel left right out)
    (unique : AssignmentsNodup left) (noEqualities : left.equalities = [])
    (loopFree : Spec.Match.Merge.SemanticLoopFree out)
    (nonvariable : AssignmentsNonVariable out) :
    CanonicalClassCoherent out loopFree nonvariable := by
  apply canonicalClassCoherent_of_evalCoherentAt loopFree nonvariable
  intro source smaller
  exact (declMerge_evalCoherentAt loopFree nonvariable source smaller merged
    (BindingSubrecord.refl _) unique
    (evalCoherentIn_of_no_equalities _ source (FreshPrivateMerge.mergeRel_left_subrecord merged)
      unique noEqualities)).1

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.ModelTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-- Actual merge output has canonical coherence when its unique equality-free
seed and its right record share a model. The conclusion is earned from the
actual recursive reconciliation, not supplied as output admission. -/
theorem mergeBindings_canonicalClassCoherent_of_common_model
    {left right out : Bindings} {fuel : Nat} {valuation : String → Metta.Atom}
    (member : out ∈ mergeBindings left right fuel)
    (unique : AssignmentsNodup left) (noEqualities : left.equalities = [])
    (leftShape : AssignmentsNonVariable left)
    (rightShape : AssignmentsNonVariable right)
    (leftModel : HEBindingSatisfied valuation left)
    (rightModel : HEBindingSatisfied valuation right) :
    CanonicalClassCoherent out
      (mergeBindings_semanticLoopFree_of_common_model member leftShape rightShape
        leftModel rightModel)
      (mergeBindings_assignmentsNonVariable_model member leftShape rightShape) :=
  declMerge_canonicalClassCoherent_of_no_equalities
    (DeclMergeSpec.mergeBindings_sound member) unique noEqualities
    (mergeBindings_semanticLoopFree_of_common_model member leftShape rightShape
      leftModel rightModel)
    (mergeBindings_assignmentsNonVariable_model member leftShape rightShape)

/-- The executable HE binding model's own structurally covered readout is a
most-general solution after actual successful reconciliation from a unique
equality-free seed. A common input model suffices; neither caller coherence
nor output readout correspondence is assumed. -/
theorem mergeBindings_applyFull_mostGeneral_of_common_model
    {left right out : Bindings} {fuel : Nat} {valuation : String → Metta.Atom}
    (member : out ∈ mergeBindings left right fuel)
    (unique : AssignmentsNodup left) (noEqualities : left.equalities = [])
    (leftShape : AssignmentsNonVariable left)
    (rightShape : AssignmentsNonVariable right)
    (leftModel : HEBindingSatisfied valuation left)
    (rightModel : HEBindingSatisfied valuation right) :
    MostGeneralSolution out (fun name =>
      encodeModelAtom (out.applyFull (.var name) (out.resolutionFuel (.var name)))) :=
  applyFull_mostGeneralSolution
    (mergeBindings_semanticLoopFree_of_common_model member leftShape rightShape
      leftModel rightModel)
    (mergeBindings_assignmentsNonVariable_model member leftShape rightShape)
    (mergeBindings_canonicalClassCoherent_of_common_model member unique noEqualities
      leftShape rightShape leftModel rightModel)

end ActualMergePrincipality

namespace Controls

/-! Actual HE principal-readout controls. -/

section PrincipalReadoutControls

open Spec.Match.ModelTheory
open Spec.Type.RuntimeRefinement

/-- Same alias theory, different stable representatives and edge multiplicity. -/
def principalAliasLeft : Bindings := ⟨[], [("x", "y"), ("y", "z")]⟩
def principalAliasRight : Bindings := ⟨[], [("z", "y"), ("y", "x"), ("z", "x")]⟩

def principalAliasObservations : List Atom :=
  [.var "x", .var "y", .var "outside", .var "z", .var "x"]

private theorem empty_assignments_nonvariable {bindings : Bindings}
    (empty : bindings.assignments = []) : AssignmentsNonVariable bindings := by
  intro key value member
  simp [empty] at member

private theorem empty_assignments_coherent {bindings : Bindings}
    (empty : bindings.assignments = [])
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings) :
    CanonicalClassCoherent bindings loopFree nonvariable := by
  intro source assignment
  have member := assignment.2.1
  simp [empty] at member

theorem principalAlias_same_solutions (valuation : String → Atom) :
    TypeBindingSatisfied valuation principalAliasLeft ↔
      TypeBindingSatisfied valuation principalAliasRight := by
  have left : TypeBindingSatisfied valuation principalAliasLeft ↔
      valuation "x" = valuation "y" ∧ valuation "y" = valuation "z" := by
    simp [TypeBindingSatisfied, principalAliasLeft]
    aesop
  have right : TypeBindingSatisfied valuation principalAliasRight ↔
      valuation "z" = valuation "y" ∧ valuation "y" = valuation "x" ∧
        valuation "z" = valuation "x" := by
    simp [TypeBindingSatisfied, principalAliasRight]
    aesop
  rw [left, right]
  constructor
  · rintro ⟨xy, yz⟩
    exact ⟨yz.symm, xy.symm, yz.symm.trans xy.symm⟩
  · rintro ⟨zy, yx, _⟩
    exact ⟨yx.symm, zy.symm⟩

theorem principalAlias_joint_permutation :
    ∃ permutation : Equiv.Perm String,
      principalAliasRight.applyFull (.expression principalAliasObservations)
          (principalAliasRight.resolutionFuel (.expression principalAliasObservations)) =
        renameTypeVars permutation
          (principalAliasLeft.applyFull (.expression principalAliasObservations)
            (principalAliasLeft.resolutionFuel (.expression principalAliasObservations))) := by
  have leftLoop : Spec.Match.Merge.SemanticLoopFree principalAliasLeft :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp
      (Bindings.hasLoop_false_of_assignments_nil _ rfl)
  have rightLoop : Spec.Match.Merge.SemanticLoopFree principalAliasRight :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp
      (Bindings.hasLoop_false_of_assignments_nil _ rfl)
  exact applyFull_joint_permutation_of_solution_equiv leftLoop rightLoop
    (empty_assignments_nonvariable rfl) (empty_assignments_nonvariable rfl)
    (empty_assignments_coherent rfl leftLoop _)
    (empty_assignments_coherent rfl rightLoop _)
    principalAlias_same_solutions principalAliasObservations _ _
    (Bindings.applyFullCovered_resolutionFuel _ _)
    (Bindings.applyFullCovered_resolutionFuel _ _)

/-- The semantic theorem does not identify physical checkpoint rows. -/
theorem principalAlias_not_record_permutation :
    ¬Spec.Bindings.ScopeObservation.BindingRecordPerm principalAliasLeft principalAliasRight := by
  intro related
  have lengths := related.equalities.length_eq
  simp [principalAliasLeft, principalAliasRight] at lengths

#guard principalAliasLeft.applyFull (.expression principalAliasObservations)
    (principalAliasLeft.resolutionFuel (.expression principalAliasObservations)) ==
  .expression [.var "x", .var "x", .var "outside", .var "x", .var "x"]
#guard principalAliasRight.applyFull (.expression principalAliasObservations)
    (principalAliasRight.resolutionFuel (.expression principalAliasObservations)) ==
  .expression [.var "z", .var "z", .var "outside", .var "z", .var "z"]

/-- A compound value shares one unbound alias class in both child positions. -/
def principalCompound : Bindings :=
  ⟨[("a", .expression [.symbol "F", .var "z", .var "z"])], [("z", "w")]⟩

private theorem principalCompound_nonvariable : AssignmentsNonVariable principalCompound := by
  intro key value member
  simp only [principalCompound, List.mem_singleton, Prod.mk.injEq] at member
  rw [member.2]
  rfl

private theorem principalCompound_loopFree : Spec.Match.Merge.SemanticLoopFree principalCompound :=
  (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide)

private theorem principalCompound_coherent :
    CanonicalClassCoherent principalCompound principalCompound_loopFree
      principalCompound_nonvariable := by
  apply canonicalClassCoherent_of_subsingleton_classAssignments
  intro source
  constructor
  intro left right
  apply Subtype.ext
  have leftMember := left.2.1
  have rightMember := right.2.1
  simp only [principalCompound, List.mem_singleton] at leftMember rightMember
  exact leftMember.trans rightMember.symm

theorem principalCompound_actual_principal :
    MostGeneralSolution principalCompound
      (fun name => Spec.Match.SolutionTheory.encodeModelAtom
        (principalCompound.applyFull (.var name)
          (principalCompound.resolutionFuel (.var name)))) :=
  applyFull_mostGeneralSolution principalCompound_loopFree
    principalCompound_nonvariable principalCompound_coherent

#guard principalCompound.applyFull (.expression [.var "a", .var "z", .var "w"])
    (principalCompound.resolutionFuel (.expression [.var "a", .var "z", .var "w"])) ==
  .expression [.expression [.symbol "F", .var "z", .var "z"], .var "z", .var "z"]
#guard principalCompound.applyFullCovered (.var "a") 0 == false
#guard principalCompound.applyFull (.var "a") 0 == .var "a"
#guard principalCompound.applyFull (.var "a") 0 !=
  principalCompound.applyFull (.var "a") (principalCompound.resolutionFuel (.var "a"))

/-- Acyclic but conflicting raw records are not promoted to principal models. -/
theorem incoherent_actual_readout_not_model :
    ¬Spec.Match.SolutionTheory.HEBindingSatisfied
      (fun name => Spec.Match.SolutionTheory.encodeModelAtom
        (incompatibleAcyclicProbe.applyFull (.var name)
          (incompatibleAcyclicProbe.resolutionFuel (.var name))))
      incompatibleAcyclicProbe := by
  intro model
  exact incompatibleAcyclicProbe_has_no_model ⟨_, model⟩

#guard incompatibleAcyclicProbe.hasLoop == false
#guard incompatibleAcyclicProbe.applyFull (.var "x")
    (incompatibleAcyclicProbe.resolutionFuel (.var "x")) == .symbol "a"
#guard incompatibleAcyclicProbe.applyFull (.var "y")
    (incompatibleAcyclicProbe.resolutionFuel (.var "y")) == .symbol "a"

/-- Pointwise renaming would incorrectly forget the equality of two uses. -/
theorem repeated_observation_not_independently_renamable :
    ¬∃ permutation : Equiv.Perm String,
      (.expression [.var "x", .var "y"] : Atom) =
        renameTypeVars permutation (.expression [.var "x", .var "x"]) := by
  rintro ⟨permutation, equal⟩
  simp only [renameTypeVars, List.map_cons, List.map_nil,
    Atom.expression.injEq, List.cons.injEq, Atom.var.injEq] at equal
  have impossible : ("x" : String) = "y" := equal.1.trans equal.2.1.symm
  contradiction

/-- Two private extensions differ as whole theories but preserve the same
joint public observation, including repeated uses of one public hole. -/
def principalPrivateLeft : Bindings := ⟨[], [("privateLeft", "public")]⟩
def principalPrivateRight : Bindings := ⟨[], [("privateRight", "public")]⟩

theorem principalPrivate_scoped_equiv :
    Spec.Bindings.ScopeObservation.BindingTheoryEquivAt ["public", "outside"]
      principalPrivateLeft principalPrivateRight := by
  constructor
  · intro model _
    let extended : String → Atom := fun name =>
      if name = "privateRight" then model "public" else model name
    refine ⟨extended, ?_, ?_⟩
    · constructor
      · intro name value member
        simp [principalPrivateRight] at member
      · intro left right member
        have eqs : left = "privateRight" ∧ right = "public" := by
          simpa [principalPrivateRight] using member
        rcases eqs with ⟨rfl, rfl⟩
        simp [extended]
    · intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [extended]
  · intro model _
    let extended : String → Atom := fun name =>
      if name = "privateLeft" then model "public" else model name
    refine ⟨extended, ?_, ?_⟩
    · constructor
      · intro name value member
        simp [principalPrivateLeft] at member
      · intro left right member
        have eqs : left = "privateLeft" ∧ right = "public" := by
          simpa [principalPrivateLeft] using member
        rcases eqs with ⟨rfl, rfl⟩
        simp [extended]
    · intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [extended]

theorem principalPrivate_joint_permutation :
    ∃ permutation : Equiv.Perm String,
      principalPrivateRight.applyFull
          (.expression [.var "public", .var "outside", .var "public"]) 8 =
        renameTypeVars permutation
          (principalPrivateLeft.applyFull
            (.expression [.var "public", .var "outside", .var "public"]) 8) := by
  have leftLoop : Spec.Match.Merge.SemanticLoopFree principalPrivateLeft :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp
      (Bindings.hasLoop_false_of_assignments_nil _ rfl)
  have rightLoop : Spec.Match.Merge.SemanticLoopFree principalPrivateRight :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp
      (Bindings.hasLoop_false_of_assignments_nil _ rfl)
  apply applyFull_joint_permutation_of_scoped_solution_equiv leftLoop rightLoop
    (empty_assignments_nonvariable rfl) (empty_assignments_nonvariable rfl)
    (empty_assignments_coherent rfl leftLoop _)
    (empty_assignments_coherent rfl rightLoop _) principalPrivate_scoped_equiv
  · intro name member
    simp [Spec.Type.Presentation.TypeSubst.typeVars,
      Spec.Type.Presentation.TypeSubst.typeVarsList] at member ⊢
    aesop
  · decide
  · decide

theorem principalPrivate_not_same_full_theory :
    ¬∀ valuation : String → Atom,
      TypeBindingSatisfied valuation principalPrivateLeft ↔
        TypeBindingSatisfied valuation principalPrivateRight := by
  intro same
  let model : String → Atom := fun name =>
    if name = "privateRight" then .symbol "B" else .symbol "A"
  have left : TypeBindingSatisfied model principalPrivateLeft := by
    constructor
    · intro name value member
      simp [principalPrivateLeft] at member
    · intro left right member
      have eqs : left = "privateLeft" ∧ right = "public" := by
        simpa [principalPrivateLeft] using member
      rcases eqs with ⟨rfl, rfl⟩
      simp [model]
  have bad := ((same model).mp left).2 "privateRight" "public" (by simp [principalPrivateRight])
  simp [model] at bad

#guard principalPrivateLeft.applyFull
    (.expression [.var "public", .var "outside", .var "public"]) 8 ==
  .expression [.var "privateLeft", .var "outside", .var "privateLeft"]
#guard principalPrivateRight.applyFull
    (.expression [.var "public", .var "outside", .var "public"]) 8 ==
  .expression [.var "privateRight", .var "outside", .var "privateRight"]

end PrincipalReadoutControls

/-! Actual merge-to-principal-readout controls. -/

section ActualMergeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.ModelTheory

def closedPrivateSeed : Bindings := ⟨[("private",.symbol "saved")],[]⟩
def duplicateAliasCaller : Bindings := ⟨[],[("z","w"),("z","w")]⟩
def duplicateAliasOut : Bindings :=
  ⟨[("private",.symbol "saved")],[("z","w"),("z","w")]⟩

#guard mergeBindings closedPrivateSeed duplicateAliasCaller 12 == [duplicateAliasOut]
#guard duplicateAliasOut.equalities.length == 2
#guard duplicateAliasOut.hasLoop == false

theorem duplicateAlias_reached :
    duplicateAliasOut ∈ mergeBindings closedPrivateSeed duplicateAliasCaller 12 := by decide

theorem duplicateAlias_nonvariable : AssignmentsNonVariable duplicateAliasOut := by
  intro key value stored
  have same : key = "private" ∧ value = .symbol "saved" := by
    simpa [duplicateAliasOut] using stored
  rw [same.2]
  rfl

theorem duplicateAlias_loopFree : Spec.Match.Merge.SemanticLoopFree duplicateAliasOut :=
  (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide)

def reconciledCompoundOut : Bindings :=
  ⟨[("x",.expression [.symbol "f",.var "y"]),("y",.symbol "a")],[]⟩

#guard mergeBindings Bindings.empty satisfiableUnreconciledProbe 16 == [reconciledCompoundOut]
#guard reconciledCompoundOut.hasLoop == false
#guard reconciledCompoundOut.applyFull (.expression [.var "x",.var "y",.var "x"])
    (reconciledCompoundOut.resolutionFuel
      (.expression [.var "x",.var "y",.var "x"])) ==
  .expression [.expression [.symbol "f",.symbol "a"], .symbol "a",
    .expression [.symbol "f",.symbol "a"]]

theorem reconciledCompound_reached :
    reconciledCompoundOut ∈ mergeBindings Bindings.empty satisfiableUnreconciledProbe 16 := by
  decide

theorem reconciledCompound_nonvariable : AssignmentsNonVariable reconciledCompoundOut := by
  intro key value stored
  simp [reconciledCompoundOut] at stored
  rcases stored with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl

theorem reconciledCompound_loopFree : Spec.Match.Merge.SemanticLoopFree reconciledCompoundOut :=
  (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide)

#guard mergeBindings cyclicMergeLeft cyclicMergeRight 4 == [cyclicMergeOut]
#guard cyclicMergeOut.hasLoop == true

/-- Successful raw merging alone cannot supply final semantic admission. -/
theorem cyclicMerge_reached :
    cyclicMergeOut ∈ mergeBindings cyclicMergeLeft cyclicMergeRight 4 := by decide

theorem cyclicMerge_not_loopFree : ¬ Spec.Match.Merge.SemanticLoopFree cyclicMergeOut := by
  intro accepted
  have noLoop := (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mpr accepted
  have actual : cyclicMergeOut.hasLoop = true := by decide
  simp [actual] at noLoop

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.ModelTheory
open Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

theorem duplicateAlias_coherent :
    CanonicalClassCoherent duplicateAliasOut duplicateAlias_loopFree duplicateAlias_nonvariable :=
  declMerge_canonicalClassCoherent_of_no_equalities
    (DeclMergeSpec.mergeBindings_sound duplicateAlias_reached)
    (by simp [AssignmentsNodup,closedPrivateSeed]) rfl duplicateAlias_loopFree duplicateAlias_nonvariable

/-- The actual replay repairs a satisfiable but canonically incoherent input.
Its missing `y = a` constraint is now present, and the actual resolver is principal. -/
theorem reconciledCompound_principal :
    MostGeneralSolution reconciledCompoundOut (fun name =>
      encodeModelAtom (reconciledCompoundOut.applyFull (.var name)
        (reconciledCompoundOut.resolutionFuel (.var name)))) := by
  obtain ⟨valuation, model⟩ := satisfiableUnreconciledProbe_has_model
  exact mergeBindings_applyFull_mostGeneral_of_common_model
    reconciledCompound_reached (by simp [AssignmentsNodup,Bindings.empty]) rfl
    (by intro key value stored; cases stored)
    satisfiableUnreconciledProbe_nonvariable (hesat_empty valuation) model

def reversedAliasCaller : Bindings := ⟨[],[("w","z")]⟩
def reversedAliasOut : Bindings := ⟨[("private",.symbol "saved")],[("w","z")]⟩

theorem reversedAlias_reached :
    reversedAliasOut ∈ mergeBindings closedPrivateSeed reversedAliasCaller 12 := by decide

theorem reversedAlias_nonvariable : AssignmentsNonVariable reversedAliasOut := by
  intro key value stored
  have same : key = "private" ∧ value = .symbol "saved" := by
    simpa [reversedAliasOut] using stored
  rw [same.2]
  rfl

theorem reversedAlias_loopFree : Spec.Match.Merge.SemanticLoopFree reversedAliasOut :=
  (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide)

theorem reversedAlias_coherent :
    CanonicalClassCoherent reversedAliasOut reversedAlias_loopFree reversedAlias_nonvariable :=
  declMerge_canonicalClassCoherent_of_no_equalities
    (DeclMergeSpec.mergeBindings_sound reversedAlias_reached)
    (by simp [AssignmentsNodup,closedPrivateSeed]) rfl reversedAlias_loopFree reversedAlias_nonvariable

theorem replayedAliases_same_solutions (valuation : String → Atom) :
    TypeBindingSatisfied valuation duplicateAliasOut ↔
      TypeBindingSatisfied valuation reversedAliasOut := by
  have forward : TypeBindingSatisfied valuation duplicateAliasOut ↔
      valuation "private" = .symbol "saved" ∧ valuation "z" = valuation "w" := by
    simp [TypeBindingSatisfied, duplicateAliasOut, applyTypeValuation]
  have backward : TypeBindingSatisfied valuation reversedAliasOut ↔
      valuation "private" = .symbol "saved" ∧ valuation "w" = valuation "z" := by
    simp [TypeBindingSatisfied, reversedAliasOut, applyTypeValuation]
  rw [forward, backward]
  exact and_congr Iff.rfl eq_comm

def replayedAliasObservations : List Atom :=
  [.var "z", .var "private", .var "w", .var "outside", .var "z"]

/-- Both records were actually reached, and one joint residual renaming
relates all live observations despite different edge multiplicity/orientation. -/
theorem replayedAliases_joint_permutation :
    ∃ permutation : Equiv.Perm String,
      reversedAliasOut.applyFull (.expression replayedAliasObservations)
          (reversedAliasOut.resolutionFuel (.expression replayedAliasObservations)) =
        renameTypeVars permutation
          (duplicateAliasOut.applyFull (.expression replayedAliasObservations)
            (duplicateAliasOut.resolutionFuel (.expression replayedAliasObservations))) :=
  applyFull_joint_permutation_of_solution_equiv duplicateAlias_loopFree reversedAlias_loopFree
    duplicateAlias_nonvariable reversedAlias_nonvariable duplicateAlias_coherent reversedAlias_coherent
    replayedAliases_same_solutions replayedAliasObservations _ _
    (Bindings.applyFullCovered_resolutionFuel _ _) (Bindings.applyFullCovered_resolutionFuel _ _)

theorem replayedAliases_not_record_permutation :
    ¬Spec.Bindings.ScopeObservation.BindingRecordPerm duplicateAliasOut reversedAliasOut := by
  intro records
  have lengths := records.equalities.length_eq
  simp [duplicateAliasOut,reversedAliasOut] at lengths

#guard duplicateAliasOut.applyFull (.expression replayedAliasObservations)
    (duplicateAliasOut.resolutionFuel (.expression replayedAliasObservations)) ==
  .expression [.var "z",.symbol "saved",.var "z",.var "outside",.var "z"]
#guard reversedAliasOut.applyFull (.expression replayedAliasObservations)
    (reversedAliasOut.resolutionFuel (.expression replayedAliasObservations)) ==
  .expression [.var "w",.symbol "saved",.var "w",.var "outside",.var "w"]

theorem reconciledCompound_same_solutions (valuation : String → Atom) :
    TypeBindingSatisfied valuation reconciledCompoundOut ↔
      TypeBindingSatisfied valuation satisfiableUnreconciledProbe := by
  have nativeEquations : TypeBindingSatisfied valuation reconciledCompoundOut ↔
      valuation "x" = .expression [.symbol "f", valuation "y"] ∧
        valuation "y" = .symbol "a" := by
    constructor
    · intro satisfied
      constructor
      · simpa [applyTypeValuation] using
          satisfied.1 "x" (.expression [.symbol "f", .var "y"])
            (by simp [reconciledCompoundOut])
      · simpa [applyTypeValuation] using
          satisfied.1 "y" (.symbol "a") (by simp [reconciledCompoundOut])
    · rintro ⟨x, y⟩
      refine ⟨?_, ?_⟩
      · intro key value member
        simp [reconciledCompoundOut] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [applyTypeValuation] using x
        · simpa [applyTypeValuation] using y
      · intro left right member
        cases member
  have sourceEquations : TypeBindingSatisfied valuation satisfiableUnreconciledProbe ↔
      valuation "x" = .expression [.symbol "f", valuation "y"] ∧
        valuation "x" = .expression [.symbol "f", .symbol "a"] := by
    constructor
    · intro satisfied
      constructor
      · simpa [applyTypeValuation] using
          satisfied.1 "x" (.expression [.symbol "f", .var "y"])
            (by simp [satisfiableUnreconciledProbe])
      · simpa [applyTypeValuation] using
          satisfied.1 "x" (.expression [.symbol "f", .symbol "a"])
            (by simp [satisfiableUnreconciledProbe])
    · rintro ⟨x, xa⟩
      refine ⟨?_, ?_⟩
      · intro key value member
        simp [satisfiableUnreconciledProbe] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [applyTypeValuation] using x
        · simpa [applyTypeValuation] using xa
      · intro left right member
        cases member
  rw [nativeEquations, sourceEquations]
  constructor
  · rintro ⟨x, y⟩
    exact ⟨x, by simpa [y] using x⟩
  · rintro ⟨x, xa⟩
    refine ⟨x, ?_⟩
    have same := x.symm.trans xa
    simpa using same

theorem reconciledCompound_coherent :
    CanonicalClassCoherent reconciledCompoundOut
      reconciledCompound_loopFree reconciledCompound_nonvariable :=
  declMerge_canonicalClassCoherent_of_no_equalities
    (DeclMergeSpec.mergeBindings_sound reconciledCompound_reached)
    (by simp [AssignmentsNodup, Bindings.empty]) rfl
    reconciledCompound_loopFree reconciledCompound_nonvariable

/-- The source record is satisfiable but not a coherent resolver input;
its equation presentation still agrees jointly with actual reconciled readout. -/
theorem unreconciledSource_joint_materialization :
    ∃ normalized,
      BindingMaterializationRel satisfiableUnreconciledProbe
          (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"])
          normalized ∧
        ∃ permutation : Equiv.Perm String,
          normalized = renameTypeVars permutation
            (reconciledCompoundOut.applyFull
              (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"])
              (reconciledCompoundOut.resolutionFuel
                (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"]))) := by
  apply exists_joint_bindingMaterialization_of_scoped_solution_equiv
    reconciledCompound_loopFree reconciledCompound_nonvariable reconciledCompound_coherent
    (scope := ["x", "y", "outside"])
  · exact Spec.Bindings.ScopeObservation.BindingTheoryEquivAt.of_solution_iff
      reconciledCompound_same_solutions _
  · intro name member
    simpa [TypeSubst.typeVars, TypeSubst.typeVarsList, or_assoc, or_left_comm, or_comm] using member
  · exact Bindings.applyFullCovered_resolutionFuel _ _

#guard satisfiableUnreconciledProbe.applyFull
    (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"])
    (satisfiableUnreconciledProbe.resolutionFuel
      (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"])) ==
  .expression [.expression [.symbol "f", .var "y"], .var "outside", .var "y",
    .expression [.symbol "f", .var "y"], .var "outside"]

#guard reconciledCompoundOut.applyFull
    (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"])
    (reconciledCompoundOut.resolutionFuel
      (.expression [.var "x", .var "outside", .var "y", .var "x", .var "outside"])) ==
  .expression [.expression [.symbol "f", .symbol "a"], .var "outside", .symbol "a",
    .expression [.symbol "f", .symbol "a"], .var "outside"]

end ActualMergeControls

end Controls

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.ModelTheory

/-- The actual covered native tuple has a finite normal independent
presentation of the same complete source theory. The construction carries
one model-fixed representative change of the source's genuine ordered fold. -/
theorem exists_exact_native_presentation
    {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (sameSolutions : ∀ valuation,TypeBindingSatisfied valuation native ↔
      TypeBindingSatisfied valuation independent)
    (observations : List Atom) (depth : Nat)
    (covered : native.applyFullCovered (.expression observations) depth=true) :
    ∃ (presentation : TypeSubst) (p : Equiv.Perm String),
      EquationListPresentationRel (bindingAtomEquations independent) [] presentation ∧
      (presentation.renameVars p).Normal ∧
      (∀ valuation,TypeSubstSatisfied valuation (presentation.renameVars p) ↔
        TypeBindingSatisfied valuation independent) ∧
      (presentation.renameVars p).apply (.expression observations)=
        native.applyFull (.expression observations) depth ∧
      (∀ valuation,TypeBindingSatisfied valuation independent →
        ∀ name,valuation (p name)=valuation name) ∧
      (∀ name,name∉specBindingVars independent → p name=name) := by
  have model : ∃ valuation,TypeBindingSatisfied valuation independent :=
    ⟨_,(sameSolutions _).mp (applyFull_typeBindingSatisfied loopFree nonvariable coherent)⟩
  obtain ⟨presentation,fold⟩:=exists_binding_presentation model
  have materialized : BindingMaterializationRel independent (.expression observations)
      (presentation.apply (.expression observations)):=⟨presentation,fold,rfl⟩
  obtain ⟨p,readout,fixed,_outside,_theory⟩:=
    applyFull_joint_model_fixed_permutation_of_bindingMaterialization loopFree nonvariable coherent
      sameSolutions observations depth covered materialized
  have inverseFixed : ∀ valuation,TypeBindingSatisfied valuation independent →
      ∀ name,valuation (p.symm name)=valuation name := by
    intro valuation model name
    simpa only [p.apply_symm_apply] using (fixed valuation model (p.symm name)).symm
  have representative:=fold.model_fixed_representative p.symm inverseFixed
  refine ⟨presentation,p.symm,fold,representative.1,representative.2.1,?_,inverseFixed,
    model_fixed_fixes_outside p.symm model inverseFixed⟩
  rw [representative.2.2,readout,renameTypeVars_perm_inverse]

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.ModelTheory

/-- A name outside the complete binding record is unchanged by the actual
resolver at every depth, independently of the record's other classes. -/
theorem applyFull_var_of_outside {bindings : Bindings} {name : String}
    (outside : name ∉ specBindingVars bindings) (depth : Nat) :
    bindings.applyFull (.var name) depth = .var name := by
  have frame := FreshPrivateMerge.readFrame_of_fresh
    (keys := fun key => key=name) (bindings := bindings)
    (by intro key same; subst key; exact outside)
  have singleton := frame.orderedClass rfl
  have missing := frame.reads name rfl
  cases depth with
  | zero => rfl
  | succ depth => simp [Bindings.applyFull,Bindings.resolveFull,singleton,missing]

/-- One finite representative is selected from the complete binding record.
The same presentation then agrees with every covered native readout, rather
than being chosen separately for the operand being observed. -/
theorem exists_uniform_exact_native_presentation
    {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (sameSolutions : ∀ valuation,TypeBindingSatisfied valuation native ↔
      TypeBindingSatisfied valuation independent) :
    ∃ (presentation : TypeSubst) (p : Equiv.Perm String),
      EquationListPresentationRel (bindingAtomEquations independent) [] presentation ∧
      (presentation.renameVars p).Normal ∧
      (∀ valuation,TypeSubstSatisfied valuation (presentation.renameVars p) ↔
        TypeBindingSatisfied valuation independent) ∧
      (∀ atom depth,native.applyFullCovered atom depth=true →
        (presentation.renameVars p).apply atom=native.applyFull atom depth) ∧
      (∀ valuation,TypeBindingSatisfied valuation independent →
        ∀ name,valuation (p name)=valuation name) ∧
      (∀ name,name∉specBindingVars independent → p name=name) := by
  let scope := specBindingVars native ++ specBindingVars independent
  let tuple : Atom := .expression (scope.map Atom.var)
  let depth := native.resolutionFuel tuple
  obtain ⟨presentation,p,fold,normal,theory,observed,fixed,outside⟩ :=
    exists_exact_native_presentation loopFree nonvariable coherent sameSolutions
      (scope.map Atom.var) depth (native.applyFullCovered_resolutionFuel tuple)
  let selected := presentation.renameVars p
  let nativeValuation := fun name =>
    native.applyFull (.var name) (native.resolutionFuel (.var name))
  have tupleRead := applyFull_eq_readoutValuation_of_covered loopFree nonvariable coherent
    tuple depth (native.applyFullCovered_resolutionFuel tuple)
  have mapped : scope.map (fun name => selected.apply (.var name)) =
      scope.map nativeValuation := by
    have equal := observed.trans tupleRead
    simpa only [tuple,TypeSubst.apply,applyTypeValuation,List.map_map,
      Atom.expression.injEq,Function.comp_def,selected,nativeValuation] using equal
  have each : ∀ name ∈ scope,selected.apply (.var name)=nativeValuation name := by
    intro name member
    have mapEqual : ∀ names : List String,
        names.map (fun name => selected.apply (.var name))=names.map nativeValuation →
        ∀ name∈names,selected.apply (.var name)=nativeValuation name := by
      intro names
      induction names with
      | nil => simp
      | cons first rest ih =>
        intro equal name member
        have parts := List.cons.inj equal
        rcases List.mem_cons.mp member with rfl | restMember
        · exact parts.1
        · exact ih parts.2 name restMember
    exact mapEqual scope mapped name member
  have allVariables : ∀ name,selected.apply (.var name)=nativeValuation name := by
    intro name
    by_cases present : name∈scope
    · exact each name present
    · have noNative : name∉specBindingVars native := fun member=>
        present (List.mem_append_left _ member)
      have noIndependent : name∉specBindingVars independent := fun member=>
        present (List.mem_append_right _ member)
      have historical : presentation.apply (.var name)=.var name :=
        BindingMaterializationRel.outside_result ⟨presentation,fold,rfl⟩
          (by simpa [TypeSubst.typeVars] using noIndependent)
      have selectedRead := (fold.model_fixed_representative p fixed).2.2 (.var name)
      simpa only [selected,historical,renameTypeVars,outside name noIndependent,
        nativeValuation,applyFull_var_of_outside noNative] using selectedRead
  refine ⟨presentation,p,fold,normal,theory,?_,fixed,outside⟩
  intro atom atDepth covered
  rw [applyFull_eq_readoutValuation_of_covered loopFree nonvariable coherent atom atDepth covered]
  rw [← applyTypeValuation_presented_eq_apply selected atom]
  congr 1
  exact funext allVariables

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.ModelTheory

/-- The executable representation of one complete native binding record.
Each distinct supported name is resolved once at its structural bound. -/
def nativeReadoutPresentation (bindings : Bindings) : TypeSubst :=
  TypeSubst.finiteReadout (specBindingVars bindings).eraseDups
    (fun name => bindings.applyFull (.var name) (bindings.resolutionFuel (.var name)))

theorem nativeReadoutPresentation_apply_var (bindings : Bindings) (name : String) :
    (nativeReadoutPresentation bindings).apply (.var name)=
      bindings.applyFull (.var name) (bindings.resolutionFuel (.var name)) := by
  rw [nativeReadoutPresentation,TypeSubst.finiteReadout_apply_var]
  by_cases present : name∈specBindingVars bindings
  · simp [present]
  · simp [present,applyFull_var_of_outside present]

/-- The computed table is shared by every materialized operand. -/
theorem nativeReadoutPresentation_apply {bindings : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (nonvariable : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree nonvariable)
    (atom : Atom) (depth : Nat) (covered : bindings.applyFullCovered atom depth=true) :
    (nativeReadoutPresentation bindings).apply atom=bindings.applyFull atom depth := by
  rw [←applyTypeValuation_presented_eq_apply]
  rw [applyFull_eq_readoutValuation_of_covered loopFree nonvariable coherent atom depth covered]
  congr 1
  exact funext (nativeReadoutPresentation_apply_var bindings)

/-- A concrete finite table computed from the native checkpoint is normal
and has exactly the complete theory of the independent source endpoint. -/
theorem nativeReadoutPresentation_principal {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (sameSolutions : ∀ valuation,TypeBindingSatisfied valuation native ↔
      TypeBindingSatisfied valuation independent) :
    (nativeReadoutPresentation native).Normal ∧
      ∀ valuation,TypeSubstSatisfied valuation (nativeReadoutPresentation native) ↔
        TypeBindingSatisfied valuation independent := by
  obtain ⟨presentation,p,_fold,normal,theory,readout,_fixed,_outside⟩ :=
    exists_uniform_exact_native_presentation loopFree nonvariable coherent sameSolutions
  have variableRead (name : String) :
      (presentation.renameVars p).apply (.var name)=
        native.applyFull (.var name) (native.resolutionFuel (.var name)) :=
    readout _ _ (native.applyFullCovered_resolutionFuel _)
  have tableNormal : (nativeReadoutPresentation native).Normal := by
    apply TypeSubst.finiteReadout_normal (Mettapedia.Util.LinearHash.eraseDups_nodup _) normal
    exact fun name => (variableRead name).symm
  refine ⟨tableNormal,?_⟩
  intro valuation
  exact (TypeSubst.satisfied_iff_of_same_readout tableNormal normal
    (fun name => (nativeReadoutPresentation_apply_var native name).trans (variableRead name).symm)
    valuation).trans (theory valuation)

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement

/-- The computed finite representation observes exact ordered-class authority,
not physical repeated edge occurrences. The equality holds for an entire
future operand, preserving correlations between all its variable occurrences. -/
theorem nativeReadoutPresentation_apply_eq_of_ordered_classes {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key)
    (lookups : ∀ key, second.lookup key = first.lookup key) (atom : Atom) :
    (nativeReadoutPresentation second).apply atom =
      (nativeReadoutPresentation first).apply atom := by
  rw [← applyTypeValuation_presented_eq_apply, ← applyTypeValuation_presented_eq_apply]
  congr 1
  funext name
  change (nativeReadoutPresentation second).apply (.var name) =
    (nativeReadoutPresentation first).apply (.var name)
  rw [nativeReadoutPresentation_apply_var, nativeReadoutPresentation_apply_var]
  exact BindingResolutionReadSupport.complete_applyFull_eq_of_ordered_classes classes lookups _

/-- Appending an already present edge changes the retained raw record but not
its uniform finite readout table's action on any later operand. -/
theorem nativeReadoutPresentation_apply_addEquality_of_mem {bindings : Bindings}
    {left right : String} (stored : (left, right) ∈ bindings.equalities) (atom : Atom) :
    (nativeReadoutPresentation (bindings.addEquality left right)).apply atom =
      (nativeReadoutPresentation bindings).apply atom :=
  nativeReadoutPresentation_apply_eq_of_ordered_classes
    (EqualityClosure.eqClassOrdered_addEquality_of_mem stored) (fun _ => rfl) atom

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation Spec.Type.Presentation.BindingTheory

private theorem variable_pair_forces {left right : String} (different : left ≠ right)
    {output : TypeSubst} (matched : AppliedReducedTypeMatchRel [] (.var left) (.var right) output) :
    output=[(left,.var right)] := by
  cases matched with
  | identical => contradiction
  | bindLeft => simp [TypeSubst.bind,TypeSubst.erase]
  | bindRight notVariable _ => exact (notVariable left rfl).elim

def publicAlias : Bindings := ⟨[],[("public","private")]⟩

theorem publicAlias_native_readout :
    publicAlias.applyFull (.var "private") 20 = .var "public" := by decide +kernel

/-- This record is produced by the actual open-variable matcher. -/
theorem publicAlias_actual_match :
    publicAlias ∈ matchAtoms (.var "public") (.var "private") 8 := by decide +kernel

theorem publicAlias_source_fold {presentation : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations publicAlias) [] presentation) :
    presentation=[("public",.var "private")] := by
  change EquationListPresentationRel [(.var "public",.var "private")] [] presentation at fold
  cases fold with
  | cons head tail =>
    cases tail
    cases head with
    | ordinary left right matched =>
      rw [TypeSubst.apply_empty] at left right
      subst left right
      exact variable_pair_forces (by decide : "public" ≠ "private") matched

theorem publicAlias_source_readout {normalized : Atom}
    (materialized : BindingMaterializationRel publicAlias (.var "private") normalized) :
    normalized = .var "private" := by
  obtain ⟨presentation,fold,output⟩ := materialized
  rw [publicAlias_source_fold fold] at output
  simpa [TypeSubst.apply,TypeSubst.lookup] using output

/-- The extra chronological convention prevents the caller's own alias name
from occurring in ANY materialized source body, although native resolution
selects exactly that name. This is a source-model restriction, not a native bug. -/
theorem publicAlias_source_excludes_public {raw normalized : Atom}
    (materialized : BindingMaterializationRel publicAlias raw normalized) :
    "public"∉TypeSubst.typeVars normalized := by
  obtain ⟨presentation,fold,rfl⟩:=materialized
  intro occurs
  apply fold.bindingTheory.1.apply_variable_not_key raw "public" occurs
  rw [publicAlias_source_fold fold]
  simp [TypeSubst.keys]

theorem publicAlias_rejects_literal_materializer_equality :
    ¬BindingMaterializationRel publicAlias (.var "private")
      (publicAlias.applyFull (.var "private") 20) := by
  intro h
  have fixed := publicAlias_source_readout h
  rw [publicAlias_native_readout] at fixed
  exact (by decide : (Atom.var "public") ≠ .var "private") fixed

/-- Fixing the public representative would make the required residual
renaming impossible. Rule freshness and residual readout use different actions. -/
theorem publicAlias_residual_permutation_cannot_fix_public
    (permutation : Equiv.Perm String)
    (observed : .var "private" = renameTypeVars permutation (.var "public")) :
    permutation "public" ≠ "public" := by
  simp only [renameTypeVars,Atom.var.injEq] at observed
  intro fixed
  rw [fixed] at observed
  contradiction

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.Controls

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.ModelTheory

#guard nativeReadoutPresentation publicAlias == [("private",.var "public")]
#guard (nativeReadoutPresentation publicAlias).apply
    (.expression [.var "private",.var "public",.var "untouched",.var "private"]) ==
  .expression [.var "public",.var "public",.var "untouched",.var "public"]

theorem publicAlias_uniform_principal_table :
    (nativeReadoutPresentation publicAlias).Normal ∧
      ∀ valuation,TypeSubstSatisfied valuation (nativeReadoutPresentation publicAlias) ↔
        TypeBindingSatisfied valuation publicAlias := by
  have loop : Spec.Match.Merge.SemanticLoopFree publicAlias :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  have shape : AssignmentsNonVariable publicAlias := by
    intro key value present
    cases present
  have coherent : CanonicalClassCoherent publicAlias loop shape := by
    intro node assignment
    rcases assignment with ⟨⟨key,value⟩,present,_⟩
    cases present
  exact nativeReadoutPresentation_principal loop shape coherent (fun _=>Iff.rfl)

/-- Dropping the alias is rejected by the complete-theory certificate. -/
theorem publicAlias_empty_table_erases_constraint :
    ¬(∀ valuation,TypeSubstSatisfied valuation [] ↔ TypeBindingSatisfied valuation publicAlias) := by
  intro equivalence
  let valuation : String → Atom := fun name => if name="public" then .symbol "A" else .symbol "B"
  have bad := (equivalence valuation).mp (by simp [TypeSubstSatisfied])
  have equation := bad.2 "public" "private" (by simp [publicAlias])
  simp [valuation] at equation

/-- Giving two names distinct values also rejects a proposed presentation
which invents their equality. -/
theorem empty_bindings_reject_invented_alias :
    ¬(∀ valuation,TypeSubstSatisfied valuation [("left",.var "right")] ↔
      TypeBindingSatisfied valuation Bindings.empty) := by
  intro equivalence
  let valuation : String → Atom := fun name => if name="left" then .symbol "A" else .symbol "B"
  have bad := (equivalence valuation).mpr (by simp [TypeBindingSatisfied,Bindings.empty])
  have equation := bad "left" (.var "right") (by simp)
  simp [valuation,applyTypeValuation] at equation

/-- The uniform computed table preserves the same repeated residual across
arbitrary future operands. It is not an atom-indexed choice. -/
theorem publicAlias_every_future_operand (atom : Atom) (depth : Nat)
    (covered : publicAlias.applyFullCovered atom depth=true) :
    (nativeReadoutPresentation publicAlias).apply atom=publicAlias.applyFull atom depth := by
  have loop : Spec.Match.Merge.SemanticLoopFree publicAlias :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  have shape : AssignmentsNonVariable publicAlias := by
    intro key value present
    cases present
  have coherent : CanonicalClassCoherent publicAlias loop shape := by
    intro node assignment
    rcases assignment with ⟨⟨key,value⟩,present,_⟩
    cases present
  exact nativeReadoutPresentation_apply loop shape coherent atom depth covered

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.Controls


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.ModelTheory Spec.Match.StructuralModel Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-- The actual expression matcher retains its seed through each concrete merge. -/
theorem declMatchList_seed_subrecord {left right : List Atom} {seed out : Bindings}
    (derived : DeclMatchSpec.MatchListAccRel left right seed out) :
    BindingSubrecord seed out :=
  match derived with
  | .nil => .refl _
  | .cons _ merged tail =>
      (FreshPrivateMerge.merge_left_subrecord merged).trans (declMatchList_seed_subrecord tail)
termination_by structural derived

/-- Fixed-target coherence is propagated along the matcher's actual accumulator,
including variable aliases. There is no closed-target premise. -/
theorem declMatchList_evalCoherentAt
    {target : Bindings} (loopFree : Spec.Match.Merge.SemanticLoopFree target)
    (nonvariable : AssignmentsNonVariable target) (source : DependencyNode target)
    (smaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target loopFree nonvariable node =
          applyClassSolution (canonicalValuation target loopFree nonvariable)
            (encodeModelAtom assignment.1.2))
    {left right : List Atom} {seed out : Bindings}
    (derived : DeclMatchSpec.MatchListAccRel left right seed out)
    (included : BindingSubrecord out target) (unique : AssignmentsNodup seed)
    (coherent : ClassAssignmentsEvalCoherentIn target seed
      (canonicalValuation target loopFree nonvariable) source) :
    ClassAssignmentsEvalCoherentIn target out
        (canonicalValuation target loopFree nonvariable) source ∧ AssignmentsNodup out :=
  match derived with
  | .nil => ⟨coherent,unique⟩
  | .cons _ merged tail => by
    have nextIncluded := (declMatchList_seed_subrecord tail).trans included
    obtain ⟨nextCoherent,nextUnique⟩ := declMerge_evalCoherentAt loopFree nonvariable source smaller
      (DeclMergeSpec.mergeBindings_sound merged) nextIncluded unique coherent
    exact declMatchList_evalCoherentAt loopFree nonvariable source smaller tail included
      nextUnique nextCoherent
termination_by structural derived

/-- Every actual atom-match result has the fixed-target invariant needed to
continue reconciliation. Variable/variable matches retain equality edges. -/
theorem declMatch_evalCoherentAt
    {target : Bindings} (loopFree : Spec.Match.Merge.SemanticLoopFree target)
    (nonvariable : AssignmentsNonVariable target) (source : DependencyNode target)
    (smaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target loopFree nonvariable node =
          applyClassSolution (canonicalValuation target loopFree nonvariable)
            (encodeModelAtom assignment.1.2))
    {left right : Atom} {matched : Bindings}
    (derived : DeclMatchSpec.MatchRel left right matched)
    (included : BindingSubrecord matched target) :
    ClassAssignmentsEvalCoherentIn target matched
        (canonicalValuation target loopFree nonvariable) source ∧ AssignmentsNodup matched := by
  cases derived with
  | symSym | varVar | grounded =>
      exact ⟨⟨included,by intros; contradiction⟩,by simp [AssignmentsNodup]⟩
  | varNonVar | nonVarVar =>
      refine ⟨evalCoherentIn_of_no_equalities _ source included ?_ rfl,?_⟩ <;>
        simp [AssignmentsNodup]
  | expr list _ =>
      exact declMatchList_evalCoherentAt loopFree nonvariable source smaller list included
        (by simp [AssignmentsNodup,Bindings.empty])
        ⟨(declMatchList_seed_subrecord list).trans included,by intros; contradiction⟩

/-- The candidate-first query merge earns canonical coherence for an open
native match. Its actual candidate may contain aliases and compound values. -/
theorem declMerge_canonicalClassCoherent_of_match
    {left right : Atom} {matched caller out : Bindings}
    (matching : DeclMatchSpec.MatchRel left right matched)
    (merged : DeclMergeSpec.MergeRel matched caller out)
    (loopFree : Spec.Match.Merge.SemanticLoopFree out)
    (nonvariable : AssignmentsNonVariable out) :
    CanonicalClassCoherent out loopFree nonvariable := by
  apply canonicalClassCoherent_of_evalCoherentAt loopFree nonvariable
  intro source smaller
  obtain ⟨seedCoherent,seedUnique⟩ := declMatch_evalCoherentAt loopFree nonvariable source smaller
    matching (FreshPrivateMerge.mergeRel_left_subrecord merged)
  exact (declMerge_evalCoherentAt loopFree nonvariable source smaller merged
    (BindingSubrecord.refl _) seedUnique seedCoherent).1

/-- Native open matching followed by actual caller reconciliation constructs
its principal readout from one finite solution and the caller's assignment
shape. Output coherence, loop freedom and principality are conclusions. -/
theorem mergeBindings_applyFull_mostGeneral_of_match_model
    {left right : Atom} {matched caller out : Bindings} {matchFuel mergeFuel : Nat}
    {valuation : String → Metta.Atom}
    (matching : matched ∈ matchAtoms left right matchFuel)
    (merged : out ∈ mergeBindings matched caller mergeFuel)
    (callerShape : AssignmentsNonVariable caller)
    (equation : HEAtomEquationSatisfied valuation left right)
    (callerModel : HEBindingSatisfied valuation caller) :
    MostGeneralSolution out (fun name =>
      encodeModelAtom (out.applyFull (.var name) (out.resolutionFuel (.var name)))) := by
  have matchedShape := matchAtoms_assignmentsNonVariable_model matching
  have matchedModel := (matchAtoms_solution_iff matching valuation).mpr equation
  have shape := mergeBindings_assignmentsNonVariable_model merged matchedShape callerShape
  have loopFree := mergeBindings_semanticLoopFree_of_common_model merged matchedShape callerShape
    matchedModel callerModel
  exact applyFull_mostGeneralSolution loopFree shape
    (declMerge_canonicalClassCoherent_of_match (DeclMatchSpec.matchAtoms_sound matching)
      (DeclMergeSpec.mergeBindings_sound merged) loopFree shape)

/-- A surviving actual query-merge candidate constructs a principal readout.
The finite model is earned from actual reconciliation and its cycle check;
no caller model or equality-free match restriction is required. -/
theorem mergeBindings_applyFull_mostGeneral_of_match
    {left right : Atom} {matched caller out : Bindings} {matchFuel mergeFuel : Nat}
    (matching : matched ∈ matchAtoms left right matchFuel)
    (merged : out ∈ mergeBindings matched caller mergeFuel)
    (callerShape : AssignmentsNonVariable caller)
    (admitted : out.hasLoop = false) :
    MostGeneralSolution out (fun name =>
      encodeModelAtom (out.applyFull (.var name) (out.resolutionFuel (.var name)))) := by
  have shape := mergeBindings_assignmentsNonVariable_model merged
    (matchAtoms_assignmentsNonVariable_model matching) callerShape
  have loopFree := (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree out).mp admitted
  exact applyFull_mostGeneralSolution loopFree shape
    (declMerge_canonicalClassCoherent_of_match (DeclMatchSpec.matchAtoms_sound matching)
      (DeclMergeSpec.mergeBindings_sound merged) loopFree shape)

namespace OpenMatchControls
private def query : Atom :=
  .expression [.symbol "pair",.var "public",.expression [.symbol "F",.var "public"]]
private def pattern : Atom :=
  .expression [.symbol "pair",.var "privateA",.var "privateB"]
private def matched : Bindings := (matchAtoms query pattern 32)[0]!
private def caller : Bindings := ⟨[("public",.symbol "A")],[("public","outside")]⟩
private def merged : Bindings := (mergeBindings matched caller 32)[0]!

theorem selected_match : matched ∈ matchAtoms query pattern 32 := by decide +kernel
theorem selected_merge : merged ∈ mergeBindings matched caller 32 := by decide +kernel

theorem alias_match_is_open : matched.equalities ≠ [] ∧
    Spec.Type.Presentation.TypeSubst.typeVars query ≠ [] := by decide +kernel

theorem selected_principal :
    MostGeneralSolution merged (fun name =>
      encodeModelAtom (merged.applyFull (.var name) (merged.resolutionFuel (.var name)))) := by
  apply mergeBindings_applyFull_mostGeneral_of_match selected_match selected_merge
  · intro key value present
    have same : key="public" ∧ value=.symbol "A" := by simpa [caller] using present
    rw [same.2]
    rfl
  · decide +kernel

#guard merged.applyFull (.expression [.var "public",.var "privateA",.var "privateB",.var "outside"])
    32 == .expression [.symbol "A",.symbol "A",.expression [.symbol "F",.symbol "A"],.symbol "A"]

private def incompatible : Bindings :=
  ⟨[("public",.symbol "A"),("public",.symbol "B")],[]⟩
#guard mergeBindings matched incompatible 32 == []
private def cyclic : Bindings :=
  ⟨[("public",.expression [.symbol "F",.var "public"])],[]⟩
#guard ((mergeBindings matched cyclic 32).filter (fun bindings => !bindings.hasLoop)) == []
end OpenMatchControls

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection





namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Match.Completeness
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-- A surviving actual open query constructs an independent matcher and caller
merge with the same full solution theory and support. The source endpoint is
constructed by semantic completeness; it need not share the native row layout. -/
theorem open_match_source_endpoint
    {query pattern : Atom} {matched caller independent out : Bindings} {matchFuel mergeFuel : Nat}
    (matching : matched ∈ matchAtoms query pattern matchFuel)
    (merged : out ∈ mergeBindings matched caller mergeFuel)
    (callerShape : AssignmentsNonVariable caller)
    (independentShape : AssignmentsNonVariable independent)
    (admitted : out.hasLoop=false)
    (inputTheory : ∀ valuation,TypeBindingSatisfied valuation caller ↔
      TypeBindingSatisfied valuation independent)
    (inputSupport : ∀ name,name∈specBindingVars caller ↔ name∈specBindingVars independent) :
    ∃ sourceMatched sourceOut,
      MatchRel equalityGroundedSemantic query pattern sourceMatched ∧
      MergeRel equalityGroundedSemantic sourceMatched independent sourceOut ∧
      AssignmentsNonVariable sourceOut ∧ SemanticLoopFree sourceOut ∧
      (∃ valuation,TypeBindingSatisfied valuation sourceOut) ∧
      (∀ valuation,TypeBindingSatisfied valuation out ↔ TypeBindingSatisfied valuation sourceOut) ∧
      (∀ name,name∈specBindingVars out ↔ name∈specBindingVars sourceOut) := by
  have shape := mergeBindings_assignmentsNonVariable_model merged
    (matchAtoms_assignmentsNonVariable_model matching) callerShape
  have loopFree := (hasLoop_eq_false_iff_semanticLoopFree out).mp admitted
  have coherent := declMerge_canonicalClassCoherent_of_match (DeclMatchSpec.matchAtoms_sound matching)
    (DeclMergeSpec.mergeBindings_sound merged) loopFree shape
  let valuation : String → Atom := fun name=>out.applyFull (.var name) (out.resolutionFuel (.var name))
  have nativeModel : TypeBindingSatisfied valuation out := applyFull_typeBindingSatisfied loopFree shape coherent
  have nativeInputs := (mergeBindings_solution_iff merged (fun name=>encodeModelAtom (valuation name))).mp
    (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied nativeModel)
  have sourceCallerModel : HEBindingSatisfied (fun name=>encodeModelAtom (valuation name)) independent :=
    Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied
      ((inputTheory valuation).mp
        ((Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation caller).mpr
          nativeInputs.2))
  obtain ⟨sourceMatched,sourceMatch,sourceMatchModel⟩ := exists_specMatch_of_solution
    ((matchAtoms_solution_iff matching (fun name=>encodeModelAtom (valuation name))).mp nativeInputs.1)
  have sourceCallerShape : HEAssignmentsNonVariable independent := by
    intro key target stored
    have impossible := independentShape key (.var target) stored
    simp [isVariableB] at impossible
  obtain ⟨sourceOut,sourceMerge,sourceModel,sourceShape⟩ := exists_specMerge_of_solution
    sourceMatchModel (specMatch_assignmentsNonVariable sourceMatch) sourceCallerModel sourceCallerShape
  have nonvariable : AssignmentsNonVariable sourceOut := by
    intro key value stored
    cases value with
    | var name => exact (sourceShape key name stored).elim
    | symbol | grounded | expression => rfl
  refine ⟨sourceMatched,sourceOut,sourceMatch,sourceMerge,nonvariable,
    semanticLoopFree_of_satisfied_nonvariable sourceModel nonvariable,
    ⟨valuation,(Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated
      valuation sourceOut).mpr sourceModel⟩,?_,?_⟩
  · intro observer
    rw [Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated observer out,
      Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated observer sourceOut,
      mergeBindings_solution_iff merged,
      Spec.Match.SolutionTheory.mergeRel_solution_iff sourceMerge,
      matchAtoms_solution_iff matching,
      Spec.Match.SolutionTheory.matchRel_solution_iff sourceMatch]
    have callerModels : HEBindingSatisfied (fun name=>encodeModelAtom (observer name)) caller ↔
        HEBindingSatisfied (fun name=>encodeModelAtom (observer name)) independent :=
      (Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated observer caller).symm.trans
        ((inputTheory observer).trans
          (Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated observer independent))
    rw [callerModels]
    rfl
  · intro name
    rw [FreshPrivateMerge.merge_support_iff merged name,FreshPrivateMerge.match_support_iff matching name,
      SourceSupport.merge_support sourceMerge name,SourceSupport.match_support sourceMatch name,inputSupport]

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Type.Presentation.BindingTheory
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Match.Completeness
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-- A surviving open query constructs an independent source match, actual
candidate-first source merge, and one correlated readout for an arbitrary whole
continuation tuple. The same residual permutation preserves the complete
source theory and exact freshness support and fixes every outside name.
This does not assert equivariance of unchanged name-inspecting host policies. -/
theorem open_match_joint_source_endpoint
    {query pattern : Atom} {matched caller independent out : Bindings} {matchFuel mergeFuel : Nat}
    (matching : matched ∈ matchAtoms query pattern matchFuel)
    (merged : out ∈ mergeBindings matched caller mergeFuel)
    (callerShape : AssignmentsNonVariable caller)
    (independentShape : AssignmentsNonVariable independent)
    (admitted : out.hasLoop=false)
    (inputTheory : ∀ valuation,TypeBindingSatisfied valuation caller ↔
      TypeBindingSatisfied valuation independent)
    (inputSupport : ∀ name,name∈specBindingVars caller ↔ name∈specBindingVars independent)
    (observations : List Atom) (depth : Nat)
    (covered : out.applyFullCovered (.expression observations) depth=true) :
    ∃ (sourceMatched sourceOut : Bindings) (normalized : Atom) (p : Equiv.Perm String),
      MatchRel equalityGroundedSemantic query pattern sourceMatched ∧
      MergeRel equalityGroundedSemantic sourceMatched independent sourceOut ∧
      AssignmentsNonVariable sourceOut ∧ SemanticLoopFree sourceOut ∧
      BindingMaterializationRel sourceOut (.expression observations) normalized ∧
      normalized=renameTypeVars p (out.applyFull (.expression observations) depth) ∧
      (∀ valuation,TypeBindingSatisfied valuation out ↔ TypeBindingSatisfied valuation sourceOut) ∧
      (∀ name,name∈specBindingVars out ↔ name∈specBindingVars sourceOut) ∧
      (∀ valuation,TypeBindingSatisfied valuation sourceOut →
        ∀ atom,applyTypeValuation valuation (renameTypeVars p atom)=applyTypeValuation valuation atom) ∧
      (∀ name,name∉specBindingVars sourceOut → p name=name) ∧
      (∀ valuation,TypeBindingSatisfied valuation out ↔
        TypeBindingSatisfied valuation (renameBindings p sourceOut)) ∧
      (∀ name,name∈specBindingVars out ↔ name∈specBindingVars (renameBindings p sourceOut)) := by
  obtain ⟨sourceMatched,sourceOut,sourceMatch,sourceMerge,sourceShape,sourceLoop,sourceModel,
      theory,support⟩ := open_match_source_endpoint matching merged callerShape independentShape
        admitted inputTheory inputSupport
  obtain ⟨normalized,materialized⟩ :=
    BindingMaterializationRel.exists_of_satisfiable sourceModel (.expression observations)
  have shape := mergeBindings_assignmentsNonVariable_model merged
    (matchAtoms_assignmentsNonVariable_model matching) callerShape
  have loopFree := (hasLoop_eq_false_iff_semanticLoopFree out).mp admitted
  have coherent := declMerge_canonicalClassCoherent_of_match (DeclMatchSpec.matchAtoms_sound matching)
    (DeclMergeSpec.mergeBindings_sound merged) loopFree shape
  obtain ⟨p,readout,fixed,_outside,renamedTheory⟩ :=
    applyFull_joint_model_fixed_permutation_of_bindingMaterialization loopFree shape coherent
      theory observations depth covered materialized
  exact ⟨sourceMatched,sourceOut,normalized,p,sourceMatch,sourceMerge,sourceShape,sourceLoop,
    materialized,readout,theory,support,
    fun valuation model atom=>applyTypeValuation_model_fixed p valuation (fixed valuation model) atom,
    model_fixed_fixes_outside p sourceModel fixed,
    fun valuation=>(theory valuation).trans (renamedTheory valuation).symm,
    fun name=>(support name).trans (renameBindings_support_of_model_fixed p sourceModel fixed name).symm⟩

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Match.ModelTheory

/-- The finite readout of an actual stronger binding frame absorbs a previous
principal frame's readout. Raw records, origins and saved syntax are retained. -/
theorem nativeReadoutPresentation_absorbs_of_models
    {earlier later : Bindings}
    (earlierLoop : Spec.Match.Merge.SemanticLoopFree earlier)
    (earlierShape : AssignmentsNonVariable earlier)
    (earlierCoherent : CanonicalClassCoherent earlier earlierLoop earlierShape)
    (laterLoop : Spec.Match.Merge.SemanticLoopFree later)
    (laterShape : AssignmentsNonVariable later)
    (laterCoherent : CanonicalClassCoherent later laterLoop laterShape)
    (refines : ∀ valuation, TypeBindingSatisfied valuation later →
      TypeBindingSatisfied valuation earlier) (atom : Atom) :
    (nativeReadoutPresentation later).apply ((nativeReadoutPresentation earlier).apply atom) =
      (nativeReadoutPresentation later).apply atom := by
  have old := nativeReadoutPresentation_principal earlierLoop earlierShape earlierCoherent
    (fun _ => Iff.rfl)
  have next := nativeReadoutPresentation_principal laterLoop laterShape laterCoherent
    (fun _ => Iff.rfl)
  exact apply_absorbs_of_solution_implication next.1
    (fun valuation model => (old.2 valuation).mpr (refines valuation ((next.2 valuation).mp model))) atom

/-- The same absorption holds for the actual covered resolver calls, including
different sufficient depths before and after refinement. -/
theorem applyFull_absorbs_of_models
    {earlier later : Bindings}
    (earlierLoop : Spec.Match.Merge.SemanticLoopFree earlier)
    (earlierShape : AssignmentsNonVariable earlier)
    (earlierCoherent : CanonicalClassCoherent earlier earlierLoop earlierShape)
    (laterLoop : Spec.Match.Merge.SemanticLoopFree later)
    (laterShape : AssignmentsNonVariable later)
    (laterCoherent : CanonicalClassCoherent later laterLoop laterShape)
    (refines : ∀ valuation, TypeBindingSatisfied valuation later →
      TypeBindingSatisfied valuation earlier)
    (atom : Atom) (earlierDepth laterNestedDepth laterRawDepth : Nat)
    (earlierCovered : earlier.applyFullCovered atom earlierDepth = true)
    (nestedCovered : later.applyFullCovered (earlier.applyFull atom earlierDepth) laterNestedDepth = true)
    (rawCovered : later.applyFullCovered atom laterRawDepth = true) :
    later.applyFull (earlier.applyFull atom earlierDepth) laterNestedDepth =
      later.applyFull atom laterRawDepth := by
  rw [← nativeReadoutPresentation_apply laterLoop laterShape laterCoherent _ _ nestedCovered,
    ← nativeReadoutPresentation_apply earlierLoop earlierShape earlierCoherent _ _ earlierCovered,
    nativeReadoutPresentation_absorbs_of_models earlierLoop earlierShape earlierCoherent
      laterLoop laterShape laterCoherent refines,
    nativeReadoutPresentation_apply laterLoop laterShape laterCoherent _ _ rawCovered]

/-- A principal runtime record constructs one certified finite readout for an
independent presentation of its complete theory. The table is shared by all
future operands, rather than selected separately for each observation. -/
theorem nativeReadoutPresentation_certificate {native independent : Bindings}
    (loopFree : Spec.Match.Merge.SemanticLoopFree native)
    (nonvariable : AssignmentsNonVariable native)
    (coherent : CanonicalClassCoherent native loopFree nonvariable)
    (sameSolutions : ∀ valuation, TypeBindingSatisfied valuation native ↔
      TypeBindingSatisfied valuation independent) :
    BindingTheory.ReadoutCertificate independent (nativeReadoutPresentation native) := by
  have principal := nativeReadoutPresentation_principal loopFree nonvariable coherent sameSolutions
  exact BindingTheory.ReadoutCertificate.of_normal_theory principal.1 principal.2

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.LogicalMergeBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- Every actual raw merge occurrence preserves the full original conjunction.
This says nothing about a subsequent loop filter or selected representative. -/
theorem native_merge_agreement {left right output : Bindings} {depth : Nat}
    (occurred : output ∈ mergeBindings left right depth) :
    BindingSourceAgreement output
      ⟨left.assignments ++ right.assignments, left.equalities ++ right.equalities⟩ := by
  constructor
  · intro valuation
    rw [bindingSatisfied_append_iff]
    simp only [specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
    exact mergeBindings_solution_iff occurred _
  · intro name
    rw [mem_specBindingVars_append]
    exact FreshPrivateMerge.merge_support_iff occurred name

theorem of_native_merge {left right output : Bindings} {depth : Nat}
    (occurred : output ∈ mergeBindings left right depth)
    (model : ∃ valuation : String → Atom, TypeBindingSatisfied valuation output) :
    LogicalMergeRel left right output := ⟨native_merge_agreement occurred, model⟩

theorem native_merge_iff_common_model {left right output : Bindings} {depth : Nat}
    (occurred : output ∈ mergeBindings left right depth) :
    LogicalMergeRel left right output ↔
      ∃ valuation : String → Atom,
        TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right := by
  constructor
  · exact LogicalMergeRel.common_model
  · rintro ⟨valuation, leftModel, rightModel⟩
    have agreement := native_merge_agreement occurred
    exact ⟨agreement, valuation, (agreement.solutions valuation).mpr
      ((bindingSatisfied_append_iff valuation left right).mpr ⟨leftModel, rightModel⟩)⟩


end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.LogicalMergeBridge


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.LogicalMergeBridge.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge
open Spec.Eval.Steps.LogicalMergeControls

def inconsistent : Bindings := ⟨[("x", .symbol "A"), ("x", .symbol "B")], []⟩

theorem inconsistent_has_no_model :
    ¬∃ valuation : String → Atom, TypeBindingSatisfied valuation inconsistent := by
  rintro ⟨valuation, satisfied⟩
  have first := satisfied.1 "x" (.symbol "A") (by simp [inconsistent])
  have second := satisfied.1 "x" (.symbol "B") (by simp [inconsistent])
  have impossible := first.symm.trans second
  simp [applyTypeValuation] at impossible

theorem raw_merge_and_loop_filter_are_not_finite_model_evidence :
    MergeRel equalityGroundedSemantic inconsistent Bindings.empty inconsistent ∧
      mergeBindings inconsistent Bindings.empty 1 = [inconsistent] ∧
      inconsistent.hasLoop = false ∧
      ¬LogicalMergeRel inconsistent Bindings.empty inconsistent :=
  ⟨.mk (.refl []) .nil, by decide +kernel, by decide +kernel,
    fun logical => inconsistent_has_no_model logical.2⟩

theorem alias_exposure_constructs_an_independent_output :
    ∃ output, MergeRel equalityGroundedSemantic
        (aliasConstraints matched) (aliasConstraints aliases) output ∧
      LogicalMergeRel matched aliases output ∧ Spec.Match.ModelTheory.AssignmentsNonVariable output ∧
      SemanticLoopFree output :=
  Spec.Match.Completeness.exists_alias_specMerge_of_common_model logical_alias_conjunction.common_model

theorem one_new_certificate_absorbs_all_pending_operands :
    ∃ oldTable nextTable,
      ReadoutCertificate aliases oldTable ∧ ReadoutCertificate conjoined nextTable ∧
      ∀ pending : List Atom,
        (pending.map oldTable.apply).map nextTable.apply = pending.map nextTable.apply := by
  obtain ⟨oldTable, fold⟩ := exists_binding_presentation ⟨_, aliases_model⟩
  have old := ReadoutCertificate.of_fold fold
  obtain ⟨nextTable, next, absorbed⟩ := logical_alias_conjunction.certifies_pending old
  exact ⟨oldTable, nextTable, old, next, absorbed⟩

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.LogicalMergeBridge.Controls


/-! ## Coherent alias-aware local merge/readout operation

This boundary constructs the finite readout used by the retained worker.
It exposes bare aliases as equality constraints before actual reconciliation,
keeps the structural cycle filter, and earns one ordered-class readout for
all pending syntax. Finite matching coverage remains explicit.
-/

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Match.ModelTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- Execute the existing merger on a constraint-equivalent alias presentation,
retain its structural cycle filter, and compute one finite ordered-class
readout for each surviving occurrence. No readout is supplied by a caller. -/
def mergeReadouts (matched incoming : Bindings) (depth : Nat) :
    List (Bindings × TypeSubst) :=
  (mergeBindings matched (aliasConstraints incoming) depth).filterMap fun output =>
    if output.hasLoop then none else some (output, nativeReadoutPresentation output)

/-- Actual matching retains its ordered occurrences before the repaired local
merge/readout boundary. This operation does not evaluate the matched syntax. -/
def unifyReadouts (target pattern : Atom) (incoming : Bindings) (depth : Nat) :
    List (Bindings × TypeSubst) :=
  (matchAtoms target pattern depth).flatMap fun matched => mergeReadouts matched incoming depth

/-- Structural application uses the same earned table for the whole branch. -/
def results (target pattern branch : Atom) (incoming : Bindings) (depth : Nat) : ResultSet :=
  (unifyReadouts target pattern incoming depth).map fun result =>
    (result.2.apply branch, result.1)

theorem mem_mergeReadouts {matched incoming output : Bindings} {table : TypeSubst} {depth : Nat} :
    (output, table) ∈ mergeReadouts matched incoming depth ↔
      output ∈ mergeBindings matched (aliasConstraints incoming) depth ∧
      output.hasLoop = false ∧ table = nativeReadoutPresentation output := by
  simp only [mergeReadouts, List.mem_filterMap]
  constructor
  · rintro ⟨actual, occurred, selected⟩
    split at selected
    · contradiction
    · have same := Option.some.inj selected
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨occurred, by simpa using ‹¬actual.hasLoop = true›, rfl⟩
  · rintro ⟨occurred, acyclic, rfl⟩
    exact ⟨output, occurred, by simp [acyclic]⟩

theorem mem_unifyReadouts {target pattern : Atom} {incoming output : Bindings}
    {table : TypeSubst} {depth : Nat} :
    (output, table) ∈ unifyReadouts target pattern incoming depth ↔
      ∃ matched, matched ∈ matchAtoms target pattern depth ∧
        (output, table) ∈ mergeReadouts matched incoming depth := by
  simp [unifyReadouts]

/-- Actual match/reconciliation and the retained structural filter earn the
complete finite model and selected readout. Input aliases are unrestricted;
there is no output-model, principal-output or expected-reader premise. -/
theorem mergeReadouts_sound
    {target pattern : Atom} {matched incoming output : Bindings}
    {table : TypeSubst} {matchDepth depth : Nat}
    (matching : matched ∈ matchAtoms target pattern matchDepth)
    (occurred : (output, table) ∈ mergeReadouts matched incoming depth) :
    BindingSourceAgreement output
        ⟨matched.assignments ++ incoming.assignments, matched.equalities ++ incoming.equalities⟩ ∧
      (∃ valuation : String → Atom, TypeBindingSatisfied valuation output) ∧
      ReadoutCertificate output table ∧
      (∀ atom readDepth, output.applyFullCovered atom readDepth = true →
        table.apply atom = output.applyFull atom readDepth) := by
  obtain ⟨merged, noLoop, rfl⟩ := mem_mergeReadouts.mp occurred
  have inputShape : AssignmentsNonVariable (aliasConstraints incoming) :=
    aliasConstraints_nonvariable incoming
  have shape := mergeBindings_assignmentsNonVariable_model merged
    (matchAtoms_assignmentsNonVariable_model matching) inputShape
  have loopFree := (hasLoop_eq_false_iff_semanticLoopFree output).mp noLoop
  have coherent := declMerge_canonicalClassCoherent_of_match
    (DeclMatchSpec.matchAtoms_sound matching) (DeclMergeSpec.mergeBindings_sound merged)
    loopFree shape
  have complete : BindingSourceAgreement output
      ⟨matched.assignments ++ incoming.assignments, matched.equalities ++ incoming.equalities⟩ := by
    constructor
    · intro valuation
      rw [bindingSatisfied_append_iff]
      have exactMerge : TypeBindingSatisfied valuation output ↔
          TypeBindingSatisfied valuation matched ∧
          TypeBindingSatisfied valuation (aliasConstraints incoming) := by
        simp only [specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
        exact mergeBindings_solution_iff merged _
      exact exactMerge.trans (and_congr Iff.rfl (aliasConstraints_models incoming valuation))
    · intro name
      rw [mem_specBindingVars_append, FreshPrivateMerge.merge_support_iff merged,
        aliasConstraints_support]
  exact ⟨complete,
    ⟨_, applyFull_typeBindingSatisfied loopFree shape coherent⟩,
    nativeReadoutPresentation_certificate loopFree shape coherent (fun _ => Iff.rfl),
    nativeReadoutPresentation_apply loopFree shape coherent⟩

/-- A successful local operation proves that its original input was consistent;
it does not rely on a fabricated model of a rewritten output record. -/
theorem mergeReadouts_input_model
    {target pattern : Atom} {matched incoming output : Bindings}
    {table : TypeSubst} {matchDepth depth : Nat}
    (matching : matched ∈ matchAtoms target pattern matchDepth)
    (occurred : (output, table) ∈ mergeReadouts matched incoming depth) :
    ∃ valuation : String → Atom,
      TypeBindingSatisfied valuation matched ∧ TypeBindingSatisfied valuation incoming := by
  obtain ⟨agreement, ⟨valuation, model⟩, _certificate, _reads⟩ :=
    mergeReadouts_sound matching occurred
  exact ⟨valuation, (bindingSatisfied_append_iff valuation matched incoming).mp
    ((agreement.solutions valuation).mp model)⟩

/-- The old selected input table and every future operand are transported
jointly; no representative is chosen separately at a use site. -/
theorem mergeReadouts_pending_absorbed
    {target pattern : Atom} {matched incoming output : Bindings}
    {oldTable table : TypeSubst} {matchDepth depth : Nat}
    (old : ReadoutCertificate incoming oldTable)
    (matching : matched ∈ matchAtoms target pattern matchDepth)
    (occurred : (output, table) ∈ mergeReadouts matched incoming depth)
    (pending : List Atom) :
    (pending.map oldTable.apply).map table.apply = pending.map table.apply := by
  obtain ⟨agreement, _model, certificate, _reads⟩ := mergeReadouts_sound matching occurred
  apply old.pending_absorbed certificate _ pending
  intro valuation model
  exact ((bindingSatisfied_append_iff valuation matched incoming).mp
    ((agreement.solutions valuation).mp model)).2

/-- Newly selected residual names follow the actual ordered equality classes
of the retained output record. Names outside the complete support stay free. -/
theorem mergeReadouts_outside_fixed
    {matched incoming output : Bindings} {table : TypeSubst} {depth : Nat}
    (occurred : (output, table) ∈ mergeReadouts matched incoming depth)
    (name : String) (outside : name ∉ specBindingVars output) :
    table.apply (.var name) = .var name := by
  obtain ⟨_merged, _noLoop, rfl⟩ := mem_mergeReadouts.mp occurred
  rw [nativeReadoutPresentation_apply_var, applyFull_var_of_outside outside]

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Match.ModelTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- Each selected occurrence retains its actual matching origin, complete
constraint theory, and a single internally constructed output table. -/
theorem unifyReadouts_sound
    {target pattern : Atom} {incoming output : Bindings} {table : TypeSubst} {depth : Nat}
    (occurred : (output, table) ∈ unifyReadouts target pattern incoming depth) :
    ∃ matched, matched ∈ matchAtoms target pattern depth ∧
      BindingSourceAgreement output
        ⟨matched.assignments ++ incoming.assignments, matched.equalities ++ incoming.equalities⟩ ∧
      (∃ valuation : String → Atom, TypeBindingSatisfied valuation output) ∧
      ReadoutCertificate output table ∧
      (∀ atom readDepth, output.applyFullCovered atom readDepth = true →
        table.apply atom = output.applyFull atom readDepth) := by
  obtain ⟨matched, matching, selected⟩ := mem_unifyReadouts.mp occurred
  exact ⟨matched, matching, mergeReadouts_sound matching selected⟩

theorem unifyReadouts_pending_absorbed
    {target pattern : Atom} {incoming output : Bindings}
    {oldTable table : TypeSubst} {depth : Nat}
    (old : ReadoutCertificate incoming oldTable)
    (occurred : (output, table) ∈ unifyReadouts target pattern incoming depth)
    (pending : List Atom) :
    (pending.map oldTable.apply).map table.apply = pending.map table.apply := by
  obtain ⟨matched, matching, selected⟩ := mem_unifyReadouts.mp occurred
  exact mergeReadouts_pending_absorbed old matching selected pending

/-- Replacing the branch reader by the earned finite table preserves the
entire ordered occurrence list of the existing operation on the exposed
constraint presentation. In particular, this is stronger than membership
equivalence or set equality. -/
theorem results_eq_exposed_unifySuccessResults
    (target pattern branch : Atom) (incoming : Bindings) (depth : Nat) :
    results target pattern branch incoming depth =
      unifySuccessResults target pattern branch (aliasConstraints incoming) depth := by
  simp only [results, unifyReadouts, List.map_flatMap, unifySuccessResults, aliasConstraints_idempotent]
  apply List.flatMap_congr
  intro matched matching
  simp only [mergeReadouts, List.map_filterMap]
  apply List.filterMap_congr
  intro output merged
  by_cases cyclic : output.hasLoop = true
  · simp [cyclic]
  · have acyclic : output.hasLoop = false := by simpa using cyclic
    have selected : (output, nativeReadoutPresentation output) ∈
        mergeReadouts matched incoming depth :=
      mem_mergeReadouts.mpr ⟨merged, acyclic, rfl⟩
    have reader := (mergeReadouts_sound matching selected).2.2.2
      branch (output.resolutionFuel branch) (output.applyFullCovered_resolutionFuel branch)
    simp [acyclic, reader]

/-- The actual primitive operation reads each occurrence through the same earned table. -/
theorem results_eq_unifySuccessResults
    (target pattern branch : Atom) (incoming : Bindings) (depth : Nat) :
    results target pattern branch incoming depth =
      unifySuccessResults target pattern branch incoming depth := by
  rw [results_eq_exposed_unifySuccessResults]
  simp only [unifySuccessResults, aliasConstraints_idempotent]

/-- The former supported fragment is literally unchanged, including binding
records, result order, duplicate occurrences, and residual spelling. -/
theorem results_eq_unifySuccessResults_of_nonvariable
    (target pattern branch : Atom) {incoming : Bindings} (depth : Nat)
    (shape : AssignmentsNonVariable incoming) :
    results target pattern branch incoming depth =
      unifySuccessResults target pattern branch incoming depth := by
  rw [results_eq_exposed_unifySuccessResults, aliasConstraints_eq_self shape]

/-- Covered actual matching/reconciliation makes the selected list independent
of later matching budgets. Uncovered exhaustion is not a semantic refusal. -/
theorem results_stable (target pattern branch : Atom) (incoming : Bindings)
    (depth extra : Nat)
    (covered : unifyMatchesCovered target pattern (aliasConstraints incoming) depth = true) :
    results target pattern branch incoming (depth + extra) =
      results target pattern branch incoming depth := by
  rw [results_eq_exposed_unifySuccessResults, results_eq_exposed_unifySuccessResults]
  exact unifyMatchesCovered_stable target pattern branch (aliasConstraints incoming)
    depth extra covered

/-- Inconsistent incoming constraints cannot be turned into a successful
readout merely by exposing aliases. This applies at every matching depth. -/
theorem unifyReadouts_empty_of_inconsistent
    (target pattern : Atom) (incoming : Bindings) (depth : Nat)
    (inconsistent : ¬∃ valuation : String → Atom, TypeBindingSatisfied valuation incoming) :
    unifyReadouts target pattern incoming depth = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨output, table⟩ occurred
  obtain ⟨matched, matching, selected⟩ := mem_unifyReadouts.mp occurred
  obtain ⟨valuation, _matchedModel, inputModel⟩ := mergeReadouts_input_model matching selected
  exact inconsistent ⟨valuation, inputModel⟩

theorem results_empty_of_inconsistent
    (target pattern branch : Atom) (incoming : Bindings) (depth : Nat)
    (inconsistent : ¬∃ valuation : String → Atom, TypeBindingSatisfied valuation incoming) :
    results target pattern branch incoming depth = [] := by
  simp [results, unifyReadouts_empty_of_inconsistent target pattern incoming depth inconsistent]

/-- For each actual reconciled occurrence the structural filter is exact:
it survives precisely when the original two input theories have a common
finite model. The table and its coherent readout are computed on success. -/
theorem mergeReadouts_selected_iff_common_model
    {target pattern : Atom} {matched incoming output : Bindings} {matchDepth depth : Nat}
    (matching : matched ∈ matchAtoms target pattern matchDepth)
    (merged : output ∈ mergeBindings matched (aliasConstraints incoming) depth) :
    (output, nativeReadoutPresentation output) ∈ mergeReadouts matched incoming depth ↔
      ∃ valuation : String → Atom,
        TypeBindingSatisfied valuation matched ∧ TypeBindingSatisfied valuation incoming := by
  constructor
  · exact mergeReadouts_input_model matching
  · rintro ⟨valuation, matchedModel, inputModel⟩
    have acyclic := mergeBindings_semanticLoopFree_of_common_model merged
      (matchAtoms_assignmentsNonVariable_model matching) (aliasConstraints_nonvariable incoming)
      (heBindingSatisfied_of_specTypeBindingSatisfied matchedModel)
      (heBindingSatisfied_of_specTypeBindingSatisfied
        ((aliasConstraints_models incoming valuation).mpr inputModel))
    exact mem_mergeReadouts.mpr
      ⟨merged, (hasLoop_eq_false_iff_semanticLoopFree output).mpr acyclic, rfl⟩

/-- Exact logical success at an actual matched/reconciled occurrence does not
prescribe how much fuel is needed to discover that occurrence. -/
theorem unifyReadouts_nonempty_iff
    (target pattern : Atom) (incoming : Bindings) (depth : Nat) :
    (∃ entry, entry ∈ unifyReadouts target pattern incoming depth) ↔
      ∃ matched output, matched ∈ matchAtoms target pattern depth ∧
        output ∈ mergeBindings matched (aliasConstraints incoming) depth ∧
        ∃ valuation : String → Atom,
          TypeBindingSatisfied valuation matched ∧ TypeBindingSatisfied valuation incoming := by
  constructor
  · rintro ⟨⟨output, table⟩, occurred⟩
    obtain ⟨matched, matching, selected⟩ := mem_unifyReadouts.mp occurred
    exact ⟨matched, output, matching, (mem_mergeReadouts.mp selected).1,
      mergeReadouts_input_model matching selected⟩
  · rintro ⟨matched, output, matching, merged, commonModel⟩
    exact ⟨(output, nativeReadoutPresentation output), mem_unifyReadouts.mpr
      ⟨matched, matching, (mergeReadouts_selected_iff_common_model matching merged).mpr commonModel⟩⟩

/-- Stability preserves the actual result records and their one shared table,
not just the materialization of a chosen branch. -/
theorem unifyReadouts_stable (target pattern : Atom) (incoming : Bindings)
    (depth extra : Nat)
    (covered : unifyMatchesCovered target pattern (aliasConstraints incoming) depth = true) :
    unifyReadouts target pattern incoming (depth + extra) =
      unifyReadouts target pattern incoming depth := by
  obtain ⟨matchedCovered, mergedCovered⟩ := Bool.and_eq_true_iff.mp covered
  have sameMatch := matchCovered_stable depth extra (.atoms target pattern) matchedCovered
  change matchAtoms target pattern (depth + extra) = matchAtoms target pattern depth at sameMatch
  simp only [unifyReadouts, sameMatch]
  apply List.flatMap_congr
  intro matched matching
  have sameMerge := matchCovered_stable depth extra (.merge matched (aliasConstraints incoming))
    (by simpa only [aliasConstraints_idempotent] using
      (List.all_eq_true.mp mergedCovered matched matching))
  change mergeBindings matched (aliasConstraints incoming) (depth + extra) =
    mergeBindings matched (aliasConstraints incoming) depth at sameMerge
  simp only [mergeReadouts, sameMerge]

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Match.ModelTheory
open Spec.Match.Completeness
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- An actual repaired occurrence constructs an independent match and the
full conjunction contract against the chosen source input. The source input
may itself contain bare aliases; representation agreement does not assert
nonvariable shape, an expected output, or a chosen valuation. -/
theorem mergeReadouts_source
    {target pattern : Atom} {matched incoming independent output : Bindings}
    {table : TypeSubst} {matchDepth depth : Nat}
    (input : BindingSourceAgreement incoming independent)
    (matching : matched ∈ matchAtoms target pattern matchDepth)
    (occurred : (output, table) ∈ mergeReadouts matched incoming depth) :
    ∃ sourceMatched,
      MatchRel equalityGroundedSemantic target pattern sourceMatched ∧
      BindingSourceAgreement output
        ⟨sourceMatched.assignments ++ independent.assignments,
          sourceMatched.equalities ++ independent.equalities⟩ ∧
      (∃ valuation : String → Atom, TypeBindingSatisfied valuation output) ∧
      ReadoutCertificate output table ∧
      (∀ atom readDepth, output.applyFullCovered atom readDepth = true →
        table.apply atom = output.applyFull atom readDepth) := by
  obtain ⟨agreement, ⟨valuation, model⟩, certificate, reads⟩ :=
    mergeReadouts_sound matching occurred
  have matchedModel := ((bindingSatisfied_append_iff valuation matched incoming).mp
    ((agreement.solutions valuation).mp model)).1
  obtain ⟨sourceMatched, sourceMatch, _sourceModel⟩ := exists_specMatch_of_solution
    ((matchAtoms_solution_iff matching (fun name => encodeModelAtom (valuation name))).mp
      (heBindingSatisfied_of_specTypeBindingSatisfied matchedModel))
  have matchAgreement : BindingSourceAgreement matched sourceMatched := by
    constructor
    · intro observer
      rw [specTypeBindingSatisfied_iff_heBindingSatisfied_translated,
        specTypeBindingSatisfied_iff_heBindingSatisfied_translated,
        matchAtoms_solution_iff matching, Spec.Match.SolutionTheory.matchRel_solution_iff sourceMatch]
      rfl
    · intro name
      rw [FreshPrivateMerge.match_support_iff matching name,
        SourceSupport.match_support sourceMatch name]
  refine ⟨sourceMatched, sourceMatch, agreement.trans ?_, ⟨valuation, model⟩, certificate, reads⟩
  constructor
  · intro observer
    rw [bindingSatisfied_append_iff, bindingSatisfied_append_iff,
      matchAgreement.solutions observer, input.solutions observer]
  · intro name
    rw [mem_specBindingVars_append, mem_specBindingVars_append,
      matchAgreement.support name, input.support name]

theorem unifyReadouts_source
    {target pattern : Atom} {incoming independent output : Bindings}
    {table : TypeSubst} {depth : Nat}
    (input : BindingSourceAgreement incoming independent)
    (occurred : (output, table) ∈ unifyReadouts target pattern incoming depth) :
    ∃ sourceMatched,
      MatchRel equalityGroundedSemantic target pattern sourceMatched ∧
      BindingSourceAgreement output
        ⟨sourceMatched.assignments ++ independent.assignments,
          sourceMatched.equalities ++ independent.equalities⟩ ∧
      (∃ valuation : String → Atom, TypeBindingSatisfied valuation output) ∧
      ReadoutCertificate output table ∧
      (∀ atom readDepth, output.applyFullCovered atom readDepth = true →
        table.apply atom = output.applyFull atom readDepth) := by
  obtain ⟨matched, matching, selected⟩ := mem_unifyReadouts.mp occurred
  exact mergeReadouts_source input matching selected

/-- Complete local matcher and merge coverage is equivalent to the
independent existence of a satisfiable unify candidate. Both directions
construct their witnesses, including for arbitrary incoming aliases. -/
theorem covered_unifyReadouts_iff_source
    {target pattern : Atom} {incoming : Bindings} {depth : Nat}
    (covered : unifyMatchesCovered target pattern incoming depth = true) :
    (∃ entry, entry ∈ unifyReadouts target pattern incoming depth) ↔
      ∃ output, Spec.Eval.Steps.UnifyCandidateRel target pattern incoming output := by
  constructor
  · rintro ⟨⟨output,table⟩,occurred⟩
    obtain ⟨sourceMatched,matching,agreement,⟨valuation,model⟩,_,_⟩ :=
      unifyReadouts_source (.refl incoming) occurred
    have common := (bindingSatisfied_append_iff valuation sourceMatched incoming).mp
      ((agreement.solutions valuation).mp model)
    exact ⟨_,sourceMatched,matching,LogicalMergeRel.append_of_common_model ⟨valuation,common⟩⟩
  · rintro ⟨sourceOutput,sourceMatched,sourceMatch,sourceMerge⟩
    obtain ⟨valuation,model⟩ := sourceMerge.2
    have parts := (sourceMerge.solutions valuation).mp model
    let observer : String → Metta.Atom := fun name => encodeModelAtom (valuation name)
    have equation : HEAtomEquationSatisfied observer target pattern :=
      (Spec.Match.SolutionTheory.matchRel_solution_iff sourceMatch observer).mp
        (heBindingSatisfied_of_specTypeBindingSatisfied parts.1)
    obtain ⟨matchCovered,mergeCovered⟩ := Bool.and_eq_true_iff.mp covered
    obtain ⟨matched,matching⟩ := covered_match_of_solution matchCovered equation
    have matchedModel : HEBindingSatisfied observer matched :=
      (matchAtoms_solution_iff matching observer).mpr equation
    have callerModel : HEBindingSatisfied observer (aliasConstraints incoming) :=
      heBindingSatisfied_of_specTypeBindingSatisfied
        ((aliasConstraints_models incoming valuation).mpr parts.2)
    have callerShape : HEAssignmentsNonVariable (aliasConstraints incoming) := by
      intro key name present
      have impossible := aliasConstraints_nonvariable incoming key (.var name) present
      simp [isVariableB] at impossible
    obtain ⟨output,witnessDepth,occurred⟩ := exists_mergeBindings_of_common_model
      matchedModel (heAssignmentsNonVariable_of_matchAtoms matching) callerModel callerShape
    have later := DeclMatchSpec.mergeBindings_mono matched (aliasConstraints incoming)
      witnessDepth depth occurred
    have stable := matchCovered_stable depth witnessDepth (.merge matched (aliasConstraints incoming))
      (List.all_eq_true.mp mergeCovered matched matching)
    change mergeBindings matched (aliasConstraints incoming) (depth + witnessDepth) =
      mergeBindings matched (aliasConstraints incoming) depth at stable
    rw [Nat.add_comm witnessDepth depth,stable] at later
    have selected := (mergeReadouts_selected_iff_common_model matching later).mpr
      ⟨valuation,(specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr
        matchedModel,parts.2⟩
    exact ⟨_,mem_unifyReadouts.mpr ⟨matched,matching,selected⟩⟩

/-- A completed empty primitive result is exactly independent failure of
the full match-and-caller conjunction. This licenses the else branch after
merge rejection as well as after structural mismatch. -/
theorem covered_unify_empty_iff
    {target pattern branch : Atom} {incoming : Bindings} {depth : Nat}
    (covered : unifyMatchesCovered target pattern incoming depth = true) :
    unifySuccessResults target pattern branch incoming depth = [] ↔
      Spec.Eval.Steps.UnifyNoMatchRel target pattern incoming := by
  rw [← results_eq_unifySuccessResults]
  change (unifyReadouts target pattern incoming depth).map _ = [] ↔ _
  rw [List.map_eq_nil_iff]
  constructor
  · intro empty output candidate
    obtain ⟨entry,occurred⟩ := (covered_unifyReadouts_iff_source covered).mpr ⟨output,candidate⟩
    rw [empty] at occurred
    exact List.not_mem_nil occurred
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry occurred
    obtain ⟨output,candidate⟩ := (covered_unifyReadouts_iff_source covered).mp ⟨entry,occurred⟩
    exact absent output candidate

/-- The chosen source certificate is absorbed by the actual computed table
simultaneously on the complete pending tuple. -/
theorem unifyReadouts_source_pending
    {target pattern : Atom} {incoming independent output : Bindings}
    {oldTable table : TypeSubst} {depth : Nat}
    (input : BindingSourceAgreement incoming independent)
    (old : ReadoutCertificate independent oldTable)
    (occurred : (output, table) ∈ unifyReadouts target pattern incoming depth)
    (pending : List Atom) :
    (pending.map oldTable.apply).map table.apply = pending.map table.apply := by
  obtain ⟨matched, _sourceMatch, agreement, _model, certificate, _reads⟩ :=
    unifyReadouts_source input occurred
  apply old.pending_absorbed certificate _ pending
  intro valuation model
  exact ((bindingSatisfied_append_iff valuation matched independent).mp
    ((agreement.solutions valuation).mp model)).2

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Match.ModelTheory

def oldTable : TypeSubst := [("u", .var "v"), ("t", .var "w")]
def incoming : Bindings := ⟨oldTable, []⟩
def matched : Bindings := ⟨[], [("u", "w"), ("t", "v")]⟩
def target : Atom := .expression [.var "u", .var "t"]
def pattern : Atom := .expression [.var "w", .var "v"]
def output : Bindings := ⟨[], [("u", "w"), ("t", "v"), ("u", "v"), ("t", "w")]⟩
def pending : Atom := .expression [.var "u", .var "t", .var "u", .var "v", .var "w"]

theorem incoming_normal : oldTable.Normal := by
  simp [TypeSubst.Normal, TypeSubst.keys, oldTable, TypeSubst.typeVars, or_imp, forall_and]

theorem incoming_acyclic : incoming.hasLoop = false := by decide +kernel

theorem normalized_input : CurrentStore.normalize oldTable =
    [("t", .var "w"), ("u", .var "v")] := by
  simp [CurrentStore.normalize, CurrentStore.normalizeFrom, oldTable, TypeSubst.bind,
    TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase, TypeSubst.applyAssignment]

theorem normalized_input_reads (atom : Atom) :
    oldTable.apply atom = (CurrentStore.normalize oldTable).apply atom := by
  rw [← applyTypeValuation_presented_eq_apply, ← applyTypeValuation_presented_eq_apply]
  apply congrArg (fun valuation => applyTypeValuation valuation atom)
  funext name
  rw [normalized_input]
  by_cases u : name = "u" <;> by_cases t : name = "t" <;>
    simp_all [presentedValuation, oldTable, TypeSubst.apply, TypeSubst.lookup]

theorem input_certificate : ReadoutCertificate incoming oldTable := by
  have normalized : ReadoutCertificate incoming (CurrentStore.normalize oldTable) :=
    CurrentStore.normalize_certified_of_noLoop (by decide +kernel) incoming_acyclic
  obtain ⟨folded, choice, fold, fixed, outside, allOperands⟩ := normalized.representative
  exact ⟨incoming_normal, folded, choice, fold, fixed, outside,
    fun atom => (normalized_input_reads atom).trans (allOperands atom)⟩

theorem actual_match : matchAtoms target pattern 12 = [matched] := by decide +kernel

theorem actual_alias_merge : mergeBindings matched (aliasConstraints incoming) 12 = [output] := by
  decide +kernel

theorem output_acyclic : output.hasLoop = false := by decide +kernel

theorem exactly_one_readout : unifyReadouts target pattern incoming 12 =
    [(output, nativeReadoutPresentation output)] := by
  simp [unifyReadouts, actual_match, mergeReadouts, actual_alias_merge, output_acyclic]

theorem actual_occurrence : (output, nativeReadoutPresentation output) ∈
    unifyReadouts target pattern incoming 12 := by rw [exactly_one_readout]; simp

theorem internally_earned_certificate :
    ReadoutCertificate output (nativeReadoutPresentation output) := by
  obtain ⟨_matched, _matching, _agreement, _model, certificate, _reads⟩ :=
    unifyReadouts_sound actual_occurrence
  exact certificate

theorem crossed_aliases_accept_jointly : results target pattern pending incoming 12 =
    [(.expression [.var "u", .var "u", .var "u", .var "u", .var "u"], output)] := by
  rw [results_eq_exposed_unifySuccessResults]
  decide +kernel

theorem selected_table_keeps_every_shared_use :
    (nativeReadoutPresentation output).apply pending =
      .expression [.var "u", .var "u", .var "u", .var "u", .var "u"] := by
  have ran := crossed_aliases_accept_jointly
  simpa [results, exactly_one_readout] using ran

theorem all_pending_positions_absorb_old_table (atoms : List Atom) :
    (atoms.map oldTable.apply).map (nativeReadoutPresentation output).apply =
      atoms.map (nativeReadoutPresentation output).apply :=
  unifyReadouts_pending_absorbed input_certificate actual_occurrence atoms

theorem actual_coverage : unifyMatchesCovered target pattern (aliasConstraints incoming) 12 = true := by
  decide +kernel

/-- Complete actual search constructs an independent source candidate for
the crossed bare-alias caller, without a normalized-caller premise. -/
theorem crossed_aliases_have_source_candidate :
    ∃ selected, Spec.Eval.Steps.UnifyCandidateRel target pattern incoming selected := by
  apply (covered_unifyReadouts_iff_source (depth := 12) (by decide +kernel)).mp
  exact ⟨_,actual_occurrence⟩

theorem every_larger_depth_keeps_the_occurrence (extra : Nat) :
    results target pattern pending incoming (12 + extra) =
      [(.expression [.var "u", .var "u", .var "u", .var "u", .var "u"], output)] :=
  (results_stable target pattern pending incoming 12 extra actual_coverage).trans
    crossed_aliases_accept_jointly

/-- The former operation rejects this normal, independently certified input.
This compares actual computations, not only abstract record presentations. -/
theorem former_worker_rejects :
    ((matchAtoms target pattern 12).flatMap fun matched =>
      (mergeBindings matched incoming 12).filterMap fun output =>
        if output.hasLoop then none
        else some (output.applyFull pending (output.resolutionFuel pending), output)) = [] := by
  decide +kernel

theorem former_worker_is_covered :
    (matchCovered 12 (.atoms target pattern) &&
      (matchAtoms target pattern 12).all fun matched => matchCovered 12 (.merge matched incoming)) = true := by
  decide +kernel

theorem old_filter_cannot_just_be_removed :
    let raw : Bindings := ⟨oldTable, matched.equalities⟩
    raw.applyFull (.var "u") 12 ≠ raw.applyFull (.var "w") 12 ∧
      ("u", "w") ∈ raw.equalities := by decide +kernel

theorem syntax_application_does_not_evaluate_calls :
    results target pattern (.expression [.symbol "tick", .var "u", .var "u"]) incoming 12 =
      [(.expression [.symbol "tick", .var "u", .var "u"], output)] := by
  rw [results_eq_exposed_unifySuccessResults]
  decide +kernel

theorem outside_name_stays_free :
    (nativeReadoutPresentation output).apply (.var "outside") = .var "outside" := by
  apply mergeReadouts_outside_fixed
    (mem_mergeReadouts.mpr ⟨by rw [actual_alias_merge]; simp, output_acyclic, rfl⟩)
  decide +kernel

def groundCaller : Bindings := ⟨[("x", .symbol "A")], [("x", "saved") ]⟩

/-- Structural matching succeeds, but the caller's incompatible constraint
rejects the merge. Completed search licenses genuine source failure. -/
theorem post_merge_failure_is_source_failure :
    matchAtoms (.var "x") (.symbol "B") 12 ≠ [] ∧
      unifySuccessResults (.var "x") (.symbol "B") (.symbol "yes") groundCaller 12 = [] ∧
      Spec.Eval.Steps.UnifyNoMatchRel (.var "x") (.symbol "B") groundCaller := by
  have empty : unifySuccessResults (.var "x") (.symbol "B") (.symbol "yes") groundCaller 12 = [] := by
    decide +kernel
  exact ⟨by decide +kernel,empty,(covered_unify_empty_iff (by decide +kernel)).mp empty⟩

/-- The same empty helper output at depth zero cannot establish that
failure: the independent source still has a live candidate. -/
theorem truncated_unify_is_not_source_failure :
    unifySuccessResults target pattern pending incoming 0 = [] ∧
      unifyMatchesCovered target pattern incoming 0 = false ∧
      ¬Spec.Eval.Steps.UnifyNoMatchRel target pattern incoming := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro absent
  obtain ⟨selected,candidate⟩ := crossed_aliases_have_source_candidate
  exact absent selected candidate

theorem nonvariable_fragment_unchanged (left right branch : Atom) (depth : Nat) :
    results left right branch groundCaller depth =
      unifySuccessResults left right branch groundCaller depth := by
  apply results_eq_unifySuccessResults_of_nonvariable
  intro key value stored
  simp [groundCaller] at stored
  obtain ⟨rfl, rfl⟩ := stored
  rfl

theorem structural_occurs_still_refuses :
    results (.var "x") (.expression [.symbol "f", .var "x"])
      (.symbol "accepted") Bindings.empty 12 = [] := by
  rw [results_eq_exposed_unifySuccessResults]
  decide +kernel

theorem rigid_disagreement_still_refuses :
    results (.symbol "A") (.symbol "B") (.symbol "accepted") incoming 12 = [] := by
  rw [results_eq_exposed_unifySuccessResults]
  decide +kernel

def inconsistent : Bindings := ⟨[("x", .symbol "A"), ("x", .symbol "B")], []⟩

theorem inconsistent_has_no_model :
    ¬∃ valuation : String → Atom, TypeBindingSatisfied valuation inconsistent := by
  rintro ⟨valuation, assignments, _equalities⟩
  have first := assignments "x" (.symbol "A") (by simp [inconsistent])
  have second := assignments "x" (.symbol "B") (by simp [inconsistent])
  exact (by decide : Atom.symbol "A" ≠ Atom.symbol "B")
    (by simpa [applyTypeValuation] using first.symm.trans second)

theorem inconsistent_seed_cannot_succeed (left right branch : Atom) (depth : Nat) :
    results left right branch inconsistent depth = [] :=
  results_empty_of_inconsistent left right branch inconsistent depth inconsistent_has_no_model

/-- An acyclic shape check alone does not supply consistency. -/
theorem inconsistent_seed_has_no_structural_loop : inconsistent.hasLoop = false := by decide +kernel

theorem shallow_exhaustion_is_not_coverage :
    results target pattern pending incoming 0 = [] ∧
      unifyMatchesCovered target pattern (aliasConstraints incoming) 0 = false := by
  rw [results_eq_exposed_unifySuccessResults]
  decide +kernel

def forwardAlias : Bindings := ⟨[], [("a", "b")]⟩
def backwardAlias : Bindings := ⟨[], [("b", "a")]⟩

theorem reordered_aliases_agree : BindingSourceAgreement forwardAlias backwardAlias := by
  constructor
  · intro valuation
    simp [TypeBindingSatisfied, forwardAlias, backwardAlias, eq_comm]
  · intro name
    simp [specBindingVars, forwardAlias, backwardAlias, or_comm]

/-- The existing ordered-class representative policy is retained. Equivalent
input theories do not force the same printed free-variable spelling. -/
theorem representative_spelling_is_not_arbitrary_literal_invariance :
    results (.symbol "same") (.symbol "same") (.var "a") forwardAlias 12 =
      [(.var "a", forwardAlias)] ∧
    results (.symbol "same") (.symbol "same") (.var "a") backwardAlias 12 =
      [(.var "b", backwardAlias)] := by
  rw [results_eq_exposed_unifySuccessResults, results_eq_exposed_unifySuccessResults]
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.AliasReadout.Controls

namespace Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Match.Completeness
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- A finite source type match survives a change of the incoming constraint
representation. The independent merge is constructed from its common model;
its output retains the full solution theory and freshening support. The
admitted input stores aliases as equality edges, not variable-valued
assignments. Literal representative readouts are a separate contract. -/
theorem typeMatch_finite {native independent output : Bindings} {expected actual : Atom}
    (input : BindingSourceAgreement native independent)
    (shape : HEAssignmentsNonVariable independent)
    (matched : TypeMatchRel expected actual native output)
    (finite : ∃ valuation : String → Atom, TypeBindingSatisfied valuation output) :
    ∃ sourceOutput,
      TypeMatchRel expected actual independent sourceOutput ∧
      BindingSourceAgreement output sourceOutput ∧
      HEAssignmentsNonVariable sourceOutput ∧
      ∃ valuation : String → Atom, TypeBindingSatisfied valuation sourceOutput := by
  cases matched with
  | undefinedLeft =>
      obtain ⟨valuation, model⟩ := finite
      exact ⟨independent, .undefinedLeft _ _, input, shape, valuation, (input.solutions valuation).mp model⟩
  | atomLeft =>
      obtain ⟨valuation, model⟩ := finite
      exact ⟨independent, .atomLeft _ _, input, shape, valuation, (input.solutions valuation).mp model⟩
  | undefinedRight =>
      obtain ⟨valuation, model⟩ := finite
      exact ⟨independent, .undefinedRight _ _, input, shape, valuation, (input.solutions valuation).mp model⟩
  | atomRight =>
      obtain ⟨valuation, model⟩ := finite
      exact ⟨independent, .atomRight _ _, input, shape, valuation, (input.solutions valuation).mp model⟩
  | @structural _ _ _ matchingBindings _ leftUndefined leftAtom rightUndefined rightAtom matching merged =>
      obtain ⟨valuation, model⟩ := finite
      have conjunction := (bindingSatisfied_append_iff valuation native matchingBindings).mp
        ((merged.bindingSourceAgreement.solutions valuation).mp model)
      have independentModel := (input.solutions valuation).mp conjunction.1
      obtain ⟨sourceOutput, sourceMerge, sourceModel, sourceShape⟩ := exists_specMerge_of_solution
        ((specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation independent).mp independentModel)
        shape
        ((specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matchingBindings).mp conjunction.2)
        (Spec.Match.ModelTheory.specMatch_assignmentsNonVariable matching)
      refine ⟨sourceOutput,
        .structural leftUndefined leftAtom rightUndefined rightAtom matching sourceMerge,
        merged.bindingSourceAgreement.trans
          ((input.append (.refl matchingBindings)).trans sourceMerge.bindingSourceAgreement.symm),
        sourceShape, valuation, ?_⟩
      exact (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation sourceOutput).mpr sourceModel

/-- Finite candidate existence and rejection depend on the incoming theory
and its support, rather than assignment order or alias-edge orientation.
This is an existence law, not a completed candidate-bag or readout law. -/
theorem typeMatch_finite_exists_iff {native independent : Bindings} {expected actual : Atom}
    (input : BindingSourceAgreement native independent)
    (nativeShape : HEAssignmentsNonVariable native)
    (sourceShape : HEAssignmentsNonVariable independent) :
    (∃ output, TypeMatchRel expected actual native output ∧
      ∃ valuation : String → Atom, TypeBindingSatisfied valuation output) ↔
    (∃ output, TypeMatchRel expected actual independent output ∧
      ∃ valuation : String → Atom, TypeBindingSatisfied valuation output) := by
  constructor
  · rintro ⟨output, matched, finite⟩
    obtain ⟨sourceOutput, sourceMatch, _, _, sourceModel⟩ := input.typeMatch_finite sourceShape matched finite
    exact ⟨sourceOutput, sourceMatch, sourceModel⟩
  · rintro ⟨output, matched, finite⟩
    obtain ⟨nativeOutput, nativeMatch, _, _, nativeModel⟩ :=
      input.symm.typeMatch_finite nativeShape matched finite
    exact ⟨nativeOutput, nativeMatch, nativeModel⟩

end Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- Equivalent incoming constraints and the same source type query determine
equivalent output constraint theories and support.
The chosen equality-edge order and alias representative are not fixed by
this law, and it does not assert literal equality of materialized reads. -/
theorem TypeMatchRel.output_agreement {expected actual : Atom}
    {leftBefore rightBefore first second : Bindings}
    (left : TypeMatchRel expected actual leftBefore first)
    (right : TypeMatchRel expected actual rightBefore second)
    (incoming : BindingSourceAgreement leftBefore rightBefore) :
    BindingSourceAgreement first second := by
  by_cases wildcard : expected = Atom.undefinedType ∨ expected = Atom.atomType ∨
      actual = Atom.undefinedType ∨ actual = Atom.atomType
  · simpa only [left.wildcard_output wildcard,right.wildcard_output wildcard] using incoming
  · have ordinary : expected ≠ Atom.undefinedType ∧ expected ≠ Atom.atomType ∧
        actual ≠ Atom.undefinedType ∧ actual ≠ Atom.atomType := by
      simpa only [not_or] using wildcard
    obtain ⟨expectedDefined,expectedOrdinary,actualDefined,actualOrdinary⟩ := ordinary
    obtain ⟨leftMatch,leftMatched,leftMerged⟩ := left.structural_of_nonWildcard
      expectedDefined expectedOrdinary actualDefined actualOrdinary
    obtain ⟨rightMatch,rightMatched,rightMerged⟩ := right.structural_of_nonWildcard
      expectedDefined expectedOrdinary actualDefined actualOrdinary
    have matched : BindingSourceAgreement leftMatch rightMatch := by
      constructor
      · intro valuation
        rw [specTypeBindingSatisfied_iff_heBindingSatisfied_translated,
          specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
        exact Spec.Match.SolutionTheory.matchRel_solutionTheory_unique leftMatched rightMatched _
      · intro name
        rw [QueryBindingProjection.SourceSupport.match_support leftMatched name,
          QueryBindingProjection.SourceSupport.match_support rightMatched name]
    exact leftMerged.bindingSourceAgreement.trans
      ((incoming.append matched).trans rightMerged.bindingSourceAgreement.symm)

private theorem first_selected_eq {Item : Type} (accepted : Item → Prop)
    (leftPrefix rightPrefix leftTail rightTail : List Item) (left right : Item)
    (same : leftPrefix ++ left :: leftTail = rightPrefix ++ right :: rightTail)
    (leftRejected : ∀ item ∈ leftPrefix, ¬accepted item)
    (rightRejected : ∀ item ∈ rightPrefix, ¬accepted item)
    (leftAccepted : accepted left) (rightAccepted : accepted right) : left = right := by
  induction leftPrefix generalizing rightPrefix with
  | nil =>
      cases rightPrefix with
      | nil => exact (List.cons.inj same).1
      | cons head rest =>
          have heads : left = head := (List.cons.inj same).1
          exact (rightRejected head (by simp) (heads ▸ leftAccepted)).elim
  | cons head rest ih =>
      cases rightPrefix with
      | nil =>
          have heads : head = right := (List.cons.inj same).1
          exact (leftRejected head (by simp) (heads.symm ▸ rightAccepted)).elim
      | cons other tail =>
          exact ih tail (List.cons.inj same).2
            (fun item present => leftRejected item (List.mem_cons_of_mem _ present))
            (fun item present => rightRejected item (List.mem_cons_of_mem _ present))

/-- Complete casts over the same functional query agree occurrence by
occurrence once their matching policy is a subrelation of source matching.
This covers both raw matching and guarded finite matching. Failed type
copies remain separate occurrences, even when their diagnostics coincide. -/
theorem TypeCastBatchRel.output_agreement {space : Space} {atom expected : Atom}
    {before : Bindings} {lookup : TypeLookupRel}
    {matching : Atom → Atom → Bindings → Bindings → Prop} {first second : ResultSet}
    (queryUnique : ∀ left right, lookup before atom expected left →
      lookup before atom expected right → left = right)
    (sourceMatching : ∀ actual output, matching expected actual before output →
      TypeMatchRel expected actual before output)
    (left : TypeCastBatchRel space atom expected before first (lookup := lookup) (matching := matching))
    (right : TypeCastBatchRel space atom expected before second (lookup := lookup) (matching := matching)) :
    List.Forall₂ (fun first second : ResultPair =>
      first.1 = second.1 ∧ BindingSourceAgreement first.2 second.2) first second := by
  cases left with
  | @success _ _ leftTypes leftPrefix leftTail leftType leftOutput leftQuery leftSplit leftRejected leftMatched =>
      cases right with
      | @success _ _ rightTypes rightPrefix rightTail rightType rightOutput rightQuery rightSplit rightRejected rightMatched =>
          have selected := first_selected_eq
            (fun actual => ∃ output, matching expected actual before output)
            leftPrefix rightPrefix leftTail rightTail leftType rightType
            (leftSplit.symm.trans ((queryUnique _ _ leftQuery rightQuery).trans rightSplit))
            (fun actual present ⟨output,matched⟩ => leftRejected actual present output matched)
            (fun actual present ⟨output,matched⟩ => rightRejected actual present output matched)
            ⟨leftOutput,leftMatched⟩ ⟨rightOutput,rightMatched⟩
          cases selected
          exact .cons ⟨rfl,(sourceMatching _ _ leftMatched).output_agreement
            (sourceMatching _ _ rightMatched) (.refl before)⟩ .nil
      | failure rightQuery rejected =>
          have present : leftType ∈ leftTypes := by rw [leftSplit]; simp
          have present' := (queryUnique _ _ leftQuery rightQuery) ▸ present
          exact (rejected leftType present' leftOutput leftMatched).elim
  | failure leftQuery rejected =>
      cases right with
      | @success _ _ rightTypes rightPrefix rightTail rightType rightOutput rightQuery rightSplit rightRejected rightMatched =>
          have present : rightType ∈ rightTypes := by rw [rightSplit]; simp
          have present' := (queryUnique _ _ rightQuery leftQuery) ▸ present
          exact (rejected rightType present' rightOutput rightMatched).elim
      | failure rightQuery _ =>
          have same := queryUnique _ _ leftQuery rightQuery
          cases same
          apply List.forall₂_same.mpr
          intro result present
          exact ⟨rfl,BindingSourceAgreement.refl result.2⟩

/-- The whole ordered caller/value observation is independent of a source
cast's chosen constraint presentation. Each list position remains present;
an unsatisfiable occurrence is not collapsed into an empty result list. -/
theorem TypeCastBatchRel.joint_observation_eq {space : Space} {atom expected : Atom}
    {before : Bindings} {lookup : TypeLookupRel}
    {matching : Atom → Atom → Bindings → Bindings → Prop} {first second : ResultSet}
    (queryUnique : ∀ left right, lookup before atom expected left →
      lookup before atom expected right → left = right)
    (sourceMatching : ∀ actual output, matching expected actual before output →
      TypeMatchRel expected actual before output)
    (left : TypeCastBatchRel space atom expected before first (lookup := lookup) (matching := matching))
    (right : TypeCastBatchRel space atom expected before second (lookup := lookup) (matching := matching))
    (publicScope : List String) :
    first.map (fun result => observedTuples result.2 (publicScope.map Atom.var ++ [result.1])) =
      second.map (fun result => observedTuples result.2 (publicScope.map Atom.var ++ [result.1])) := by
  have paired := left.output_agreement queryUnique sourceMatching right
  clear left right
  induction paired with
  | nil => rfl
  | @cons head other tail remaining related rest ih =>
      obtain ⟨same,agreement⟩ := related
      have observed := (agreement.theoryEquivAt
        (TypeSubst.typeVarsList (publicScope.map Atom.var ++ [other.1]))).observedTuples_eq
        (publicScope.map Atom.var ++ [other.1]) (fun _ present => present)
      simpa only [List.map_cons,same,observed] using congrArg (List.cons _) ih

/-- The published literal type-query profile discharges the two local query
and match obligations of joint observation uniqueness. The source programs,
open caller constraints and public observer are arbitrary. -/
theorem TypeCastBatchRel.raw_joint_observation_eq {space : Space} {atom expected : Atom}
    {before : Bindings} {first second : ResultSet}
    (left : TypeCastBatchRel space atom expected before first)
    (right : TypeCastBatchRel space atom expected before second)
    (publicScope : List String) :
    first.map (fun result => observedTuples result.2 (publicScope.map Atom.var ++ [result.1])) =
      second.map (fun result => observedTuples result.2 (publicScope.map Atom.var ++ [result.1])) :=
  left.joint_observation_eq (fun _ _ left right => left.unique right)
    (fun _ _ matched => matched) right publicScope

end Mettapedia.Languages.MeTTa.HE.Spec.Type

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-- Logical unification succeeds exactly when the incoming constraints and
the new equation have a common finite model. The source matcher and output
conjunction are constructed from that model. -/
theorem unifyCandidate_exists_iff_equation_model (target pattern : Atom) (incoming : Bindings) :
    (∃ output, UnifyCandidateRel target pattern incoming output) ↔
      ∃ valuation : String → Atom, TypeBindingSatisfied valuation incoming ∧
        applyTypeValuation valuation target = applyTypeValuation valuation pattern := by
  constructor
  · rintro ⟨output,matched,matching,merged⟩
    obtain ⟨valuation,satisfied⟩ := merged.2
    have model := (UnifyCandidateRel.solutions ⟨matched,matching,merged⟩ valuation).mp satisfied
    exact ⟨valuation,model.2,model.1⟩
  · rintro ⟨valuation,incomingModel,equation⟩
    have translated : HEAtomEquationSatisfied
        (fun name => encodeModelAtom (valuation name)) target pattern := by
      simpa only [HEAtomEquationSatisfied,encodeModelAtom_applyTypeValuation] using
        congrArg encodeModelAtom equation
    obtain ⟨matched,matching,matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution translated
    have sourceModel : TypeBindingSatisfied valuation matched :=
      (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel
    exact ⟨_,matched,matching,LogicalMergeRel.append_of_common_model
      ⟨valuation,sourceModel,incomingModel⟩⟩

/-- A subsequent source unification reads its operands without changing
their meaning in any model of the actual incoming frame. -/
theorem UnifyCandidateRel.solutions_of_certified_reads {incoming output : Bindings}
    {table : TypeSubst} {target pattern : Atom}
    (certificate : ReadoutCertificate incoming table)
    (candidate : UnifyCandidateRel (table.apply target) (table.apply pattern) incoming output)
    (valuation : String → Atom) :
    TypeBindingSatisfied valuation output ↔
      applyTypeValuation valuation target = applyTypeValuation valuation pattern ∧
        TypeBindingSatisfied valuation incoming := by
  rw [candidate.solutions valuation]
  apply and_congr_left
  intro model
  rw [certificate.preserves_model valuation model target,
    certificate.preserves_model valuation model pattern]

/-- The reached constraint inventory includes precisely the old support and
the original operands, regardless of the certified representatives read. -/
theorem UnifyCandidateRel.support_of_certified_reads {incoming output : Bindings}
    {table : TypeSubst} {target pattern : Atom}
    (certificate : ReadoutCertificate incoming table)
    (candidate : UnifyCandidateRel (table.apply target) (table.apply pattern) incoming output)
    (name : String) :
    name ∈ specBindingVars output ↔
      name ∈ specBindingVars incoming ∨ name ∈ TypeSubst.typeVars target ∨ name ∈ TypeSubst.typeVars pattern := by
  obtain ⟨matched,matching,merged⟩ := candidate
  rw [merged.support name,QueryBindingProjection.SourceSupport.match_support matching name]
  have targetSupport := certificate.support_union_apply target name
  have patternSupport := certificate.support_union_apply pattern name
  tauto

/-- An actual future unification preserves full theory/support agreement
between two certified frames. Each side keeps its chosen readout table. -/
theorem UnifyCandidateRel.output_agreement_of_certified_reads
    {leftBefore rightBefore leftAfter rightAfter : Bindings} {leftTable rightTable : TypeSubst}
    {target pattern : Atom}
    (incoming : BindingSourceAgreement leftBefore rightBefore)
    (leftCertificate : ReadoutCertificate leftBefore leftTable)
    (rightCertificate : ReadoutCertificate rightBefore rightTable)
    (left : UnifyCandidateRel (leftTable.apply target) (leftTable.apply pattern) leftBefore leftAfter)
    (right : UnifyCandidateRel (rightTable.apply target) (rightTable.apply pattern) rightBefore rightAfter) :
    BindingSourceAgreement leftAfter rightAfter := by
  constructor
  · intro valuation
    rw [left.solutions_of_certified_reads leftCertificate valuation,
      right.solutions_of_certified_reads rightCertificate valuation,incoming.solutions valuation]
  · intro name
    rw [left.support_of_certified_reads leftCertificate name,
      right.support_of_certified_reads rightCertificate name,incoming.support name]

/-- Success existence agrees before either side selects an output record.
This is a local operation law, not an assumed evaluator simulation. -/
theorem certified_unify_exists_iff {leftBefore rightBefore : Bindings}
    {leftTable rightTable : TypeSubst} (incoming : BindingSourceAgreement leftBefore rightBefore)
    (leftCertificate : ReadoutCertificate leftBefore leftTable)
    (rightCertificate : ReadoutCertificate rightBefore rightTable) (target pattern : Atom) :
    (∃ output, UnifyCandidateRel (leftTable.apply target) (leftTable.apply pattern) leftBefore output) ↔
      ∃ output, UnifyCandidateRel (rightTable.apply target) (rightTable.apply pattern) rightBefore output := by
  rw [unifyCandidate_exists_iff_equation_model,unifyCandidate_exists_iff_equation_model]
  constructor
  · rintro ⟨valuation,model,equation⟩
    have otherModel := (incoming.solutions valuation).mp model
    refine ⟨valuation,otherModel,?_⟩
    rw [rightCertificate.preserves_model valuation otherModel target,
      rightCertificate.preserves_model valuation otherModel pattern]
    simpa only [leftCertificate.preserves_model valuation model target,
      leftCertificate.preserves_model valuation model pattern] using equation
  · rintro ⟨valuation,model,equation⟩
    have otherModel := (incoming.solutions valuation).mpr model
    refine ⟨valuation,otherModel,?_⟩
    rw [leftCertificate.preserves_model valuation otherModel target,
      leftCertificate.preserves_model valuation otherModel pattern]
    simpa only [rightCertificate.preserves_model valuation model target,
      rightCertificate.preserves_model valuation model pattern] using equation

theorem certified_unify_noMatch_iff {leftBefore rightBefore : Bindings}
    {leftTable rightTable : TypeSubst} (incoming : BindingSourceAgreement leftBefore rightBefore)
    (leftCertificate : ReadoutCertificate leftBefore leftTable)
    (rightCertificate : ReadoutCertificate rightBefore rightTable) (target pattern : Atom) :
    UnifyNoMatchRel (leftTable.apply target) (leftTable.apply pattern) leftBefore ↔
      UnifyNoMatchRel (rightTable.apply target) (rightTable.apply pattern) rightBefore := by
  simpa only [not_exists,UnifyNoMatchRel] using
    not_congr (certified_unify_exists_iff incoming leftCertificate rightCertificate target pattern)

/-- A successful operation constructs its counterpart on the other certified
presentation. The counterpart is not a premise of representation independence. -/
theorem UnifyCandidateRel.transport_certified_reads
    {leftBefore rightBefore leftAfter : Bindings} {leftTable rightTable : TypeSubst}
    {target pattern : Atom}
    (incoming : BindingSourceAgreement leftBefore rightBefore)
    (leftCertificate : ReadoutCertificate leftBefore leftTable)
    (rightCertificate : ReadoutCertificate rightBefore rightTable)
    (left : UnifyCandidateRel (leftTable.apply target) (leftTable.apply pattern) leftBefore leftAfter) :
    ∃ rightAfter,
      UnifyCandidateRel (rightTable.apply target) (rightTable.apply pattern) rightBefore rightAfter ∧
      BindingSourceAgreement leftAfter rightAfter := by
  obtain ⟨rightAfter,right⟩ :=
    (certified_unify_exists_iff incoming leftCertificate rightCertificate target pattern).mp ⟨_,left⟩
  exact ⟨rightAfter,right,left.output_agreement_of_certified_reads incoming
    leftCertificate rightCertificate right⟩

/-- Both actual operations earn their new readout certificates. The later
tables absorb all earlier pending reads, and preserve the entire joint packet
observation, including repeated caller and return variables. -/
theorem UnifyCandidateRel.certifies_paired_pending
    {leftBefore rightBefore leftAfter : Bindings} {leftTable rightTable : TypeSubst}
    {target pattern : Atom}
    (incoming : BindingSourceAgreement leftBefore rightBefore)
    (leftCertificate : ReadoutCertificate leftBefore leftTable)
    (rightCertificate : ReadoutCertificate rightBefore rightTable)
    (left : UnifyCandidateRel (leftTable.apply target) (leftTable.apply pattern) leftBefore leftAfter) :
    ∃ rightAfter leftNext rightNext,
      UnifyCandidateRel (rightTable.apply target) (rightTable.apply pattern) rightBefore rightAfter ∧
      BindingSourceAgreement leftAfter rightAfter ∧
      ReadoutCertificate leftAfter leftNext ∧ ReadoutCertificate rightAfter rightNext ∧
      ∀ pending : List Atom,
        (pending.map leftTable.apply).map leftNext.apply = pending.map leftNext.apply ∧
        (pending.map rightTable.apply).map rightNext.apply = pending.map rightNext.apply ∧
        observedTuples leftAfter ((pending.map leftTable.apply).map leftNext.apply) =
          observedTuples rightAfter ((pending.map rightTable.apply).map rightNext.apply) := by
  obtain ⟨rightAfter,right,outputs⟩ := left.transport_certified_reads incoming
    leftCertificate rightCertificate
  obtain ⟨_,_,leftMerge⟩ := left
  have ⟨_,_,rightMerge⟩ := right
  obtain ⟨leftNext,leftCertified,leftAbsorbs⟩ := leftMerge.certifies_pending leftCertificate
  obtain ⟨rightNext,rightCertified,rightAbsorbs⟩ := rightMerge.certifies_pending rightCertificate
  refine ⟨rightAfter,leftNext,rightNext,right,outputs,leftCertified,rightCertified,?_⟩
  intro pending
  refine ⟨leftAbsorbs pending,rightAbsorbs pending,?_⟩
  rw [leftAbsorbs pending,rightAbsorbs pending,
    leftCertified.observedTuples_eq,rightCertified.observedTuples_eq]
  exact (outputs.theoryEquivAt (TypeSubst.typeVarsList pending)).observedTuples_eq pending
    (fun _ present => present)

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.CertifiedUnifyControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation Spec.Eval.Steps
open AliasReadout.Controls

private def firstTable : TypeSubst := [("a",.var "b")]
private def secondTable : TypeSubst := [("b",.var "a")]

private theorem first_certificate : ReadoutCertificate forwardAlias firstTable := by
  apply ReadoutCertificate.of_normal_theory
  · simp [firstTable,TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars]
  · intro valuation
    simp [TypeSubstSatisfied,TypeBindingSatisfied,firstTable,forwardAlias,applyTypeValuation]

private theorem second_certificate : ReadoutCertificate backwardAlias secondTable := by
  apply ReadoutCertificate.of_normal_theory
  · simp [secondTable,TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars]
  · intro valuation
    simp [TypeSubstSatisfied,TypeBindingSatisfied,secondTable,backwardAlias,applyTypeValuation]

/-- Opposite certified alias representatives take the same next constraint
and preserve one correlated caller/return packet. Neither the second output
nor the two later readout certificates is supplied by the control. -/
theorem opposite_aliases_take_next_unification :
    firstTable.apply (.var "a") ≠ secondTable.apply (.var "a") ∧
    ∃ leftAfter rightAfter leftNext rightNext,
      UnifyCandidateRel (firstTable.apply (.var "a")) (.symbol "T") forwardAlias leftAfter ∧
      UnifyCandidateRel (secondTable.apply (.var "a")) (.symbol "T") backwardAlias rightAfter ∧
      BindingSourceAgreement leftAfter rightAfter ∧
      ReadoutCertificate leftAfter leftNext ∧ ReadoutCertificate rightAfter rightNext ∧
      observedTuples leftAfter
          (([Atom.var "a",.var "b",.var "a"].map firstTable.apply).map leftNext.apply) =
        observedTuples rightAfter
          (([Atom.var "a",.var "b",.var "a"].map secondTable.apply).map rightNext.apply) := by
  refine ⟨by simp [firstTable,secondTable,TypeSubst.apply,TypeSubst.lookup],?_⟩
  obtain ⟨leftAfter,left⟩ := (unifyCandidate_exists_iff_equation_model
    (firstTable.apply (.var "a")) (.symbol "T") forwardAlias).mpr
      ⟨fun _ => .symbol "T",by simp [TypeBindingSatisfied,forwardAlias],by
        simp [firstTable,TypeSubst.apply,TypeSubst.lookup,applyTypeValuation]⟩
  obtain ⟨rightAfter,leftNext,rightNext,right,agreement,leftCertified,rightCertified,pending⟩ :=
    UnifyCandidateRel.certifies_paired_pending (target := .var "a") (pattern := .symbol "T")
      reordered_aliases_agree first_certificate second_certificate
        (by simpa only [TypeSubst.apply] using left)
  have right' : UnifyCandidateRel (secondTable.apply (.var "a")) (.symbol "T") backwardAlias rightAfter := by
    simpa only [TypeSubst.apply] using right
  exact ⟨leftAfter,rightAfter,leftNext,rightNext,left,right',agreement,leftCertified,rightCertified,
    (pending [Atom.var "a",.var "b",.var "a"]).2.2⟩

private def uncertifiedTable : TypeSubst := [("a",.symbol "Wrong")]

/-- Normal table shape alone cannot justify future-operation transport.
The unearned assignment changes an actual source success into no-match. -/
theorem normal_table_without_certificate_changes_success :
    uncertifiedTable.Normal ∧
      (∃ output, UnifyCandidateRel (.var "a") (.symbol "Right") Bindings.empty output) ∧
      UnifyNoMatchRel (uncertifiedTable.apply (.var "a")) (.symbol "Right") Bindings.empty ∧
      ¬ReadoutCertificate Bindings.empty uncertifiedTable := by
  refine ⟨by simp [uncertifiedTable,TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars],?_,?_,?_⟩
  · exact (unifyCandidate_exists_iff_equation_model _ _ _).mpr
      ⟨fun _ => .symbol "Right",by simp [TypeBindingSatisfied,Bindings.empty],by simp [applyTypeValuation]⟩
  · intro output candidate
    have ⟨_,_,merged⟩ := candidate
    obtain ⟨valuation,model⟩ := merged.2
    have equation := ((candidate.solutions valuation).mp model).1
    simp [uncertifiedTable,TypeSubst.apply,TypeSubst.lookup,applyTypeValuation] at equation
  · intro certificate
    have unbound := certificate.lookup_none_of_outside (name := "a")
      (by simp [specBindingVars,Bindings.empty])
    simp [uncertifiedTable,TypeSubst.lookup] at unbound

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.CertifiedUnifyControls
