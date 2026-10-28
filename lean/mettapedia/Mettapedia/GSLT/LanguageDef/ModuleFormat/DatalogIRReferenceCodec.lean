import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPrimitiveRows

/-! Expansion of the physical reference pool recovers semantic IR data.
The dictionary is the one emitted by executable preparation. No source
characters or alternate runtime representation are introduced here. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem relation_value_disjoint (first second : Nat) : relationRef first ≠ valueRef second := by
  intro same
  have text := Pattern.fvar.inj same
  have different := congrArg (fun word : String => (word.toList.drop 3).head?) text
  simp only [String.toList_append] at different
  change some 'r' = some 'v' at different
  exact (by decide : ('r' : Char) ≠ 'v') (Option.some.inj different)

private theorem expand_reference (bindings : Bindings) (name : String) (value : Pattern)
    (present : (name,value) ∈ bindings)
    (unique : ∀ pair ∈ bindings, pair.1 = name → pair.2 = value) :
    applyBindings bindings (.fvar name) = value := by
  cases found : bindings.find? (·.1 == name) with
  | none =>
    have missing := List.find?_eq_none.mp found (name,value) present
    simp at missing
  | some pair =>
    have member := List.mem_of_find?_eq_some found
    have key : pair.1 = name := by simpa using List.find?_some found
    simpa [applyBindings,found] using unique pair member key

theorem relation_dictionary_expands (pools : Join.Pools) (index : Nat) (name : QualifiedName)
    (atIndex : pools.relations[index]? = some name) :
    applyBindings (dictionary pools) (relationRef index) = IRCodec.relation name := by
  apply expand_reference
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨(name,index),List.mk_mem_zipIdx_iff_getElem?.mpr atIndex,rfl⟩
  · intro pair member key
    rcases List.mem_append.mp member with relation | literal
    · obtain ⟨⟨other,otherIndex⟩,inside,same⟩ := List.mem_map.mp relation
      subst pair
      have sameIndex := relationRef_injective (congrArg Pattern.fvar key)
      subst otherIndex
      have otherAt := List.mk_mem_zipIdx_iff_getElem?.mp inside
      have sameName := Option.some.inj (otherAt.symm.trans atIndex)
      cases sameName
      rfl
    · obtain ⟨⟨other,otherIndex⟩,_,same⟩ := List.mem_map.mp literal
      subst pair
      exact False.elim (relation_value_disjoint index otherIndex (congrArg Pattern.fvar key).symm)

theorem value_dictionary_expands (pools : Join.Pools) (index : Nat) (value : Value)
    (atIndex : pools.literals[index]? = some value) :
    applyBindings (dictionary pools) (valueRef index) = IRCodec.value value := by
  apply expand_reference
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨(value,index),List.mk_mem_zipIdx_iff_getElem?.mpr atIndex,rfl⟩
  · intro pair member key
    rcases List.mem_append.mp member with relation | literal
    · obtain ⟨⟨other,otherIndex⟩,_,same⟩ := List.mem_map.mp relation
      subst pair
      exact False.elim (relation_value_disjoint otherIndex index (congrArg Pattern.fvar key))
    · obtain ⟨⟨other,otherIndex⟩,inside,same⟩ := List.mem_map.mp literal
      subst pair
      have sameIndex := valueRef_injective (congrArg Pattern.fvar key)
      subst otherIndex
      have otherAt := List.mk_mem_zipIdx_iff_getElem?.mp inside
      have sameValue := Option.some.inj (otherAt.symm.trans atIndex)
      cases sameValue
      rfl

private theorem index_reads_value {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (value : α) (index : Nat) (found : items.idxOf? value = some index) :
    items[index]? = some value := by
  obtain ⟨bound,same,_⟩ := List.idxOf?_eq_some_iff.mp found
  simp [bound,same]

private theorem encode_values_defined (pools : Join.Pools) (values : List Value)
    (available : ∀ value ∈ values, value ∈ pools.literals) :
    ∃ encoded, values.mapM (fun value => valueRef <$> pools.literals.idxOf? value) = some encoded := by
  induction values with
  | nil => exact ⟨[],rfl⟩
  | cons value rest ih =>
    obtain ⟨index,first⟩ := Option.isSome_iff_exists.mp ((List.isSome_idxOf?).mpr (available value (by simp)))
    obtain ⟨codes,tail⟩ := ih (fun other member => available other (by simp [member]))
    refine ⟨valueRef index :: codes,?_⟩
    simp only [List.mapM_cons,first]
    change (rest.mapM (fun value => valueRef <$> pools.literals.idxOf? value)).bind
      (fun rest => some (valueRef index :: rest)) = some (valueRef index :: codes)
    rw [tail]
    rfl

theorem fact?_defined (pools : Join.Pools) (source : GroundFact)
    (relation : source.relation ∈ pools.relations)
    (values : ∀ value ∈ source.values, value ∈ pools.literals) :
    ∃ encoded, fact? pools source = some encoded := by
  obtain ⟨index,found⟩ := Option.isSome_iff_exists.mp ((List.isSome_idxOf?).mpr relation)
  obtain ⟨codes,encoded⟩ := encode_values_defined pools source.values values
  refine ⟨.apply "GroundFact" [relationRef index,.apply "GroundTuple" [Join.vector codes]],?_⟩
  simp only [fact?,found]
  change (source.values.mapM (fun value => valueRef <$> pools.literals.idxOf? value)).bind
    (fun values => some (Pattern.apply "GroundFact" [relationRef index,.apply "GroundTuple" [Join.vector values]])) = _
  rw [encoded]
  rfl

theorem input_fact_encodes (program : Program) (known : List GroundFact) (source : GroundFact)
    (present : source ∈ known) : ∃ encoded, fact? (Join.Program.pools program known) source = some encoded := by
  apply fact?_defined
  · apply List.mem_dedup.mpr
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨source,present,rfl⟩
  · intro value member
    apply List.mem_dedup.mpr
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨source,present,member⟩

theorem encoded_values_expand (pools : Join.Pools) (values : List Value) (encoded : List Pattern)
    (formed : values.mapM (fun value => valueRef <$> pools.literals.idxOf? value) = some encoded) :
    encoded.map (applyBindings (dictionary pools)) = values.map IRCodec.value := by
  induction values generalizing encoded with
  | nil =>
    have same : encoded = [] := by simpa using formed.symm
    subst encoded
    rfl
  | cons value rest ih =>
    cases first : pools.literals.idxOf? value with
    | none => simp [List.mapM_cons,first] at formed
    | some index =>
      simp only [List.mapM_cons,first] at formed
      change (rest.mapM (fun value => valueRef <$> pools.literals.idxOf? value)).bind
        (fun codes => some (valueRef index :: codes)) = some encoded at formed
      cases tail : rest.mapM (fun value => valueRef <$> pools.literals.idxOf? value) with
      | none => rw [tail] at formed; cases formed
      | some codes =>
        rw [tail] at formed
        have same : valueRef index :: codes = encoded := Option.some.inj formed
        subst encoded
        change applyBindings (dictionary pools) (valueRef index) ::
          codes.map (applyBindings (dictionary pools)) = IRCodec.value value :: rest.map IRCodec.value
        rw [value_dictionary_expands pools index value (index_reads_value _ _ _ first),ih codes tail]

private theorem expand_node (bindings : Bindings) (head : String) (children : List Pattern) :
    applyBindings bindings (.apply head children) = .apply head (children.map (applyBindings bindings)) := by
  simp only [applyBindings]

private theorem expand_vector (bindings : Bindings) (children : List Pattern) :
    applyBindings bindings (.collection .vec children none) =
      .collection .vec (children.map (applyBindings bindings)) none := by
  simp only [applyBindings,List.append_nil]

theorem fact_expands (pools : Join.Pools) (source : GroundFact) (encoded : Pattern)
    (formed : fact? pools source = some encoded) :
    applyBindings (dictionary pools) encoded = IRCodec.groundFact source := by
  cases relation : pools.relations.idxOf? source.relation with
  | none => simp [fact?,relation] at formed
  | some index =>
    simp only [fact?,relation] at formed
    change (source.values.mapM (fun value => valueRef <$> pools.literals.idxOf? value)).bind
      (fun codes => some (.apply "GroundFact" [relationRef index,.apply "GroundTuple" [Join.vector codes]])) =
      some encoded at formed
    cases values : source.values.mapM (fun value => valueRef <$> pools.literals.idxOf? value) with
    | none => rw [values] at formed; cases formed
    | some codes =>
      rw [values] at formed
      have same : Pattern.apply "GroundFact" [relationRef index,.apply "GroundTuple" [Join.vector codes]] = encoded :=
        Option.some.inj formed
      subst encoded
      simp only [Join.vector,expand_node,expand_vector,List.map_cons,List.map_nil,
        relation_dictionary_expands pools index source.relation (index_reads_value _ _ _ relation),
        encoded_values_expand pools source.values codes values]
      rfl

theorem fact_encoding_injective (pools : Join.Pools) (first second : GroundFact) (encoded : Pattern)
    (left : fact? pools first = some encoded) (right : fact? pools second = some encoded) : first = second := by
  have same := (fact_expands pools first encoded left).symm.trans (fact_expands pools second encoded right)
  have decoded := congrArg IRCodec.groundFact? same
  simpa using decoded

theorem decodeFact?_roundtrip (prepared : Prepared) (source : GroundFact) (encoded : Pattern)
    (formed : fact? prepared.vocabulary source = some encoded) :
    decodeFact? prepared encoded = some source := by
  unfold decodeFact?
  rw [fact_expands prepared.vocabulary source encoded formed]
  exact IRCodec.groundFact_roundtrip source

namespace Controls

def references : Join.Pools := ⟨[["Relation"],["Other"]],[.symbol "-1",.number (-1),.unsigned 1]⟩
def stringFact : GroundFact := ⟨["Relation"],[.symbol "-1"]⟩
def integerFact : GroundFact := ⟨["Relation"],[.number (-1)]⟩

#guard (fact? references stringFact).isSome
#guard (fact? references integerFact).isSome
#guard fact? references stringFact != fact? references integerFact
#guard (fact? references ⟨["Missing"],[.number (-1)]⟩).isNone
#guard (fact? references ⟨["Relation"],[.number 7]⟩).isNone

end Controls

#print axioms relation_value_disjoint
#print axioms relation_dictionary_expands
#print axioms value_dictionary_expands
#print axioms fact_expands
#print axioms fact_encoding_injective
#print axioms decodeFact?_roundtrip
#print axioms input_fact_encodes

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable
