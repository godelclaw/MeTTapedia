import Mettapedia.Languages.OpenTheory.Binding

/-!
# Opening the final named binder

Elaboration resolves the nearest variable with the same name and type.
Opening its final context entry by the corresponding free variable recovers
elaboration in the original context, including beneath shadowing binders.
This connects positional opening to the named body returned by source BETA.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

theorem boundIndex_lt_length {sourceVar : SourceVar} {binders : List SourceVar}
    {index : Nat} (found : boundIndex sourceVar binders = some index) :
    index < binders.length := by
  exact (List.getElem?_eq_some_iff.mp (DBTerm.boundIndex_preserves_var found)).1

theorem boundIndex_append_last (sourceVar needle : SourceVar) (binders : List SourceVar) :
    boundIndex sourceVar (binders ++ [needle]) =
      match boundIndex sourceVar binders with
      | some index => some index
      | none => if sourceVarSame sourceVar needle then some binders.length else none := by
  induction binders with
  | nil => simp [boundIndex]
  | cons binder binders ih =>
      by_cases same : sourceVar = binder
      · simp [boundIndex, same]
      · simp only [List.cons_append, boundIndex, sourceVarSame_eq_true_iff,
          same, ↓reduceIte]
        rw [ih]
        cases found : boundIndex sourceVar binders <;>
          by_cases last : sourceVar = needle <;> simp [last]

namespace SourceTerm

theorem instantiateAt_toDB_append_last (source : SourceTerm) (binders : List SourceVar)
    (needle : SourceVar) :
    DBTerm.instantiateAt (.free needle) binders.length
        (source.toDB (binders ++ [needle])) = source.toDB binders := by
  cases source with
  | const constant type => simp only [SourceTerm.toDB, DBTerm.instantiateAt]
  | var name type =>
      let sourceVar : SourceVar := ⟨name, type⟩
      simp only [SourceTerm.toDB]
      change DBTerm.instantiateAt (.free needle) binders.length
          (match boundIndex sourceVar (binders ++ [needle]) with
           | some index => .bound index | none => .free sourceVar) =
        (match boundIndex sourceVar binders with
         | some index => .bound index | none => .free sourceVar)
      rw [boundIndex_append_last]
      cases found : boundIndex sourceVar binders with
      | some index =>
          have different : index ≠ binders.length :=
            Nat.ne_of_lt (boundIndex_lt_length found)
          simp [DBTerm.instantiateAt, different]
      | none =>
          by_cases same : sourceVar = needle
          · simp [same]
          · simp [same, DBTerm.instantiateAt]
  | app function argument =>
      simp only [SourceTerm.toDB, DBTerm.instantiateAt]
      rw [instantiateAt_toDB_append_last function, instantiateAt_toDB_append_last argument]
  | abs name domain body =>
      simp only [SourceTerm.toDB, DBTerm.instantiateAt]
      congr 1
      simpa only [List.cons_append, List.length_cons] using
        instantiateAt_toDB_append_last body (⟨name, domain⟩ :: binders) needle
termination_by sizeOf source

theorem instantiateAt_toDB_singleton (source : SourceTerm) (needle : SourceVar) :
    DBTerm.instantiateAt (.free needle) 0 (source.toDB [needle]) = source.toDB [] := by
  simpa using instantiateAt_toDB_append_last source [] needle

end SourceTerm

namespace SourceBindingControls

private def x : SourceVar := ⟨.global "x", Ty.bool⟩
private def y : SourceVar := ⟨.global "y", Ty.bool⟩

/-- Opening the outer binder beneath a different binder retains the original
free identity instead of making the occurrence refer to the inner binder. -/
theorem nested_outer_occurrence :
    DBTerm.instantiateAt (.free x) 0
      ((SourceTerm.abs y.name y.ty (.var x.name x.ty)).toDB [x]) =
      .abs y.ty (.free x) := by
  simp [SourceTerm.toDB, boundIndex, x, y, DBTerm.instantiateAt, sourceVarSame, Name.global]

/-- A nearer binder with exactly the same typed identity shadows the entry
being discharged; its positional occurrence is not opened. -/
theorem inner_shadow_retained :
    DBTerm.instantiateAt (.free x) 0
      ((SourceTerm.abs x.name x.ty (.var x.name x.ty)).toDB [x]) =
      .abs x.ty (.bound 0) := by
  simp [SourceTerm.toDB, boundIndex, x, DBTerm.instantiateAt]

/-- Dropping the closed-replacement condition can capture an occurrence.
The executed-opening theorem does not authorize this replacement. -/
theorem open_replacement_captures :
    DBTerm.instantiateAt (.bound 0) 0
      ((SourceTerm.abs y.name y.ty (.var x.name x.ty)).toDB [x]) ≠
      (SourceTerm.abs y.name y.ty (.var x.name x.ty)).toDB [] := by
  simp [SourceTerm.toDB, boundIndex, x, y, DBTerm.instantiateAt, sourceVarSame, Name.global]

end SourceBindingControls

end Mettapedia.Languages.OpenTheory
