import Mettapedia.Languages.OpenTheory.SignatureFormation

/-!
# Schema matching over the shared HOL type substitution

The authored HOL library matches a declaration schema against an occurrence.
Its assignments use the existing simultaneous substitution, with first-match
lookup. Matching extends this table without changing any earlier assignment;
it never unifies distinct parameters or substitutes inside a replacement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.TypeMatching

open Mettapedia.Languages.OpenTheory
open SignatureFormation

mutual
  def matchType (schema occurrence : Ty) (assignments : TypeSubst) : Option TypeSubst :=
    match schema with
    | .var name =>
        match assignments.lookup name with
        | none => some ⟨(name, occurrence) :: assignments.entries⟩
        | some previous => if Ty.same previous occurrence then some assignments else none
    | .op operator arguments =>
        match occurrence with
        | .var _ => none
        | .op target values =>
            if TypeOp.same operator target then matchTypes arguments values assignments else none
  termination_by sizeOf schema

  def matchTypes (schemas instances : List Ty) (assignments : TypeSubst) : Option TypeSubst :=
    match schemas, instances with
    | [], [] => some assignments
    | first :: rest, value :: values => do
        let next ← matchType first value assignments
        matchTypes rest values next
    | _, _ => none
  termination_by sizeOf schemas
end

/-- A successful match retains every existing first-match assignment. -/
def Extends (before after : TypeSubst) : Prop :=
  ∀ name value, before.lookup name = some value → after.lookup name = some value

theorem Extends.refl (assignments : TypeSubst) : Extends assignments assignments :=
  fun _ _ found => found

theorem Extends.trans {first second third : TypeSubst}
    (left : Extends first second) (right : Extends second third) : Extends first third :=
  fun name value found => right name value (left name value found)

private theorem extends_cons (assignments : TypeSubst) (name : Name) (occurrence : Ty)
    (fresh : assignments.lookup name = none) :
    Extends assignments ⟨(name, occurrence) :: assignments.entries⟩ := by
  intro other value found
  have different : other ≠ name := by
    intro same
    subst other
    rw [fresh] at found
    cases found
  simpa [TypeSubst.lookup, List.lookup, different, beq_eq_decide] using found

/-- A type already realized by an assignment table stays realized by a
successful extension. Only assigned variables may occur in this statement. -/
theorem apply_preserved {before after : TypeSubst} (extended : Extends before after)
    {schema occurrence : Ty} (realized : before.apply schema = occurrence)
    (assigned : ∀ name, before.lookup name = none → name ∉ schema.typeVariables) :
    after.apply schema = occurrence := by
  rw [← realized]
  clear realized occurrence
  cases schema with
  | var name =>
      cases found : before.lookup name with
      | none => exact False.elim (assigned name found (by simp [Ty.typeVariables]))
      | some value => simp [found, extended name value found]
  | op operator arguments =>
      simp only [TypeSubst.apply]
      congr 1
      apply List.map_congr_left
      intro argument member
      apply apply_preserved extended rfl
      intro name absent present
      exact assigned name absent (by simpa only [Ty.typeVariables] using (mem_typeVariablesList name arguments).mpr ⟨argument, member, present⟩)
termination_by sizeOf schema

/-- Every parameter occurring in the matched schema has an explicit assignment
after matching, including identity assignments. -/
def Assigned (assignments : TypeSubst) (schema : Ty) : Prop :=
  ∀ name, assignments.lookup name = none → name ∉ schema.typeVariables

mutual
  theorem matchType_sound {schema occurrence : Ty} {before after : TypeSubst}
      (matched : matchType schema occurrence before = some after) :
      Extends before after ∧ Assigned after schema ∧ after.apply schema = occurrence := by
    cases schema with
    | var name =>
        cases found : before.lookup name with
        | none =>
            simp only [matchType, found, Option.some.injEq] at matched
            subst after
            refine ⟨extends_cons before name occurrence found, ?_, ?_⟩
            · intro other absent present
              have same : other = name := by simpa [Ty.typeVariables] using present
              subst other
              simp [TypeSubst.lookup, List.lookup] at absent
            · simp [TypeSubst.lookup, List.lookup]
        | some previous =>
            simp only [matchType, found] at matched
            split at matched
            · rename_i same
              have equal := (Ty.same_eq_true_iff previous occurrence).mp same
              have tables := Option.some.inj matched
              subst after
              refine ⟨Extends.refl before, ?_, ?_⟩
              · intro other absent present
                have names : other = name := by simpa [Ty.typeVariables] using present
                subst other
                rw [found] at absent
                cases absent
              · simp [found, equal]
            · cases matched
    | op operator arguments =>
        cases occurrence with
        | var name => simp [matchType] at matched
        | op target values =>
            simp only [matchType] at matched
            split at matched
            · rename_i same
              have equal := (TypeOp.same_eq_true_iff operator target).mp same
              obtain ⟨extended, assigned, realized⟩ := matchTypes_sound matched
              refine ⟨extended, ?_, ?_⟩
              · intro name absent present
                simp only [Ty.typeVariables, mem_typeVariablesList] at present
                obtain ⟨argument, member, present⟩ := present
                exact assigned argument member name absent present
              · simp only [TypeSubst.apply, equal, realized]
            · cases matched
  termination_by sizeOf schema

  theorem matchTypes_sound {schemas instances : List Ty} {before after : TypeSubst}
      (matched : matchTypes schemas instances before = some after) :
      Extends before after ∧ (∀ schema ∈ schemas, Assigned after schema) ∧
        schemas.map after.apply = instances := by
    cases schemas with
    | nil =>
        cases instances with
        | nil =>
            simp only [matchTypes, Option.some.injEq] at matched
            subst after
            exact ⟨Extends.refl before, by simp, rfl⟩
        | cons => simp [matchTypes] at matched
    | cons first rest =>
        cases instances with
        | nil => simp [matchTypes] at matched
        | cons value values =>
            cases nextFound : matchType first value before with
            | none => simp [matchTypes, nextFound] at matched
            | some next =>
                simp only [matchTypes, nextFound] at matched
                obtain ⟨firstExtension, firstAssigned, firstRealized⟩ := matchType_sound nextFound
                obtain ⟨restExtension, restAssigned, restRealized⟩ := matchTypes_sound matched
                refine ⟨firstExtension.trans restExtension, ?_, ?_⟩
                · intro schema member
                  rcases List.mem_cons.mp member with rfl | member
                  · intro name absent present
                    cases found : next.lookup name with
                    | none => exact firstAssigned name found present
                    | some type => rw [restExtension name type found] at absent; cases absent
                  · exact restAssigned schema member
                · simp only [List.map_cons, restRealized,
                    apply_preserved restExtension firstRealized firstAssigned]
  termination_by sizeOf schemas
end

/-- Constant occurrence admission receives an actual shared substitution
certificate, rather than only the matcher's success bit. -/
theorem matchType_instantiates {schema occurrence : Ty} {before after : TypeSubst}
    (matched : matchType schema occurrence before = some after) : after.apply schema = occurrence :=
  (matchType_sound matched).2.2

/-- A candidate substitution respects all assignments made so far. Identity
assignments need not be stored by that candidate's normalized representation. -/
def Realizes (witness assignments : TypeSubst) : Prop :=
  ∀ name value, assignments.lookup name = some value → witness.apply (.var name) = value

private theorem realizes_cons {witness before : TypeSubst}
    (compatible : Realizes witness before) (name : Name) (occurrence : Ty)
    (realized : witness.apply (.var name) = occurrence) :
    Realizes witness ⟨(name, occurrence) :: before.entries⟩ := by
  intro other value found
  by_cases same : other = name
  · subst other
    have equal : occurrence = value := by simpa [TypeSubst.lookup, List.lookup] using found
    exact realized.trans equal
  · apply compatible other value
    simpa [TypeSubst.lookup, List.lookup, same, beq_eq_decide] using found

mutual
  theorem matchType_complete (witness : TypeSubst) {before : TypeSubst}
      (compatible : Realizes witness before) {schema occurrence : Ty}
      (realized : witness.apply schema = occurrence) :
      ∃ after, matchType schema occurrence before = some after ∧ Realizes witness after := by
    cases schema with
    | var name =>
        cases found : before.lookup name with
        | none =>
            exact ⟨⟨(name, occurrence) :: before.entries⟩,
              by simp [matchType, found], realizes_cons compatible name occurrence realized⟩
        | some previous =>
            have same : previous = occurrence := (compatible name previous found).symm.trans realized
            exact ⟨before, by simp [matchType, found, same], compatible⟩
    | op operator arguments =>
        cases occurrence with
        | var => simp at realized
        | op target values =>
            have decomposition : operator = target ∧ arguments.map witness.apply = values := by
              simpa only [TypeSubst.apply_op, Ty.op.injEq] using realized
            obtain ⟨same, instantiated⟩ := decomposition
            subst target
            obtain ⟨after, matched, retained⟩ := matchTypes_complete witness compatible instantiated
            exact ⟨after, by simpa [matchType] using matched, retained⟩
  termination_by sizeOf schema

  theorem matchTypes_complete (witness : TypeSubst) {before : TypeSubst}
      (compatible : Realizes witness before) {schemas occurrences : List Ty}
      (realized : schemas.map witness.apply = occurrences) :
      ∃ after, matchTypes schemas occurrences before = some after ∧ Realizes witness after := by
    cases schemas with
    | nil =>
        have empty : occurrences = [] := by simpa using realized.symm
        subst occurrences
        exact ⟨before, by simp [matchTypes], compatible⟩
    | cons first rest =>
        cases occurrences with
        | nil => simp at realized
        | cons value values =>
            obtain ⟨head, tail⟩ := List.cons.inj realized
            obtain ⟨next, firstMatched, nextCompatible⟩ := matchType_complete witness compatible head
            obtain ⟨after, restMatched, retained⟩ := matchTypes_complete witness nextCompatible tail
            exact ⟨after, by simp [matchTypes, firstMatched, restMatched], retained⟩
  termination_by sizeOf schemas
end

/-- Admission by the matcher is exactly simultaneous instantiation of the
schema, including polymorphism and repeated formal parameters. -/
theorem matching_iff_instance (schema occurrence : Ty) :
    (∃ after, matchType schema occurrence TypeSubst.empty = some after) ↔
      ∃ witness : TypeSubst, witness.apply schema = occurrence := by
  constructor
  · rintro ⟨after, matched⟩
    exact ⟨after, matchType_instantiates matched⟩
  · rintro ⟨witness, realized⟩
    obtain ⟨after, matched, _⟩ := matchType_complete witness (before := TypeSubst.empty)
      (by simp [Realizes, TypeSubst.empty, TypeSubst.lookup]) realized
    exact ⟨after, matched⟩

/-- Every stored replacement remains a formed carrier in the selected
signature. This obligation does not assert carrier inhabitation. -/
def AssignmentsFormed (signature : Signature) (assignments : TypeSubst) : Prop :=
  ∀ name value, assignments.lookup name = some value → TypeFormed signature value

mutual
  theorem matchType_formed (signature : Signature) {before after : TypeSubst}
      (beforeFormed : AssignmentsFormed signature before) {schema occurrence : Ty}
      (occurrenceFormed : TypeFormed signature occurrence)
      (matched : matchType schema occurrence before = some after) :
      AssignmentsFormed signature after := by
    cases schema with
    | var name =>
        cases found : before.lookup name with
        | none =>
            simp only [matchType, found, Option.some.injEq] at matched
            subst after
            intro other value registered
            by_cases same : other = name
            · subst other
              have equal : occurrence = value := by
                simpa [TypeSubst.lookup, List.lookup] using registered
              exact equal ▸ occurrenceFormed
            · apply beforeFormed other value
              simpa [TypeSubst.lookup, List.lookup, same, beq_eq_decide] using registered
        | some previous =>
            simp only [matchType, found] at matched
            split at matched
            · have same := Option.some.inj matched
              exact same ▸ beforeFormed
            · cases matched
    | op operator arguments =>
        cases occurrence with
        | var => simp [matchType] at matched
        | op target values =>
            simp only [matchType] at matched
            split at matched
            · have formedValues : ∀ value ∈ values, TypeFormed signature value :=
                by simp only [TypeFormed] at occurrenceFormed; exact occurrenceFormed.2
              exact matchTypes_formed signature beforeFormed formedValues matched
            · cases matched
  termination_by sizeOf schema

  theorem matchTypes_formed (signature : Signature) {before after : TypeSubst}
      (beforeFormed : AssignmentsFormed signature before) {schemas occurrences : List Ty}
      (occurrencesFormed : ∀ occurrence ∈ occurrences, TypeFormed signature occurrence)
      (matched : matchTypes schemas occurrences before = some after) :
      AssignmentsFormed signature after := by
    cases schemas with
    | nil =>
        cases occurrences with
        | nil =>
            have same : before = after := by simpa [matchTypes] using matched
            exact same ▸ beforeFormed
        | cons => simp [matchTypes] at matched
    | cons first rest =>
        cases occurrences with
        | nil => simp [matchTypes] at matched
        | cons value values =>
            cases found : matchType first value before with
            | none => simp [matchTypes, found] at matched
            | some next =>
                have nextFormed := matchType_formed signature beforeFormed
                  (occurrencesFormed value List.mem_cons_self) found
                exact matchTypes_formed signature nextFormed
                  (fun occurrence member => occurrencesFormed occurrence (List.mem_cons_of_mem _ member))
                  (by simpa [matchTypes, found] using matched)
  termination_by sizeOf schemas
end

theorem constant_admission_iff (signature : Signature) (constant : Const) (schema occurrence : Ty)
    (registered : signature.constants constant = some schema) :
    (∃ after, matchType schema occurrence TypeSubst.empty = some after) ↔
      ConstantInstance signature constant occurrence := by
  rw [matching_iff_instance]
  constructor
  · rintro ⟨witness, realized⟩
    exact ⟨schema, witness, registered, realized⟩
  · rintro ⟨other, witness, found, realized⟩
    have same : other = schema := Option.some.inj (found.symm.trans registered)
    exact ⟨witness, same ▸ realized⟩

theorem repeated_parameter_conflict (name : Name) (left right : Ty)
    (different : Ty.same left right = false) :
    matchTypes [.var name, .var name] [left, right] TypeSubst.empty = none := by
  simp [matchTypes, matchType, TypeSubst.empty, TypeSubst.lookup, List.lookup, different]

theorem repeated_parameter_agrees (name : Name) (type : Ty) :
    matchTypes [.var name, .var name] [type, type] TypeSubst.empty =
      some ⟨[(name, type)]⟩ := by
  simp [matchTypes, matchType, TypeSubst.empty, TypeSubst.lookup, List.lookup,
    Ty.same_eq_true_iff]

end Mettapedia.Languages.HOLLight.TypeMatching
