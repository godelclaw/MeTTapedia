import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionOrder
import Mathlib.Data.List.Nodup

/-! Each projected statement retains its source-item position and its position
within a grouped declaration. Erasure agrees with structural projection,
including arbitrary accumulator tails and duplicate statement occurrences. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection

open Mettapedia.OSLF.MeTTaIL.Syntax

structure StatementOrigin where
  itemIndex : Nat
  expansionIndex : Nat
  deriving DecidableEq, Repr

structure LocatedStatement where
  origin : StatementOrigin
  statement : Pattern
  deriving DecidableEq, Repr

namespace Origins

open Reference

def locate (itemIndex : Nat) (statements : List Pattern) : List LocatedStatement :=
  statements.zipIdx.map fun (statement, expansionIndex) =>
    ⟨⟨itemIndex, expansionIndex⟩, statement⟩

def erase (statements : List LocatedStatement) : List Pattern := statements.map (·.statement)

theorem erase_append (first second : List LocatedStatement) :
    erase (first ++ second) = erase first ++ erase second := List.map_append

theorem erase_locate (itemIndex : Nat) (statements : List Pattern) :
    erase (locate itemIndex statements) = statements := by
  simp only [erase, locate, List.map_map]
  exact List.zipIdx_map_fst 0 statements

theorem locate_member {itemIndex : Nat} {statements : List Pattern} {located : LocatedStatement}
    (member : located ∈ locate itemIndex statements) :
    located.origin.itemIndex = itemIndex ∧
      statements[located.origin.expansionIndex]? = some located.statement := by
  change located ∈ statements.zipIdx.map _ at member
  obtain ⟨entry, entryMember, produced⟩ := List.mem_map.mp member
  obtain ⟨statement, index⟩ := entry
  subst located
  exact ⟨rfl, List.mk_mem_zipIdx_iff_getElem?.mp entryMember⟩

theorem locate_origins_nodup (itemIndex : Nat) (statements : List Pattern) :
    ((locate itemIndex statements).map (·.origin)).Nodup := by
  apply List.Nodup.of_map (fun origin => origin.expansionIndex)
  simp only [locate, List.map_map]
  change (statements.zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

def items? (source : Pattern) (itemIndex : Nat) : Option (List LocatedStatement) :=
  match source with
  | .apply "dl-src:items-empty" [] => some []
  | .apply "dl-src:items-more" [head, _, rest] => do
      let tail ← items? rest (itemIndex + 1)
      let values ← itemInto? head []
      pure (locate itemIndex values ++ tail)
  | _ => none

theorem items_erasure (source : Pattern) (itemIndex : Nat) :
    (items? source itemIndex).map erase = itemsInto? source [] := by
  unfold items?
  split
  · rfl
  · rename_i head gap rest
    rw [itemsInto?]
    have tail := items_erasure rest (itemIndex + 1)
    cases selected : items? rest (itemIndex + 1) with
    | none =>
      simp only [selected, Option.map_none] at tail
      simp only [← tail, Option.bind_eq_bind, Option.bind_none, Option.map_none]
    | some values =>
      simp only [selected, Option.map_some] at tail
      rw [← tail]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have append := itemInto_append head [] (erase values)
      rw [List.nil_append] at append
      rw [append]
      cases itemInto? head [] <;>
        simp [erase_append, erase_locate]
  · unfold itemsInto?
    split <;> simp_all
termination_by sizeOf source
decreasing_by simp_all; omega

theorem items_erasure_into (source : Pattern) (itemIndex : Nat) (tail : List Pattern) :
    (items? source itemIndex).map (fun values => erase values ++ tail) =
      itemsInto? source tail := by
  rw [← List.nil_append tail, itemsInto_append, ← items_erasure source itemIndex]
  simp only [Option.map_map, List.nil_append]
  rfl

/-- The position of an actual source item in the authored item spine. -/
inductive ItemAt : Pattern → Nat → Pattern → Prop where
  | here (head gap rest : Pattern) :
      ItemAt (.apply "dl-src:items-more" [head, gap, rest]) 0 head
  | there (head gap rest item : Pattern) (index : Nat) :
      ItemAt rest index item →
      ItemAt (.apply "dl-src:items-more" [head, gap, rest]) (index + 1) item

theorem source_of_member (source : Pattern) (itemIndex : Nat)
    {values : List LocatedStatement} (selected : items? source itemIndex = some values)
    {located : LocatedStatement} (member : located ∈ values) :
    ∃ index item statements,
      located.origin.itemIndex = itemIndex + index ∧ ItemAt source index item ∧
      itemInto? item [] = some statements ∧
      statements[located.origin.expansionIndex]? = some located.statement := by
  unfold items? at selected
  split at selected
  · cases Option.some.inj selected
    cases member
  · rename_i head gap rest
    cases restSelected : items? rest (itemIndex + 1) with
    | none => simp [restSelected, Option.bind_eq_bind] at selected
    | some restValues =>
      cases headSelected : itemInto? head [] with
      | none => simp [restSelected, headSelected, Option.bind_eq_bind] at selected
      | some headValues =>
        simp only [restSelected, headSelected, Option.bind_eq_bind, Option.bind_some] at selected
        cases selected
        rcases List.mem_append.mp member with earlier | later
        · obtain ⟨sameItem, atPosition⟩ := locate_member earlier
          exact ⟨0, head, headValues, by simpa using sameItem, .here head gap rest,
            headSelected, atPosition⟩
        · obtain ⟨index, item, statements, sameItem, atItem, projected, atPosition⟩ :=
            source_of_member rest (itemIndex + 1) restSelected later
          exact ⟨index + 1, item, statements, by omega,
            .there head gap rest item index atItem, projected, atPosition⟩
  · cases selected
termination_by sizeOf source
decreasing_by simp_all; omega

theorem item_index_lower_bound (source : Pattern) (itemIndex : Nat)
    {values : List LocatedStatement} (selected : items? source itemIndex = some values)
    {located : LocatedStatement} (member : located ∈ values) :
    itemIndex ≤ located.origin.itemIndex := by
  obtain ⟨index, item, statements, position, _⟩ := source_of_member source itemIndex selected member
  omega

theorem items_origins_nodup (source : Pattern) (itemIndex : Nat)
    {values : List LocatedStatement} (selected : items? source itemIndex = some values) :
    (values.map (·.origin)).Nodup := by
  unfold items? at selected
  split at selected
  · cases Option.some.inj selected
    exact .nil
  · rename_i head gap rest
    cases restSelected : items? rest (itemIndex + 1) with
    | none => simp [restSelected, Option.bind_eq_bind] at selected
    | some restValues =>
      cases headSelected : itemInto? head [] with
      | none => simp [restSelected, headSelected, Option.bind_eq_bind] at selected
      | some headValues =>
        simp only [restSelected, headSelected, Option.bind_eq_bind, Option.bind_some] at selected
        cases selected
        rw [List.map_append]
        apply List.nodup_append.mpr
        refine ⟨locate_origins_nodup _ _, items_origins_nodup rest _ restSelected, ?_⟩
        intro firstOrigin earlier secondOrigin later same
        obtain ⟨left, leftMember, leftOrigin⟩ := List.mem_map.mp earlier
        obtain ⟨right, rightMember, rightOrigin⟩ := List.mem_map.mp later
        have firstIndex := (locate_member leftMember).1
        have nextIndex := item_index_lower_bound rest (itemIndex + 1) restSelected rightMember
        have equalIndex := congrArg StatementOrigin.itemIndex
          (leftOrigin.trans (same.trans rightOrigin.symm))
        omega
  · cases selected
termination_by sizeOf source
decreasing_by simp_all; omega

def program? : Pattern → Option (List LocatedStatement)
  | .apply "dl-src:program" [_, source] => items? source 0
  | _ => none

theorem program_erasure (source : Pattern) :
    (program? source).map (fun values => program (erase values)) = projectProgram? source := by
  unfold program?
  split
  · rw [projectProgram?, ← items_erasure]
    simp only [Option.map_map]
    rfl
  · unfold projectProgram?
    split <;> simp_all

#print axioms erase_locate
#print axioms locate_member
#print axioms locate_origins_nodup
#print axioms items_erasure
#print axioms items_erasure_into
#print axioms source_of_member
#print axioms items_origins_nodup
#print axioms program_erasure

end Origins
end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection
