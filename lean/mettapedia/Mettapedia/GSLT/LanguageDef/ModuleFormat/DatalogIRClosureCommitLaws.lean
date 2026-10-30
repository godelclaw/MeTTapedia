import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureKeyLaws

/-! A successful batch commit conserves exactly the facts and finite logical
keys represented by its receipts. Replaying a receipt adds no new identity. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine.Conservation

open Mettapedia.OSLF.MeTTaIL Syntax

private instance : LawfulBEq Pattern where
  rfl := by intro value; change decide (value = value) = true; simp
  eq_of_beq := by intro left right same; change decide (left = right) = true at same; exact of_decide_eq_true same

deriving instance ReflBEq, LawfulBEq for Key

private theorem mem_insert {α : Type} [BEq α] [LawfulBEq α] (items : List α) (item wanted : α) :
    wanted ∈ insert items item ↔ wanted ∈ items ∨ wanted = item := by
  by_cases present : item ∈ items
  · simp only [insert,show items.contains item = true from by simpa using present,if_true]
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · simp only [insert,show items.contains item = false from by simpa using present,
      Bool.false_eq_true,if_false,List.mem_append,List.mem_singleton]

theorem commit_observations (prepared : Executable.Prepared) (snapshot : List Pattern)
    (batch : List GeneralOccurrenceSemantics.Receipt) (facts : List Pattern) (keys : List Key)
    (resultFacts : List Pattern) (resultKeys : List Key)
    (committed : commit? prepared snapshot batch facts keys = some (resultFacts,resultKeys)) :
    (∀ fact, fact ∈ resultFacts ↔ fact ∈ facts ∨ fact ∈ batch.map (·.target)) ∧
    (∀ key, key ∈ resultKeys ↔ key ∈ keys ∨ key ∈ batch.filterMap (key? prepared snapshot)) ∧
    ∀ receipt ∈ batch, (key? prepared snapshot receipt).isSome := by
  induction batch generalizing facts keys with
  | nil =>
    have same : (facts,keys) = (resultFacts,resultKeys) := Option.some.inj committed
    cases same
    exact ⟨by simp,by simp,by simp⟩
  | cons first rest ih =>
    cases read : key? prepared snapshot first with
    | none => simp [commit?,read] at committed
    | some firstKey =>
      have front : commit? prepared snapshot (first :: rest) facts keys =
          commit? prepared snapshot rest (insert facts first.target) (insert keys firstKey) := by
        simp only [commit?,read]
        rfl
      rw [front] at committed
      obtain ⟨factMembership,keyMembership,allRead⟩ := ih _ _ committed
      refine ⟨?_,?_,?_⟩
      · intro fact
        rw [factMembership,mem_insert]
        simp only [List.map_cons,List.mem_cons]
        tauto
      · intro key
        rw [keyMembership,mem_insert]
        simp only [List.filterMap_cons,read,List.mem_cons]
        tauto
      · intro receipt member
        rcases List.mem_cons.mp member with rfl | later
        · simp [read]
        · exact allRead receipt later

theorem insert_replayed {α : Type} [BEq α] [LawfulBEq α] (items : List α) (item : α) :
    insert (insert items item) item = insert items item := by
  have present : item ∈ insert items item := (mem_insert items item item).mpr (Or.inr rfl)
  change (if (insert items item).contains item then insert items item else insert items item ++ [item]) = insert items item
  rw [show (insert items item).contains item = true from by simpa using present]
  rfl

#print axioms commit_observations
#print axioms insert_replayed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine.Conservation
