import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Nested queries over a store their bodies may write

A nested query reads a store of rows level by level.  A level accepts rows
given the rows chosen at the levels before it.  The innermost body receives
the chosen rows and the current store, and gives a new store and its answers.

The source schedule reads a level once, when its branch is reached, and runs
the branches in the order of that read, each to completion; a branch reads
what the bodies of the branches before it wrote.  A fused schedule joins
levels against the store as it was when the query began, and then runs the
bodies.  Fusing every level, or every level but the last (which is then read
for each joined prefix), are both fused schedules.

Where no body changes the store, every fused schedule agrees with the source
schedule exactly, answers and their order included, and a schedule that
arranges the rows of each read differently only permutes the answers.  Where
a body writes, neither holds: a three-level query that writes a row per
answer answers 16 times on the source schedule, 4 times with its prefix fused
and twice fully fused, and twice on the source schedule over its rows in
reverse order.
-/

namespace Mettapedia.Machines.NestedQuerySchedule

universe u v w
variable {Row : Type u} {Answer : Type v}

/-- One level: which rows it accepts, given the rows chosen before it. -/
abbrev Level (Row : Type u) := List Row → Row → Bool

/-- The innermost body: from the chosen rows and the current store, a new
store and the body's answers. -/
abbrev Body (Row : Type u) (Answer : Type v) :=
  List Row → List Row → List Row × List Answer

/-- A body that leaves every store as it found it. -/
def Body.Preserves (body : Body Row Answer) : Prop :=
  ∀ chosen store, (body chosen store).1 = store

/-- Run `branch` for each item in order, each from the store the one before
it left, collecting the answers in order. -/
def sequence {Item : Type w} (branch : Item → List Row → List Row × List Answer) :
    List Item → List Row × List Answer → List Row × List Answer
  | [], acc => acc
  | item :: items, acc =>
      sequence branch items
        ((branch item acc.1).1, acc.2 ++ (branch item acc.1).2)

/-- The source schedule: a level is read once, when its branch is reached;
`order` arranges the rows the read returns. -/
def source (order : List Row → List Row) (body : Body Row Answer) :
    List (Level Row) → List Row → List Row → List Row × List Answer
  | [], chosen, store => body chosen store
  | level :: rest, chosen, store =>
      sequence (fun row store' => source order body rest (chosen ++ [row]) store')
        (order (store.filter (level chosen))) (store, [])

/-- Every way of choosing a row at each level, read against one store, with
`order` arranging each read. -/
def joinWith (order : List Row → List Row) (store : List Row) :
    List (Level Row) → List Row → List (List Row)
  | [], chosen => [chosen]
  | level :: rest, chosen =>
      (order (store.filter (level chosen))).flatMap
        fun row => joinWith order store rest (chosen ++ [row])

/-- The join in the order of the store. -/
abbrev join (store : List Row) (levels : List (Level Row)) (chosen : List Row) :
    List (List Row) :=
  joinWith id store levels chosen

/-- Every level joined against the store the query began with, then the
bodies in the join's order. -/
def fused (body : Body Row Answer) (levels : List (Level Row)) (store : List Row) :
    List Row × List Answer :=
  sequence body (join store levels []) (store, [])

/-- The levels before `last` joined against the store the query began with;
`last` is read for each joined prefix, when its bodies are reached. -/
def prefixFused (body : Body Row Answer) (pre : List (Level Row)) (last : Level Row)
    (store : List Row) : List Row × List Answer :=
  sequence (fun chosen store' => source id body [last] chosen store')
    (join store pre []) (store, [])

theorem sequence_preserving {Item : Type w}
    (branch : Item → List Row → List Row × List Answer)
    (keeps : ∀ item store, (branch item store).1 = store) :
    ∀ (items : List Item) (store : List Row) (answers : List Answer),
      sequence branch items (store, answers) =
        (store, answers ++ items.flatMap fun item => (branch item store).2)
  | [], store, answers => by simp [sequence]
  | item :: items, store, answers => by
      simp only [sequence, keeps]
      rw [sequence_preserving branch keeps items store]
      simp [List.flatMap_cons, List.append_assoc]

/-- With a body that leaves the store alone, the source schedule leaves it
alone too, and answers each joined choice's answers in the join's order. -/
theorem source_preserving (order : List Row → List Row) (body : Body Row Answer)
    (keeps : body.Preserves) :
    ∀ (levels : List (Level Row)) (chosen store : List Row),
      source order body levels chosen store =
        (store, (joinWith order store levels chosen).flatMap
          fun choice => (body choice store).2)
  | [], chosen, store => by
      simp only [source, joinWith, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact Prod.ext (keeps chosen store) rfl
  | level :: rest, chosen, store => by
      simp only [source, joinWith]
      rw [sequence_preserving _
        (fun row store' => by rw [source_preserving order body keeps rest]) _ store []]
      simp only [List.nil_append, source_preserving order body keeps rest, List.flatMap_assoc]

/-- **Fusion is admitted where no body writes**: the fused schedule is the
source schedule, store, answers and order of answers included. -/
theorem fusion_admitted (body : Body Row Answer) (keeps : body.Preserves)
    (levels : List (Level Row)) (store : List Row) :
    fused body levels store = source id body levels [] store := by
  rw [fused, sequence_preserving body keeps, source_preserving id body keeps]
  simp

theorem joinWith_append (order : List Row → List Row) (store : List Row) :
    ∀ (pre post : List (Level Row)) (chosen : List Row),
      joinWith order store (pre ++ post) chosen =
        (joinWith order store pre chosen).flatMap fun choice =>
          joinWith order store post choice
  | [], post, chosen => by simp [joinWith]
  | level :: rest, post, chosen => by
      simp only [List.cons_append, joinWith, List.flatMap_assoc]
      congr 1
      funext row
      exact joinWith_append order store rest post (chosen ++ [row])

/-- Fusing every level but the last is admitted on the same condition. -/
theorem prefix_fusion_admitted (body : Body Row Answer) (keeps : body.Preserves)
    (pre : List (Level Row)) (last : Level Row) (store : List Row) :
    prefixFused body pre last store = source id body (pre ++ [last]) [] store := by
  rw [prefixFused,
    sequence_preserving _ (fun chosen store' => by
      rw [source_preserving id body keeps]) _ store [],
    source_preserving id body keeps, joinWith_append]
  simp only [List.nil_append, source_preserving id body keeps, List.flatMap_assoc]

theorem joinWith_perm (order : List Row → List Row)
    (permutes : ∀ rows, (order rows).Perm rows) (store : List Row) :
    ∀ (levels : List (Level Row)) (chosen : List Row),
      (joinWith order store levels chosen).Perm (join store levels chosen)
  | [], chosen => by simp [joinWith]
  | level :: rest, chosen => by
      simp only [joinWith, id]
      exact ((permutes _).flatMap_right _).trans
        (List.Perm.flatMap_left _ fun row _ => joinWith_perm order permutes store rest
          (chosen ++ [row]))

/-- With a body that leaves the store alone, arranging each read's rows
differently permutes the answers and changes nothing else. -/
theorem order_permutes_answers (order : List Row → List Row)
    (permutes : ∀ rows, (order rows).Perm rows) (body : Body Row Answer)
    (keeps : body.Preserves) (levels : List (Level Row)) (chosen store : List Row) :
    (source order body levels chosen store).1 = store ∧
      (source order body levels chosen store).2.Perm
        (source id body levels chosen store).2 := by
  rw [source_preserving order body keeps, source_preserving id body keeps]
  exact ⟨rfl, (joinWith_perm order permutes store levels chosen).flatMap_right _⟩

/-! ## A query whose body writes

Rows are edges.  The first level reads every edge `(x, y)`, the second the
edges leaving `y`, the third those leaving the second edge's target `w`;
each answer writes the edge `(3, w)` and answers the chosen edges. -/

/-- The target of the edge chosen `back` levels ago, 0 when there is none. -/
def target (back : Nat) (chosen : List (Nat × Nat)) : Nat :=
  ((chosen.reverse.drop back).head?.map Prod.snd).getD 0

def edgeLevels : List (Level (Nat × Nat)) :=
  [fun _ _ => true,
   fun chosen edge => edge.1 == target 0 chosen,
   fun chosen edge => edge.1 == target 0 chosen]

def writesEdge : Body (Nat × Nat) (List (Nat × Nat)) :=
  fun chosen store => (store ++ [(3, target 0 chosen)], [chosen])

def answersOnly : Body (Nat × Nat) (List (Nat × Nat)) :=
  fun chosen store => (store, [chosen])

def edges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (2, 4)]

theorem source_answers_sixteen :
    (source id writesEdge edgeLevels [] edges).2.length = 16 := by decide

theorem prefix_fused_answers_four :
    (prefixFused writesEdge (edgeLevels.take 2) (fun chosen edge => edge.1 == target 0 chosen)
      edges).2.length = 4 := by decide

theorem fused_answers_two :
    (fused writesEdge edgeLevels edges).2.length = 2 := by decide

/-- **Fusion where a body writes is not the source schedule**. -/
theorem fusion_unrestricted_fails :
    (fused writesEdge edgeLevels edges).2.length ≠
        (source id writesEdge edgeLevels [] edges).2.length ∧
      (prefixFused writesEdge (edgeLevels.take 2)
          (fun chosen edge => edge.1 == target 0 chosen) edges).2.length ≠
        (source id writesEdge edgeLevels [] edges).2.length := by
  rw [fused_answers_two, prefix_fused_answers_four, source_answers_sixteen]
  decide

/-- Where a body writes, the order of the rows changes what the source
schedule answers: the program's answers depend on its schedule. -/
theorem written_answers_depend_on_order :
    (source id writesEdge edgeLevels [] edges.reverse).2.length = 2 := by decide

/-- The same query with a body that writes nothing: fused and source agree,
and reversing the rows permutes the answers. -/
theorem answersOnly_fused_eq_source :
    fused answersOnly edgeLevels edges = source id answersOnly edgeLevels [] edges :=
  fusion_admitted answersOnly (fun _ _ => rfl) edgeLevels edges

theorem answersOnly_reverse_permutes :
    (source id answersOnly edgeLevels [] edges.reverse).2.Perm
      (source id answersOnly edgeLevels [] edges).2 := by decide

end Mettapedia.Machines.NestedQuerySchedule
