import Mettapedia.GSLT.Dynamics.JoinAggregation

/-!
# Weighted path aggregation of arbitrary finite length

The reference enumerates every path in premise order, retaining its rows and
left-associated weight product. The execution route scans each new relation
into the existing keyed group table, multiplying the previous message on the
left. Addition is commutative; multiplication need not commute or associate.
Repeated relation rows contribute repeatedly. A message forgets path witnesses,
so these laws license an aggregate consumer, not ordered path delivery.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ChainAggregation

open JoinAggregation

variable {Key Weight : Type*}

structure Edge (Key Weight : Type*) where
  source : Key
  target : Key
  weight : Weight
  deriving DecidableEq

structure Path (Key Weight : Type*) where
  rows : List (Edge Key Weight)
  endpoint : Key
  weight : Weight
  deriving DecidableEq

def seed (relation : List (Edge Key Weight)) : List (Path Key Weight) :=
  relation.map fun row => ⟨[row], row.target, row.weight⟩

def attach [Mul Weight] (path : Path Key Weight) (row : Edge Key Weight) :
    Path Key Weight :=
  ⟨path.rows ++ [row], row.target, path.weight * row.weight⟩

def extend [DecidableEq Key] [Mul Weight]
    (paths : List (Path Key Weight)) (relation : List (Edge Key Weight)) :
    List (Path Key Weight) :=
  paths.flatMap fun path => relation.flatMap fun row =>
    if row.source = path.endpoint then [attach path row] else []

def extendRight [DecidableEq Key] [Mul Weight]
    (paths : List (Path Key Weight)) (relation : List (Edge Key Weight)) :
    List (Path Key Weight) :=
  relation.flatMap fun row => paths.flatMap fun path =>
    if row.source = path.endpoint then [attach path row] else []

theorem extend_perm_right [DecidableEq Key] [Mul Weight]
    (paths : List (Path Key Weight)) (relation : List (Edge Key Weight)) :
    (extend paths relation).Perm (extendRight paths relation) :=
  flatMap_flatMap_perm paths relation _

section Aggregation

variable [DecidableEq Key] [NonUnitalNonAssocSemiring Weight]

def summary (paths : List (Path Key Weight)) : Key → Weight :=
  groupSum Path.endpoint Path.weight paths

def start (relation : List (Edge Key Weight)) : Key → Weight :=
  groupTable Edge.target Edge.weight relation

def step (previous : Key → Weight) (relation : List (Edge Key Weight)) :
    Key → Weight :=
  groupTable Edge.target (fun row => previous row.source * row.weight) relation

theorem groupSum_append {Row : Type*} (key : Row → Key) (weight : Row → Weight)
    (first second : List Row) (endpoint : Key) :
    groupSum key weight (first ++ second) endpoint =
      groupSum key weight first endpoint + groupSum key weight second endpoint := by
  simp [groupSum]

theorem groupSum_flatMap {Row Item : Type*} (key : Item → Key)
    (weight : Item → Weight) (rows : List Row) (emit : Row → List Item)
    (endpoint : Key) :
    groupSum key weight (rows.flatMap emit) endpoint =
      (rows.map fun row => groupSum key weight (emit row) endpoint).sum := by
  induction rows with
  | nil => simp [groupSum]
  | cons row rest ih => simp [List.flatMap_cons, groupSum_append, ih]

theorem summary_seed (relation : List (Edge Key Weight)) :
    summary (seed relation) = start relation := by
  funext endpoint
  rw [start, groupTable_apply]
  simp [summary, seed, groupSum, List.filter_map, List.map_map,
    Function.comp_def]

theorem summary_right_block (paths : List (Path Key Weight))
    (row : Edge Key Weight) (endpoint : Key) :
    summary (paths.flatMap fun path =>
      if row.source = path.endpoint then [attach path row] else []) endpoint =
    if row.target = endpoint then summary paths row.source * row.weight else 0 := by
  induction paths with
  | nil => simp [summary, groupSum]
  | cons path rest ih =>
      rw [List.flatMap_cons]
      change groupSum Path.endpoint Path.weight (_ ++ _) endpoint = _
      rw [groupSum_append]
      change summary _ endpoint + summary _ endpoint = _
      rw [ih]
      by_cases matched : row.source = path.endpoint
      · by_cases selected : row.target = endpoint
        · simp [summary, attach, matched, selected, groupSum_cons, add_mul]
        · simp [summary, attach, matched, selected, groupSum_cons]
      · by_cases selected : row.target = endpoint
        · simp [summary, matched, selected, groupSum_cons, Ne.symm matched]
        · simp [summary, matched, selected]

theorem groupSum_eq_sum_ite {Row : Type*} (key : Row → Key)
    (weight : Row → Weight) (rows : List Row) (endpoint : Key) :
    groupSum key weight rows endpoint =
      (rows.map fun row => if key row = endpoint then weight row else 0).sum := by
  induction rows with
  | nil => simp [groupSum]
  | cons row rest ih => simp [groupSum_cons, ih]

/-- The one-pass message computes the grouped path aggregate. The exchange
of enumeration blocks uses only commutative addition, never multiplication. -/
theorem summary_extend (paths : List (Path Key Weight))
    (relation : List (Edge Key Weight)) :
    summary (extend paths relation) = step (summary paths) relation := by
  funext endpoint
  have permutation := ((extend_perm_right paths relation).filter
    (fun path => decide (path.endpoint = endpoint))).map Path.weight
  change ((extend paths relation).filter _ |>.map Path.weight).sum = _
  rw [permutation.sum_eq]
  change summary (extendRight paths relation) endpoint = _
  rw [summary, extendRight, groupSum_flatMap]
  change (relation.map fun row => summary (paths.flatMap fun path =>
    if row.source = path.endpoint then [attach path row] else []) endpoint).sum = _
  simp_rw [summary_right_block]
  rw [step, groupTable_apply, groupSum_eq_sum_ite]

def enumerateFrom (paths : List (Path Key Weight)) :
    List (List (Edge Key Weight)) → List (Path Key Weight)
  | [] => paths
  | relation :: rest => enumerateFrom (extend paths relation) rest

def runFrom (previous : Key → Weight) : List (List (Edge Key Weight)) → Key → Weight
  | [] => previous
  | relation :: rest => runFrom (step previous relation) rest

theorem summary_enumerateFrom (paths : List (Path Key Weight))
    (relations : List (List (Edge Key Weight))) :
    summary (enumerateFrom paths relations) = runFrom (summary paths) relations := by
  induction relations generalizing paths with
  | nil => rfl
  | cons relation rest ih =>
      rw [enumerateFrom, runFrom, ih, summary_extend]

def enumerate : List (List (Edge Key Weight)) → List (Path Key Weight)
  | [] => []
  | relation :: rest => enumerateFrom (seed relation) rest

def run : List (List (Edge Key Weight)) → Key → Weight
  | [] => 0
  | relation :: rest => runFrom (start relation) rest

theorem arbitrary_chain_aggregate (relations : List (List (Edge Key Weight))) :
    summary (enumerate relations) = run relations := by
  cases relations with
  | nil => funext endpoint; simp [enumerate, run, summary, groupSum]
  | cons relation rest =>
      rw [enumerate, run, summary_enumerateFrom, summary_seed]

def total (paths : List (Path Key Weight)) : Weight :=
  (paths.map Path.weight).sum

def close (previous : Key → Weight) (relation : List (Edge Key Weight)) : Weight :=
  (relation.map fun row => previous row.source * row.weight).sum

theorem total_right_block (paths : List (Path Key Weight)) (row : Edge Key Weight) :
    total (paths.flatMap fun path =>
      if row.source = path.endpoint then [attach path row] else []) =
    summary paths row.source * row.weight := by
  induction paths with
  | nil => simp [total, summary, groupSum]
  | cons path rest ih =>
      rw [List.flatMap_cons]
      unfold total
      rw [List.map_append, List.sum_append]
      change total _ + total _ = _
      rw [ih]
      by_cases matched : row.source = path.endpoint
      · simp [total, attach, summary, groupSum_cons, matched, add_mul]
      · simp [total, summary, groupSum_cons, matched, Ne.symm matched]

theorem total_extend (paths : List (Path Key Weight))
    (relation : List (Edge Key Weight)) :
    total (extend paths relation) = close (summary paths) relation := by
  have permutation := (extend_perm_right paths relation).map Path.weight
  unfold total
  rw [permutation.sum_eq, extendRight, sum_map_flatMap]
  change (relation.map fun row => total (paths.flatMap fun path =>
    if row.source = path.endpoint then [attach path row] else [])).sum = _
  simp_rw [total_right_block]
  rfl

/-- The last relation closes the scalar aggregate directly, without retaining
a table for terminal keys. Every earlier relation passes one keyed message. -/
def finish (previous : Key → Weight) (relation : List (Edge Key Weight)) :
    List (List (Edge Key Weight)) → Weight
  | [] => close previous relation
  | next :: rest => finish (step previous relation) next rest

theorem total_enumerateFrom (paths : List (Path Key Weight))
    (relation : List (Edge Key Weight)) (rest : List (List (Edge Key Weight))) :
    total (enumerateFrom paths (relation :: rest)) =
      finish (summary paths) relation rest := by
  induction rest generalizing paths relation with
  | nil => exact total_extend paths relation
  | cons next rest ih =>
      rw [enumerateFrom, finish, ih, summary_extend]

def aggregate : List (List (Edge Key Weight)) → Weight
  | [] => 0
  | [relation] => (relation.map Edge.weight).sum
  | first :: second :: rest => finish (start first) second rest

theorem arbitrary_chain_total (relations : List (List (Edge Key Weight))) :
    total (enumerate relations) = aggregate relations := by
  cases relations with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => simp [enumerate, enumerateFrom, total, seed, aggregate,
          List.map_map, Function.comp_def]
      | cons second rest =>
          rw [enumerate, total_enumerateFrom, summary_seed, aggregate]

theorem step_absent_key (previous : Key → Weight) (relation : List (Edge Key Weight))
    (key : Key) (absent : key ∉ (relation.map Edge.target).toFinset) :
    step previous relation key = 0 := by
  rw [step, groupTable_apply]
  apply groupSum_eq_zero
  intro row member same
  apply absent
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, member, same⟩)

omit [NonUnitalNonAssocSemiring Weight] in
theorem retained_keys_bounded (relation : List (Edge Key Weight)) :
    (relation.map Edge.target).toFinset.card ≤ relation.length := by
  exact (List.toFinset_card_le _).trans_eq (List.length_map _)

/-- An instrumented version of the same keyed-table scan. The account counts
row visits and distinct keys, not hash probes, allocation or key equality. -/
structure ScanAccount (Key Weight : Type*) where
  table : Key → Weight
  visits : Nat
  keys : Finset Key

def scanUpdate (weight : Edge Key Weight → Weight) (state : ScanAccount Key Weight)
    (row : Edge Key Weight) : ScanAccount Key Weight :=
  ⟨Function.update state.table row.target (state.table row.target + weight row),
    state.visits + 1, insert row.target state.keys⟩

def scan (weight : Edge Key Weight → Weight) (relation : List (Edge Key Weight))
    (state : ScanAccount Key Weight) : ScanAccount Key Weight :=
  relation.foldl (scanUpdate weight) state

theorem scan_account (weight : Edge Key Weight → Weight)
    (relation : List (Edge Key Weight)) (state : ScanAccount Key Weight) :
    (scan weight relation state).table =
      relation.foldl (fun table row =>
        Function.update table row.target (table row.target + weight row)) state.table ∧
    (scan weight relation state).visits = state.visits + relation.length ∧
    (scan weight relation state).keys = state.keys ∪ (relation.map Edge.target).toFinset := by
  induction relation generalizing state with
  | nil => simp [scan]
  | cons row rest ih =>
      rw [scan, List.foldl_cons]
      have following := ih (scanUpdate weight state row)
      simp only [scan, scanUpdate, List.foldl_cons, List.length_cons,
        List.map_cons, List.toFinset_cons] at following ⊢
      rcases following with ⟨table, visits, keys⟩
      refine ⟨table, by omega, ?_⟩
      rw [keys]
      ext key
      simp

theorem scan_realizes_groupTable (weight : Edge Key Weight → Weight)
    (relation : List (Edge Key Weight)) :
    (scan weight relation ⟨0, 0, ∅⟩).table = groupTable Edge.target weight relation ∧
    (scan weight relation ⟨0, 0, ∅⟩).visits = relation.length ∧
    (scan weight relation ⟨0, 0, ∅⟩).keys.card ≤ relation.length := by
  obtain ⟨table, visits, keys⟩ := scan_account weight relation ⟨0, 0, ∅⟩
  refine ⟨table, by simpa using visits, ?_⟩
  rw [keys, Finset.empty_union]
  exact retained_keys_bounded relation

omit [NonUnitalNonAssocSemiring Weight] in
theorem adjacent_messages_key_bound
    (previous current : List (Edge Key Weight)) :
    (previous.map Edge.target).toFinset.card +
      (current.map Edge.target).toFinset.card ≤ previous.length + current.length :=
  Nat.add_le_add (retained_keys_bounded previous) (retained_keys_bounded current)

end Aggregation

namespace Controls

def repeated : List (Edge Nat Nat) := [⟨0, 0, 1⟩, ⟨0, 0, 1⟩]

theorem four_relations_count_occurrences :
    (enumerate [repeated, repeated, repeated, repeated]).length = 16 ∧
    aggregate [repeated, repeated, repeated, repeated] = 16 ∧
    (repeated.map Edge.target).toFinset.card = 1 := by
  decide

theorem deduplication_changes_aggregate :
    aggregate [repeated, repeated, repeated, repeated] ≠
      aggregate [repeated.eraseDups, repeated.eraseDups,
        repeated.eraseDups, repeated.eraseDups] := by
  decide

theorem missing_bridge_kills_path :
    aggregate [[⟨0, 1, 3⟩], [⟨2, 3, 5⟩], [⟨3, 4, 7⟩], [⟨4, 5, 11⟩]] = (0 : Nat) := by
  decide

end Controls

end Mettapedia.GSLT.Dynamics.ChainAggregation
