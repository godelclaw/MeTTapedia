import Mettapedia.GSLT.Core.Composition
import Mathlib.Data.Finset.Image
import Mettapedia.Data.List.CheckedUnion

/-!
# Origin-sensitive declaration fragments

The term/projection fragment of MeTTaIL's `pres.rs` identifies declarations by
origin, checks agreement along shared paths, and rejects independently introduced
declarations with one label. This module gives its extensional algebra. Ordered
builders, source spans, completed cores, and the other upstream entry kinds have
separate contracts; this is not a decoder for the complete Rust presentation.

Source: F1R3FLY-io/mettail-rust, commit
`8c1bb3b0ef3890406e375c2c5387dc9a3cdf0439`, `mettail-elab/src/pres.rs`.
-/

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra

universe u v w

/-- The origin is independent of the exposed label and its specification. -/
structure Entry (Origin : Type u) (Label : Type v) (Body : Type w) where
  origin : Origin
  label : Label
  body : Body
  deriving DecidableEq

variable {Origin : Type u} {Label : Type v} {Body : Type w}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

abbrev Fragment := Finset (Entry Origin Label Body)

/-- Shared origins must agree; one exposed label cannot denote two origins. -/
def Valid (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries,
    (first.origin = second.origin ∨ first.label = second.label) → first = second

instance (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Decidable (Valid entries) := by unfold Valid; infer_instance

/-- A finite, conflict-free fragment. This admits shared ancestors. -/
abbrev Presentation (Origin : Type u) (Label : Type v) (Body : Type w)
    [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] :=
  {entries : Finset (Entry Origin Label Body) // Valid entries}

/-- An explicitly supplied order for an extensional declaration fragment.
Neither the finite set nor its storage iteration determines this order. -/
structure OrderedView (fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body)) where
  entries : List (Entry Origin Label Body)
  nodup : entries.Nodup
  covers : entries.toFinset = fragment

/-- Validate the caller's order without sorting, dropping or adding entries. -/
def orderedView? (fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body))
    (entries : List (Entry Origin Label Body)) : Option (OrderedView fragment) :=
  if accepted : entries.Nodup ∧ entries.toFinset = fragment then
    some ⟨entries, accepted.1, accepted.2⟩
  else none

theorem orderedView_isSome_iff
    (fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body))
    (entries : List (Entry Origin Label Body)) :
    (orderedView? fragment entries).isSome = true ↔
      entries.Nodup ∧ entries.toFinset = fragment := by
  simp [orderedView?]

theorem orderedView_entries
    {fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    {entries : List (Entry Origin Label Body)} {view : OrderedView fragment}
    (accepted : orderedView? fragment entries = some view) : view.entries = entries := by
  unfold orderedView? at accepted
  split at accepted
  · cases Option.some.inj accepted
    rfl
  · cases accepted

/-- Looking up an occurrence retains its declaration's portable origin. -/
def OrderedView.originAt
    {fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (view : OrderedView fragment) (index : Fin view.entries.length) : Origin :=
  view.entries[index].origin

theorem OrderedView.entry_mem
    {fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (view : OrderedView fragment) (index : Fin view.entries.length) :
    view.entries[index] ∈ fragment := by
  have member : view.entries[index] ∈ view.entries.toFinset :=
    List.mem_toFinset.mpr (List.getElem_mem index.isLt)
  simpa only [view.covers] using member

/-- An explicit reversal is a different order for the same declarations. -/
def OrderedView.reverse
    {fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (view : OrderedView fragment) : OrderedView fragment :=
  ⟨view.entries.reverse, List.nodup_reverse.mpr view.nodup, by simpa using view.covers⟩

@[simp] theorem OrderedView.reverse_entries
    {fragment : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (view : OrderedView fragment) : view.reverse.entries = view.entries.reverse := rfl

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
@[simp] theorem valid_empty : Valid (∅ : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) := by simp [Valid]

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem Valid.mono {entries smaller : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} (valid : Valid entries) (subset : smaller ⊆ entries) :
    Valid smaller := by
  intro first firstMem second secondMem overlap
  exact valid first (subset firstMem) second (subset secondMem) overlap

def empty : Presentation Origin Label Body := ⟨∅, valid_empty⟩

/-- A checked union, rather than name-based or content-based deduplication. -/
def check (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Option (Presentation Origin Label Body) :=
  if h : Valid entries then some ⟨entries, h⟩ else none

def join (first second : Presentation Origin Label Body) :
    Option (Presentation Origin Label Body) := check (first.val ∪ second.val)

/-- Pairwise form of the existing origin-coherent admission contract. -/
def entryCompatible (first second : Entry Origin Label Body) : Bool :=
  decide ((first.origin = second.origin ∨ first.label = second.label) → first = second)

@[simp] theorem entryCompatible_self (entry : Entry Origin Label Body) :
    entryCompatible entry entry = true := by simp [entryCompatible]

theorem entryCompatible_symm (first second : Entry Origin Label Body) :
    entryCompatible first second = entryCompatible second first := by
  apply Bool.decide_congr
  constructor
  · intro accepted overlap
    exact (accepted (overlap.imp Eq.symm Eq.symm)).symm
  · intro accepted overlap
    exact (accepted (overlap.imp Eq.symm Eq.symm)).symm

theorem allCompatible_iff_valid (entries : List (Entry Origin Label Body)) :
    List.AllCompatible entryCompatible entries ↔ Valid entries.toFinset := by
  simp only [List.AllCompatible, entryCompatible, decide_eq_true_eq, Valid, List.mem_toFinset]

/-- Check every declaration and retain its first position. A diamond import
is shared only when its full origin, label and body agree. -/
def orderedCheck? (entries : List (Entry Origin Label Body)) :
    Option (List (Entry Origin Label Body)) :=
  List.unionCompatible? entryCompatible [] entries

theorem orderedCheck_isSome_iff (entries : List (Entry Origin Label Body)) :
    (orderedCheck? entries).isSome = true ↔ Valid entries.toFinset := by
  rw [orderedCheck?, List.unionCompatible?_from_empty_isSome_iff entryCompatible
    entryCompatible_self entryCompatible_symm, allCompatible_iff_valid]

theorem orderedCheck_toFinset (entries result : List (Entry Origin Label Body))
    (checked : orderedCheck? entries = some result) : result.toFinset = entries.toFinset := by
  simpa only [List.toFinset_nil, Finset.empty_union] using
    List.unionCompatible?_toFinset entryCompatible [] entries result checked

theorem orderedCheck_nodup (entries result : List (Entry Origin Label Body))
    (checked : orderedCheck? entries = some result) : result.Nodup :=
  List.unionCompatible?_nodup entryCompatible [] entries result (by simp) checked

/-- The executable ordered checker refines the original finite-presentation
checker, including rejection; no compilation of bodies precedes admission. -/
theorem orderedCheck_agrees (entries : List (Entry Origin Label Body)) :
    (orderedCheck? entries).bind (fun result => check result.toFinset) = check entries.toFinset := by
  cases completed : orderedCheck? entries with
  | none =>
      have refused : ¬ Valid entries.toFinset := by
        intro accepted
        have := (orderedCheck_isSome_iff entries).mpr accepted
        simp [completed] at this
      simp [check, refused]
  | some result => simp [orderedCheck_toFinset entries result completed]

def orderedJoin? (first second : List (Entry Origin Label Body)) :
    Option (List (Entry Origin Label Body)) := orderedCheck? (first ++ second)

theorem orderedJoin_isSome_iff (first second : List (Entry Origin Label Body)) :
    (orderedJoin? first second).isSome = true ↔ Valid (first.toFinset ∪ second.toFinset) := by
  simpa only [orderedJoin?, List.toFinset_append] using orderedCheck_isSome_iff (first ++ second)

theorem orderedJoin_agrees (first second : List (Entry Origin Label Body)) :
    (orderedJoin? first second).bind (fun result => check result.toFinset) =
      check (first.toFinset ∪ second.toFinset) := by
  simpa only [orderedJoin?, List.toFinset_append] using orderedCheck_agrees (first ++ second)

@[simp] theorem check_val (p : Presentation Origin Label Body) : check p.val = some p := by
  simp [check, p.property]

theorem check_eq_some_iff {entries : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} {p : Presentation Origin Label Body} :
    check entries = some p ↔ entries = p.val := by
  by_cases h : Valid entries
  · simp only [check, dif_pos h, Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [check, dif_neg h, reduceCtorEq, false_iff]
    intro equal
    exact h (equal ▸ p.property)

@[simp] theorem check_eq_none_iff (entries : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) : check entries = none ↔ ¬ Valid entries := by
  simp [check]

theorem join_eq_some_iff {p q r : Presentation Origin Label Body} :
    join p q = some r ↔ p.val ∪ q.val = r.val := check_eq_some_iff

/-- Cross-fragment overlap is checked independently of each side's validity. -/
def Compatible (first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) : Prop :=
  ∀ a ∈ first, ∀ b ∈ second,
    (a.origin = b.origin ∨ a.label = b.label) → a = b

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem Compatible.symm {first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} (compatible : Compatible first second) :
    Compatible second first := by
  intro a ha b hb overlap
  exact (compatible b hb a ha (overlap.imp Eq.symm Eq.symm)).symm

theorem valid_union_iff {first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} :
    Valid (first ∪ second) ↔ Valid first ∧ Valid second ∧ Compatible first second := by
  constructor
  · intro valid
    exact ⟨valid.mono Finset.subset_union_left, valid.mono Finset.subset_union_right,
      fun a ha b hb overlap => valid a (Finset.mem_union_left _ ha)
        b (Finset.mem_union_right _ hb) overlap⟩
  · rintro ⟨firstValid, secondValid, cross⟩ a ha b hb overlap
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact firstValid a ha b hb overlap
    · exact cross a ha b hb overlap
    · apply (cross b hb a ha ?_).symm
      exact overlap.imp Eq.symm Eq.symm
    · exact secondValid a ha b hb overlap

/-- Checking early and checking the entire union agree, including failure. -/
theorem check_union (first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) :
    check (first ∪ second) =
      (check first).bind fun p => (check second).bind fun q => join p q := by
  by_cases hf : Valid first
  · by_cases hs : Valid second
    · simp [check, hf, hs, join]
    · have h : ¬ Valid (first ∪ second) :=
        fun h => hs (h.mono Finset.subset_union_right)
      simp [check, hs, h]
  · have h : ¬ Valid (first ∪ second) :=
      fun h => hf (h.mono Finset.subset_union_left)
    simp [check, hf, h]

theorem join_comm (p q : Presentation Origin Label Body) : join p q = join q p := by
  simp only [join, Finset.union_comm]

theorem join_eq_none_iff (p q : Presentation Origin Label Body) :
    join p q = none ↔ ¬ Compatible p.val q.val := by
  simp [join, valid_union_iff, p.property, q.property]

/-- Every failed join exposes either a disagreeing shared origin or a label
collision between distinct entries. -/
theorem join_failure_witness (p q : Presentation Origin Label Body) :
    join p q = none ↔ ∃ a ∈ p.val, ∃ b ∈ q.val,
      (a.origin = b.origin ∨ a.label = b.label) ∧ a ≠ b := by
  rw [join_eq_none_iff]
  simp only [Compatible]
  push Not
  rfl

@[simp] theorem join_self (p : Presentation Origin Label Body) : join p p = some p := by
  simp [join]

/-- Upstream meet selects the left representatives of shared origins. -/
def meet (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val.filter (fun a => ∃ b ∈ q.val, a.origin = b.origin),
    p.property.mono (Finset.filter_subset _ _)⟩

/-- Difference removes shared origins even if their exposed declarations differ. -/
def diff (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val.filter (fun a => ¬ ∃ b ∈ q.val, a.origin = b.origin),
    p.property.mono (Finset.filter_subset _ _)⟩

theorem meet_val_of_compatible (p q : Presentation Origin Label Body)
    (compatible : Compatible p.val q.val) : (meet p q).val = p.val ∩ q.val := by
  ext a
  simp only [meet, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨ha, b, hb, origin⟩
    exact ⟨ha, (compatible a ha b hb (Or.inl origin)) ▸ hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, a, hb, rfl⟩

theorem meet_comm_of_compatible (p q : Presentation Origin Label Body)
    (compatible : Compatible p.val q.val) : meet p q = meet q p := by
  apply Subtype.ext
  rw [meet_val_of_compatible p q compatible, meet_val_of_compatible q p compatible.symm,
    Finset.inter_comm]

theorem meet_diff_partition (p q : Presentation Origin Label Body) :
    (meet p q).val ∪ (diff p q).val = p.val := by
  ext a
  simp only [meet, diff, Finset.mem_union, Finset.mem_filter]
  by_cases h : ∃ b ∈ q.val, a.origin = b.origin <;> simp [h]

theorem join_meet_diff (p q : Presentation Origin Label Body) :
    join (meet p q) (diff p q) = some p := join_eq_some_iff.mpr (meet_diff_partition p q)

def origins (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Finset Origin := entries.image Entry.origin

/-! ## Origin-preserving compilation of declaration bodies

Compilation may forget notation or formal names. It preserves a successful
source join, but a noninjective body map need not reflect a source conflict.
The source admission check must therefore precede such compilation.
-/

section BodyCompilation

variable {Body' : Type} [DecidableEq Body']

def mapBodyEntry (compile : Body → Body') (entry : Entry Origin Label Body) :
    Entry Origin Label Body' := ⟨entry.origin, entry.label, compile entry.body⟩

def mapBodies (compile : Body → Body') (p : Presentation Origin Label Body) :
    Presentation Origin Label Body' :=
  ⟨p.val.image (mapBodyEntry compile), by
    intro first firstMember second secondMember overlap
    obtain ⟨a, aMember, rfl⟩ := Finset.mem_image.mp firstMember
    obtain ⟨b, bMember, rfl⟩ := Finset.mem_image.mp secondMember
    exact congrArg (mapBodyEntry compile) (p.property a aMember b bMember overlap)⟩

/-- The compiled payloads retain the exact successful shared-module union. -/
theorem mapBodies_join_of_success (compile : Body → Body')
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    join (mapBodies compile p) (mapBodies compile q) = some (mapBodies compile r) := by
  apply join_eq_some_iff.mpr
  change p.val.image (mapBodyEntry compile) ∪ q.val.image (mapBodyEntry compile) =
    r.val.image (mapBodyEntry compile)
  rw [← Finset.image_union, join_eq_some_iff.mp joined]

theorem origins_mapBodies (compile : Body → Body') (p : Presentation Origin Label Body) :
    origins (mapBodies compile p).val = origins p.val := by
  simp only [origins, mapBodies, Finset.image_image, mapBodyEntry, Function.comp_def]

theorem mapBodies_comp {Body'' : Type} [DecidableEq Body'']
    (first : Body → Body') (second : Body' → Body'') (p : Presentation Origin Label Body) :
    mapBodies second (mapBodies first p) = mapBodies (second ∘ first) p := by
  apply Subtype.ext
  simp only [mapBodies, Finset.image_image]
  rfl

/-- Compilation functions need agree only on the module's retained entries. -/
theorem mapBodies_congr (first second : Body → Body')
    (p : Presentation Origin Label Body)
    (same : ∀ entry ∈ p.val, first entry.body = second entry.body) :
    mapBodies first p = mapBodies second p := by
  apply Subtype.ext
  apply Finset.image_congr
  intro entry member
  cases entry with
  | mk origin label body =>
      simpa only [mapBodyEntry, Entry.mk.injEq, true_and] using same ⟨origin, label, body⟩ member

end BodyCompilation

/-- Replacement changes a declaration in place, retaining its origin. -/
def replaceEntry (origin : Origin) (label : Label) (body : Body)
    (entry : Entry Origin Label Body) : Entry Origin Label Body :=
  if entry.origin = origin then ⟨entry.origin, label, body⟩ else entry

def replace (p : Presentation Origin Label Body) (origin : Origin) (label : Label)
    (body : Body) : Option (Presentation Origin Label Body) :=
  check (p.val.image (replaceEntry origin label body))

omit [DecidableEq Label] [DecidableEq Body] in
@[simp] theorem replaceEntry_origin (origin : Origin) (label : Label) (body : Body)
    (entry : Entry Origin Label Body) :
    (replaceEntry origin label body entry).origin = entry.origin := by
  simp [replaceEntry]; split <;> rfl

theorem origins_replace (p q : Presentation Origin Label Body) (origin : Origin)
    (label : Label) (body : Body) (success : replace p origin label body = some q) :
    origins q.val = origins p.val := by
  have value := check_eq_some_iff.mp success
  rw [← value]
  simp only [origins, Finset.image_image, Function.comp_def, replaceEntry_origin]

/-- Fresh application stamps newly introduced declarations, leaving imported
ancestors to be supplied separately to `join`. -/
def stamp {Instance : Type*} (instanceId : Instance) (entry : Entry Origin Label Body) :
    Entry (Instance × Origin) Label Body := ⟨(instanceId, entry.origin), entry.label, entry.body⟩

def stampPresentation {Instance : Type*} [DecidableEq Instance] (instanceId : Instance)
    (p : Presentation Origin Label Body) : Presentation (Instance × Origin) Label Body :=
  ⟨p.val.image (stamp instanceId), by
    intro a ha b hb overlap
    obtain ⟨originalA, memberA, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨originalB, memberB, rfl⟩ := Finset.mem_image.mp hb
    have equal : originalA = originalB := p.property _ memberA _ memberB
      (overlap.imp (congrArg Prod.snd) id)
    rw [equal]⟩

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem stamps_disjoint {Instance : Type*} [DecidableEq Instance]
    (first second : Instance) (different : first ≠ second)
    (a b : Entry Origin Label Body) :
    (stamp first a).origin ≠ (stamp second b).origin := by
  intro equal
  exact different (congrArg Prod.fst equal)

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra
