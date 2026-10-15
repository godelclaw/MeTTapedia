import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Authoring

/-!
# Composition of distinct structural views at shared origins

The existing `ModuleAlgebra.Presentation` is origin-coherent: a shared origin
must expose the same full declaration. This module gives a second contract.
An origin view is identified by its origin and full structural declaration,
including its exposed label. Different views of one origin remain distinct;
unequal declarations exposing one label still conflict.

This is an extensional declaration algebra, not a byte-module parser or a claim
about any historical implementation's module semantics. Origins are retained.
Ordered builder occurrences, source spans, and rule realizations require their
own interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginView

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

universe u v w

variable {Origin : Type u} {Label : Type v} {Body : Type w}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

/-- The structural declaration includes both its exposed label and its body. -/
def viewKey (entry : Entry Origin Label Body) : Origin × (Label × Body) :=
  (entry.origin, entry.label, entry.body)

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem viewKey_injective : Function.Injective
    (viewKey : Entry Origin Label Body → Origin × (Label × Body)) := by
  intro first second same
  cases first
  cases second
  simpa only [viewKey, Prod.mk.injEq, Entry.mk.injEq] using same

/-- One exposed label names one full origin view. Shared origins need not agree. -/
def Valid (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries, first.label = second.label → first = second

instance (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Decidable (Valid entries) := by unfold Valid; infer_instance

abbrev Presentation (Origin : Type u) (Label : Type v) (Body : Type w)
    [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] :=
  {entries : Finset (Entry Origin Label Body) // Valid entries}

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
@[simp] theorem valid_empty : Valid (∅ : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) := by simp [Valid]

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem Valid.mono {entries smaller : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (valid : Valid entries) (subset : smaller ⊆ entries) : Valid smaller := by
  intro first firstMem second secondMem sameLabel
  exact valid first (subset firstMem) second (subset secondMem) sameLabel

def empty : Presentation Origin Label Body := ⟨∅, valid_empty⟩

def check (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Option (Presentation Origin Label Body) :=
  if h : Valid entries then some ⟨entries, h⟩ else none

def join (first second : Presentation Origin Label Body) :
    Option (Presentation Origin Label Body) := check (first.val ∪ second.val)

/-- Pairwise form of the existing structural-view admission contract. -/
def entryCompatible (first second : Entry Origin Label Body) : Bool :=
  decide (first.label = second.label → first = second)

@[simp] theorem entryCompatible_self (entry : Entry Origin Label Body) :
    entryCompatible entry entry = true := by simp [entryCompatible]

theorem entryCompatible_symm (first second : Entry Origin Label Body) :
    entryCompatible first second = entryCompatible second first := by
  apply Bool.decide_congr
  constructor
  · intro accepted sameLabel
    exact (accepted sameLabel.symm).symm
  · intro accepted sameLabel
    exact (accepted sameLabel.symm).symm

theorem allCompatible_iff_valid (entries : List (Entry Origin Label Body)) :
    List.AllCompatible entryCompatible entries ↔ Valid entries.toFinset := by
  simp only [List.AllCompatible, entryCompatible, decide_eq_true_eq, Valid, List.mem_toFinset]

/-- Reuse the ordered checker while allowing distinct exposed views of one
origin. Equal declarations retain their first position. -/
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

theorem check_eq_some_iff {entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    {p : Presentation Origin Label Body} : check entries = some p ↔ entries = p.val := by
  by_cases h : Valid entries
  · simp only [check, dif_pos h, Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [check, dif_neg h, reduceCtorEq, false_iff]
    intro same
    exact h (same ▸ p.property)

@[simp] theorem check_eq_none_iff (entries : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) : check entries = none ↔ ¬ Valid entries := by
  simp [check]

theorem check_isSome_iff (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    (check entries).isSome = true ↔ Valid entries := by
  simp [check]

theorem join_eq_some_iff {p q r : Presentation Origin Label Body} :
    join p q = some r ↔ p.val ∪ q.val = r.val := check_eq_some_iff

def Compatible (first second : Fragment (Origin := Origin) (Label := Label) (Body := Body)) : Prop :=
  ∀ a ∈ first, ∀ b ∈ second, a.label = b.label → a = b

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem Compatible.symm {first second : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (compatible : Compatible first second) : Compatible second first := by
  intro a ha b hb same
  exact (compatible b hb a ha same.symm).symm

theorem valid_union_iff {first second : Fragment (Origin := Origin) (Label := Label) (Body := Body)} :
    Valid (first ∪ second) ↔ Valid first ∧ Valid second ∧ Compatible first second := by
  constructor
  · intro valid
    exact ⟨valid.mono Finset.subset_union_left, valid.mono Finset.subset_union_right,
      fun a ha b hb same => valid a (Finset.mem_union_left _ ha)
        b (Finset.mem_union_right _ hb) same⟩
  · rintro ⟨firstValid, secondValid, cross⟩ a ha b hb same
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · exact firstValid a ha b hb same
    · exact cross a ha b hb same
    · exact (cross b hb a ha same.symm).symm
    · exact secondValid a ha b hb same

theorem check_union (first second : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    check (first ∪ second) =
      (check first).bind fun p => (check second).bind fun q => join p q := by
  by_cases hf : Valid first
  · by_cases hs : Valid second
    · simp [check, hf, hs, join]
    · have h : ¬ Valid (first ∪ second) := fun h => hs (h.mono Finset.subset_union_right)
      simp [check, hs, h]
  · have h : ¬ Valid (first ∪ second) := fun h => hf (h.mono Finset.subset_union_left)
    simp [check, hf, h]

theorem join_comm (p q : Presentation Origin Label Body) : join p q = join q p := by
  simp only [join, Finset.union_comm]

theorem join_eq_none_iff (p q : Presentation Origin Label Body) :
    join p q = none ↔ ¬ Compatible p.val q.val := by
  simp [join, valid_union_iff, p.property, q.property]

theorem join_failure_witness (p q : Presentation Origin Label Body) :
    join p q = none ↔ ∃ a ∈ p.val, ∃ b ∈ q.val, a.label = b.label ∧ a ≠ b := by
  rw [join_eq_none_iff]
  simp only [Compatible]
  push Not
  rfl

@[simp] theorem join_self (p : Presentation Origin Label Body) : join p p = some p := by
  simp [join]

/-- View intersection compares full declarations and origins, not only origins. -/
def meet (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val ∩ q.val, p.property.mono Finset.inter_subset_left⟩

def diff (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val \ q.val, p.property.mono Finset.sdiff_subset⟩

@[simp] theorem meet_val (p q : Presentation Origin Label Body) : (meet p q).val = p.val ∩ q.val := rfl
@[simp] theorem diff_val (p q : Presentation Origin Label Body) : (diff p q).val = p.val \ q.val := rfl

theorem meet_comm (p q : Presentation Origin Label Body) : meet p q = meet q p := by
  apply Subtype.ext
  exact Finset.inter_comm _ _

theorem meet_assoc (p q r : Presentation Origin Label Body) :
    meet (meet p q) r = meet p (meet q r) := by
  apply Subtype.ext
  exact Finset.inter_assoc _ _ _

@[simp] theorem meet_self (p : Presentation Origin Label Body) : meet p p = p := by
  apply Subtype.ext
  exact Finset.inter_self _

@[simp] theorem diff_self (p : Presentation Origin Label Body) : diff p p = empty := by
  apply Subtype.ext
  exact Finset.sdiff_self _

theorem meet_diff_partition (p q : Presentation Origin Label Body) :
    (meet p q).val ∪ (diff p q).val = p.val := by
  ext entry
  simp only [meet_val, diff_val, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem meet_diff_disjoint (p q : Presentation Origin Label Body) :
    Disjoint (meet p q).val (diff p q).val := by
  apply Finset.disjoint_left.mpr
  intro entry first second
  exact (Finset.mem_sdiff.mp second).2 (Finset.mem_inter.mp first).2

theorem join_meet_diff (p q : Presentation Origin Label Body) :
    join (meet p q) (diff p q) = some p := join_eq_some_iff.mpr (meet_diff_partition p q)

/-! Membership and view keys retain full declarations, including their origins. -/

abbrev Member (p : Presentation Origin Label Body) := {entry // entry ∈ p.val}

def includeLeft {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (entry : Member p) : Member r :=
  ⟨entry.val, (join_eq_some_iff.mp joined) ▸ Finset.mem_union_left _ entry.property⟩

def includeRight {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (entry : Member q) : Member r :=
  ⟨entry.val, (join_eq_some_iff.mp joined) ▸ Finset.mem_union_right _ entry.property⟩

@[simp] theorem includeLeft_entry {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (entry : Member p) : (includeLeft joined entry).val = entry.val := rfl

@[simp] theorem includeRight_entry {p q r : Presentation Origin Label Body}
    (joined : join p q = some r) (entry : Member q) : (includeRight joined entry).val = entry.val := rfl

theorem includeLeft_injective {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    Function.Injective (includeLeft joined) := by
  intro first second same
  exact Subtype.ext (congrArg (fun entry : Member r => entry.val) same)

theorem includeRight_injective {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    Function.Injective (includeRight joined) := by
  intro first second same
  exact Subtype.ext (congrArg (fun entry : Member r => entry.val) same)

theorem member_viewKey_injective (p : Presentation Origin Label Body) :
    Function.Injective (fun entry : Member p => viewKey entry.val) := by
  intro first second same
  exact Subtype.ext (viewKey_injective same)

theorem join_origins {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    ModuleAlgebra.origins r.val = ModuleAlgebra.origins p.val ∪ ModuleAlgebra.origins q.val := by
  rw [← join_eq_some_iff.mp joined, ModuleAlgebra.origins, Finset.image_union]
  rfl

theorem join_member_iff {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (entry : Entry Origin Label Body) : entry ∈ r.val ↔ entry ∈ p.val ∨ entry ∈ q.val := by
  rw [← join_eq_some_iff.mp joined, Finset.mem_union]

/-! ## Exact relationship to origin-coherent composition -/

def OneRepresentativePerOrigin
    (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries, first.origin = second.origin → first = second

instance (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Decidable (OneRepresentativePerOrigin entries) := by
  unfold OneRepresentativePerOrigin
  infer_instance

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem OneRepresentativePerOrigin.mono
    {entries smaller : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (single : OneRepresentativePerOrigin entries) (subset : smaller ⊆ entries) :
    OneRepresentativePerOrigin smaller := by
  intro first firstMem second secondMem same
  exact single first (subset firstMem) second (subset secondMem) same

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem coherent_valid_iff (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    ModuleAlgebra.Valid entries ↔ Valid entries ∧ OneRepresentativePerOrigin entries := by
  constructor
  · intro valid
    exact ⟨fun a ha b hb same => valid a ha b hb (Or.inr same),
      fun a ha b hb same => valid a ha b hb (Or.inl same)⟩
  · rintro ⟨labels, origins⟩ a ha b hb (same | same)
    · exact origins a ha b hb same
    · exact labels a ha b hb same

def OriginAgreement (first second : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Prop := ∀ a ∈ first, ∀ b ∈ second, a.origin = b.origin → a = b

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem OriginAgreement.symm {first second : Fragment (Origin := Origin) (Label := Label) (Body := Body)}
    (agree : OriginAgreement first second) : OriginAgreement second first := by
  intro a ha b hb same
  exact (agree b hb a ha same.symm).symm

theorem union_single_iff (p q : ModuleAlgebra.Presentation Origin Label Body) :
    OneRepresentativePerOrigin (p.val ∪ q.val) ↔ OriginAgreement p.val q.val := by
  constructor
  · intro single a ha b hb same
    exact single a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb) same
  · intro agree a ha b hb same
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · exact p.property a ha b hb (Or.inl same)
    · exact agree a ha b hb same
    · exact (agree b hb a ha same.symm).symm
    · exact q.property a ha b hb (Or.inl same)

def ofCoherent (p : ModuleAlgebra.Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val, ((coherent_valid_iff p.val).mp p.property).1⟩

@[simp] theorem ofCoherent_val (p : ModuleAlgebra.Presentation Origin Label Body) :
    (ofCoherent p).val = p.val := rfl

theorem ofCoherent_injective : Function.Injective
    (ofCoherent : ModuleAlgebra.Presentation Origin Label Body → Presentation Origin Label Body) := by
  intro p q same
  exact Subtype.ext (congrArg (fun view : Presentation Origin Label Body => view.val) same)

/-- Recovery checks the additional origin-coherence obligation; it does not erase views. -/
def coherentOfView? (p : Presentation Origin Label Body) :
    Option (ModuleAlgebra.Presentation Origin Label Body) := ModuleAlgebra.check p.val

theorem coherentOfView_isSome_iff (p : Presentation Origin Label Body) :
    (coherentOfView? p).isSome = true ↔ OneRepresentativePerOrigin p.val := by
  simp [coherentOfView?, ModuleAlgebra.check, coherent_valid_iff, p.property]

@[simp] theorem coherentOfView_ofCoherent (p : ModuleAlgebra.Presentation Origin Label Body) :
    coherentOfView? (ofCoherent p) = some p := ModuleAlgebra.check_val p

theorem ofCoherent_recovered {p : Presentation Origin Label Body}
    {q : ModuleAlgebra.Presentation Origin Label Body} (recovered : coherentOfView? p = some q) :
    ofCoherent q = p := by
  apply Subtype.ext
  exact (ModuleAlgebra.check_eq_some_iff.mp recovered).symm

theorem check_coherent_through_view
    (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    (check entries).bind coherentOfView? = ModuleAlgebra.check entries := by
  by_cases valid : Valid entries
  · simp [check, valid, coherentOfView?]
  · have invalid : ¬ ModuleAlgebra.Valid entries :=
      fun h => valid ((coherent_valid_iff entries).mp h).1
    simp [check, valid, ModuleAlgebra.check, invalid]

theorem join_coherent_through_view (p q : ModuleAlgebra.Presentation Origin Label Body) :
    (join (ofCoherent p) (ofCoherent q)).bind coherentOfView? = ModuleAlgebra.join p q :=
  check_coherent_through_view (p.val ∪ q.val)

theorem coherent_join_isSome_iff (p q : ModuleAlgebra.Presentation Origin Label Body) :
    (ModuleAlgebra.join p q).isSome = true ↔
      (join (ofCoherent p) (ofCoherent q)).isSome = true ∧ OriginAgreement p.val q.val := by
  have coherentCheck : (ModuleAlgebra.check (p.val ∪ q.val)).isSome = true ↔
      ModuleAlgebra.Valid (p.val ∪ q.val) := by simp [ModuleAlgebra.check]
  change (ModuleAlgebra.check (p.val ∪ q.val)).isSome = true ↔
    (check (p.val ∪ q.val)).isSome = true ∧ OriginAgreement p.val q.val
  rw [coherentCheck, check_isSome_iff, coherent_valid_iff, union_single_iff]

theorem check_agreement_of_single
    (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body))
    (single : OneRepresentativePerOrigin entries) :
    (ModuleAlgebra.check entries).map ofCoherent = check entries := by
  by_cases valid : Valid entries
  · have coherent := (coherent_valid_iff entries).mpr ⟨valid, single⟩
    simp [ModuleAlgebra.check, coherent, check, valid, ofCoherent]
  · have invalid : ¬ ModuleAlgebra.Valid entries :=
      fun h => valid ((coherent_valid_iff entries).mp h).1
    simp [ModuleAlgebra.check, invalid, check, valid]

/-- The agreement obligation concerns the union, not each operand separately. -/
theorem join_agreement_of_union_single (p q : ModuleAlgebra.Presentation Origin Label Body)
    (single : OneRepresentativePerOrigin (p.val ∪ q.val)) :
    (ModuleAlgebra.join p q).map ofCoherent = join (ofCoherent p) (ofCoherent q) :=
  check_agreement_of_single (p.val ∪ q.val) single

theorem meet_agreement_of_union_single (p q : ModuleAlgebra.Presentation Origin Label Body)
    (single : OneRepresentativePerOrigin (p.val ∪ q.val)) :
    ofCoherent (ModuleAlgebra.meet p q) = meet (ofCoherent p) (ofCoherent q) := by
  apply Subtype.ext
  ext entry
  change (entry ∈ p.val.filter (fun a => ∃ b ∈ q.val, a.origin = b.origin)) ↔
    entry ∈ p.val ∩ q.val
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hp, other, hq, same⟩
    have equal := single entry (Finset.mem_union_left _ hp)
      other (Finset.mem_union_right _ hq) same
    exact ⟨hp, equal ▸ hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨hp, entry, hq, rfl⟩

theorem diff_agreement_of_union_single (p q : ModuleAlgebra.Presentation Origin Label Body)
    (single : OneRepresentativePerOrigin (p.val ∪ q.val)) :
    ofCoherent (ModuleAlgebra.diff p q) = diff (ofCoherent p) (ofCoherent q) := by
  apply Subtype.ext
  ext entry
  change (entry ∈ p.val.filter (fun a => ¬ ∃ b ∈ q.val, a.origin = b.origin)) ↔
    entry ∈ p.val \ q.val
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp, noOrigin⟩
    exact ⟨hp, fun hq => noOrigin ⟨entry, hq, rfl⟩⟩
  · rintro ⟨hp, absent⟩
    refine ⟨hp, ?_⟩
    rintro ⟨other, hq, same⟩
    have equal := single entry (Finset.mem_union_left _ hp)
      other (Finset.mem_union_right _ hq) same
    exact absent (equal ▸ hq)

theorem meet_agreement_iff (p q : ModuleAlgebra.Presentation Origin Label Body) :
    ofCoherent (ModuleAlgebra.meet p q) = meet (ofCoherent p) (ofCoherent q) ↔
      OriginAgreement p.val q.val := by
  constructor
  · intro same a ha b hb origin
    have kept : a ∈ (ModuleAlgebra.meet p q).val :=
      Finset.mem_filter.mpr ⟨ha, b, hb, origin⟩
    have represented : a ∈ (meet (ofCoherent p) (ofCoherent q)).val := by
      rw [← same]
      exact kept
    exact q.property a (Finset.mem_inter.mp represented).2 b hb (Or.inl origin)
  · intro agree
    exact meet_agreement_of_union_single p q ((union_single_iff p q).mpr agree)

theorem diff_agreement_iff (p q : ModuleAlgebra.Presentation Origin Label Body) :
    ofCoherent (ModuleAlgebra.diff p q) = diff (ofCoherent p) (ofCoherent q) ↔
      OriginAgreement p.val q.val := by
  constructor
  · intro same a ha b hb origin
    by_contra different
    have absent : a ∉ q.val := by
      intro member
      exact different (q.property a member b hb (Or.inl origin))
    have kept : a ∈ (diff (ofCoherent p) (ofCoherent q)).val := Finset.mem_sdiff.mpr ⟨ha, absent⟩
    have coherentKept : a ∈ (ModuleAlgebra.diff p q).val := by
      rw [← same] at kept
      exact kept
    exact (Finset.mem_filter.mp coherentKept).2 ⟨b, hb, origin⟩
  · intro agree
    exact diff_agreement_of_union_single p q ((union_single_iff p q).mpr agree)

/-! ## Authored composition through the existing coGSLT boundary -/

section Authoring

variable {Origin Label Body : Type}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

abbrev Document (Origin Label Body : Type) := ModuleAlgebra.Document Origin Label Body

def elaborate (document : Document Origin Label Body) : Option (Presentation Origin Label Body) :=
  check (ModuleAlgebra.unionFragments document.values)

def quote (p : Presentation Origin Label Body) : Document Origin Label Body := .declaration p.val

@[simp] theorem elaborate_quote (p : Presentation Origin Label Body) :
    elaborate (quote p) = some p := by
  simp [elaborate, quote, DeclarationDocument.values, ModuleAlgebra.unionFragments]

def presentationSystem : GSLT.CompositionalElaboration (Presentation Origin Label Body) where
  authoring := ExactDeclarationCodec.documentCompositional (Finset (Entry Origin Label Body))
  elaboration := {
    elaborate := elaborate
    quote := quote
    elaborate_quote := elaborate_quote
    equation := by
      intro first second equivalent
      change first.values = second.values at equivalent
      unfold elaborate
      rw [equivalent]
    rewrite := by intro first second impossible; exact False.elim impossible }
  emptyPayload := empty
  merge := join
  elaborate_empty := by
    simp [elaborate, ExactDeclarationCodec.documentCompositional,
      DeclarationDocument.values, DeclarationDocument.valuesList, ModuleAlgebra.unionFragments,
      check, empty]
  elaborate_append := by
    intro first second
    change Document Origin Label Body at first second
    change elaborate (.bundle [first, second]) = _
    simp only [elaborate, DeclarationDocument.values, DeclarationDocument.valuesList,
      List.append_nil]
    rw [ModuleAlgebra.unionFragments_append, check_union]

theorem join_assoc (first second third : Presentation Origin Label Body) :
    (join first second).bind (fun merged => join merged third) =
      (join second third).bind (fun merged => join first merged) :=
  presentationSystem.toPartialMonoid.op_assoc first second third

def presentationLayer (Base : Type) : CompositionalLayer Base where
  Fiber := fun _ => Presentation Origin Label Body
  system := fun _ => presentationSystem

def presentationCoGSLT (Base : Type) : CoGSLTLayer Base :=
  (presentationLayer (Origin := Origin) (Label := Label) (Body := Body) Base).toCoGSLTLayer

theorem elaborate_coherent_through_view (document : Document Origin Label Body) :
    (elaborate document).bind coherentOfView? = ModuleAlgebra.elaborate document :=
  check_coherent_through_view (ModuleAlgebra.unionFragments document.values)

end Authoring

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginView
