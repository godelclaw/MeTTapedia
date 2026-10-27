import Mettapedia.GSLT.Coordination.HomeLocation

/-!
# Occurrence identities qualified by the location that allocates them

`HomeLocation` takes freshness from one global set of used identities. No location can consult
such a set without coordination. This module removes it: every identity names the location that
allocated it (`maker`), and each location keeps only its own record of what it allocated
(`LNet.allocated`). A commit at a location may make only identities that the location qualifies
and that its own record does not contain (`LAccepts`).

## Freshness is local

* **For an identity qualified by a location, being new to that location is being new everywhere**
  (`fresh_local`): when every location's record holds only identities it qualifies
  (`Qualified`), an identity qualified by `site` is outside the union of all records exactly when
  it is outside `site`'s record.
* **A per-location counter realizes the record** (`counter_fresh`): with identities `(site, k)`,
  a location whose record holds only numbers below its counter allocates `(site, counter)`
  without asking anyone.

## The global set is derived, and the refinement survives

The union of the local records plays the role of `HomeLocation`'s global set (`LNet.toNet`).

* **Every locally accepted commit is accepted by the global rule** (`accepts_of_laccepts`), and
  the located step is the global step (`toNet_lstep_commit`, `toNet_lstep_deliver`).
* **Every located run is an atomic run** (`lrun_refines`): the commits a located network performs
  are a legal run of the atomic semantics from the whole initial store, ending at the whole final
  store. This is `HomeLocation.run_refines` with the global set discharged.

Occurrence identities are not content identities: the label of an occurrence is its content, and
two occurrences with one label are two identities (`OccurrenceCommits.Commits`). Qualified
identities are the occurrence identities a runtime keeps next to content identities; claims,
epochs and takes refer to them.

## Controls

* `Controls.unqualified_collision`: two locations that each allocate from their own record, with
  no qualification, both make identity `7`; each was fresh locally, the second is not fresh in the
  whole store, and the two commits are not an atomic run.
* `Controls.foreign_refused`: a location may not allocate an identity qualified by another
  location.
* `Controls.qualified_no_collision`: the same two allocations, qualified, are an atomic run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.LocatedIdentities

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Coordination.ReplicaMerge
open Mettapedia.GSLT.Coordination.HomeLocation

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {L : Type w} [DecidableEq L]

/-- A located network: each location's store, the messages in flight, and each location's own
record of the identities it allocated. There is no global record. -/
structure LNet (O : Type u) (L : Type w) where
  store : L → Finset O
  inflight : Finset O
  allocated : L → Finset O

variable (label : O → R) (home : R → L) (maker : O → L)

/-- **Local acceptance**: the commit is enabled at its location's store, every identity it makes
is qualified by that location, and none is in that location's own record. -/
def LAccepts (net : LNet O L) (p : Placed O R L) : Prop :=
  Enabled label (net.store p.site) p.commit ∧ (∀ o ∈ p.commit.made, maker o = p.site) ∧
    Disjoint p.commit.made (net.allocated p.site)

instance (net : LNet O L) (p : Placed O R L) : Decidable (LAccepts label maker net p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- One event of a located network. A commit records its new identities at its own location only. -/
def lstep (net : LNet O L) : Event O R L → LNet O L
  | .commit p =>
      if LAccepts label maker net p then
        { store := Function.update net.store p.site
            ((net.store p.site \ p.commit.taken) ∪ madeHere label home p.site p.commit)
          inflight := net.inflight ∪ madeAway label home p.site p.commit
          allocated := Function.update net.allocated p.site (net.allocated p.site ∪ p.commit.made) }
      else net
  | .deliver o =>
      if o ∈ net.inflight then
        { net with
          store := Function.update net.store (home (label o)) (insert o (net.store (home (label o))))
          inflight := net.inflight.erase o }
      else net

variable {label home maker}

/-- Every location's record holds only identities that it qualifies. -/
def Qualified (net : LNet O L) : Prop := ∀ l, ∀ o ∈ net.allocated l, maker o = l

variable [Fintype L]

/-- The union of the local records: what a central allocator would have had to keep. -/
def LNet.used (net : LNet O L) : Finset O := Finset.univ.biUnion net.allocated

/-- The network of `HomeLocation` that a located network stands for. -/
def LNet.toNet (net : LNet O L) : Net O L := ⟨net.store, net.inflight, net.used⟩

omit [DecidableEq L] in
theorem mem_used {net : LNet O L} {o : O} : o ∈ net.used ↔ ∃ l, o ∈ net.allocated l := by
  simp [LNet.used]

omit [DecidableEq L] in
/-- **Freshness is local.** For an identity qualified by `site`, being outside every location's
record is being outside `site`'s own record. -/
theorem fresh_local {net : LNet O L} (qualified : Qualified (maker := maker) net)
    {site : L} {o : O} (qualifies : maker o = site) :
    o ∉ net.used ↔ o ∉ net.allocated site := by
  rw [mem_used]
  constructor
  · exact fun notUsed inSite => notUsed ⟨site, inSite⟩
  · rintro notSite ⟨l, inL⟩
    have := qualified l o inL
    rw [qualifies] at this
    subst this
    exact notSite inL

omit [DecidableEq L] in
theorem disjoint_used_of_local {net : LNet O L} (qualified : Qualified (maker := maker) net)
    {site : L} {made : Finset O} (qualifies : ∀ o ∈ made, maker o = site)
    (local' : Disjoint made (net.allocated site)) : Disjoint made net.used :=
  Finset.disjoint_left.mpr fun o member =>
    (fresh_local qualified (qualifies o member)).mpr (Finset.disjoint_left.mp local' member)

omit [DecidableEq L] in
/-- **A locally accepted commit is accepted by the global rule.** -/
theorem accepts_of_laccepts {net : LNet O L} (qualified : Qualified (maker := maker) net)
    {p : Placed O R L} (accepts : LAccepts label maker net p) : Accepts label net.toNet p :=
  ⟨accepts.1, disjoint_used_of_local qualified accepts.2.1 accepts.2.2⟩

omit [DecidableEq O] in
theorem used_update [DecidableEq O] (allocated : L → Finset O) (site : L) (made : Finset O) :
    Finset.univ.biUnion (Function.update allocated site (allocated site ∪ made)) =
      Finset.univ.biUnion allocated ∪ made := by
  ext o
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Function.update_apply]
  constructor
  · rintro ⟨l, member⟩
    split_ifs at member with same
    · rcases Finset.mem_union.mp member with old | new
      · exact Or.inl ⟨site, old⟩
      · exact Or.inr new
    · exact Or.inl ⟨l, member⟩
  · rintro (⟨l, member⟩ | new)
    · by_cases same : l = site
      · subst same
        exact ⟨l, by rw [if_pos rfl]; exact Finset.mem_union_left _ member⟩
      · exact ⟨l, by rw [if_neg same]; exact member⟩
    · exact ⟨site, by rw [if_pos rfl]; exact Finset.mem_union_right _ new⟩

/-- An accepted located commit is the global step. -/
theorem toNet_lstep_commit {net : LNet O L} (qualified : Qualified (maker := maker) net)
    {p : Placed O R L} (accepts : LAccepts label maker net p) :
    (lstep label home maker net (.commit p)).toNet = step label home net.toNet (.commit p) := by
  have global := accepts_of_laccepts qualified accepts
  simp only [step]
  rw [if_pos global]
  simp only [lstep, if_pos accepts, LNet.toNet, LNet.used, used_update]

/-- A delivery is the global delivery. -/
theorem toNet_lstep_deliver (net : LNet O L) (o : O) :
    (lstep label home maker net (.deliver o)).toNet = step label home net.toNet (.deliver o) := by
  by_cases flying : o ∈ net.inflight
  · simp [lstep, step, LNet.toNet, LNet.used, flying]
  · simp [lstep, step, LNet.toNet, flying]

omit [Fintype L] in
/-- Every step keeps the records qualified. -/
theorem qualified_lstep {net : LNet O L} (qualified : Qualified (maker := maker) net)
    (e : Event O R L) : Qualified (maker := maker) (lstep label home maker net e) := by
  cases e with
  | commit p =>
      simp only [lstep]
      split_ifs with accepts
      · intro l o member
        simp only [Function.update_apply] at member
        split_ifs at member with same
        · subst same
          rcases Finset.mem_union.mp member with old | new
          · exact qualified _ o old
          · exact accepts.2.1 o new
        · exact qualified l o member
      · exact qualified
  | deliver o =>
      simp only [lstep]
      split_ifs
      · exact qualified
      · exact qualified

/-! ## Runs -/

variable (label home maker)

/-- The commits a located event performs. -/
def lperformed (net : LNet O L) : Event O R L → List (Commit O R)
  | .commit p => if LAccepts label maker net p then [p.commit] else []
  | .deliver _ => []

/-- A located run. -/
def lrunNet (net : LNet O L) : List (Event O R L) → LNet O L
  | [] => net
  | e :: es => lrunNet (lstep label home maker net e) es

/-- The commits a located run performs, in order. -/
def lperformedAll (net : LNet O L) : List (Event O R L) → List (Commit O R)
  | [] => []
  | e :: es => lperformed label maker net e ++ lperformedAll (lstep label home maker net e) es

variable {label home maker}

/-- **Every located run is an atomic run**: with qualified records and the invariant of
`HomeLocation` for the derived network, the commits a located run performs are a legal run of the
atomic semantics from the whole initial store, ending at the whole final store. No location ever
consulted another's record. -/
theorem lrun_refines {program : List (Placed O R L)} (homedAll : ∀ p ∈ program, HomedAt label home p)
    (closed : ClosedQueries label program) (events : List (Event O R L))
    (inProgram : ∀ p, Event.commit p ∈ events → p ∈ program) :
    ∀ net : LNet O L, Qualified (maker := maker) net → Inv label home program net.toNet →
      Executable label (whole net.toNet) (lperformedAll label home maker net events) ∧
        whole (lrunNet label home maker net events).toNet =
          fireList (whole net.toNet) (lperformedAll label home maker net events) := by
  induction events with
  | nil => intro net _ _; exact ⟨Executable.nil _, rfl⟩
  | cons e rest ih =>
      intro net qualified inv
      have restProgram : ∀ p, Event.commit p ∈ rest → p ∈ program :=
        fun p member => inProgram p (List.mem_cons_of_mem _ member)
      have qualifiedNext := qualified_lstep (label := label) (home := home) qualified e
      cases e with
      | commit p =>
          have pIn := inProgram p (List.mem_cons_self ..)
          by_cases accepts : LAccepts label maker net p
          · have global := accepts_of_laccepts qualified accepts
            obtain ⟨enabled, wholeEq⟩ := commit_refines inv pIn (homedAll p pIn) global
            have invNext : Inv label home program (lstep label home maker net (.commit p)).toNet := by
              rw [toNet_lstep_commit qualified accepts]
              exact inv_commit homedAll closed inv pIn global
            obtain ⟨legal, final⟩ := ih restProgram _ qualifiedNext invNext
            have wholeNext : whole (lstep label home maker net (.commit p)).toNet =
                fire (whole net.toNet) p.commit := by
              rw [toNet_lstep_commit qualified accepts]; exact wholeEq
            simp only [lperformedAll, lperformed, if_pos accepts, List.singleton_append, lrunNet]
            rw [wholeNext] at legal final
            exact ⟨Executable.cons enabled legal, final⟩
          · have same : lstep label home maker net (.commit p) = net := by simp [lstep, accepts]
            simp only [lperformedAll, lperformed, if_neg accepts, List.nil_append, lrunNet, same]
            exact ih restProgram net qualified inv
      | deliver o =>
          have invNext : Inv label home program (lstep label home maker net (.deliver o)).toNet := by
            rw [toNet_lstep_deliver]
            exact inv_deliver inv o
          obtain ⟨legal, final⟩ := ih restProgram _ qualifiedNext invNext
          have wholeNext : whole (lstep label home maker net (.deliver o)).toNet = whole net.toNet := by
            rw [toNet_lstep_deliver]; exact deliver_whole o
          simp only [lperformedAll, lperformed, List.nil_append, lrunNet]
          rw [wholeNext] at legal final
          exact ⟨legal, final⟩

/-! ## A counter per location -/

section Counter

variable {L : Type w} [DecidableEq L] [Fintype L]

/-- **A counter per location realizes the record**: with identities `(site, k)`, if `site`'s
record holds only numbers below its counter, `(site, counter)` is new to every location. -/
theorem counter_fresh {net : LNet (L × ℕ) L} (qualified : Qualified (maker := Prod.fst) net)
    {site : L} {counter : ℕ} (below : ∀ o ∈ net.allocated site, o.2 < counter) :
    (site, counter) ∉ net.used :=
  (fresh_local qualified rfl).mpr fun member => by
    have := below _ member
    simp at this

end Counter

/-! ## Controls -/

namespace Controls

/-- Labels: the location an occurrence is for. -/
def toward : ℕ → Bool := fun o => decide (o % 2 = 0)

/-- Each location makes occurrence `7` for itself. -/
def makeSeven : Commit ℕ Bool := ⟨∅, ∅, {7}, []⟩

/-- Acceptance with each location's own record and no qualification: only local freshness. -/
def unqualifiedAccepts (net : LNet ℕ Bool) (p : Placed ℕ Bool Bool) : Prop :=
  Enabled toward (net.store p.site) p.commit ∧ Disjoint p.commit.made (net.allocated p.site)

/-- The empty located network. -/
def empty : LNet ℕ Bool := ⟨fun _ => ∅, ∅, fun _ => ∅⟩

/-- **Unqualified local allocation collides**: both locations accept making `7`, each fresh in its
own record, and the two commits are not an atomic run, because the second identity is not fresh
once the first exists. -/
theorem unqualified_collision :
    unqualifiedAccepts empty ⟨makeSeven, true⟩ ∧
      unqualifiedAccepts ⟨fun site => if site then {7} else ∅, ∅,
          fun site => if site then {7} else ∅⟩ ⟨makeSeven, false⟩ ∧
      ¬ Executable toward (∅ : Finset ℕ) [makeSeven, makeSeven] := by
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by simp [makeSeven]⟩, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide, by simp [makeSeven]⟩, by decide⟩, ?_⟩
  intro legal
  cases legal with
  | cons _ rest =>
      cases rest with
      | cons enabled _ =>
          have := enabled.fresh
          simp [makeSeven, fire] at this

/-- Identities `(location, k)`; the maker is the first component. -/
def qualifiedSeven (site : Bool) : Commit (Bool × ℕ) Bool := ⟨∅, ∅, {(site, 7)}, []⟩

/-- **A location may not allocate an identity qualified by another location.** -/
theorem foreign_refused :
    ¬ LAccepts (fun o : Bool × ℕ => o.1) Prod.fst (⟨fun _ => ∅, ∅, fun _ => ∅⟩ : LNet (Bool × ℕ) Bool)
      ⟨qualifiedSeven true, false⟩ := by
  rintro ⟨_, qualifies, _⟩
  have := qualifies (true, 7) (by simp [qualifiedSeven])
  simp at this

/-- **Qualified, the same two allocations are an atomic run**: `(true, 7)` and `(false, 7)` are two
identities. -/
theorem qualified_no_collision :
    Executable (fun o : Bool × ℕ => o.1) (∅ : Finset (Bool × ℕ)) [qualifiedSeven true, qualifiedSeven false] := by
  refine Executable.cons ⟨by simp [qualifiedSeven], by simp [qualifiedSeven], by simp [qualifiedSeven],
    by simp [qualifiedSeven], by simp [qualifiedSeven]⟩ ?_
  refine Executable.cons ⟨by simp [qualifiedSeven], by simp [qualifiedSeven], by simp [qualifiedSeven],
    ?_, by simp [qualifiedSeven]⟩ (Executable.nil _)
  simp [qualifiedSeven, fire]

/-! ### Qualified records -/

/-- Each site has allocated identity `7` qualified by itself. -/
def sitesQualified : LNet (Bool × ℕ) Bool := ⟨fun _ => ∅, ∅, fun site => {(site, 7)}⟩

/-- Each site has recorded identity `7` qualified by the other site. -/
def sitesSwapped : LNet (Bool × ℕ) Bool := ⟨fun _ => ∅, ∅, fun site => {(!site, 7)}⟩

/-- **Positive control**: every record holds only identities its own site qualifies. -/
theorem sitesQualified_qualified : Qualified (maker := Prod.fst) sitesQualified := by
  unfold Qualified; decide

/-- **Negative control**: each record holds an identity the other site qualifies. -/
theorem sitesSwapped_not_qualified : ¬ Qualified (maker := Prod.fst) sitesSwapped := by
  unfold Qualified; decide

/-- **A location allocates an identity qualified by itself**: the positive side of
`foreign_refused`. -/
theorem own_accepted :
    LAccepts (fun o : Bool × ℕ => o.1) Prod.fst (⟨fun _ => ∅, ∅, fun _ => ∅⟩ : LNet (Bool × ℕ) Bool)
      ⟨qualifiedSeven true, true⟩ := by
  decide

end Controls

end Mettapedia.GSLT.Coordination.LocatedIdentities
