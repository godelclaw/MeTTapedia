import Mettapedia.Computability.RegularLanguages.RegexPublicSearch

/-!
# Conservative first-consumption rejection

A finite certificate contains the entry and is closed under every epsilon
edge, including assertions treated as possible. It rejects accepting sites
and requires every exposed consuming class to reject the current scalar.
Such a certificate excludes *all* accepting traces, not merely the selected
one. Removing these completed-absent attempts from the ordered start scan
preserves captures and priority. Bounded/incomplete attempts are not erased.

The native ASCII bitset is a conservative representation of these exposed
classes; non-ASCII inputs and unknown/nullable graphs remain admitted. This
file proves the graph/scan law, not the native analysis or injected-frontier C
implementation. In particular it does not justify dropping an active thread.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexStartFilter

open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe)

universe u v w z
variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- The check is local and independent of the search implementation. Ignoring
assertion truth overapproximates paths instead of assuming assertions hold. -/
def ClosedReject (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (position : Fin (length + 1))
    (sites : Set State) : Prop :=
  ∀ state ∈ sites, match graph state with
    | .accept _ => False
    | .dead => True
    | .consume class_ _ => probe.contains class_ position = false
    | .jump next | .save _ next | .assertion _ next => next ∈ sites
    | .choice first second => first ∈ sites ∧ second ∈ sites

theorem next_stays {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {position : Fin (length + 1)} {sites : Set State}
    (closed : ClosedReject graph probe position sites) {first target : Thread State length}
    (member : first.point.1 ∈ sites) (positionEq : first.point.2 = position)
    (step : action graph probe first = .next target) :
    target.point.1 ∈ sites ∧ target.point.2 = position := by
  have checked := closed first.point.1 member
  cases node : graph first.point.1 <;>
    simp_all [action, Thread.at, Thread.saved, Thread.branch]
  case jump => rw [← step]; exact ⟨checked, rfl⟩
  case save => rw [← step]; exact ⟨checked, rfl⟩
  case assertion =>
    split at step <;> simp_all
    rw [← step]; exact ⟨checked, rfl⟩

theorem branches_stay {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {position : Fin (length + 1)} {sites : Set State}
    (closed : ClosedReject graph probe position sites) {first left right : Thread State length}
    (member : first.point.1 ∈ sites) (positionEq : first.point.2 = position)
    (step : action graph probe first = .branch left right) :
    (left.point.1 ∈ sites ∧ left.point.2 = position) ∧
      (right.point.1 ∈ sites ∧ right.point.2 = position) := by
  have checked := closed first.point.1 member
  cases node : graph first.point.1 <;>
    simp_all [action, Thread.at, Thread.saved, Thread.branch]
  case choice =>
    obtain ⟨rfl, rfl⟩ := step
    exact ⟨⟨checked.1, rfl⟩, ⟨checked.2, rfl⟩⟩
  case assertion => split at step <;> simp_all

theorem rejects_trace {graph : State → Node State Class Assertion Tag}
    {probe : Probe Class Assertion length} {eligible : Thread State length → Bool}
    {position : Fin (length + 1)} {sites : Set State}
    (closed : ClosedReject graph probe position sites)
    {first last : Thread State length} {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe eligible first code points last tag)
    (member : first.point.1 ∈ sites) (positionEq : first.point.2 = position) : False := by
  induction trace with
  | @done first tag step _ =>
      have checked := closed _ member
      cases node : graph first.point.1 <;> simp_all [action]
      split at step <;> simp_all
  | next step _ ih =>
      have next := next_stays closed member positionEq step
      exact ih next.1 next.2
  | left step _ ih =>
      have next := (branches_stay closed member positionEq step).1
      exact ih next.1 next.2
  | right step _ ih =>
      have next := (branches_stay closed member positionEq step).2
      exact ih next.1 next.2

theorem rejected_entry_absent [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length) (sites : Set State)
    (member : first.point.1 ∈ sites) (closed : ClosedReject graph probe first.point.2 sites)
    (fuel : Nat) (enough : Fintype.card (Point State length) + 1 < fuel) :
    RegexPublicSearch.anchored graph probe eligible fuel first = .finished none := by
  apply (RegexPublicSearch.anchored_absent_iff graph probe eligible first fuel enough).mpr
  rintro ⟨last, tag, least, _⟩
  obtain ⟨code, points, label, trace, _, _⟩ := least
  exact rejects_trace closed trace member rfl

/-- Only proved completed absence may be skipped. An earlier unfinished
attempt still blocks later candidates under the original scan contract. -/
theorem scan_filter {Start : Type u} {Value : Type v} {Label : Type w}
    (attempt : Start → RegexPikeVM.Result Value Label) (keep : Start → Bool)
    (absent : ∀ start, keep start = false → attempt start = .finished none)
    (starts : List Start) :
    RegexPublicSearch.scan attempt (starts.filter keep) = RegexPublicSearch.scan attempt starts := by
  induction starts with
  | nil => rfl
  | cons first rest ih =>
      cases kept : keep first with
      | false => simp [kept, RegexPublicSearch.scan, absent first kept, ih]
      | true =>
          simp only [List.filter_cons, kept, ↓reduceIte, RegexPublicSearch.scan]
          cases attempt first with
          | incomplete => rfl
          | finished selected => cases selected <;> simp [ih]

theorem certified_scan_filter [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (entry : State) (keep : Fin (length + 1) → Bool)
    (certificates : ∀ position, keep position = false →
      ∃ sites, entry ∈ sites ∧ ClosedReject graph probe position sites)
    (fuel : Nat) (enough : Fintype.card (Point State length) + 1 < fuel)
    (starts : List (Fin (length + 1))) :
    RegexPublicSearch.search graph probe eligible entry fuel (starts.filter keep) =
      RegexPublicSearch.search graph probe eligible entry fuel starts := by
  apply scan_filter
  intro position rejected
  obtain ⟨sites, member, closed⟩ := certificates position rejected
  exact rejected_entry_absent graph probe eligible (RegexPublicSearch.entry entry position)
    sites member closed fuel enough

theorem accepting_site_cannot_be_rejected
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (position : Fin (length + 1)) (sites : Set State) (state : State) (tag : Tag)
    (member : state ∈ sites) (accepting : graph state = .accept tag) :
    ¬ ClosedReject graph probe position sites := by
  intro closed
  simpa [accepting] using closed state member

/-- A rejected consuming loop is safe even though its graph is cyclic. -/
example (probe : Probe Unit Unit length) (position : Fin (length + 1))
    (reject : probe.contains () position = false) :
    ClosedReject (Tag := Unit) (fun _ : Unit => .consume () ()) probe position Set.univ := by
  intro state _
  exact reject

/-- Incomplete work is not a rejection certificate for removing a start. -/
example : RegexPublicSearch.scan (fun _ : Nat => (RegexPikeVM.Result.incomplete : RegexPikeVM.Result Unit Unit))
    [0] ≠ RegexPublicSearch.scan (fun _ : Nat => (RegexPikeVM.Result.incomplete : RegexPikeVM.Result Unit Unit))
    [] := by simp [RegexPublicSearch.scan]

#print axioms rejects_trace
#print axioms certified_scan_filter

end Mettapedia.Computability.RegularLanguages.RegexStartFilter
