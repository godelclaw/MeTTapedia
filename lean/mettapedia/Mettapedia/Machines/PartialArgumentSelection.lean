import Mettapedia.GSLT.LanguageDef.MatchDecisionContract
import Mettapedia.Machines.MatchIndexProjection

/-!
# Partial argument observations for ordered candidate selection

A logical list carrier can make one argument's physical representation
unsuitable for a structural index. This forgets that argument's entire
subtree, retaining available observations of the other arguments. It does
not infer that an unavailable argument is absent or unevaluated.

The native adapter must establish faithful observations at the positions it
keeps. Its representation metadata and the ordinary matcher's effects,
bindings and lifetime behavior are separate implementation obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.PartialArgumentSelection

open Mettapedia.GSLT.LanguageDef.MatchDecisionContract (Path)
open Mettapedia.GSLT.LanguageDef.MatchDecisionContract.Shaped

def available (arguments : Nat → Bool) : Path → Bool
  | [] => true
  | 0 :: _ => true
  | (argument + 1) :: _ => arguments argument

def observe {V : Type} (arguments : Nat → Bool) (source : Skeleton V) : Skeleton V :=
  fun path => if available arguments path then source path else .unknown

theorem observe_le {V : Type} (arguments : Nat → Bool) (source : Skeleton V) :
    Skeleton.LE (observe arguments source) source := by
  intro path
  simp only [observe]
  split
  · exact Obs.le.refl _
  · trivial

theorem unavailable_subtree {V : Type} (arguments : Nat → Bool) (source : Skeleton V)
    (argument : Nat) (suffix : Path) (unavailable : arguments argument = false) :
    observe arguments source ((argument + 1) :: suffix) = .unknown := by
  simp [observe, available, unavailable]

theorem available_subtree {V : Type} (arguments : Nat → Bool) (source : Skeleton V)
    (argument : Nat) (suffix : Path) (ready : arguments argument = true) :
    observe arguments source ((argument + 1) :: suffix) =
      source ((argument + 1) :: suffix) := by
  simp [observe, available, ready]

theorem realizes_observe {V : Type} (arguments : Nat → Bool)
    {source : Skeleton V} {term : Term V} (realized : Realizes term source) :
    Realizes term (observe arguments source) :=
  realized.anti (observe_le arguments source)

theorem candidate_retained {V : Type} [DecidableEq V] (arguments : Nat → Bool)
    (samples : List Path) (source : Skeleton V) (rows : List (Candidate V))
    (row : Candidate V) (term : Term V) (member : row ∈ rows)
    (query : Realizes term source) (matched : Realizes term row.pat) :
    row ∈ candidates samples (observe arguments source) rows :=
  mem_candidates_of_realizes member (realizes_observe arguments query) matched

theorem ordered_sublist {V : Type} [DecidableEq V] (arguments : Nat → Bool)
    (samples : List Path) (source : Skeleton V) (rows : List (Candidate V)) :
    (candidates samples (observe arguments source) rows).Sublist rows :=
  candidates_sublist _ _ _

theorem exact_after_matching {V : Type} [DecidableEq V] (arguments : Nat → Bool)
    (samples : List Path) (source : Skeleton V) (rows : List (Candidate V))
    (accept : Candidate V → Bool)
    (accepted : ∀ row, accept row = true →
      ∃ term, Realizes term source ∧ Realizes term row.pat) :
    (candidates samples (observe arguments source) rows).filter accept =
      rows.filter accept := by
  apply MatchIndexProjection.filter_candidates
  intro row matched
  obtain ⟨term, query, pattern⟩ := accepted row matched
  cases conflict : conflictsOn samples (observe arguments source) row.pat with
  | false => rfl
  | true =>
      obtain ⟨path, disagreement⟩ := conflictsOn_sound conflict
      exact False.elim (Obs.conflictB_sound disagreement
        ((realizes_observe arguments query) path) (pattern path))

/-- A bounded observation word leaves every later argument unknown. The
bound limits index work; it does not restrict the source call's arity. -/
def bounded (limit : Nat) (safe : Nat → Bool) (argument : Nat) : Bool :=
  decide (argument < limit) && safe argument

theorem beyond_bound_unknown {V : Type} (limit argument : Nat) (safe : Nat → Bool)
    (source : Skeleton V) (suffix : Path) (outside : limit ≤ argument) :
    observe (bounded limit safe) source ((argument + 1) :: suffix) = .unknown := by
  apply unavailable_subtree
  simp [bounded, Nat.not_lt.mpr outside]

private def query : Skeleton Nat := fun path =>
  if path = [1] then .present 123 else if path = [2] then .present 7 else .unknown

private def row (id key : Nat) : Candidate Nat :=
  ⟨id, fun path => if path = [1] then .present 123
    else if path = [2] then .present key else .unknown⟩

-- The carrier is opaque, while the independent key still excludes a row.
-- Two surviving source occurrences remain two, in their original order.
example : (candidates [[1], [2]] (observe (fun n => decide (n ≠ 0)) query)
    [row 10 8, row 11 7, row 12 7]).map Candidate.id = [11, 12] := by decide

-- Hiding all argument fields is safe but loses useful selection information.
example : (candidates [[1], [2]] (observe (fun _ => false) query)
    [row 10 8, row 11 7, row 12 7]).map Candidate.id = [10, 11, 12] := by decide

-- Reading the private carrier's tag as logical structure rejects a real row.
example : conflictsOn [[1]]
    (fun _ => Obs.present (999 : Nat)) (row 11 7).pat = true ∧
    conflictsOn [[1]] (observe (fun _ => false) query) (row 11 7).pat = false := by decide

end Mettapedia.Machines.PartialArgumentSelection
