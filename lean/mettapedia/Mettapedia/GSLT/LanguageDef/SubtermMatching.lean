import Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
# Ordered subterm-match observations

A match records its authored occurrence and its zero-based child path.
Observations are in subject preorder, then authored rule order. Identical
authored patterns therefore remain distinct observations.

These are matching locations, not permissions to rewrite there. A language's
context, premise, and effect policy remains responsible for rule execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SubtermMatching

open OrderedPatternMatrixCompilation

universe u v
variable {Head : Type u}

abbrev Position := MatchDecisionContract.Path

structure Location where
  position : Position
  occurrence : Nat
deriving DecidableEq, Repr

/-- Project one syntactic child path without interpreting its term. -/
def project : Position → Subject Head → Option (Subject Head)
  | [], subject => some subject
  | i :: path, .node _ children => children[i]?.bind (project path)

theorem project_append (root path : Position) (subject : Subject Head) :
    project (root ++ path) subject = (project root subject).bind (project path) := by
  induction root generalizing subject with
  | nil => rfl
  | cons i root ih =>
      cases subject with
      | node h cs =>
          simp only [List.cons_append, project]
          cases found : cs[i]? <;> simp [ih]

/-- Select authored occurrence indices without deduplication. -/
def select (test : Pattern Head → Bool) : Nat → List (Pattern Head) → List Nat
  | _, [] => []
  | next, p :: ps =>
      if test p then next :: select test (next + 1) ps
      else select test (next + 1) ps

theorem select_congr (test₁ test₂ : Pattern Head → Bool) (patterns : List (Pattern Head))
    (same : ∀ p ∈ patterns, test₁ p = test₂ p) (next : Nat) :
    select test₁ next patterns = select test₂ next patterns := by
  induction patterns generalizing next with
  | nil => rfl
  | cons p ps ih =>
      simp only [select, same p (by simp)]
      rw [ih (fun q hq => same q (by simp [hq]))]

theorem select_eq_zipIdx (test : Pattern Head → Bool) (patterns : List (Pattern Head)) (next : Nat) :
    select test next patterns =
      (patterns.zipIdx next).filterMap (fun entry => if test entry.1 then some entry.2 else none) := by
  induction patterns generalizing next with
  | nil => rfl
  | cons p ps ih =>
      simp only [select, List.zipIdx_cons, List.filterMap_cons]
      rw [ih]
      split <;> rfl

mutual
  /-- Enumerate every subterm in preorder, retaining the actual subject. -/
  def positions : Subject Head → List (Position × Subject Head)
    | s@(.node _ children) => ([], s) :: positionsList 0 children

  def positionsList : Nat → List (Subject Head) → List (Position × Subject Head)
    | _, [] => []
    | next, child :: children =>
        (positions child).map (fun entry => (next :: entry.1, entry.2)) ++
          positionsList (next + 1) children
end

mutual
  /-- Relabelling constructors retains every syntactic position and its
  correspondingly relabelled subtree. -/
  theorem positions_mapHeads {Target : Type v} (f : Head → Target)
      (subject : Subject Head) :
      positions (Subject.mapHeads f subject) =
        (positions subject).map (fun entry => (entry.1, Subject.mapHeads f entry.2)) := by
    cases subject with
    | node head children =>
        simp only [Subject.mapHeads, positions, List.map_cons]
        rw [positionsList_mapHeads f 0 children]

  theorem positionsList_mapHeads {Target : Type v} (f : Head → Target)
      (next : Nat) (subjects : List (Subject Head)) :
      positionsList next (Subject.mapHeadsList f subjects) =
        (positionsList next subjects).map (fun entry => (entry.1, Subject.mapHeads f entry.2)) := by
    cases subjects with
    | nil => rfl
    | cons first rest =>
        simp only [Subject.mapHeadsList, positionsList, List.map_append]
        rw [positions_mapHeads f first, positionsList_mapHeads f (next + 1) rest]
        simp only [List.map_map, Function.comp_def]
end

/-- An injective head encoding keeps the same authored structural matches. -/
theorem select_match_mapHeads {Target : Type v} [DecidableEq Head] [DecidableEq Target]
    (f : Head → Target) (injective : Function.Injective f)
    (patterns : List (Pattern Head)) (subject : Subject Head) (next : Nat) :
    select (fun pattern => structuralMatch pattern (Subject.mapHeads f subject)) next
      (patterns.map (Pattern.mapHeads f)) =
        select (fun pattern => structuralMatch pattern subject) next patterns := by
  induction patterns generalizing next with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, select, structuralMatch_mapHeads f injective]
      rw [ih]

mutual
  /-- Every enumerated position denotes precisely the retained subterm. -/
  theorem positions_sound (subject : Subject Head) (entry : Position × Subject Head)
      (found : entry ∈ positions subject) : project entry.1 subject = some entry.2 := by
    cases subject with
    | node h cs =>
        simp only [positions, List.mem_cons] at found
        rcases found with rfl | found
        · rfl
        · exact positionsList_sound h cs [] entry found

  theorem positionsList_sound (head : Head) (subjects initialChildren : List (Subject Head))
      (entry : Position × Subject Head) (found : entry ∈ positionsList initialChildren.length subjects) :
      project entry.1 (.node head (initialChildren ++ subjects)) = some entry.2 := by
    cases subjects with
    | nil => simp [positionsList] at found
    | cons s ss =>
        simp only [positionsList, List.mem_append] at found
        rcases found with found | found
        · obtain ⟨inner, member, rfl⟩ := List.mem_map.mp found
          simpa [project] using positions_sound s inner member
        · have tail := positionsList_sound head ss (initialChildren ++ [s]) entry
            (by simpa using found)
          simpa [List.append_assoc] using tail
end

/-- Canonical structural reference: independently match every authored
pattern at every syntactic subterm. -/
def reference [DecidableEq Head] (patterns : List (Pattern Head))
    (subject : Subject Head) : List Location :=
  (positions subject).flatMap fun entry =>
    (select (fun p => structuralMatch p entry.2) 0 patterns).map
      (fun occurrence => ⟨entry.1, occurrence⟩)

/-- Encoding constructor labels changes neither locations nor authored
occurrence multiplicity in the canonical subterm-match reference. -/
theorem reference_mapHeads {Target : Type v} [DecidableEq Head] [DecidableEq Target]
    (f : Head → Target) (injective : Function.Injective f)
    (patterns : List (Pattern Head)) (subject : Subject Head) :
    reference (patterns.map (Pattern.mapHeads f)) (Subject.mapHeads f subject) =
      reference patterns subject := by
  simp only [reference, positions_mapHeads, List.flatMap_map,
    select_match_mapHeads f injective]

end Mettapedia.GSLT.LanguageDef.SubtermMatching
