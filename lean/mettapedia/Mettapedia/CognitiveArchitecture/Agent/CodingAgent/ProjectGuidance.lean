import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Repository guidance for a coding task

The inputs are filesystem observations, not a model of an operating system.
A directory chain is supplied from workspace to filesystem root. Discovery
stops at the nearest repository marker and returns the selected scope in the
opposite order, so ancestor instructions precede local instructions.

Within each directory, candidates are already ordered by precedence. Project
discovery selects the first regular file, including an empty file. Global
discovery falls through an empty file. Read errors remain errors.

The saved instruction message is an ordinary part of the conversation. Restoring
it either attaches it once, accepts its exact existing copy, or reports a
conflict. Compaction retains guidance verbatim.

Main results:
* `searchScope_append_of_some`: ancestors above an already found root cannot
  change discovery;
* `mem_of_searchScope`: selected directories belong to the supplied chain;
* `selectProject_first_regular`: lower-priority candidates cannot replace the
  first regular project file, even when it is empty;
* `selectGlobal_empty`: empty global files permit fallback;
* `restore_projection` and `restore_idempotent`: successful restoration has
  exactly one exact instruction message and does not duplicate it on resume;
* `compact_guidance`: compaction retains precisely the guidance it received.

These statements do not claim that a language model obeys an instruction, that
a filesystem observation is trustworthy, or that hashes prevent malicious edits.
Native discovery traces can be checked against `selectProject` separately.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.CodingAgent.ProjectGuidance

universe u

variable {α : Type u}

/-- A workspace-to-root directory observation and whether it contains a marker. -/
structure Directory (α : Type u) where
  name : α
  marker : Bool
  deriving DecidableEq, Repr

/-- Find the nearest marked directory, returning root-to-workspace scope. -/
def searchScope : List (Directory α) → Option (List α)
  | [] => none
  | d :: ds => if d.marker then some [d.name]
    else (searchScope ds).map (fun names => names ++ [d.name])

/-- With no repository marker, only the initial workspace is in scope. -/
def scope (up : List (Directory α)) : List α :=
  (searchScope up).getD ((up.take 1).map Directory.name)

theorem searchScope_marked (name : α) (ancestors : List (Directory α)) :
    searchScope (⟨name, true⟩ :: ancestors) = some [name] := by
  simp [searchScope]

theorem searchScope_append_of_some (near far : List (Directory α))
    (names : List α) (h : searchScope near = some names) :
    searchScope (near ++ far) = some names := by
  induction near generalizing names with
  | nil => simp [searchScope] at h
  | cons d ds ih =>
    cases hm : d.marker
    · simp only [List.cons_append, searchScope, hm, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hs : searchScope ds with
      | none => simp [hs] at h
      | some rest =>
        simp only [hs, Option.map_some, Option.some.injEq] at h
        rw [ih rest hs]
        simpa using congrArg some h
    · simpa [searchScope, hm] using h

theorem mem_of_searchScope (up : List (Directory α)) (names : List α)
    (h : searchScope up = some names) (x : α) (hx : x ∈ names) :
    x ∈ up.map Directory.name := by
  induction up generalizing names with
  | nil => simp [searchScope] at h
  | cons d ds ih =>
    cases hm : d.marker
    · simp only [searchScope, hm, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : searchScope ds with
      | none => simp [hs] at h
      | some rest =>
        simp only [hs, Option.map_some, Option.some.injEq] at h
        subst names
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact List.mem_cons_of_mem _ (ih rest hs hx)
        · simp [hx]
    · simp only [searchScope, hm, ↓reduceIte, Option.some.injEq] at h
      subst names
      simp only [List.mem_singleton] at hx
      simp [hx]

theorem scope_without_marker (up : List (Directory α)) (h : searchScope up = none) :
    scope up = (up.take 1).map Directory.name := by
  simp [scope, h]

/-- Missing and nonregular candidates are skipped. A regular file may be blank. -/
inductive Candidate (α : Type u) where
  | skip
  | regular (text : Option α)
  | failed (detail : String)
  deriving DecidableEq, Repr

abbrev Selection (α : Type u) := Except String (Option α)

def selectProject : List (Candidate α) → Selection α
  | [] => .ok none
  | .skip :: rest => selectProject rest
  | .regular text :: _ => .ok text
  | .failed why :: _ => .error why

def selectGlobal : List (Candidate α) → Selection α
  | [] => .ok none
  | .skip :: rest => selectGlobal rest
  | .regular none :: rest => selectGlobal rest
  | .regular (some text) :: _ => .ok (some text)
  | .failed why :: _ => .error why

theorem selectProject_first_regular (skipped : List (Candidate α))
    (h : ∀ c ∈ skipped, c = .skip) (text : Option α) (rest : List (Candidate α)) :
    selectProject (skipped ++ .regular text :: rest) = .ok text := by
  induction skipped with
  | nil => rfl
  | cons c cs ih =>
    have hc : c = .skip := h c (by simp)
    subst c
    simpa [selectProject] using ih (fun x hx => h x (by simp [hx]))

theorem selectProject_empty (rest : List (Candidate α)) :
    selectProject (.regular none :: rest) = .ok none := rfl

theorem selectGlobal_empty (rest : List (Candidate α)) :
    selectGlobal (.regular none :: rest) = selectGlobal rest := rfl

theorem selectProject_failure (why : String) (rest : List (Candidate α)) :
    selectProject (.failed why :: rest) = .error why := rfl

/-- Guidance is retained alongside user input; transient evidence may be folded. -/
inductive Message (α : Type u) where
  | guidance (text : α)
  | user (text : α)
  | evidence
  deriving DecidableEq, Repr

def guidanceTexts : List (Message α) → List α
  | [] => []
  | .guidance text :: rest => text :: guidanceTexts rest
  | _ :: rest => guidanceTexts rest

def compact : List (Message α) → List (Message α)
  | [] => []
  | .evidence :: rest => compact rest
  | message :: rest => message :: compact rest

theorem guidanceTexts_append (a b : List (Message α)) :
    guidanceTexts (a ++ b) = guidanceTexts a ++ guidanceTexts b := by
  induction a with
  | nil => rfl
  | cons m ms ih => cases m <;> simp [guidanceTexts, ih]

theorem compact_guidance (messages : List (Message α)) :
    guidanceTexts (compact messages) = guidanceTexts messages := by
  induction messages with
  | nil => rfl
  | cons m ms ih => cases m <;> simp [compact, guidanceTexts, ih]

variable [DecidableEq α]

/-- The expected value includes both the saved identity and exact instruction text. -/
def restore (expected : α) (messages : List (Message α)) : Except Unit (List (Message α)) :=
  if guidanceTexts messages = [] then .ok (messages ++ [.guidance expected])
  else if guidanceTexts messages = [expected] then .ok messages
  else .error ()

theorem restore_projection (expected : α) (before after : List (Message α))
    (h : restore expected before = .ok after) :
    guidanceTexts after = [expected] := by
  unfold restore at h
  split_ifs at h with he hf
  · cases h
    simp [guidanceTexts_append, he, guidanceTexts]
  · cases h
    exact hf
theorem restore_idempotent (expected : α) (before after : List (Message α))
    (h : restore expected before = .ok after) :
    restore expected after = .ok after := by
  have hp := restore_projection expected before after h
  simp [restore, hp]

theorem restore_conflict (expected : α) (messages : List (Message α))
    (hne : guidanceTexts messages ≠ []) (hbad : guidanceTexts messages ≠ [expected]) :
    restore expected messages = .error () := by
  simp [restore, hne, hbad]

theorem compact_restored (expected : α) (before after : List (Message α))
    (h : restore expected before = .ok after) :
    restore expected (compact after) = .ok (compact after) := by
  simp [restore, compact_guidance, restore_projection expected before after h]

end Mettapedia.CognitiveArchitecture.Agent.CodingAgent.ProjectGuidance
