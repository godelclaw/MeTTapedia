import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.MatchReadings
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# The rows of the computable matcher are positive reads

`MORK.Conformance.Computable.cmatchPattern` matches the premises of a positive
pattern against a space and returns one row for each simultaneous match: a
substitution with the atoms that witnessed the premises.
`cmatchPattern_mono` says that adding atoms to the space keeps every row.

This module completes that statement to the reading of one answer of a match as a
positive read, and adds the complete reading of the whole list of rows.

* `cmatchPattern_restrict_to_witnesses`: **a row is a row over its own
  witnesses.**  Taking away every atom that is not a witness keeps it.
* `cmatchPattern_mem_iff_witnesses`: a row of one space is a row of another
  exactly when that space contains its witnesses.  From right to left this is the
  restriction followed by `cmatchPattern_mono`; from left to right it is
  `cmatchPattern_consumed_subset`.  So the footprint of one answer is its
  witnesses; no addition invalidates it, and no removal of an atom that is not a
  witness.
* `cmatchPattern_mem_iff_positive_reads`: with the space read by kinds, that is
  the publication of the steps that see the witnesses (`seeKind`).
* `cmatchPattern_append_single`: **the whole list of rows of a pattern with one
  premise, after one atom is added to the space, is the old list followed by the
  row of that atom if the premise matches it.**  An atom the premise does not
  match changes nothing; an atom it matches adds a row: the phantom.  For any
  number of premises, atoms that match no premise change nothing
  (`cmatchPattern_append_of_right_never_matches`).
* `atomKinds`, `rigidClash`, `atomKinds_disjoint_of_rigidClash`: a test of
  disjointness for the pattern atoms of this matcher.  Two pattern atoms that
  differ at a position outside every variable match no atom in common.  The test
  is sound and not complete; the exact test, by unification, is proved for
  first-order terms in `PatternFootprints.Patterns`.  A positive pair:
  `MatcherControls.seenAny_triedAny_disjoint`; a negative pair:
  `MatcherControls.seenAny_seenA_not_disjoint`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- **A row is a row over its own witnesses.** -/
theorem cmatchPattern_restrict_to_witnesses (σ₀ : Subst) (space : CSpace) (p : Pattern)
    (σ : Subst) (consumed : List Atom) (matched : (σ, consumed) ∈ cmatchPattern σ₀ space p) :
    (σ, consumed) ∈ cmatchPattern σ₀ consumed p := by
  simp only [cmatchPattern] at matched ⊢
  suffices h : ∀ (patterns : List Atom) (σIn : Subst) (consumedIn : List Atom) (σOut : Subst)
      (consumedOut : List Atom),
      (σOut, consumedOut) ∈ cmatchPattern.go space patterns σIn consumedIn →
        (∀ atom ∈ consumedIn, atom ∈ consumedOut) ∧
          (σOut, consumedOut) ∈ cmatchPattern.go consumedOut patterns σIn consumedIn by
    exact (h p.atoms σ₀ [] σ consumed matched).2
  intro patterns
  induction patterns with
  | nil =>
      intro σIn consumedIn σOut consumedOut member
      simp only [cmatchPattern.go, List.mem_singleton, Prod.mk.injEq] at member ⊢
      obtain ⟨rfl, rfl⟩ := member
      exact ⟨fun _ present => present, rfl, rfl⟩
  | cons pattern rest induction =>
      intro σIn consumedIn σOut consumedOut member
      simp only [cmatchPattern.go] at member ⊢
      rw [List.mem_flatMap] at member ⊢
      obtain ⟨⟨σMid, atom⟩, foundInSpace, continued⟩ := member
      obtain ⟨grows, restricted⟩ := induction σMid (atom :: consumedIn) σOut consumedOut continued
      refine ⟨fun other present => grows other (List.mem_cons_of_mem atom present),
        (σMid, atom), ?_, restricted⟩
      rw [List.mem_filterMap] at foundInSpace ⊢
      obtain ⟨concrete, -, matchedAtom⟩ := foundInSpace
      have same : concrete = atom := by
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at matchedAtom
        obtain ⟨_, -, -, rfl⟩ := matchedAtom
        rfl
      subst same
      exact ⟨concrete, grows concrete List.mem_cons_self, matchedAtom⟩

/-- **One answer of the matcher is a positive read of its witnesses.**  A row of
one space is a row of another exactly when that space contains its witnesses. -/
theorem cmatchPattern_mem_iff_witnesses {σ₀ : Subst} {space : CSpace} {p : Pattern} {σ : Subst}
    {consumed : List Atom} (matched : (σ, consumed) ∈ cmatchPattern σ₀ space p) (other : CSpace) :
    (σ, consumed) ∈ cmatchPattern σ₀ other p ↔ ∀ atom ∈ consumed, atom ∈ other :=
  ⟨cmatchPattern_consumed_subset σ₀ other p σ consumed, fun present =>
    cmatchPattern_mono σ₀ consumed other p present σ consumed
      (cmatchPattern_restrict_to_witnesses σ₀ space p σ consumed matched)⟩

/-- **The whole list of rows of one premise, after one atom is added.**  It is the
old list, followed by the row of the new atom if the premise matches it. -/
theorem cmatchPattern_append_single (σ₀ : Subst) (space : CSpace) (pattern atom : Atom) :
    cmatchPattern σ₀ (space ++ [atom]) (mkPattern [pattern]) =
      cmatchPattern σ₀ space (mkPattern [pattern]) ++
        ((cmatchAtom σ₀ pattern atom).map fun σ => (σ, [atom])).toList := by
  simp only [cmatchPattern, mkPattern, cmatchPattern.go, List.filterMap_append,
    List.flatMap_append]
  congr 1
  cases matched : cmatchAtom σ₀ pattern atom with
  | none => simp [matched]
  | some σ => simp [matched]

/-! ## A test of disjointness for the atoms of the matcher -/

/-- **The kinds a pattern atom matches**: the atoms the matcher accepts for it,
from the empty substitution. -/
def atomKinds (pattern : Atom) : Set Atom :=
  {atom | (cmatchAtom [] pattern atom).isSome}

mutual
/-- **A rigid clash** of two pattern atoms: at one position, outside every
variable, they have two different symbols, two different grounded values, two
different numbers of arguments, or two different forms. -/
def rigidClash : Atom → Atom → Bool
  | .var _, _ => false
  | .symbol _, .var _ => false
  | .grounded _, .var _ => false
  | .expression _, .var _ => false
  | .symbol first, .symbol second => !(first == second)
  | .grounded first, .grounded second => !(first == second)
  | .expression first, .expression second => rigidClashList first second
  | .symbol _, .grounded _ => true
  | .symbol _, .expression _ => true
  | .grounded _, .symbol _ => true
  | .grounded _, .expression _ => true
  | .expression _, .symbol _ => true
  | .expression _, .grounded _ => true

/-- A rigid clash of two lists of pattern atoms, position by position. -/
def rigidClashList : List Atom → List Atom → Bool
  | [], [] => false
  | first :: firstRest, second :: secondRest =>
      rigidClash first second || rigidClashList firstRest secondRest
  | [], _ :: _ => true
  | _ :: _, [] => true
end

mutual
/-- No atom is matched by both of two pattern atoms that clash rigidly, whatever
substitutions the two matches start from. -/
theorem cmatchAtom_eq_none_of_rigidClash (first second : Atom)
    (clash : rigidClash first second = true) (σ τ : Subst) (atom : Atom) :
    cmatchAtom σ first atom = none ∨ cmatchAtom τ second atom = none := by
  match first, second, atom with
  | .var _, _, _ => simp [rigidClash] at clash
  | .symbol _, .var _, _ => simp [rigidClash] at clash
  | .grounded _, .var _, _ => simp [rigidClash] at clash
  | .expression _, .var _, _ => simp [rigidClash] at clash
  | .symbol a, .symbol b, .symbol c =>
      simp only [rigidClash, Bool.not_eq_true', beq_eq_false_iff_ne] at clash
      by_cases same : a = c
      · right
        have different : ¬ b = c := fun equal => clash (same.trans equal.symm)
        simp [cmatchAtom, different]
      · left
        simp [cmatchAtom, same]
  | .symbol _, .symbol _, .var _ => left; simp [cmatchAtom]
  | .symbol _, .symbol _, .grounded _ => left; simp [cmatchAtom]
  | .symbol _, .symbol _, .expression _ => left; simp [cmatchAtom]
  | .grounded a, .grounded b, .grounded c =>
      simp only [rigidClash, Bool.not_eq_true', beq_eq_false_iff_ne] at clash
      by_cases same : a = c
      · right
        have different : ¬ b = c := fun equal => clash (same.trans equal.symm)
        simp [cmatchAtom, different]
      · left
        simp [cmatchAtom, same]
  | .grounded _, .grounded _, .var _ => left; simp [cmatchAtom]
  | .grounded _, .grounded _, .symbol _ => left; simp [cmatchAtom]
  | .grounded _, .grounded _, .expression _ => left; simp [cmatchAtom]
  | .expression firstArguments, .expression secondArguments, .expression arguments =>
      simp only [rigidClash] at clash
      simpa [cmatchAtom] using
        cmatchAtomList_eq_none_of_rigidClashList firstArguments secondArguments clash σ τ arguments
  | .expression _, .expression _, .var _ => left; simp [cmatchAtom]
  | .expression _, .expression _, .symbol _ => left; simp [cmatchAtom]
  | .expression _, .expression _, .grounded _ => left; simp [cmatchAtom]
  | .symbol _, .grounded _, .symbol _ => right; simp [cmatchAtom]
  | .symbol _, .grounded _, .var _ => left; simp [cmatchAtom]
  | .symbol _, .grounded _, .grounded _ => left; simp [cmatchAtom]
  | .symbol _, .grounded _, .expression _ => left; simp [cmatchAtom]
  | .symbol _, .expression _, .symbol _ => right; simp [cmatchAtom]
  | .symbol _, .expression _, .var _ => left; simp [cmatchAtom]
  | .symbol _, .expression _, .grounded _ => left; simp [cmatchAtom]
  | .symbol _, .expression _, .expression _ => left; simp [cmatchAtom]
  | .grounded _, .symbol _, .grounded _ => right; simp [cmatchAtom]
  | .grounded _, .symbol _, .var _ => left; simp [cmatchAtom]
  | .grounded _, .symbol _, .symbol _ => left; simp [cmatchAtom]
  | .grounded _, .symbol _, .expression _ => left; simp [cmatchAtom]
  | .grounded _, .expression _, .grounded _ => right; simp [cmatchAtom]
  | .grounded _, .expression _, .var _ => left; simp [cmatchAtom]
  | .grounded _, .expression _, .symbol _ => left; simp [cmatchAtom]
  | .grounded _, .expression _, .expression _ => left; simp [cmatchAtom]
  | .expression _, .symbol _, .expression _ => right; simp [cmatchAtom]
  | .expression _, .symbol _, .var _ => left; simp [cmatchAtom]
  | .expression _, .symbol _, .symbol _ => left; simp [cmatchAtom]
  | .expression _, .symbol _, .grounded _ => left; simp [cmatchAtom]
  | .expression _, .grounded _, .expression _ => right; simp [cmatchAtom]
  | .expression _, .grounded _, .var _ => left; simp [cmatchAtom]
  | .expression _, .grounded _, .symbol _ => left; simp [cmatchAtom]
  | .expression _, .grounded _, .grounded _ => left; simp [cmatchAtom]

/-- The same for lists of pattern atoms against a list of atoms. -/
theorem cmatchAtomList_eq_none_of_rigidClashList (first second : List Atom)
    (clash : rigidClashList first second = true) (σ τ : Subst) (atoms : List Atom) :
    cmatchAtomList σ first atoms = none ∨ cmatchAtomList τ second atoms = none := by
  match first, second, atoms with
  | [], [], _ => simp [rigidClashList] at clash
  | [], _ :: _, [] => right; simp [cmatchAtomList]
  | [], _ :: _, _ :: _ => left; simp [cmatchAtomList]
  | _ :: _, [], [] => left; simp [cmatchAtomList]
  | _ :: _, [], _ :: _ => right; simp [cmatchAtomList]
  | _ :: _, _ :: _, [] => left; simp [cmatchAtomList]
  | head :: rest, otherHead :: otherRest, atom :: atoms =>
      simp only [rigidClashList, Bool.or_eq_true] at clash
      simp only [cmatchAtomList]
      rcases clash with headClash | restClash
      · rcases cmatchAtom_eq_none_of_rigidClash head otherHead headClash σ τ atom with none | none
        · left; rw [none]
        · right; rw [none]
      · cases firstMatch : cmatchAtom σ head atom with
        | none => left; rfl
        | some σ' =>
            cases secondMatch : cmatchAtom τ otherHead atom with
            | none => right; rfl
            | some τ' =>
                exact cmatchAtomList_eq_none_of_rigidClashList rest otherRest restClash σ' τ' atoms
end

/-- **The test by rigid clash is sound**: two pattern atoms that clash rigidly
match no atom in common.  It is not complete: it does not look at variables that
occur twice. -/
theorem atomKinds_disjoint_of_rigidClash {first second : Atom}
    (clash : rigidClash first second = true) : Disjoint (atomKinds first) (atomKinds second) := by
  refine Set.disjoint_left.mpr fun atom inFirst inSecond => ?_
  have firstMatched : (cmatchAtom [] first atom).isSome = true := inFirst
  have secondMatched : (cmatchAtom [] second atom).isSome = true := inSecond
  rcases cmatchAtom_eq_none_of_rigidClash first second clash [] [] atom with none | none
  · rw [none] at firstMatched
    cases firstMatched
  · rw [none] at secondMatched
    cases secondMatched

/-! ## Controls -/

namespace MatcherControls

/-- The pattern `(seen $y)`. -/
def seenAny : Atom := .expression [.symbol "seen", .var "y"]

/-- The pattern `(tried $y)`. -/
def triedAny : Atom := .expression [.symbol "tried", .var "y"]

/-- The atom `(seen a)`. -/
def seenA : Atom := .expression [.symbol "seen", .symbol "a"]

/-- **A positive pair**: `(seen $y)` and `(tried $y)` clash at the head, and match
no atom in common. -/
theorem seenAny_triedAny_disjoint :
    rigidClash seenAny triedAny = true ∧ Disjoint (atomKinds seenAny) (atomKinds triedAny) :=
  ⟨by decide, atomKinds_disjoint_of_rigidClash (by decide)⟩

/-- **A negative pair**: `(seen $y)` and `(seen a)` do not clash, and both match
the atom `(seen a)`. -/
theorem seenAny_seenA_not_disjoint :
    rigidClash seenAny seenA = false ∧ seenA ∈ atomKinds seenAny ∧ seenA ∈ atomKinds seenA := by
  refine ⟨by decide, ?_, ?_⟩
  · show (cmatchAtom [] seenAny seenA).isSome = true
    rfl
  · show (cmatchAtom [] seenA seenA).isSome = true
    rfl

end MatcherControls

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

universe u

/-- **Seeing several kinds publishes exactly where all of them are present.** -/
theorem publish_seeKinds_eq_some_iff {Location : Type u} [DecidableEq Location]
    (kinds : List Location) (state : Location → ℕ) :
    publish (kinds.map seeKind) state = some state ↔ ∀ kind ∈ kinds, 0 < state kind := by
  induction kinds with
  | nil => simp
  | cons kind rest ih =>
      rw [List.map_cons, publish_cons, List.forall_mem_cons, ← ih]
      constructor
      · intro published
        obtain ⟨middle, fired, restPublished⟩ := Option.bind_eq_some_iff.mp published
        obtain ⟨present, rfl⟩ := (fire_seeKind_eq_some_iff kind state middle).mp fired
        exact ⟨present, restPublished⟩
      · rintro ⟨present, restPublished⟩
        rw [(fire_seeKind_eq_some_iff kind state state).mpr ⟨present, rfl⟩]
        exact restPublished

/-- **A row of the computable matcher is the positive reads of its witnesses.**
With the space read by kinds, a row of one space is a row of another exactly when
the steps that see its witnesses are published there. -/
theorem cmatchPattern_mem_iff_positive_reads {σ₀ : Subst} {space : CSpace} {p : Pattern}
    {σ : Subst} {consumed : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (matched : (σ, consumed) ∈ cmatchPattern σ₀ space p) (other : CSpace) :
    (σ, consumed) ∈ cmatchPattern σ₀ other p ↔
      publish (consumed.map seeKind) (marking (other : Multiset _)) =
        some (marking (other : Multiset _)) := by
  rw [cmatchPattern_mem_iff_witnesses matched, publish_seeKinds_eq_some_iff]
  refine forall₂_congr fun atom _ => ?_
  show atom ∈ other ↔ 0 < Multiset.count atom (other : Multiset _)
  rw [Multiset.count_pos, Multiset.mem_coe]

#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchPattern_restrict_to_witnesses
#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchPattern_mem_iff_witnesses
#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchPattern_append_single
#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchAtom_eq_none_of_rigidClash
#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.atomKinds_disjoint_of_rigidClash
#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.MatcherControls.seenAny_triedAny_disjoint
#print axioms Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.MatcherControls.seenAny_seenA_not_disjoint
#print axioms publish_seeKinds_eq_some_iff
#print axioms cmatchPattern_mem_iff_positive_reads

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
