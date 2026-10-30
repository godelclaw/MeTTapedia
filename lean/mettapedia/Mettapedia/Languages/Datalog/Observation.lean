import Mettapedia.Languages.Datalog.GroundInstancesComplete
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Count

/-! Finite logical firing support is independent of validation positions.
The actual producer retains those positions; this observation projects keys
and conclusions only. It does not enumerate unfolded derivation trees. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.Observation

open GroundInstances

abbrev Firing := DerivationKey × GroundFact

def firings (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) : List Firing :=
  (produce policy statementIndex clause known).map fun instanceData =>
    (instanceData.key, instanceData.conclusion)

/-- Both directions use the actual producer's soundness and coverage.
An arbitrary list of validation positions is not part of logical identity. -/
theorem mem_firings_iff (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) (key : DerivationKey) (conclusion : GroundFact) :
    (key, conclusion) ∈ firings policy statementIndex clause known ↔
      Authorized policy statementIndex clause known ⟨key, conclusion, []⟩ := by
  constructor
  · intro member
    obtain ⟨instanceData, produced, same⟩ := List.mem_map.mp member
    have keySame : instanceData.key = key := congrArg Prod.fst same
    have conclusionSame : instanceData.conclusion = conclusion := congrArg Prod.snd same
    have authorized := (produce_sound policy statementIndex clause known produced).1
    simpa only [Authorized, keySame, conclusionSame] using authorized
  · intro authorized
    obtain ⟨instanceData, produced, keySame, conclusionSame⟩ :=
      produce_complete policy statementIndex clause known ⟨key, conclusion, []⟩ authorized
    exact List.mem_map.mpr ⟨instanceData, produced, Prod.ext keySame conclusionSame⟩

theorem authorized_of_known_extension (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (before after : List GroundFact) (included : ∀ fact ∈ before, fact ∈ after) (instanceData : Instance)
    (authorized : Authorized policy statementIndex clause before instanceData) :
    Authorized policy statementIndex clause after instanceData := by
  obtain ⟨restricted, ordinal, model, headMatches, bodyMatches, available, guards, names, values⟩ := authorized
  exact ⟨restricted, ordinal, model, headMatches, bodyMatches,
    fun fact inside => included fact (available fact inside), guards, names, values⟩

theorem firings_monotone (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (before after : List GroundFact) (included : ∀ fact ∈ before, fact ∈ after) :
    ∀ firing ∈ firings policy statementIndex clause before,
      firing ∈ firings policy statementIndex clause after := by
  rintro ⟨key, conclusion⟩ member
  apply (mem_firings_iff policy statementIndex clause after key conclusion).mpr
  exact authorized_of_known_extension policy statementIndex clause before after included _
    ((mem_firings_iff policy statementIndex clause before key conclusion).mp member)

/-- Presentation order and repeated validations may change raw rows and their
positions. They preserve precisely the supported logical firings. -/
theorem firings_support_congr (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (first second : List GroundFact) (same : ∀ fact, fact ∈ first ↔ fact ∈ second) (firing : Firing) :
    firing ∈ firings policy statementIndex clause first ↔
      firing ∈ firings policy statementIndex clause second :=
  ⟨firings_monotone policy statementIndex clause first second (fun fact => (same fact).mp) firing,
    firings_monotone policy statementIndex clause second first (fun fact => (same fact).mpr) firing⟩

theorem firings_support_eraseDups (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) (firing : Firing) :
    firing ∈ firings policy statementIndex clause known.eraseDups ↔
      firing ∈ firings policy statementIndex clause known :=
  firings_support_congr policy statementIndex clause known.eraseDups known (by simp) firing

def facts (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) : List GroundFact :=
  (firings policy statementIndex clause known).map Prod.snd

theorem facts_support_congr (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (first second : List GroundFact) (same : ∀ fact, fact ∈ first ↔ fact ∈ second) (conclusion : GroundFact) :
    conclusion ∈ facts policy statementIndex clause first ↔
      conclusion ∈ facts policy statementIndex clause second := by
  simp only [facts, List.mem_map]
  constructor
  · rintro ⟨firing, member, projected⟩
    exact ⟨firing, (firings_support_congr policy statementIndex clause first second same firing).mp member,
      projected⟩
  · rintro ⟨firing, member, projected⟩
    exact ⟨firing, (firings_support_congr policy statementIndex clause first second same firing).mpr member,
      projected⟩

def factSet (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) : Finset GroundFact :=
  (facts policy statementIndex clause known).toFinset

/-- The finite one-step observation publishes one occurrence of each logical
key. It does not identify different keys that happen to share a conclusion. -/
def keyBag (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) : Multiset DerivationKey :=
  ((firings policy statementIndex clause known).map Prod.fst).toFinset.val

theorem factSet_congr (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (first second : List GroundFact) (same : ∀ fact, fact ∈ first ↔ fact ∈ second) :
    factSet policy statementIndex clause first = factSet policy statementIndex clause second := by
  apply Finset.ext
  intro conclusion
  simpa only [factSet, List.mem_toFinset] using
    facts_support_congr policy statementIndex clause first second same conclusion

theorem keyBag_congr (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (first second : List GroundFact) (same : ∀ fact, fact ∈ first ↔ fact ∈ second) :
    keyBag policy statementIndex clause first = keyBag policy statementIndex clause second := by
  apply congrArg Finset.val
  apply Finset.ext
  intro key
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨firing, member, projected⟩
    exact ⟨firing, (firings_support_congr policy statementIndex clause first second same firing).mp member,
      projected⟩
  · rintro ⟨firing, member, projected⟩
    exact ⟨firing, (firings_support_congr policy statementIndex clause first second same firing).mpr member,
      projected⟩

theorem keyBag_count (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) (key : DerivationKey) :
    (keyBag policy statementIndex clause known).count key =
      if key ∈ keyBag policy statementIndex clause known then 1 else 0 :=
  Multiset.count_eq_of_nodup (List.toFinset _).nodup

#print axioms mem_firings_iff
#print axioms firings_monotone
#print axioms firings_support_congr
#print axioms facts_support_congr
#print axioms factSet_congr
#print axioms keyBag_congr
#print axioms keyBag_count

end Mettapedia.Languages.Datalog.Observation
