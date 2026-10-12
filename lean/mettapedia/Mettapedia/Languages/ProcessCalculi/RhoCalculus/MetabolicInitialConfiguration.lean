import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicReadout

/-!
# Initial occurrences for the metabolic protocol

Every canonical source prime receives a distinct key and its supplied origin.
The inventory remains the independent source process's canonical inventory.
This construction provides actual sources for acquisition and debit histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic

open Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBag LanguageDefGSLT ResourcePredation

def annotate (process : RhoProcess) (origin : Pattern → Origin) (firstKey : Nat) : Configuration :=
  Configuration.ofList (List.ofFn fun position : Fin (contents process).length =>
    { key := firstKey + position.val
      origin := origin (contents process)[position.val]
      term := ⟨(contents process)[position.val], contents_prime process (List.getElem_mem position.isLt)⟩ })

theorem annotate_inventory (process : RhoProcess) (origin : Pattern → Origin) (firstKey : Nat) :
    inventory (annotate process origin firstKey) = fromProcess process := by
  apply Subtype.ext
  change (patterns (annotate process origin firstKey) : Multiset Pattern) =
    (contents process : Multiset Pattern)
  have same : patterns (annotate process origin firstKey) = contents process := by
    simp only [patterns, annotate, Configuration.ofList, List.map_ofFn]
    exact List.ofFn_getElem
  rw [same]

theorem annotate_distinct (process : RhoProcess) (origin : Pattern → Origin) (firstKey : Nat) :
    Distinct (annotate process origin firstKey) := by
  unfold Distinct annotate Configuration.ofList
  rw [List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro first second same
  apply Fin.ext
  change firstKey + first.val = firstKey + second.val at same
  omega

theorem annotate_origin (process : RhoProcess) (origin : Pattern → Origin) (firstKey : Nat)
    (occurrence : Occurrence) (member : occurrence ∈ (annotate process origin firstKey).occurrences) :
    occurrence.origin = origin occurrence.term.1 := by
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
