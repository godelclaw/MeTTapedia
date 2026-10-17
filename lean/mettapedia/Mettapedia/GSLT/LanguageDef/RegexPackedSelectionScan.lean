import Mettapedia.GSLT.LanguageDef.RegexPackedSelection

/-!
# Independent physical-CST scan for the late selection observer

The scan traverses materialized carrier data and retains every numeric
reference occurrence. It does not consult packed-family guards. Its exact
occurrence theorem supplies the independent late classifier used in the
policy-directed extraction equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexPackedSelectionScan

open CettaWire (Term)
open RegexSourceProjection (cst)
open RegexDependentProjection (Occurs NumericReferencesMaximal EndsDecimalRun)
open RegexPackedSelection
open Mettapedia.GSLT.Parsing.PackedForestSelection

abbrev Site := Nat × Nat × List Term

def rootSite? : Term → Option Site
  | .application "CstRuleV1" (.string "re-src:backref" :: .natural start :: .natural stop :: children) =>
      some (start, stop, children)
  | _ => none

theorem rootSite_exact (tree : Term) (start stop : Nat) (children : List Term) :
    rootSite? tree = some (start, stop, children) ↔ tree = cst "re-src:backref" children start stop := by
  unfold rootSite?
  split
  · rename_i actualStart actualStop actualChildren
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
    · intro equal
      simpa only [cst, Term.application.injEq, List.cons.injEq, Term.string.injEq,
        Term.natural.injEq, true_and] using equal
  · constructor
    · intro impossible
      cases impossible
    · intro equal
      subst tree
      simp_all [cst]

mutual
  def sites : Term → List Site
    | tree@(.application _ children) => (rootSite? tree).toList ++ childSites children
    | _ => []
  def childSites : List Term → List Site
    | [] => []
    | child :: rest => sites child ++ childSites rest
end

mutual
  theorem sites_exact (tree : Term) (start stop : Nat) (children : List Term) :
      (start,stop,children) ∈ sites tree ↔ Occurs (cst "re-src:backref" children start stop) tree := by
    cases tree with
    | symbol name | string value | natural value =>
        constructor
        · simp [sites]
        · intro impossible
          cases impossible
    | application head arguments =>
        rw [sites, List.mem_append, Option.mem_toList, rootSite_exact, childSites_exact,
          occurs_application_iff]
        exact or_congr eq_comm Iff.rfl
  theorem childSites_exact (arguments : List Term) (start stop : Nat) (children : List Term) :
      (start,stop,children) ∈ childSites arguments ↔
        ∃ child ∈ arguments, Occurs (cst "re-src:backref" children start stop) child := by
    cases arguments with
    | nil => simp [childSites]
    | cons child rest =>
        simp only [childSites, List.mem_append, sites_exact, childSites_exact, List.mem_cons]
        constructor
        · rintro (present | ⟨other, member, present⟩)
          · exact ⟨child, Or.inl rfl, present⟩
          · exact ⟨other, Or.inr member, present⟩
        · rintro ⟨other, same | member, present⟩
          · subst other
            exact Or.inl present
          · exact Or.inr ⟨other, member, present⟩
end

def check (input : List Nat) (tree : Term) : Bool :=
  (sites tree).all fun site => decimalEnd input site.2.1

theorem check_exact (input : List Nat) (tree : Term) :
    check input tree = true ↔ NumericReferencesMaximal input tree := by
  simp only [check, List.all_eq_true]
  constructor
  · intro checked first last children occurs
    exact (decimalEnd_iff input last).mp (checked _ ((sites_exact tree first last children).mpr occurs))
  · intro maximal site present
    obtain ⟨start, stop, children⟩ := site
    exact (decimalEnd_iff input stop).mpr (maximal start stop children
      ((sites_exact tree start stop children).mp present))

def checkTerms (input : List Nat) (terms : List Term) : Bool := terms.all (check input)

theorem checkTerms_exact (input : List Nat) (terms : List Term) :
    checkTerms input terms = true ↔ MaximalTerms input terms := by
  simp [checkTerms, List.all_eq_true, check_exact, MaximalTerms]

/-- This late classifier builds and scans the physical terms first; it does
not run the early family predicate. Exact equality includes output order and
each physical derivation occurrence. -/
theorem early_projection_eq_materialize_then_scan {Key Family Output : Type}
    (families : Key → List Family) (children : Family → List Key) (frame : Family → Frame)
    (input : List Nat) (project : Derivation Family → Option Output) (depth : Nat) (key : Key) :
    (extract families children (allow input ∘ frame) depth key).filterMap project =
      ((extract families children (fun _ => true) depth key).filter
        (fun tree => checkTerms input (render frame tree))).filterMap project :=
  projected_list_exact families children frame input _
    (fun tree => checkTerms_exact input (render frame tree)) project depth key

namespace Controls

theorem mixed_unicode_reference_stop_is_observed :
    check [92,49,1634] (cst "re-src:backref" [] 0 3) = true ∧
      check [92,49,1634] (cst "re-src:backref" [] 0 2) = false := by decide

theorem repeated_physical_reference_occurrences_are_not_deduplicated :
    (sites (cst "re-src:sequence" [cst "re-src:backref" [] 0 3,
      cst "re-src:backref" [] 0 3] 0 3)).length = 2 := by decide

theorem discarded_descendant_policy_is_not_just_a_root_test :
    rootSite? (cst "re-src:sequence" [cst "re-src:backref" [] 0 2] 0 3) = none ∧
      check [92,49,1634] (cst "re-src:sequence" [cst "re-src:backref" [] 0 2] 0 3) = false := by
  constructor
  · rfl
  · decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexPackedSelectionScan
