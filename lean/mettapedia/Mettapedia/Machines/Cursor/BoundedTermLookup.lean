import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Bounded structural lookup with a general fallback

The independent reference recursively reads canonical leaf and constructor
identities. The bounded probe folds child results while distinguishing a known
miss from an unsupported shape. Its depth and width are physical selection
parameters, not source fuel or language limits.

Every definite probe result agrees with the reference. Supported finite shapes
produce a definite result, and combining the probe with the general lookup
preserves all answers. Positive and negative controls keep refusal distinct
from a missing child.

Primitive table readers are supplied functions. Native stability admission,
registered pointer-cache validity, scalar encodings and memory ownership retain
their separate correspondence obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.Cursor.BoundedTermLookup
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
variable {Id : Type}

def reference (leaf : Atom → Option Id) (node : List Id → Option Id)
    (term : Atom) : Option Id :=
  match term with
  | .expression children => (childrenLookup children).bind node
  | other => leaf other
termination_by sizeOf term
where
  childrenLookup : List Atom → Option (List Id)
    | [] => some []
    | first :: rest => do
      let head ← reference leaf node first
      let tail ← childrenLookup rest
      pure (head :: tail)
  termination_by children => sizeOf children

abbrev Probe (α : Type) := Option (Option α)

def prepend (head : Probe Id) (tail : Probe (List Id)) : Probe (List Id) :=
  match head with
  | none => none
  | some none => some none
  | some (some value) =>
    match tail with
    | none => none
    | some none => some none
    | some (some values) => some (some (value :: values))

def probe (leaf : Atom → Option Id) (node : List Id → Option Id)
    (width : Nat) : Nat → Atom → Probe Id
  | 0, .expression _ => none
  | depth + 1, .expression children =>
    if width < children.length then none else
    match children.foldr (fun child tail => prepend (probe leaf node width depth child) tail)
        (some (some [])) with
    | none => none
    | some none => some none
    | some (some ids) => some (node ids)
  | _, other => some (leaf other)


def Agrees {α : Type} (result : Probe α) (expected : Option α) : Prop :=
  result = none ∨ result = some expected

theorem prepend_agrees (head : Probe Id) (tail : Probe (List Id))
    (first : Option Id) (rest : Option (List Id))
    (headAgrees : Agrees head first) (tailAgrees : Agrees tail rest) :
    Agrees (prepend head tail) (do
      let value ← first
      let values ← rest
      pure (value :: values)) := by
  rcases headAgrees with rfl | rfl
  · exact Or.inl rfl
  · rcases tailAgrees with rfl | rfl
    · cases first <;> simp [prepend, Agrees]
    · cases first <;> cases rest <;> simp [prepend, Agrees]

theorem probe_agrees (leaf : Atom → Option Id) (node : List Id → Option Id)
    (width depth : Nat) (term : Atom) :
    Agrees (probe leaf node width depth term) (reference leaf node term) := by
  induction depth generalizing term with
  | zero =>
    cases term <;> simp [probe, reference, Agrees]
  | succ depth ih =>
    cases term with
    | symbol name => simp [probe, reference, Agrees]
    | var name => simp [probe, reference, Agrees]
    | grounded value => simp [probe, reference, Agrees]
    | expression children =>
      by_cases wide : width < children.length
      · simp [probe, wide, Agrees]
      · have components : Agrees
            (children.foldr (fun child tail => prepend (probe leaf node width depth child) tail)
              (some (some [])))
            (reference.childrenLookup leaf node children) := by
          clear wide
          induction children with
          | nil => simp [Agrees, reference.childrenLookup]
          | cons first rest childrenIH =>
            simpa only [List.foldr_cons, reference.childrenLookup] using
              prepend_agrees _ _ _ _ (ih first) childrenIH
        rcases components with refused | known
        · simp [probe, wide, refused, Agrees]
        · cases outcome : reference.childrenLookup leaf node children <;>
            simp [probe, wide, known, reference, outcome, Agrees]

def hybrid (leaf : Atom → Option Id) (node : List Id → Option Id)
    (width depth : Nat) (term : Atom) : Option Id :=
  match probe leaf node width depth term with
  | none => reference leaf node term
  | some answer => answer

theorem hybrid_refines (leaf : Atom → Option Id) (node : List Id → Option Id)
    (width depth : Nat) (term : Atom) :
    hybrid leaf node width depth term = reference leaf node term := by
  rcases probe_agrees leaf node width depth term with refused | known
  · simp [hybrid, refused]
  · simp [hybrid, known]

def Fits (width : Nat) : Nat → Atom → Prop
  | 0, .expression _ => False
  | depth + 1, .expression children =>
      children.length ≤ width ∧ ∀ child ∈ children, Fits width depth child
  | _, _ => True

theorem prepend_known (head : Option Id) (tail : Option (List Id)) :
    prepend (some head) (some tail) = some (do
      let value ← head
      let values ← tail
      pure (value :: values)) := by
  cases head <;> cases tail <;> rfl

theorem fold_known (leaf : Atom → Option Id) (node : List Id → Option Id)
    (width depth : Nat) (children : List Atom)
    (known : ∀ child ∈ children,
      probe leaf node width depth child = some (reference leaf node child)) :
    children.foldr (fun child tail => prepend (probe leaf node width depth child) tail)
      (some (some [])) = some (reference.childrenLookup leaf node children) := by
  induction children with
  | nil => simp [reference.childrenLookup]
  | cons first rest ih =>
    have headKnown := known first (List.mem_cons_self ..)
    have tailKnown := ih (fun child member => known child (List.mem_cons_of_mem first member))
    simpa only [List.foldr_cons, headKnown, tailKnown, reference.childrenLookup] using
      prepend_known (reference leaf node first) (reference.childrenLookup leaf node rest)

theorem probe_complete_when_fits (leaf : Atom → Option Id) (node : List Id → Option Id)
    (width depth : Nat) (term : Atom) (fits : Fits width depth term) :
    probe leaf node width depth term = some (reference leaf node term) := by
  induction depth generalizing term with
  | zero => cases term <;> simp_all [Fits, probe, reference]
  | succ depth ih =>
    cases term with
    | symbol name => simp [probe, reference]
    | var name => simp [probe, reference]
    | grounded value => simp [probe, reference]
    | expression children =>
      have bounded := fits.1
      have known := fold_known leaf node width depth children
        (fun child member => ih child (fits.2 child member))
      have notWide : ¬ width < children.length := by omega
      cases outcome : reference.childrenLookup leaf node children <;>
        simp [probe, notWide, known, reference, outcome]

def exampleLeaf : Atom → Option Nat
  | .symbol "known" => some 17
  | _ => none

def exampleNode : List Nat → Option Nat
  | [17] => some 23
  | [17, 17] => some 31
  | [23] => some 37
  | [] => some 41
  | _ => none

theorem shallow_present_control :
    probe exampleLeaf exampleNode 2 1 (.expression [.symbol "known"]) = some (some 23) := by
  decide +kernel

theorem missing_child_is_known_absent :
    probe exampleLeaf exampleNode 2 1 (.expression [.symbol "missing"]) = some none := by
  decide +kernel

theorem depth_refusal_keeps_present_fallback :
    probe exampleLeaf exampleNode 2 1 (.expression [.expression [.symbol "known"]]) = none ∧
      hybrid exampleLeaf exampleNode 2 1 (.expression [.expression [.symbol "known"]]) = some 37 := by
  constructor
  · decide +kernel
  · rw [hybrid_refines]; decide +kernel

theorem width_refusal_keeps_present_fallback :
    probe exampleLeaf exampleNode 1 2 (.expression [.symbol "known", .symbol "known"]) = none ∧
      hybrid exampleLeaf exampleNode 1 2 (.expression [.symbol "known", .symbol "known"]) = some 31 := by
  constructor
  · decide +kernel
  · rw [hybrid_refines]; decide +kernel

end Mettapedia.Machines.Cursor.BoundedTermLookup
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.probe_agrees
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.hybrid_refines
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.probe_complete_when_fits
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.shallow_present_control
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.missing_child_is_known_absent
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.depth_refusal_keeps_present_fallback
#print axioms Mettapedia.Machines.Cursor.BoundedTermLookup.width_refusal_keeps_present_fallback
