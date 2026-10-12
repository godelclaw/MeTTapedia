import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Finite.Basic

/-!
# Complete typed ground factor data and bounded outer residues

A factor retains both the whole normalized one-hole context and its complete
input value. Its equation is checked against an independently supplied ground
value. Outer residues embed into the finite powerset of that value's inventory;
no finiteness of the signature or faithfulness of its ground action is assumed.
Selected free frames retain every sibling at its actual declared sort.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative.GroundFactors

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

abbrev Reading (source target : signature.Srt) :=
  MixedContext signature Parallel source target × Class signature Parallel source

def evaluate {source target : signature.Srt} (reading : Reading (Parallel := Parallel) source target) :
    Class signature Parallel target :=
  (mixedAction signature Parallel).read reading.1 reading.2

abbrev Factor (source : signature.Srt) {target : signature.Srt}
    (whole : Class signature Parallel target) :=
  {reading : Reading (Parallel := Parallel) source target // evaluate reading = whole}

abbrev BoundedResidue {target : signature.Srt} (whole : Class signature Parallel target) :=
  {bag : Multiset (ResiduePayload (signature := signature) (Parallel := Parallel) target) //
    bag.map Subtype.val ≤ inventoryQ whole}

theorem boundedResidue_finite {target : signature.Srt} (whole : Class signature Parallel target) :
    Finite (BoundedResidue whole) := by
  classical
  have bounded : Set.Finite {bag : Multiset (Head (signature := signature) (Parallel := Parallel) target) |
      bag ≤ inventoryQ whole} :=
    ((inventoryQ whole).powerset.finite_toSet).subset (fun _ admitted => Multiset.mem_powerset.mpr admitted)
  let _ := bounded.fintype
  apply Finite.of_injective
    (fun supplied : BoundedResidue whole => (⟨supplied.val.map Subtype.val, supplied.property⟩ :
      {bag : Multiset (Head (signature := signature) (Parallel := Parallel) target) | bag ≤ inventoryQ whole}))
  intro first second same
  apply Subtype.ext
  exact Multiset.map_injective Subtype.val_injective (congrArg Subtype.val same)

theorem outer_residue_bounded {source target : signature.Srt}
    (context : MixedContext signature Parallel source target) (input : Class signature Parallel source) :
    context.outerBag.map Subtype.val ≤ inventoryQ ((mixedAction signature Parallel).read context input) := by
  cases context with
  | parallel bag =>
    change bag.map Subtype.val ≤ inventoryQ (residue bag input)
    rw [residue_inventory]
    exact Multiset.le_add_right _ _
  | frame bag frame inner =>
    change bag.map Subtype.val ≤ inventoryQ
      (residue bag (frame.fill ((mixedAction signature Parallel).read inner input)))
    rw [residue_inventory]
    exact Multiset.le_add_right _ _

def outerResidue {source target : signature.Srt} {whole : Class signature Parallel target}
    (factor : Factor source whole) : BoundedResidue whole :=
  ⟨factor.val.1.outerBag, (outer_residue_bounded factor.val.1 factor.val.2).trans_eq
    (congrArg inventoryQ factor.property)⟩

namespace Head

abbrev Position {target : signature.Srt} :
    SortedCommutative.Head (signature := signature) (Parallel := Parallel) target → Type
  | .node constructor _ => Fin (signature.arity constructor)

instance position_finite {target : signature.Srt}
    (head : SortedCommutative.Head (signature := signature) (Parallel := Parallel) target) :
    Finite (Position head) := by
  cases head with
  | node constructor arguments =>
    change Finite (Fin (signature.arity constructor))
    exact inferInstance

def inputSort {target : signature.Srt}
    (head : SortedCommutative.Head (signature := signature) (Parallel := Parallel) target) :
    Position head → signature.Srt :=
  match head with
  | .node constructor _ => signature.input constructor

def child {target : signature.Srt}
    (head : SortedCommutative.Head (signature := signature) (Parallel := Parallel) target) :
    (position : Position head) → Class signature Parallel (inputSort head position) :=
  match head with
  | .node _ arguments => arguments

def frame {target : signature.Srt}
    (head : SortedCommutative.Head (signature := signature) (Parallel := Parallel) target)
    (position : Position head) : Frame signature Parallel (inputSort head position) target := by
  cases head with
  | node constructor arguments =>
    exact .slot constructor position (fun other _absent => arguments other)

theorem frame_child {target : signature.Srt}
    (head : SortedCommutative.Head (signature := signature) (Parallel := Parallel) target)
    (position : Position head) : (frame head position).fill (child head position) = head.class := by
  cases head with
  | node constructor arguments =>
    change (SortedCommutative.Head.node constructor
      (Frame.insert constructor position (fun other _absent => arguments other) (arguments position))).class = _
    apply congrArg SortedCommutative.Head.class
    apply congrArg (SortedCommutative.Head.node constructor)
    funext other
    by_cases same : other = position
    · subst other
      simp only [Frame.insert, dite_true]
    · simp only [Frame.insert, dif_neg same]

end Head

abbrev OccurringHead {target : signature.Srt} (whole : Class signature Parallel target) :=
  {head : SortedCommutative.Head (signature := signature) (Parallel := Parallel) target //
    head ∈ inventoryQ whole}

theorem occurringHead_finite {target : signature.Srt} (whole : Class signature Parallel target) :
    Finite (OccurringHead whole) := by
  exact (inventoryQ whole).finite_toSet

abbrev FrameCode (source : signature.Srt) {target : signature.Srt}
    (whole : Class signature Parallel target) :=
  BoundedResidue whole ×
    (Σ head : OccurringHead whole, Σ position : Head.Position head.val,
      Factor source (Head.child head.val position))

def FrameCode.reading {source target : signature.Srt} {whole : Class signature Parallel target}
    (code : FrameCode source whole) : Reading (Parallel := Parallel) source target :=
  (.frame code.1.val (Head.frame code.2.1.val code.2.2.1) code.2.2.2.val.1, code.2.2.2.val.2)

theorem FrameCode.evaluate {source target : signature.Srt} {whole : Class signature Parallel target}
    (code : FrameCode source whole) :
    GroundFactors.evaluate code.reading = residue code.1.val code.2.1.val.class := by
  change residue code.1.val ((Head.frame code.2.1.val code.2.2.1).fill
    ((mixedAction signature Parallel).read code.2.2.2.val.1 code.2.2.2.val.2)) = _
  exact (congrArg (fun input => residue code.1.val ((Head.frame code.2.1.val code.2.2.1).fill input))
    code.2.2.2.property).trans (congrArg (residue code.1.val)
      (Head.frame_child code.2.1.val code.2.2.1))

end Mettapedia.OSLF.SortedCommutative.GroundFactors
