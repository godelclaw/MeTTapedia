import Mettapedia.Computability.RegularLanguages.Literals

/-!
# Finite Thompson construction for authored selection patterns

The source keeps ordered alternatives, repetition preference, capture identity,
scalar ranges and assertions as ordinary data. Construction produces an explicit
finite address-indexed program; nullable repetition introduces a real back edge.
This file proves address-ownership and recognition-erasure properties, not adequacy of
the ordered executor or of a native implementation. Assertions are not erased:
their interpretation requires an input position and context.
-/

set_option autoImplicit false
open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.RegexSelection

open Mettapedia.Computability.RegularLanguages

abbrev ScalarRange := Nat × Nat

/-- Inclusive ranges. An inverted range contributes no scalar. -/
def rangeLetters (range : ScalarRange) : List Nat :=
  List.range' range.1 (range.2 + 1 - range.1)

def classLetters (ranges : List ScalarRange) : List Nat := ranges.flatMap rangeLetters

/-- Canonical pattern values. Unicode scalar admission is a separate boundary. -/
inductive Pattern where
  | zero
  | epsilon
  | literal (scalar : Nat)
  | any
  | class_ (ranges : List ScalarRange)
  | seq (first second : Pattern)
  | alt (first second : Pattern)
  | optional (body : Pattern) (greedy : Bool)
  | star (body : Pattern) (greedy : Bool)
  | plus (body : Pattern) (greedy : Bool)
  | capture (group : Nat) (body : Pattern)
  | assertion (name : String)
  deriving DecidableEq, Repr

/-- Public group identities are not regenerated when syntax is expanded. -/
def captureGroups : Pattern → List Nat
  | .zero | .epsilon | .literal _ | .any | .class_ _ | .assertion _ => []
  | .seq first second | .alt first second => captureGroups first ++ captureGroups second
  | .optional body _ | .star body _ | .plus body _ => captureGroups body
  | .capture group body => group :: captureGroups body

def repeatExact (body : Pattern) : Nat → Pattern
  | 0 => .epsilon
  | count + 1 => .seq body (repeatExact body count)

theorem optional_groups (body : Pattern) (greedy : Bool) :
    captureGroups (.optional body greedy) = captureGroups body := rfl

theorem plus_groups (body : Pattern) (greedy : Bool) :
    captureGroups (.plus body greedy) = captureGroups body := rfl

theorem repeatExact_groups (body : Pattern) (count : Nat) :
    captureGroups (repeatExact body count) = (List.replicate count (captureGroups body)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih => simp [repeatExact, captureGroups, ih, List.replicate_succ]

/-- Recognition erasure is partial in the absence of assertion context. This
does not classify assertion-bearing patterns as invalid or unexecutable. -/
def erase? : Pattern → Option (Regex Nat)
  | .zero => some 0
  | .epsilon => some 1
  | .literal scalar => some (literal scalar)
  | .any => some any
  | .class_ ranges => some (oneOf (classLetters ranges))
  | .seq first second => do return (← erase? first) * (← erase? second)
  | .alt first second => do return (← erase? first) + (← erase? second)
  | .optional body _ => do return (← erase? body) + 1
  | .star body _ => do return (← erase? body).star
  | .plus body _ => do
      let erased ← erase? body
      return erased * erased.star
  | .capture _ body => erase? body
  | .assertion _ => none

/-- An independent language interpretation of the context-free observation.
It does not invoke the derivative matcher or the Thompson construction. -/
def language? : Pattern → Option (Language Nat)
  | .zero => some 0
  | .epsilon => some 1
  | .literal scalar => some {[scalar]}
  | .any => some {word | ∃ scalar, word = [scalar]}
  | .class_ ranges => some {word | ∃ scalar ∈ classLetters ranges, word = [scalar]}
  | .seq first second => do return (← language? first) * (← language? second)
  | .alt first second => do return (← language? first) + (← language? second)
  | .optional body _ => do return (← language? body) + 1
  | .star body _ => do return (← language? body)∗
  | .plus body _ => do
      let interpreted ← language? body
      return interpreted * interpreted∗
  | .capture _ body => language? body
  | .assertion _ => none

/-- Captures and priorities forget to the independent recognition language.
Assertions remain an explicit missing contextual interpretation. -/
theorem erase_language (pattern : Pattern) :
    (erase? pattern).map language = language? pattern := by
  induction pattern with
  | zero => rfl
  | epsilon => rfl
  | literal scalar => rfl
  | any => rfl
  | class_ ranges =>
      simp only [erase?, language?, Option.map_some]
      congr 1
      ext input
      exact mem_language_oneOf _ _
  | seq first second ihFirst ihSecond =>
      simp only [erase?, language?]
      rw [← ihFirst, ← ihSecond]
      cases erase? first <;> cases erase? second <;> rfl
  | alt first second ihFirst ihSecond =>
      simp only [erase?, language?]
      rw [← ihFirst, ← ihSecond]
      cases erase? first <;> cases erase? second <;> rfl
  | star body greedy ih =>
      simp only [erase?, language?]
      rw [← ih]
      cases erase? body <;> rfl
  | optional body greedy ih =>
      simp only [erase?, language?]
      rw [← ih]
      cases erase? body <;> rfl
  | plus body greedy ih =>
      simp only [erase?, language?]
      rw [← ih]
      cases erase? body <;> rfl
  | capture group body ih => exact ih
  | assertion name => rfl

theorem erased_recognition_iff (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (input : List Nat) :
    language? pattern = some (language regex) ∧
      (fullMatch regex input = true ↔ input ∈ language regex) := by
  constructor
  · simpa [erased] using (erase_language pattern).symm
  · exact fullMatch_correct regex input

/-- Symbolic paths are the actual addresses emitted by the authored family.
They are relocated only after the finite compiler result has been validated. -/
inductive Address where
  | root
  | ending
  | left (parent : Address)
  | right (parent : Address)
  | body (parent : Address)
  | loop (parent : Address)
  | close (parent : Address)
  deriving DecidableEq, Repr

def Address.depth : Address → Nat
  | .root | .ending => 0
  | .left parent | .right parent | .body parent | .loop parent | .close parent => parent.depth + 1

inductive Branch where
  | left | right | body | loop | close
  deriving DecidableEq, Repr

def Address.child (branch : Branch) (parent : Address) : Address :=
  match branch with
  | .left => .left parent
  | .right => .right parent
  | .body => .body parent
  | .loop => .loop parent
  | .close => .close parent

@[simp] theorem child_depth (branch : Branch) (parent : Address) :
    (parent.child branch).depth = parent.depth + 1 := by cases branch <;> rfl

theorem child_eq_iff (first second : Branch) (parent other : Address) :
    parent.child first = other.child second ↔ first = second ∧ parent = other := by
  cases first <;> cases second <;> simp [Address.child]

inductive Within : Address → Address → Prop where
  | refl (base : Address) : Within base base
  | left {base address} : Within base address → Within base (.left address)
  | right {base address} : Within base address → Within base (.right address)
  | body {base address} : Within base address → Within base (.body address)
  | loop {base address} : Within base address → Within base (.loop address)
  | close {base address} : Within base address → Within base (.close address)

theorem Within.trans {first second third : Address}
    (before : Within first second) (after : Within second third) : Within first third := by
  induction after with
  | refl => exact before
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | body _ ih => exact .body ih
  | loop _ ih => exact .loop ih
  | close _ ih => exact .close ih

theorem Within.depth_le {base address : Address} (inside : Within base address) :
    base.depth ≤ address.depth := by
  induction inside <;> simp_all [Address.depth] <;> omega

theorem within_child_iff (base parent : Address) (branch : Branch) :
    Within base (parent.child branch) ↔ base = parent.child branch ∨ Within base parent := by
  cases branch <;> constructor
  all_goals try { intro inside; cases inside; exact Or.inl rfl; exact Or.inr (by assumption) }
  all_goals
    rintro (same | inside)
    · subst base; exact .refl _
    · first | exact .left inside | exact .right inside | exact .body inside |
        exact .loop inside | exact .close inside

theorem no_child_within_parent (parent : Address) (branch : Branch) :
    ¬ Within (parent.child branch) parent := by
  intro inside
  have bound := inside.depth_le
  simp only [child_depth] at bound
  omega

theorem parent_ne_child (parent : Address) (branch : Branch) : parent ≠ parent.child branch := by
  intro same
  have depths := congrArg Address.depth same
  simp only [child_depth] at depths
  omega

theorem distinct_children_incomparable (parent : Address) (first second : Branch)
    (distinct : first ≠ second) : ¬ Within (parent.child first) (parent.child second) := by
  rw [within_child_iff]
  rintro (same | inside)
  · exact distinct ((child_eq_iff first second parent parent).mp same).1
  · exact no_child_within_parent parent first inside

/-- Two ancestors of the same path are comparable; disjoint sibling trees
therefore cannot acquire a common descendant. -/
theorem Within.comparable {first second target : Address}
    (one : Within first target) (two : Within second target) :
    Within first second ∨ Within second first := by
  induction one with
  | refl => exact Or.inr two
  | left before ih =>
      cases two with
      | refl => exact Or.inl (.left before)
      | left inside => exact ih inside
  | right before ih =>
      cases two with
      | refl => exact Or.inl (.right before)
      | right inside => exact ih inside
  | body before ih =>
      cases two with
      | refl => exact Or.inl (.body before)
      | body inside => exact ih inside
  | loop before ih =>
      cases two with
      | refl => exact Or.inl (.loop before)
      | loop inside => exact ih inside
  | close before ih =>
      cases two with
      | refl => exact Or.inl (.close before)
      | close inside => exact ih inside

theorem sibling_subtrees_disjoint (parent target : Address) (first second : Branch)
    (distinct : first ≠ second) (one : Within (parent.child first) target)
    (two : Within (parent.child second) target) : False := by
  rcases one.comparable two with forward | backward
  · exact distinct_children_incomparable parent first second distinct forward
  · exact distinct_children_incomparable parent second first (Ne.symm distinct) backward

inductive Boundary where
  | start
  | finish
  deriving DecidableEq, Repr

inductive Instruction where
  | fail (address : Address)
  | accept (address : Address)
  | jump (address next : Address)
  | scalar (address : Address) (value : Nat) (next : Address)
  | any (address next : Address)
  | class_ (address : Address) (ranges : List ScalarRange) (next : Address)
  | split (address first second : Address)
  | save (address : Address) (group : Nat) (boundary : Boundary) (next : Address)
  | assertion (address : Address) (name : String) (next : Address)
  deriving DecidableEq, Repr

def Instruction.address : Instruction → Address
  | .fail address | .accept address | .jump address _ | .scalar address _ _
  | .any address _ | .class_ address _ _ | .split address _ _
  | .save address _ _ _ | .assertion address _ _ => address

def Instruction.targets : Instruction → List Address
  | .fail _ | .accept _ => []
  | .jump _ next | .scalar _ _ next | .any _ next | .class_ _ _ next
  | .save _ _ _ next | .assertion _ _ next => [next]
  | .split _ first second => [first, second]

def choice (address first second : Address) (greedy : Bool) : Instruction :=
  if greedy then .split address first second else .split address second first

/-- The native equation family's path-address construction. The two star choices
are kept distinct even when the body is nullable. The source body is emitted
once, so its capture identity is not duplicated or freshened. -/
def emit : Pattern → Address → Address → List Instruction
  | .zero, _, address => [.fail address]
  | .epsilon, continuation, address => [.jump address continuation]
  | .literal scalar, continuation, address => [.scalar address scalar continuation]
  | .any, continuation, address => [.any address continuation]
  | .class_ ranges, continuation, address => [.class_ address ranges continuation]
  | .assertion name, continuation, address => [.assertion address name continuation]
  | .seq first second, continuation, address =>
      .jump address (.left address) ::
        (emit first (.right address) (.left address) ++ emit second continuation (.right address))
  | .alt first second, continuation, address =>
      .split address (.left address) (.right address) ::
        (emit first continuation (.left address) ++ emit second continuation (.right address))
  | .optional body greedy, continuation, address =>
      choice address (.body address) continuation greedy ::
      emit body continuation (.body address)
  | .star body greedy, continuation, address =>
      choice address (.body address) continuation greedy ::
      choice (.loop address) (.body address) continuation greedy ::
      emit body (.loop address) (.body address)
  | .plus body greedy, continuation, address =>
      .jump address (.body address) ::
      choice (.loop address) (.body address) continuation greedy ::
      emit body (.loop address) (.body address)
  | .capture group body, continuation, address =>
      .save address group .start (.body address) ::
      .save (.close address) group .finish continuation ::
      emit body (.close address) (.body address)

structure Program where
  entry : Address
  rows : List Instruction
  deriving DecidableEq, Repr

def compile (pattern : Pattern) : Program :=
  ⟨.root, .accept .ending :: emit pattern .ending .root⟩

theorem emit_nonempty (pattern : Pattern) (continuation address : Address) :
    emit pattern continuation address ≠ [] := by
  cases pattern <;> simp [emit]

/-- Every instruction definition is owned by the source subtree that emitted
it. Continuation addresses are only references, never definitions here. -/
theorem emit_owned (pattern : Pattern) (continuation address : Address)
    (instruction : Instruction) (member : instruction ∈ emit pattern continuation address) :
    Within address instruction.address := by
  induction pattern generalizing continuation address with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ =>
      simp only [emit, List.mem_singleton] at member
      subst instruction
      exact .refl _
  | seq first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        exact .refl _
      · exact (Within.left (.refl address)).trans (ihFirst _ _ member)
      · exact (Within.right (.refl address)).trans (ihSecond _ _ member)
  | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        exact .refl _
      · exact (Within.left (.refl address)).trans (ihFirst _ _ member)
      · exact (Within.right (.refl address)).trans (ihSecond _ _ member)
  | star body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        cases greedy <;> exact .refl _
      · subst instruction
        cases greedy <;> exact .loop (.refl _)
      · exact (Within.body (.refl address)).trans (ih _ _ member)
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst instruction
        cases greedy <;> exact .refl _
      · exact (Within.body (.refl address)).trans (ih _ _ member)
  | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        exact .refl _
      · subst instruction
        cases greedy <;> exact .loop (.refl _)
      · exact (Within.body (.refl address)).trans (ih _ _ member)
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        exact .refl _
      · subst instruction
        exact .close (.refl _)
      · exact (Within.body (.refl address)).trans (ih _ _ member)

/-- The compiler never defines a sibling or enclosing continuation by accident. -/
theorem not_owned_cannot_be_defined (pattern : Pattern) (continuation address target : Address)
    (outside : ¬ Within address target) :
    ¬ ∃ instruction ∈ emit pattern continuation address, instruction.address = target := by
  rintro ⟨instruction, member, same⟩
  exact outside (same ▸ emit_owned pattern continuation address instruction member)

theorem emit_child_not_parent (pattern : Pattern) (continuation parent : Address) (branch : Branch) :
    parent ∉ (emit pattern continuation (parent.child branch)).map Instruction.address := by
  intro member
  obtain ⟨instruction, inside, same⟩ := List.mem_map.mp member
  have owned : Within (parent.child branch) instruction.address :=
    emit_owned pattern continuation _ instruction inside
  rw [same] at owned
  exact no_child_within_parent parent branch owned

theorem emit_other_child_not_mem (pattern : Pattern) (continuation parent : Address)
    (first second : Branch) (distinct : first ≠ second) :
    parent.child first ∉ (emit pattern continuation (parent.child second)).map Instruction.address := by
  intro member
  obtain ⟨instruction, inside, same⟩ := List.mem_map.mp member
  exact distinct_children_incomparable parent second first (Ne.symm distinct)
    (same ▸ emit_owned pattern continuation _ instruction inside)

theorem emit_siblings_disjoint (firstPattern secondPattern : Pattern)
    (firstContinuation secondContinuation parent : Address)
    (first second : Branch) (distinct : first ≠ second) :
    List.Disjoint
      ((emit firstPattern firstContinuation (parent.child first)).map Instruction.address)
      ((emit secondPattern secondContinuation (parent.child second)).map Instruction.address) := by
  apply List.disjoint_left.mpr
  intro address firstMember secondMember
  obtain ⟨firstInstruction, firstMember, firstSame⟩ := List.mem_map.mp firstMember
  obtain ⟨secondInstruction, secondMember, secondSame⟩ := List.mem_map.mp secondMember
  exact sibling_subtrees_disjoint parent address first second distinct
    (firstSame ▸ emit_owned firstPattern firstContinuation _ firstInstruction firstMember)
    (secondSame ▸ emit_owned secondPattern secondContinuation _ secondInstruction secondMember)

/-- Address relocation receives one definition per symbolic address. Repeated
uses of a group do not merge source subtrees or instruction occurrences. -/
theorem emit_addresses_nodup (pattern : Pattern) (continuation address : Address) :
    ((emit pattern continuation address).map Instruction.address).Nodup := by
  induction pattern generalizing continuation address with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ => simp [emit]
  | seq first second ihFirst ihSecond =>
      have one := emit_child_not_parent first (.right address) address .left
      have two := emit_child_not_parent second continuation address .right
      have disjoint := emit_siblings_disjoint first second (.right address) continuation
        address .left .right (by decide)
      simp only [Address.child] at one two disjoint
      simp [emit, Instruction.address, List.nodup_append', ihFirst, ihSecond, one, two, disjoint]
  | alt first second ihFirst ihSecond =>
      have one := emit_child_not_parent first continuation address .left
      have two := emit_child_not_parent second continuation address .right
      have disjoint := emit_siblings_disjoint first second continuation continuation
        address .left .right (by decide)
      simp only [Address.child] at one two disjoint
      simp [emit, Instruction.address, List.nodup_append', ihFirst, ihSecond, one, two, disjoint]
  | star body greedy ih =>
      have rootNot := emit_child_not_parent body (.loop address) address .body
      have loopNot := emit_other_child_not_mem body (.loop address) address .loop .body (by decide)
      simp only [Address.child] at rootNot loopNot
      cases greedy <;>
        simp [emit, choice, Instruction.address, ih, rootNot, loopNot,
          show address ≠ .loop address from parent_ne_child address .loop]
  | optional body greedy ih =>
      have rootNot := emit_child_not_parent body continuation address .body
      simp only [Address.child] at rootNot
      cases greedy <;> simp [emit, choice, Instruction.address, ih, rootNot]
  | plus body greedy ih =>
      have rootNot := emit_child_not_parent body (.loop address) address .body
      have loopNot := emit_other_child_not_mem body (.loop address) address .loop .body (by decide)
      simp only [Address.child] at rootNot loopNot
      cases greedy <;>
        simp [emit, choice, Instruction.address, ih, rootNot, loopNot,
          show address ≠ .loop address from parent_ne_child address .loop]
  | capture group body ih =>
      have rootNot := emit_child_not_parent body (.close address) address .body
      have closeNot := emit_other_child_not_mem body (.close address) address .close .body (by decide)
      simp only [Address.child] at rootNot closeNot
      simp [emit, Instruction.address, ih, rootNot, closeNot,
        show address ≠ .close address from parent_ne_child address .close]

def entryInstruction : Pattern → Address → Address → Instruction
  | .zero, _, address => .fail address
  | .epsilon, continuation, address => .jump address continuation
  | .literal scalar, continuation, address => .scalar address scalar continuation
  | .any, continuation, address => .any address continuation
  | .class_ ranges, continuation, address => .class_ address ranges continuation
  | .assertion name, continuation, address => .assertion address name continuation
  | .seq _ _, _, address => .jump address (.left address)
  | .alt _ _, _, address => .split address (.left address) (.right address)
  | .optional _ greedy, continuation, address => choice address (.body address) continuation greedy
  | .star _ greedy, continuation, address => choice address (.body address) continuation greedy
  | .plus _ _, _, address => .jump address (.body address)
  | .capture group _, _, address => .save address group .start (.body address)

theorem emit_entry_lookup (pattern : Pattern) (continuation address : Address) :
    (emit pattern continuation address).find? (fun instruction => instruction.address == address) =
      some (entryInstruction pattern continuation address) := by
  cases pattern <;> simp [emit, entryInstruction, Instruction.address]
  all_goals rename_i body greedy; cases greedy <;> simp [choice]

/-- No emitted control edge escapes the subtree except through the explicitly
supplied continuation. This remains true for nested captures and nullable loops. -/
theorem emit_targets_owned_or_continuation (pattern : Pattern) (continuation address : Address)
    (instruction : Instruction) (member : instruction ∈ emit pattern continuation address)
    (target : Address) (edge : target ∈ instruction.targets) :
    Within address target ∨ target = continuation := by
  induction pattern generalizing continuation address instruction target with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ =>
      simp only [emit, List.mem_singleton] at member
      subst instruction
      simp_all [Instruction.targets]
  | seq first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        subst target
        exact Or.inl (.left (.refl _))
      · rcases ihFirst _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.left (.refl address)).trans inside)
        · subst target; exact Or.inl (.right (.refl _))
      · rcases ihSecond _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.right (.refl address)).trans inside)
        · exact Or.inr same
  | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        simp only [Instruction.targets, List.mem_cons, List.not_mem_nil, or_false] at edge
        rcases edge with same | same
        · subst target; exact Or.inl (.left (.refl _))
        · subst target; exact Or.inl (.right (.refl _))
      · rcases ihFirst _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.left (.refl address)).trans inside)
        · exact Or.inr same
      · rcases ihSecond _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.right (.refl address)).trans inside)
        · exact Or.inr same
  | star body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        cases greedy <;>
          simp only [choice, Instruction.targets, Bool.false_eq_true, if_false, if_true,
            List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same
        all_goals subst target
        all_goals first | exact Or.inr rfl | exact Or.inl (.body (.refl _))
      · subst instruction
        cases greedy <;>
          simp only [choice, Instruction.targets, Bool.false_eq_true, if_false, if_true,
            List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same
        all_goals subst target
        all_goals first | exact Or.inr rfl | exact Or.inl (.body (.refl _))
      · rcases ih _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.body (.refl address)).trans inside)
        · subst target; exact Or.inl (.loop (.refl _))
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst instruction
        cases greedy <;>
          simp only [choice, Instruction.targets, Bool.false_eq_true, if_false, if_true,
            List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same
        all_goals subst target
        all_goals first | exact Or.inr rfl | exact Or.inl (.body (.refl _))
      · rcases ih _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.body (.refl address)).trans inside)
        · exact Or.inr same
  | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        subst target
        exact Or.inl (.body (.refl _))
      · subst instruction
        cases greedy <;>
          simp only [choice, Instruction.targets, Bool.false_eq_true, if_false, if_true,
            List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same
        all_goals subst target
        all_goals first | exact Or.inr rfl | exact Or.inl (.body (.refl _))
      · rcases ih _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.body (.refl address)).trans inside)
        · subst target; exact Or.inl (.loop (.refl _))
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        subst target
        exact Or.inl (.body (.refl _))
      · subst instruction
        simp only [Instruction.targets, List.mem_singleton] at edge
        exact Or.inr edge
      · rcases ih _ _ _ member _ edge with inside | same
        · exact Or.inl ((Within.body (.refl address)).trans inside)
        · subst target; exact Or.inl (.close (.refl _))

namespace Controls

theorem nullable_loop_has_distinct_entry_and_repeat_choices :
    emit (.star .epsilon true) .ending .root =
      [.split .root (.body .root) .ending,
       .split (.loop .root) (.body .root) .ending,
       .jump (.body .root) (.loop .root)] := rfl

theorem lazy_loop_reverses_both_priorities :
    emit (.star (.literal 97) false) .ending .root =
      [.split .root .ending (.body .root),
       .split (.loop .root) .ending (.body .root),
       .scalar (.body .root) 97 (.loop .root)] := rfl

theorem repeated_capture_keeps_group_identity :
    captureGroups (repeatExact (.capture 3 (.literal 97)) 2) = [3, 3] := rfl

theorem nested_repetitions_keep_one_source_capture :
    captureGroups (.plus (.optional (.capture 3 .epsilon) false) true) = [3] := rfl

theorem direct_plus_is_not_capture_duplicating_expansion :
    compile (.plus (.capture 3 .epsilon) true) ≠
      compile (.seq (.capture 3 .epsilon) (.star (.capture 3 .epsilon) true)) := by decide

theorem stable_capture_slots :
    emit (.capture 3 (.literal 97)) .ending .root =
      [.save .root 3 .start (.body .root),
       .save (.close .root) 3 .finish .ending,
       .scalar (.body .root) 97 (.close .root)] := rfl

theorem captures_erase_but_assertions_do_not :
    erase? (.capture 1 (.literal 97)) = some (literal 97) ∧
      erase? (.seq (.assertion "begin") (.literal 97)) = none := ⟨rfl, rfl⟩

theorem nullable_star_is_not_compiled_as_only_empty :
    compile (.star (.literal 97) true) ≠ compile .epsilon := by decide

theorem finite_class_positive :
    (erase? (.class_ [(97, 99)])).map (fun regex => fullMatch regex [98]) = some true := by decide

theorem finite_class_negative :
    (erase? (.class_ [(97, 99)])).map (fun regex => fullMatch regex [100]) = some false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSelection
