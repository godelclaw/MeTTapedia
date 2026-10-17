import Mettapedia.GSLT.LanguageDef.RegexDependentAuthored
import Mettapedia.GSLT.LanguageDef.RegexObservationKernel

/-!
# Earned ownership and relocation of dependent regex programs

Structural occurrence addresses retain each source use, including observation
bodies and their separate terminal sites. Unique definitions and closed target
ownership are proved for every actual authored compiler output, rather than
assumed by a realization record.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics


def Address.depth : Address → Nat
  | .root | .ending => 0
  | .left parent | .right parent | .body parent | .loop parent | .close parent |
    .lookBody parent | .lookEnd parent => parent.depth + 1

inductive Branch where
  | left | right | body | loop | close | lookBody | lookEnd
  deriving DecidableEq, Repr

def Address.child (branch : Branch) (parent : Address) : Address :=
  match branch with
  | .left => .left parent
  | .right => .right parent
  | .body => .body parent
  | .loop => .loop parent
  | .close => .close parent
  | .lookBody => .lookBody parent
  | .lookEnd => .lookEnd parent

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
  | lookBody {base address} : Within base address → Within base (.lookBody address)
  | lookEnd {base address} : Within base address → Within base (.lookEnd address)

theorem Within.trans {first second third : Address}
    (before : Within first second) (after : Within second third) : Within first third := by
  induction after with
  | refl => exact before
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | body _ ih => exact .body ih
  | loop _ ih => exact .loop ih
  | close _ ih => exact .close ih
  | lookBody _ ih => exact .lookBody ih
  | lookEnd _ ih => exact .lookEnd ih

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
        exact .loop inside | exact .close inside | exact .lookBody inside | exact .lookEnd inside

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

  | lookBody before ih =>
      cases two with
      | refl => exact Or.inl (.lookBody before)
      | lookBody inside => exact ih inside
  | lookEnd before ih =>
      cases two with
      | refl => exact Or.inl (.lookEnd before)
      | lookEnd inside => exact ih inside

theorem sibling_subtrees_disjoint (parent target : Address) (first second : Branch)
    (distinct : first ≠ second) (one : Within (parent.child first) target)
    (two : Within (parent.child second) target) : False := by
  rcases one.comparable two with forward | backward
  · exact distinct_children_incomparable parent first second distinct forward
  · exact distinct_children_incomparable parent second first (Ne.symm distinct) backward

theorem local_owned {pattern : Pattern} {continuation origin : Address} {row : Instruction}
    (source : Local pattern continuation origin row) : Within origin row.address := by
  cases source <;> simp only [Instruction.address]
  all_goals first
    | exact .refl _
    | exact .loop (.refl _)
    | exact .close (.refl _)
    | exact .lookEnd (.refl _)
    | rename_i body greedy
      cases greedy <;> simp [choice] <;> first | exact .refl _ | exact .loop (.refl _)

theorem source_owned {pattern : Pattern} {continuation origin : Address} {row : Instruction}
    (source : At pattern continuation origin row) : Within origin row.address := by
  induction source with
  | «local» source => exact local_owned source
  | seqLeft _ ih | altLeft _ ih => exact (Within.left (.refl _)).trans ih
  | seqRight _ ih | altRight _ ih => exact (Within.right (.refl _)).trans ih
  | optional _ ih | star _ ih | plus _ ih | capture _ ih => exact (Within.body (.refl _)).trans ih
  | look _ ih => exact (Within.lookBody (.refl _)).trans ih

theorem emit_owned (pattern : Pattern) (continuation origin : Address)
    (row : Instruction) (member : row ∈ emit pattern continuation origin) : Within origin row.address :=
  source_owned (emitted_source pattern continuation origin row member)

theorem emit_child_not_parent (pattern : Pattern) (continuation parent : Address) (branch : Branch) :
    parent ∉ (emit pattern continuation (parent.child branch)).map Instruction.address := by
  intro member
  obtain ⟨row, member, same⟩ := List.mem_map.mp member
  have owned := emit_owned pattern continuation (parent.child branch) row member
  rw [same] at owned
  exact no_child_within_parent parent branch owned

theorem emit_other_child_not_mem (pattern : Pattern) (continuation parent : Address)
    (first second : Branch) (distinct : first ≠ second) :
    parent.child first ∉ (emit pattern continuation (parent.child second)).map Instruction.address := by
  intro member
  obtain ⟨row, member, same⟩ := List.mem_map.mp member
  exact distinct_children_incomparable parent second first (Ne.symm distinct)
    (same ▸ emit_owned pattern continuation _ row member)

theorem emit_siblings_disjoint (firstPattern secondPattern : Pattern)
    (firstContinuation secondContinuation parent : Address)
    (first second : Branch) (distinct : first ≠ second) :
    List.Disjoint
      ((emit firstPattern firstContinuation (parent.child first)).map Instruction.address)
      ((emit secondPattern secondContinuation (parent.child second)).map Instruction.address) := by
  apply List.disjoint_left.mpr
  intro address firstMember secondMember
  obtain ⟨firstRow, firstMember, firstSame⟩ := List.mem_map.mp firstMember
  obtain ⟨secondRow, secondMember, secondSame⟩ := List.mem_map.mp secondMember
  exact sibling_subtrees_disjoint parent address first second distinct
    (firstSame ▸ emit_owned firstPattern firstContinuation _ firstRow firstMember)
    (secondSame ▸ emit_owned secondPattern secondContinuation _ secondRow secondMember)

theorem emit_addresses_nodup (pattern : Pattern) (continuation origin : Address) :
    ((emit pattern continuation origin).map Instruction.address).Nodup := by
  induction pattern generalizing continuation origin with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ | backref _ _ => simp [emit]
  | seq first second ihFirst ihSecond =>
      have one := emit_child_not_parent first (.right origin) origin .left
      have two := emit_child_not_parent second continuation origin .right
      have disjoint := emit_siblings_disjoint first second (.right origin) continuation
        origin .left .right (by decide)
      simp only [Address.child] at one two disjoint
      simp [emit, Instruction.address, List.nodup_append', ihFirst, ihSecond, one, two, disjoint]
  | alt first second ihFirst ihSecond =>
      have one := emit_child_not_parent first continuation origin .left
      have two := emit_child_not_parent second continuation origin .right
      have disjoint := emit_siblings_disjoint first second continuation continuation
        origin .left .right (by decide)
      simp only [Address.child] at one two disjoint
      simp [emit, Instruction.address, List.nodup_append', ihFirst, ihSecond, one, two, disjoint]
  | star body greedy ih | plus body greedy ih =>
      have rootNot := emit_child_not_parent body (.loop origin) origin .body
      have loopNot := emit_other_child_not_mem body (.loop origin) origin .loop .body (by decide)
      simp only [Address.child] at rootNot loopNot
      cases greedy <;>
        simp [emit, choice, Instruction.address, ih, rootNot, loopNot,
          show origin ≠ .loop origin from parent_ne_child origin .loop]
  | optional body greedy ih =>
      have rootNot := emit_child_not_parent body continuation origin .body
      simp only [Address.child] at rootNot
      cases greedy <;> simp [emit, choice, Instruction.address, ih, rootNot]
  | capture group body ih =>
      have rootNot := emit_child_not_parent body (.close origin) origin .body
      have closeNot := emit_other_child_not_mem body (.close origin) origin .close .body (by decide)
      simp only [Address.child] at rootNot closeNot
      simp [emit, Instruction.address, ih, rootNot, closeNot,
        show origin ≠ .close origin from parent_ne_child origin .close]
  | look kind body ih =>
      have rootNot := emit_child_not_parent body (.lookEnd origin) origin .lookBody
      have endNot := emit_other_child_not_mem body (.lookEnd origin) origin .lookEnd .lookBody (by decide)
      simp only [Address.child] at rootNot endNot
      simp [emit, Instruction.address, ih, rootNot, endNot,
        show origin ≠ .lookEnd origin from parent_ne_child origin .lookEnd]

def entryInstruction : Pattern → Address → Address → Instruction
  | .zero, _, origin => .fail origin
  | .epsilon, continuation, origin => .jump origin continuation
  | .literal scalar, continuation, origin => .scalar origin scalar continuation
  | .any, continuation, origin => .any origin continuation
  | .class_ ranges, continuation, origin => .class_ origin ranges continuation
  | .assertion name, continuation, origin => .assertion origin name continuation
  | .seq _ _, _, origin => .jump origin (.left origin)
  | .alt _ _, _, origin => .split origin (.left origin) (.right origin)
  | .optional _ greedy, continuation, origin | .star _ greedy, continuation, origin =>
      choice origin (.body origin) continuation greedy
  | .plus _ _, _, origin => .jump origin (.body origin)
  | .capture group _, _, origin => .save origin group true (.body origin)
  | .backref group mode, continuation, origin => .backref origin group mode continuation
  | .look kind _, continuation, origin => .look origin (.lookBody origin) kind continuation

theorem emit_entry_lookup (pattern : Pattern) (continuation origin : Address) :
    (emit pattern continuation origin).find? (fun row => row.address == origin) =
      some (entryInstruction pattern continuation origin) := by
  cases pattern <;> simp [emit, entryInstruction, Instruction.address]
  all_goals rename_i body greedy; cases greedy <;> simp [choice]

theorem emit_entry_present (pattern : Pattern) (continuation origin : Address) :
    origin ∈ (emit pattern continuation origin).map Instruction.address := by
  have member := List.mem_of_find?_eq_some (emit_entry_lookup pattern continuation origin)
  apply List.mem_map.mpr
  refine ⟨entryInstruction pattern continuation origin, member, ?_⟩
  cases pattern <;> simp [entryInstruction, Instruction.address]
  all_goals rename_i body greedy; cases greedy <;> simp [choice]

theorem emit_ordinary_targets_defined_or_continuation (pattern : Pattern) (continuation address : Address)
    (instruction : Instruction) (member : instruction ∈ emit pattern continuation address)
    (target : Address) (edge : target ∈ ordinaryTargets instruction) :
    target = continuation ∨ target ∈ (emit pattern continuation address).map Instruction.address := by
  induction pattern generalizing continuation address instruction target with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ | backref _ _ =>
      simp only [emit, List.mem_singleton] at member
      subst instruction
      simp_all [ordinaryTargets]
  | seq first second ihFirst ihSecond =>
      have firstDefined := emit_entry_present first (.right address) (.left address)
      have secondDefined := emit_entry_present second continuation (.right address)
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        simp only [ordinaryTargets, List.mem_singleton] at edge
        subst target
        exact Or.inr (by simp [emit, Instruction.address, firstDefined])
      · rcases ihFirst _ _ _ member _ edge with same | defined
        · subst target; exact Or.inr (by simp [emit, Instruction.address, secondDefined])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
      · rcases ihSecond _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | alt first second ihFirst ihSecond =>
      have firstDefined := emit_entry_present first continuation (.left address)
      have secondDefined := emit_entry_present second continuation (.right address)
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst instruction
        simp only [ordinaryTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
        rcases edge with same | same <;> subst target
        · exact Or.inr (by simp [emit, Instruction.address, firstDefined])
        · exact Or.inr (by simp [emit, Instruction.address, secondDefined])
      · rcases ihFirst _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
      · rcases ihSecond _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | optional body greedy ih =>
      have bodyDefined := emit_entry_present body continuation (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          ordinaryTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · rcases ih _ _ _ member _ edge with same | defined
        · exact Or.inl same
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | star body greedy ih =>
      have bodyDefined := emit_entry_present body (.loop address) (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          ordinaryTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          ordinaryTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target
          exact Or.inr (by cases greedy <;> simp [emit, choice, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | plus body greedy ih =>
      have bodyDefined := emit_entry_present body (.loop address) (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [ordinaryTargets, List.mem_singleton] at edge
        subst target
        exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · subst instruction
        cases greedy <;> simp only [choice, Bool.false_eq_true, if_false, if_true,
          ordinaryTargets, List.mem_cons, List.not_mem_nil, or_false] at edge
        all_goals rcases edge with same | same <;> subst target
        all_goals first | exact Or.inl rfl | exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target
          exact Or.inr (by cases greedy <;> simp [emit, choice, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | capture group body ih =>
      have bodyDefined := emit_entry_present body (.close address) (.body address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [ordinaryTargets, List.mem_singleton] at edge
        subst target
        exact Or.inr (by simp [emit, Instruction.address, bodyDefined])
      · subst instruction
        simp only [ordinaryTargets, List.mem_singleton] at edge
        exact Or.inl edge
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target
          exact Or.inr (by simp [emit, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])
  | look kind body ih =>
      have bodyDefined := emit_entry_present body (.lookEnd address) (.lookBody address)
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst instruction
        simp only [ordinaryTargets, List.mem_singleton] at edge
        subst target
        exact Or.inl rfl
      · subst instruction
        simp [ordinaryTargets] at edge
      · rcases ih _ _ _ member _ edge with same | defined
        · subst target; exact Or.inr (by simp [emit, Instruction.address])
        · exact Or.inr (by simp [emit, Instruction.address, defined])

theorem emit_look_body_defined (pattern : Pattern) (continuation origin rowOrigin entry next : Address)
    (kind : RegexDependentObservation.LookKind)
    (member : Instruction.look rowOrigin entry kind next ∈ emit pattern continuation origin) :
    entry ∈ (emit pattern continuation origin).map Instruction.address := by
  induction pattern generalizing continuation origin rowOrigin entry next with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ | backref _ _ => simp [emit] at member
  | seq first second ihFirst ihSecond | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · cases same
      · have owned := ihFirst _ _ _ _ _ member
        simp [emit, Instruction.address, owned]
      · have owned := ihSecond _ _ _ _ _ member
        simp [emit, Instruction.address, owned]
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · cases greedy <;> simp [choice] at same
      · have owned := ih _ _ _ _ _ member
        cases greedy <;> simp [emit, choice, Instruction.address, owned]
  | star body greedy ih | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · cases greedy <;> simp [choice] at same
      · cases greedy <;> simp [choice] at same
      · have owned := ih _ _ _ _ _ member
        cases greedy <;> simp [emit, choice, Instruction.address, owned]
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · cases same
      · cases same
      · have owned := ih _ _ _ _ _ member
        simp [emit, Instruction.address, owned]
  | look outerKind body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · cases same
        have present := emit_entry_present body (.lookEnd origin) (.lookBody origin)
        simp [emit, Instruction.address, present]
      · cases same
      · have owned := ih _ _ _ _ _ member
        simp [emit, Instruction.address, owned]

namespace Graph

def addresses (program : Program) : Finset Address := (program.rows.map Instruction.address).toFinset

abbrev Owned (program : Program) := {address // address ∈ addresses program}

instance (program : Program) : Fintype (Owned program) := inferInstance

def targets (row : Instruction) : List Address := ordinaryTargets row ++
  match row with | .look _ entry _ _ => [entry] | _ => []

theorem compile_entry_owned (pattern : Pattern) : (compile pattern).entry ∈ addresses (compile pattern) := by
  simp only [compile, addresses, List.map_cons, Instruction.address, List.mem_toFinset, List.mem_cons]
  exact Or.inr (emit_entry_present pattern .ending .root)

theorem compile_targets_owned (pattern : Pattern) (row : Instruction)
    (member : row ∈ (compile pattern).rows) (target : Address) (edge : target ∈ targets row) :
    target ∈ addresses (compile pattern) := by
  simp only [compile, List.mem_cons] at member
  rcases member with same | member
  · subst row
    simp [targets, ordinaryTargets] at edge
  · simp only [targets, List.mem_append] at edge
    rcases edge with ordinary | body
    · rcases emit_ordinary_targets_defined_or_continuation pattern .ending .root row member target ordinary with same | owned
      · subst target; simp [addresses, compile, Instruction.address]
      · simp [addresses, compile, Instruction.address, owned]
    · cases row <;> simp only [List.not_mem_nil, List.mem_singleton] at body
      subst target
      have owned := emit_look_body_defined pattern .ending .root _ _ _ _ member
      simp [addresses, compile, Instruction.address, owned]

theorem compile_addresses_nodup (pattern : Pattern) :
    ((compile pattern).rows.map Instruction.address).Nodup := by
  have absent : Address.ending ∉ (emit pattern .ending .root).map Instruction.address := by
    intro member
    obtain ⟨row, member, same⟩ := List.mem_map.mp member
    have owned := emit_owned pattern .ending .root row member
    rw [same] at owned
    cases owned
  simp [compile, Instruction.address, List.nodup_cons, absent, emit_addresses_nodup]

structure CheckedProgram where
  program : Program
  unique : (program.rows.map Instruction.address).Nodup
  entryOwned : program.entry ∈ addresses program
  targetsOwned : ∀ row ∈ program.rows, ∀ target ∈ targets row, target ∈ addresses program

/-- Admission is constructed for every actual structural compiler result. -/
def checkedCompile (pattern : Pattern) : CheckedProgram :=
  ⟨compile pattern, compile_addresses_nodup pattern, compile_entry_owned pattern, compile_targets_owned pattern⟩

def lookup (program : Program) (address : Address) : Option Instruction :=
  program.rows.find? (fun row => row.address == address)

theorem lookup_defined (program : Program) (address : Address) (owned : address ∈ addresses program) :
    ∃ row, lookup program address = some row ∧ row ∈ program.rows ∧ row.address = address := by
  have member : address ∈ program.rows.map Instruction.address := by simpa [addresses] using owned
  obtain ⟨row, member, same⟩ := List.mem_map.mp member
  cases found : lookup program address with
  | none =>
      have absent := List.find?_eq_none.mp found row member
      simp [same] at absent
  | some actual =>
      refine ⟨actual, rfl, List.mem_of_find?_eq_some found, ?_⟩
      have test : (actual.address == address) = true :=
        List.find?_some (p := fun row : Instruction => row.address == address) found
      exact beq_iff_eq.mp test

def relocate (program : Program) (address : Owned program) : Fin program.rows.length :=
  ⟨(program.rows.map Instruction.address).idxOf address.val, by
    have member : address.val ∈ program.rows.map Instruction.address := by
      simpa [addresses] using address.property
    simpa using List.idxOf_lt_length_of_mem member⟩

def atIndex (program : Program) (index : Fin program.rows.length) : Owned program :=
  ⟨program.rows[index.val].address, by
    simp only [addresses, List.mem_toFinset]
    exact List.mem_map.mpr ⟨_, List.getElem_mem index.isLt, rfl⟩⟩

theorem atIndex_relocate (program : Program) (address : Owned program) :
    atIndex program (relocate program address) = address := by
  apply Subtype.ext
  have found := List.getElem_idxOf (List.idxOf_lt_length_of_mem
    (show address.val ∈ program.rows.map Instruction.address from by simpa [addresses] using address.property))
  simpa only [atIndex, relocate, List.getElem_map] using found

theorem atIndex_injective (checked : CheckedProgram) : Function.Injective (atIndex checked.program) := by
  intro first second same
  apply Fin.ext
  apply (checked.unique.getElem_inj_iff
    (hi := by simp) (hj := by simp)).mp
  simpa [atIndex, List.getElem_map] using congrArg Subtype.val same

theorem relocate_atIndex (checked : CheckedProgram) (index : Fin checked.program.rows.length) :
    relocate checked.program (atIndex checked.program index) = index := by
  apply atIndex_injective checked
  exact atIndex_relocate checked.program (atIndex checked.program index)

/-- Compact indices and structural source occurrences are mutually inverse.
The indices are the existing emitted row order, not a fresh recompilation. -/
def relocation (checked : CheckedProgram) : Owned checked.program ≃ Fin checked.program.rows.length where
  toFun := relocate checked.program
  invFun := atIndex checked.program
  left_inv := atIndex_relocate checked.program
  right_inv := relocate_atIndex checked

theorem relocated_target_address (checked : CheckedProgram) (row : Instruction)
    (member : row ∈ checked.program.rows) (target : Address) (edge : target ∈ targets row) :
    checked.program.rows[(relocate checked.program
      ⟨target, checked.targetsOwned row member target edge⟩).val].address = target :=
  congrArg Subtype.val (atIndex_relocate checked.program ⟨target, checked.targetsOwned row member target edge⟩)

def maximumObservationDepth (program : Program) : Nat :=
  (program.rows.map (fun row => row.address.observationDepth)).foldr max 0

private theorem member_le_maximum (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih member).trans (Nat.le_max_right _ _)

theorem owned_depth_bounded (program : Program) (address : Address) (owned : address ∈ addresses program) :
    address.observationDepth ≤ maximumObservationDepth program := by
  have member : address ∈ program.rows.map Instruction.address := by simpa [addresses] using owned
  obtain ⟨row, member, same⟩ := List.mem_map.mp member
  exact member_le_maximum _ _ (List.mem_map.mpr ⟨row, member, congrArg Address.observationDepth same⟩)

/-- Remaining observation height is derived from the actual finite program;
it is not an arbitrary caller allowance. -/
def rank (program : Program) (address : Address) : Nat :=
  maximumObservationDepth program - address.observationDepth

theorem compiled_ordinary_rank (pattern : Pattern) (row : Instruction)
    (member : row ∈ (compile pattern).rows) (target : Address) (edge : target ∈ ordinaryTargets row) :
    rank (compile pattern) target ≤ rank (compile pattern) row.address := by
  simp only [compile, List.mem_cons] at member
  rcases member with same | member
  · subst row
    simp [ordinaryTargets] at edge
  · have depth := ordinary_target_same_depth pattern .ending .root rfl row member target edge
    simp only [rank, depth]
    exact le_rfl

theorem compiled_body_rank (pattern : Pattern) (origin entry next : Address)
    (kind : RegexDependentObservation.LookKind)
    (member : Instruction.look origin entry kind next ∈ (compile pattern).rows) :
    rank (compile pattern) entry < rank (compile pattern) origin := by
  have owned := compile_targets_owned pattern (.look origin entry kind next) member entry
    (by simp [targets, ordinaryTargets])
  have bounded := owned_depth_bounded (compile pattern) entry owned
  simp only [compile, List.mem_cons] at member
  rcases member with impossible | member
  · cases impossible
  · exact assertion_rank_strict _ origin entry
      (look_body_depth pattern .ending .root origin entry next kind member) bounded

end Graph

/-- Source authorization includes the explicit outer terminal. It is a
structural derivation, independent of row lookup and address relocation. -/
inductive Authorizes (pattern : Pattern) : Instruction → Prop
  | finish : Authorizes pattern (.accept .ending)
  | inside {row} : At pattern .ending .root row → Authorizes pattern row

theorem authorizes_iff_compiled (pattern : Pattern) (row : Instruction) :
    Authorizes pattern row ↔ row ∈ (compile pattern).rows := by
  constructor
  · intro source
    cases source with
    | finish => simp [compile]
    | inside source => exact List.mem_cons_of_mem _ (source_emitted source)
  · intro member
    simp only [compile, List.mem_cons] at member
    rcases member with same | member
    · subst row; exact .finish
    · exact .inside (emitted_source pattern .ending .root row member)

theorem source_operation_unique (pattern : Pattern) (first second : Instruction)
    (one : Authorizes pattern first) (two : Authorizes pattern second)
    (same : first.address = second.address) : first = second :=
  List.inj_on_of_nodup_map (Graph.compile_addresses_nodup pattern)
    ((authorizes_iff_compiled pattern first).mp one) ((authorizes_iff_compiled pattern second).mp two) same

theorem relocated_source_authorized (pattern : Pattern)
    (index : Fin (compile pattern).rows.length) : Authorizes pattern (compile pattern).rows[index.val] :=
  (authorizes_iff_compiled pattern _).mpr (List.getElem_mem index.isLt)

theorem authored_outputs_admitted {layout : RegexSourceProjection.State}
    {pattern : RegexDependentProjection.SourcePattern} {target : Pattern}
    (resolved : RegexDependentProjection.Resolves layout pattern target) :
    ∃ input, RegexDependentAuthored.encode layout pattern = some input ∧
      ∀ result, DeterministicEquations.Applies RegexExtendedEquationExecution.program
        RegexExtendedEquationExecution.host "re:compile-authored" [input] result ↔
        result = RegexExtendedAccumulatorExecution.code (Graph.checkedCompile target).program :=
  RegexDependentAuthored.resolved_authored_exact resolved

namespace Controls

private def nested : Pattern := .seq (.look .ahead (.capture 1 (.literal 97)))
  (.look .reverseBehind (.backref 1 .exact))

theorem nested_observation_targets_are_owned (row : Instruction)
    (member : row ∈ (compile nested).rows) (target : Address) (edge : target ∈ Graph.targets row) :
    target ∈ Graph.addresses (compile nested) := Graph.compile_targets_owned nested row member target edge

theorem repeated_equal_subpatterns_keep_distinct_occurrences :
    Address.left .root ≠ Address.right .root ∧
    ((compile (.alt (.literal 97) (.literal 97))).rows.map Instruction.address).Nodup :=
  ⟨by decide, Graph.compile_addresses_nodup _⟩

theorem invented_outer_failure_is_not_authorized :
    ¬ Authorizes nested (.fail .ending) := by
  rw [authorizes_iff_compiled]
  simp [nested, compile, emit]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics
