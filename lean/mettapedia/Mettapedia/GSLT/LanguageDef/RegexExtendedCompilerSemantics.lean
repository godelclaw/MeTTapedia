import Mettapedia.GSLT.LanguageDef.RegexLookaroundObservation
import Mettapedia.GSLT.LanguageDef.RegexSelectionLowering

/-!
# Structural occurrences for the context-dependent regex compiler

Local source operations and their enclosing source frames are defined without
examining compiled rows. Emission has a two-sided occurrence theorem. Assertion
body addresses carry one more observation level than their caller; ordinary
structural addresses do not create an observation level.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics

open RegexDependentObservation (Comparison LookKind)
abbrev ScalarRange := RegexSelection.ScalarRange

inductive Address where
  | root | ending
  | left (parent : Address) | right (parent : Address)
  | body (parent : Address) | loop (parent : Address) | close (parent : Address)
  | lookBody (parent : Address) | lookEnd (parent : Address)
  deriving DecidableEq, Repr

def Address.observationDepth : Address → Nat
  | .root | .ending => 0
  | .left parent | .right parent | .body parent | .loop parent | .close parent => parent.observationDepth
  | .lookBody parent | .lookEnd parent => parent.observationDepth + 1

inductive Pattern where
  | zero | epsilon | any
  | literal (scalar : Nat) | class_ (ranges : List ScalarRange) | assertion (name : String)
  | seq (first second : Pattern) | alt (first second : Pattern)
  | optional (body : Pattern) (greedy : Bool)
  | star (body : Pattern) (greedy : Bool) | plus (body : Pattern) (greedy : Bool)
  | capture (group : Nat) (body : Pattern)
  | backref (group : Nat) (comparison : Comparison)
  | look (kind : LookKind) (body : Pattern)
  deriving DecidableEq, Repr

/-- Reversal changes consuming order, not source group identities, written
alternative priority, or the independently declared direction of a look. -/
def Pattern.reverse : Pattern → Pattern
  | .zero => .zero | .epsilon => .epsilon | .any => .any
  | .literal scalar => .literal scalar
  | .class_ ranges => .class_ ranges
  | .assertion name => .assertion name
  | .seq first second => .seq second.reverse first.reverse
  | .alt first second => .alt first.reverse second.reverse
  | .optional body greedy => .optional body.reverse greedy
  | .star body greedy => .star body.reverse greedy
  | .plus body greedy => .plus body.reverse greedy
  | .capture group body => .capture group body.reverse
  | .backref group comparison => .backref group comparison
  | .look kind body => .look kind body

@[simp] theorem reverse_reverse (pattern : Pattern) : pattern.reverse.reverse = pattern := by
  induction pattern <;> simp_all [Pattern.reverse]

inductive Instruction where
  | fail (origin : Address) | accept (origin : Address)
  | jump (origin next : Address)
  | scalar (origin : Address) (scalar : Nat) (next : Address)
  | any (origin next : Address)
  | class_ (origin : Address) (ranges : List ScalarRange) (next : Address)
  | assertion (origin : Address) (name : String) (next : Address)
  | split (origin first second : Address)
  | save (origin : Address) (group : Nat) (opening : Bool) (next : Address)
  | backref (origin : Address) (group : Nat) (comparison : Comparison) (next : Address)
  | look (origin entry : Address) (kind : LookKind) (next : Address)
  deriving DecidableEq, Repr

def choice (origin body continuation : Address) (greedy : Bool) : Instruction :=
  if greedy then .split origin body continuation else .split origin continuation body

def emit : Pattern → Address → Address → List Instruction
  | .zero, _, origin => [.fail origin]
  | .epsilon, continuation, origin => [.jump origin continuation]
  | .literal scalar, continuation, origin => [.scalar origin scalar continuation]
  | .any, continuation, origin => [.any origin continuation]
  | .class_ ranges, continuation, origin => [.class_ origin ranges continuation]
  | .assertion name, continuation, origin => [.assertion origin name continuation]
  | .seq first second, continuation, origin =>
      .jump origin (.left origin) ::
        (emit first (.right origin) (.left origin) ++ emit second continuation (.right origin))
  | .alt first second, continuation, origin =>
      .split origin (.left origin) (.right origin) ::
        (emit first continuation (.left origin) ++ emit second continuation (.right origin))
  | .optional body greedy, continuation, origin =>
      choice origin (.body origin) continuation greedy :: emit body continuation (.body origin)
  | .star body greedy, continuation, origin =>
      choice origin (.body origin) continuation greedy ::
        choice (.loop origin) (.body origin) continuation greedy :: emit body (.loop origin) (.body origin)
  | .plus body greedy, continuation, origin =>
      .jump origin (.body origin) ::
        choice (.loop origin) (.body origin) continuation greedy :: emit body (.loop origin) (.body origin)
  | .capture group body, continuation, origin =>
      .save origin group true (.body origin) ::
        .save (.close origin) group false continuation :: emit body (.close origin) (.body origin)
  | .backref group comparison, continuation, origin => [.backref origin group comparison continuation]
  | .look kind body, continuation, origin =>
      .look origin (.lookBody origin) kind continuation ::
        .accept (.lookEnd origin) :: emit body (.lookEnd origin) (.lookBody origin)

def emitAcc : Pattern → Address → Address → List Instruction → List Instruction
  | .zero, _, origin, tail => .fail origin :: tail
  | .epsilon, continuation, origin, tail => .jump origin continuation :: tail
  | .literal scalar, continuation, origin, tail => .scalar origin scalar continuation :: tail
  | .any, continuation, origin, tail => .any origin continuation :: tail
  | .class_ ranges, continuation, origin, tail => .class_ origin ranges continuation :: tail
  | .assertion name, continuation, origin, tail => .assertion origin name continuation :: tail
  | .seq first second, continuation, origin, tail =>
      .jump origin (.left origin) ::
        emitAcc first (.right origin) (.left origin) (emitAcc second continuation (.right origin) tail)
  | .alt first second, continuation, origin, tail =>
      .split origin (.left origin) (.right origin) ::
        emitAcc first continuation (.left origin) (emitAcc second continuation (.right origin) tail)
  | .optional body greedy, continuation, origin, tail =>
      choice origin (.body origin) continuation greedy :: emitAcc body continuation (.body origin) tail
  | .star body greedy, continuation, origin, tail =>
      choice origin (.body origin) continuation greedy ::
        choice (.loop origin) (.body origin) continuation greedy :: emitAcc body (.loop origin) (.body origin) tail
  | .plus body greedy, continuation, origin, tail =>
      .jump origin (.body origin) ::
        choice (.loop origin) (.body origin) continuation greedy :: emitAcc body (.loop origin) (.body origin) tail
  | .capture group body, continuation, origin, tail =>
      .save origin group true (.body origin) ::
        .save (.close origin) group false continuation :: emitAcc body (.close origin) (.body origin) tail
  | .backref group comparison, continuation, origin, tail => .backref origin group comparison continuation :: tail
  | .look kind body, continuation, origin, tail =>
      .look origin (.lookBody origin) kind continuation ::
        .accept (.lookEnd origin) :: emitAcc body (.lookEnd origin) (.lookBody origin) tail

theorem emitAcc_eq (pattern : Pattern) (continuation origin : Address) (tail : List Instruction) :
    emitAcc pattern continuation origin tail = emit pattern continuation origin ++ tail := by
  induction pattern generalizing continuation origin tail <;>
    simp_all [emitAcc, emit, List.append_assoc]

structure Program where
  entry : Address
  rows : List Instruction
  deriving DecidableEq, Repr

def compile (pattern : Pattern) : Program := ⟨.root, .accept .ending :: emit pattern .ending .root⟩

def compileAcc (pattern : Pattern) : Program := ⟨.root, .accept .ending :: emitAcc pattern .ending .root []⟩

theorem compileAcc_eq (pattern : Pattern) : compileAcc pattern = compile pattern := by
  simp [compileAcc, compile, emitAcc_eq]

/-- A source constructor's own control operations. Enclosing contexts are
accounted for separately by At, rather than hidden in a compiled lookup. -/
inductive Local : Pattern → Address → Address → Instruction → Prop where
  | zero (k origin) : Local .zero k origin (.fail origin)
  | epsilon (k origin) : Local .epsilon k origin (.jump origin k)
  | literal (scalar k origin) : Local (.literal scalar) k origin (.scalar origin scalar k)
  | any (k origin) : Local .any k origin (.any origin k)
  | class_ (ranges k origin) : Local (.class_ ranges) k origin (.class_ origin ranges k)
  | assertion (name k origin) : Local (.assertion name) k origin (.assertion origin name k)
  | seq (first second k origin) : Local (.seq first second) k origin (.jump origin (.left origin))
  | alt (first second k origin) : Local (.alt first second) k origin (.split origin (.left origin) (.right origin))
  | optional (body greedy k origin) : Local (.optional body greedy) k origin (choice origin (.body origin) k greedy)
  | starEntry (body greedy k origin) : Local (.star body greedy) k origin (choice origin (.body origin) k greedy)
  | starLoop (body greedy k origin) : Local (.star body greedy) k origin (choice (.loop origin) (.body origin) k greedy)
  | plusEntry (body greedy k origin) : Local (.plus body greedy) k origin (.jump origin (.body origin))
  | plusLoop (body greedy k origin) : Local (.plus body greedy) k origin (choice (.loop origin) (.body origin) k greedy)
  | captureOpen (group body k origin) : Local (.capture group body) k origin (.save origin group true (.body origin))
  | captureClose (group body k origin) : Local (.capture group body) k origin (.save (.close origin) group false k)
  | backref (group comparison k origin) : Local (.backref group comparison) k origin (.backref origin group comparison k)
  | look (kind body k origin) : Local (.look kind body) k origin (.look origin (.lookBody origin) kind k)
  | lookDone (kind body k origin) : Local (.look kind body) k origin (.accept (.lookEnd origin))

inductive At : Pattern → Address → Address → Instruction → Prop where
  | local {pattern k origin row} : Local pattern k origin row → At pattern k origin row
  | seqLeft {first second k origin row} : At first (.right origin) (.left origin) row → At (.seq first second) k origin row
  | seqRight {first second k origin row} : At second k (.right origin) row → At (.seq first second) k origin row
  | altLeft {first second k origin row} : At first k (.left origin) row → At (.alt first second) k origin row
  | altRight {first second k origin row} : At second k (.right origin) row → At (.alt first second) k origin row
  | optional {body greedy k origin row} : At body k (.body origin) row → At (.optional body greedy) k origin row
  | star {body greedy k origin row} : At body (.loop origin) (.body origin) row → At (.star body greedy) k origin row
  | plus {body greedy k origin row} : At body (.loop origin) (.body origin) row → At (.plus body greedy) k origin row
  | capture {group body k origin row} : At body (.close origin) (.body origin) row → At (.capture group body) k origin row
  | look {kind body k origin row} : At body (.lookEnd origin) (.lookBody origin) row → At (.look kind body) k origin row

theorem local_emitted {pattern : Pattern} {k origin : Address} {row : Instruction}
    (source : Local pattern k origin row) : row ∈ emit pattern k origin := by
  cases source <;> simp [emit]

theorem source_emitted {pattern : Pattern} {k origin : Address} {row : Instruction}
    (source : At pattern k origin row) : row ∈ emit pattern k origin := by
  induction source with
  | «local» source => exact local_emitted source
  | seqLeft _ ih | seqRight _ ih | altLeft _ ih | altRight _ ih => simp [emit, ih]
  | optional _ ih | star _ ih | plus _ ih | capture _ ih | look _ ih => simp [emit, ih]

theorem emitted_source (pattern : Pattern) (k origin : Address) (row : Instruction)
    (member : row ∈ emit pattern k origin) : At pattern k origin row := by
  induction pattern generalizing k origin row with
  | zero | epsilon | any | literal _ | class_ _ | assertion _ | backref _ _ =>
      simp only [emit, List.mem_singleton] at member
      subst row
      apply At.local
      first | exact Local.zero _ _ | exact Local.epsilon _ _ | exact Local.any _ _ |
        exact Local.literal _ _ _ | exact Local.class_ _ _ _ | exact Local.assertion _ _ _ |
        exact Local.backref _ _ _ _
  | seq first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst row; exact .local (.seq _ _ _ _)
      · exact .seqLeft (ihFirst _ _ _ member)
      · exact .seqRight (ihSecond _ _ _ member)
  | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst row; exact .local (.alt _ _ _ _)
      · exact .altLeft (ihFirst _ _ _ member)
      · exact .altRight (ihSecond _ _ _ member)
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst row; exact .local (.optional _ _ _ _)
      · exact .optional (ih _ _ _ member)
  | star body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; exact .local (.starEntry _ _ _ _)
      · subst row; exact .local (.starLoop _ _ _ _)
      · exact .star (ih _ _ _ member)
  | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; exact .local (.plusEntry _ _ _ _)
      · subst row; exact .local (.plusLoop _ _ _ _)
      · exact .plus (ih _ _ _ member)
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; exact .local (.captureOpen _ _ _ _)
      · subst row; exact .local (.captureClose _ _ _ _)
      · exact .capture (ih _ _ _ member)
  | look kind body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; exact .local (.look _ _ _ _)
      · subst row; exact .local (.lookDone _ _ _ _)
      · exact .look (ih _ _ _ member)

theorem source_operation_iff_emitted (pattern : Pattern) (k origin : Address) (row : Instruction) :
    At pattern k origin row ↔ row ∈ emit pattern k origin :=
  ⟨source_emitted, emitted_source pattern k origin row⟩

def ordinaryTargets : Instruction → List Address
  | .fail _ | .accept _ => []
  | .split _ first second => [first, second]
  | .jump _ next | .scalar _ _ next | .any _ next | .class_ _ _ next |
    .assertion _ _ next | .save _ _ _ next | .backref _ _ _ next | .look _ _ _ next => [next]

def Instruction.address : Instruction → Address
  | .fail origin | .accept origin | .jump origin _ | .scalar origin _ _ | .any origin _ |
    .class_ origin _ _ | .assertion origin _ _ | .split origin _ _ | .save origin _ _ _ |
    .backref origin _ _ _ | .look origin _ _ _ => origin

theorem entry_depth (pattern : Pattern) (k origin : Address) (row : Instruction)
    (member : row ∈ emit pattern k origin) : origin.observationDepth ≤ row.address.observationDepth := by
  induction pattern generalizing k origin row with
  | zero | epsilon | any | literal _ | class_ _ | assertion _ | backref _ _ =>
      simp only [emit, List.mem_singleton] at member
      subst row
      simp [Instruction.address]
  | seq first second ihFirst ihSecond | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst row; simp [Instruction.address]
      · simpa only [Address.observationDepth] using ihFirst _ _ _ member
      · simpa only [Address.observationDepth] using ihSecond _ _ _ member
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst row; cases greedy <;> simp [choice, Instruction.address]
      · simpa only [Address.observationDepth] using ih _ _ _ member
  | star body greedy ih | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; cases greedy <;> simp [choice, Instruction.address]
      · subst row; cases greedy <;> simp [choice, Instruction.address, Address.observationDepth]
      · simpa only [Address.observationDepth] using ih _ _ _ member
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; simp [Instruction.address]
      · subst row; simp [Instruction.address, Address.observationDepth]
      · simpa only [Address.observationDepth] using ih _ _ _ member
  | look kind body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row; simp [Instruction.address]
      · subst row; simp [Instruction.address, Address.observationDepth]
      · have lower := ih _ _ _ member
        simp only [Address.observationDepth] at lower
        omega

theorem assertion_body_strict_depth (origin : Address) :
    origin.observationDepth < (Address.lookBody origin).observationDepth := by
  simp [Address.observationDepth]

theorem ordinary_target_same_depth (pattern : Pattern) (k origin : Address)
    (sameDepth : k.observationDepth = origin.observationDepth)
    (row : Instruction) (member : row ∈ emit pattern k origin)
    (target : Address) (edge : target ∈ ordinaryTargets row) :
    target.observationDepth = row.address.observationDepth := by
  induction pattern generalizing k origin row target with
  | zero | epsilon | any | literal _ | class_ _ | assertion _ | backref _ _ =>
      simp only [emit, List.mem_singleton] at member
      subst row
      simp_all [ordinaryTargets, Instruction.address]
  | seq first second ihFirst ihSecond | alt first second ihFirst ihSecond =>
      simp only [emit, List.mem_cons, List.mem_append] at member
      rcases member with same | member | member
      · subst row
        simp_all [ordinaryTargets, Instruction.address, Address.observationDepth]
        all_goals rcases edge with rfl | rfl <;> rfl
      · exact ihFirst _ _ (by simp [Address.observationDepth, sameDepth]) _ member _ edge
      · exact ihSecond _ _ (by simp [Address.observationDepth, sameDepth]) _ member _ edge
  | optional body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | member
      · subst row
        cases greedy <;> simp_all only [choice, Bool.false_eq_true, if_true, if_false,
          ordinaryTargets, Instruction.address, List.mem_cons, List.not_mem_nil, or_false]
        all_goals rcases edge with rfl | rfl <;> simp [Address.observationDepth, sameDepth]
      · exact ih _ _ (by simp [Address.observationDepth, sameDepth]) _ member _ edge
  | star body greedy ih | plus body greedy ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row
        cases greedy <;> simp_all only [choice, Bool.false_eq_true, if_true, if_false,
          ordinaryTargets, Instruction.address, List.mem_cons, List.not_mem_nil, or_false]
        all_goals rcases edge with rfl | rfl <;> simp [Address.observationDepth, sameDepth]
      · subst row
        cases greedy <;> simp_all only [choice, Bool.false_eq_true, if_true, if_false,
          ordinaryTargets, Instruction.address, List.mem_cons, List.not_mem_nil, or_false]
        all_goals rcases edge with rfl | rfl <;> simp [Address.observationDepth, sameDepth]
      · exact ih _ _ (by simp [Address.observationDepth]) _ member _ edge
  | capture group body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row
        simp_all [ordinaryTargets, Instruction.address, Address.observationDepth]
      · subst row
        simp_all [ordinaryTargets, Instruction.address, Address.observationDepth]
      · exact ih _ _ (by simp [Address.observationDepth]) _ member _ edge
  | look kind body ih =>
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | member
      · subst row
        simp_all [ordinaryTargets, Instruction.address]
      · subst row
        simp [ordinaryTargets] at edge
      · exact ih _ _ (by simp [Address.observationDepth]) _ member _ edge

theorem look_body_depth (pattern : Pattern) (k origin rowOrigin entry next : Address)
    (kind : LookKind) (member : Instruction.look rowOrigin entry kind next ∈ emit pattern k origin) :
    entry.observationDepth = rowOrigin.observationDepth + 1 := by
  have source := emitted_source pattern k origin _ member
  clear member
  generalize shape : Instruction.look rowOrigin entry kind next = row at source
  induction source with
  | «local» localSource =>
      cases localSource <;> simp_all [choice, Address.observationDepth]
      all_goals split_ifs at shape
  | seqLeft _ ih | seqRight _ ih | altLeft _ ih | altRight _ ih => exact ih shape
  | optional _ ih | star _ ih | plus _ ih | capture _ ih | look _ ih => exact ih shape

theorem assertion_rank_strict (maximum : Nat) (origin entry : Address)
    (bodyDepth : entry.observationDepth = origin.observationDepth + 1)
    (bounded : entry.observationDepth ≤ maximum) :
    maximum - entry.observationDepth < maximum - origin.observationDepth := by omega

namespace Controls

theorem reverse_changes_sequence_not_captures :
    (Pattern.seq (.capture 1 (.literal 97)) (.capture 2 (.literal 98))).reverse =
      .seq (.capture 2 (.literal 98)) (.capture 1 (.literal 97)) := rfl

theorem nested_assertion_keeps_own_direction :
    (Pattern.look .ahead (.seq (.literal 97) (.literal 98))).reverse =
      .look .ahead (.seq (.literal 97) (.literal 98)) := rfl

theorem negative_extra_row_not_authorized :
    ¬ At (.backref 1 .exact) .ending .root (.jump .root .ending) := by
  rw [source_operation_iff_emitted]
  simp [emit]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics
