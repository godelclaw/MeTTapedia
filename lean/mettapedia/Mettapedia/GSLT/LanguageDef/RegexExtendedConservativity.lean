import Mettapedia.GSLT.LanguageDef.RegexExtendedCompilerSemantics
import Mettapedia.GSLT.LanguageDef.RegexSelectionEquationExecution

/-!
# Exact preservation of regular compiled programs

The extension's source embedding preserves complete ordered instruction rows,
not just recognition. This observation concerns regular programs in isolation.
It does not identify capture-dependent pruning with point-only Pike pruning
inside arbitrary new assertion contexts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedConservativity

namespace Base
export RegexSelection (Pattern Address Instruction Boundary)
end Base

namespace Extended
export RegexExtendedCompilerSemantics (Pattern Address Instruction)
end Extended

def pattern : Base.Pattern → Extended.Pattern
  | .zero => .zero | .epsilon => .epsilon | .any => .any
  | .literal scalar => .literal scalar
  | .class_ ranges => .class_ ranges
  | .assertion name => .assertion name
  | .seq first second => .seq (pattern first) (pattern second)
  | .alt first second => .alt (pattern first) (pattern second)
  | .optional body greedy => .optional (pattern body) greedy
  | .star body greedy => .star (pattern body) greedy
  | .plus body greedy => .plus (pattern body) greedy
  | .capture group body => .capture group (pattern body)

def address : Base.Address → Extended.Address
  | .root => .root | .ending => .ending
  | .left parent => .left (address parent)
  | .right parent => .right (address parent)
  | .body parent => .body (address parent)
  | .loop parent => .loop (address parent)
  | .close parent => .close (address parent)

def instruction : Base.Instruction → Extended.Instruction
  | .fail origin => .fail (address origin)
  | .accept origin => .accept (address origin)
  | .jump origin next => .jump (address origin) (address next)
  | .scalar origin scalar next => .scalar (address origin) scalar (address next)
  | .any origin next => .any (address origin) (address next)
  | .class_ origin ranges next => .class_ (address origin) ranges (address next)
  | .assertion origin name next => .assertion (address origin) name (address next)
  | .split origin first second => .split (address origin) (address first) (address second)
  | .save origin group boundary next =>
      .save (address origin) group (boundary == .start) (address next)

theorem choice_exact (origin body continuation : Base.Address) (greedy : Bool) :
    instruction (RegexSelection.choice origin body continuation greedy) =
      RegexExtendedCompilerSemantics.choice (address origin) (address body) (address continuation) greedy := by
  cases greedy <;> rfl

theorem ordered_rows_exact (source : Base.Pattern) (continuation origin : Base.Address) :
    RegexExtendedCompilerSemantics.emit (pattern source) (address continuation) (address origin) =
      (RegexSelection.emit source continuation origin).map instruction := by
  induction source generalizing continuation origin with
  | zero | epsilon | any | literal _ | class_ _ | assertion _ => rfl
  | seq first second ihFirst ihSecond =>
      have first := ihFirst (.right origin) (.left origin)
      have second := ihSecond continuation (.right origin)
      simpa only [pattern, RegexExtendedCompilerSemantics.emit, RegexSelection.emit,
        List.map_cons, List.map_append, instruction, address] using
        congrArg (List.cons (.jump (address origin) (.left (address origin))))
        (congrArg₂ (fun (a b : List Extended.Instruction) => a ++ b) first second)
  | alt first second ihFirst ihSecond =>
      have first := ihFirst continuation (.left origin)
      have second := ihSecond continuation (.right origin)
      simpa only [pattern, RegexExtendedCompilerSemantics.emit, RegexSelection.emit,
        List.map_cons, List.map_append, instruction, address] using
        congrArg (List.cons (.split (address origin) (.left (address origin)) (.right (address origin))))
        (congrArg₂ (fun (a b : List Extended.Instruction) => a ++ b) first second)
  | optional body greedy ih =>
      have inside := ih continuation (.body origin)
      cases greedy <;> exact congrArg (List.cons _) inside
  | star body greedy ih =>
      have inside := ih (.loop origin) (.body origin)
      cases greedy <;> exact congrArg (fun rows => _ :: _ :: rows) inside
  | plus body greedy ih =>
      have inside := ih (.loop origin) (.body origin)
      cases greedy <;> exact congrArg (fun rows => _ :: _ :: rows) inside
  | capture group body ih =>
      exact congrArg (fun rows => _ :: _ :: rows) (ih (.close origin) (.body origin))

theorem graph_exact (source : Base.Pattern) :
    (RegexExtendedCompilerSemantics.compile (pattern source)).rows =
      (RegexSelection.compile source).rows.map instruction := by
  simpa only [RegexExtendedCompilerSemantics.compile, RegexSelection.compile, List.map_cons,
    instruction, address] using congrArg (List.cons (.accept .ending))
      (ordered_rows_exact source .ending .root)

theorem regular_addresses_have_no_observation_level (origin : Base.Address) :
    (address origin).observationDepth = 0 := by
  induction origin <;> simp_all [address, RegexExtendedCompilerSemantics.Address.observationDepth]

namespace Controls

theorem nullable_capture_rows_remain_exact :
    RegexExtendedCompilerSemantics.emit (pattern (.star (.capture 1 .epsilon) true)) .ending .root =
      (RegexSelection.emit (.star (.capture 1 .epsilon) true) .ending .root).map instruction :=
  ordered_rows_exact _ .ending .root

theorem ordered_alternatives_cannot_be_reversed :
    RegexExtendedCompilerSemantics.compile (pattern (.alt (.literal 97) (.literal 98))) ≠
      RegexExtendedCompilerSemantics.compile (pattern (.alt (.literal 98) (.literal 97))) := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.RegexExtendedConservativity
