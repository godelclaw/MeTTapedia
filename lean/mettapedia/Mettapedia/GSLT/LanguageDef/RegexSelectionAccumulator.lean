import Mettapedia.GSLT.LanguageDef.RegexSelectionLowering

/-!+# Tail-threaded construction of the existing symbolic regex graph

Each source subtree emits its rows once in front of a supplied tail. No source
pattern is reassociated and no address, priority or capture write is changed.
The refinement theorem compares complete ordered instruction lists, not only
their recognized languages. Native copying and ownership costs are separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Accumulator

def emitAcc : Pattern → Address → Address → List Instruction → List Instruction
  | .zero, _, origin, tail => .fail origin :: tail
  | .epsilon, continuation, origin, tail => .jump origin continuation :: tail
  | .literal value, continuation, origin, tail => .scalar origin value continuation :: tail
  | .any, continuation, origin, tail => .any origin continuation :: tail
  | .class_ values, continuation, origin, tail => .class_ origin values continuation :: tail
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
      .save origin group .start (.body origin) ::
        .save (.close origin) group .finish continuation :: emitAcc body (.close origin) (.body origin) tail

theorem emitAcc_eq (pattern : Pattern) (continuation origin : Address) (tail : List Instruction) :
    emitAcc pattern continuation origin tail = emit pattern continuation origin ++ tail := by
  induction pattern generalizing continuation origin tail <;>
    simp_all [emitAcc, emit, List.append_assoc]

def compileAcc (pattern : Pattern) : Program :=
  ⟨.root, .accept .ending :: emitAcc pattern .ending .root []⟩

theorem compileAcc_eq (pattern : Pattern) : compileAcc pattern = compile pattern := by
  simp [compileAcc, compile, emitAcc_eq]

theorem emitAcc_length (pattern : Pattern) (continuation origin : Address) (tail : List Instruction) :
    (emitAcc pattern continuation origin tail).length = (emit pattern continuation origin).length + tail.length := by
  simp [emitAcc_eq]

namespace Controls

theorem left_nested_choices_keep_order :
    emitAcc (.alt (.alt (.literal 97) (.literal 98)) (.capture 1 (.literal 99))) .ending .root
      [.accept .ending] =
      emit (.alt (.alt (.literal 97) (.literal 98)) (.capture 1 (.literal 99))) .ending .root ++ [.accept .ending] :=
  emitAcc_eq _ _ _ _

theorem nullable_lazy_shape_keeps_both_choices :
    emitAcc (.star (.capture 2 .epsilon) false) .ending .root [] =
      [.split .root .ending (.body .root),
       .split (.loop .root) .ending (.body .root),
       .save (.body .root) 2 .start (.body (.body .root)),
       .save (.close (.body .root)) 2 .finish (.loop .root),
       .jump (.body (.body .root)) (.close (.body .root))] := rfl

theorem cannot_reverse_alternatives :
    compileAcc (.alt (.literal 97) (.literal 98)) ≠ compile (.alt (.literal 98) (.literal 97)) := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.RegexSelection.Accumulator
