import Mettapedia.OSLF.Syntax.DeclaredBindingSource
import Mettapedia.OSLF.Syntax.DeclaredBindingProvenance
import Mettapedia.OSLF.Syntax.SignatureMorphismReadback

/-!
# Scope and transport controls for the authored binding interpretation

The named grammar is an explicit mathematical source fragment, not a claim
about the runtime reader. Its resolution constructs the previously admitted
intrinsic program. The capturing raw fold intentionally fails the transport
law and therefore is not supplied as a substitution-compatible model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Controls

open FreeBindingTerms

/-- The derived interpretation is essential: neither target constructor has
the unbound unary arity of the transparent `result` operation. -/
theorem no_strict_signature_morphism : ¬ Nonempty (SigMor sig Target.sig) := by
  rintro ⟨strict⟩
  have arity := strict.carriesArity Op.result
  cases actual : strict.opMap Op.result with
  | app =>
      rw [actual] at arity
      simp [sig, Target.sig, LambdaContextualRung.sig, mapArities, mapArity] at arity
  | lam =>
      rw [actual] at arity
      simp [sig, Target.sig, LambdaContextualRung.sig, mapArities, mapArity] at arity


def nested : Program [.term] :=
  .lambda (.lambda (.result (LambdaContextualRung.appT (.var (.succ .zero))
    (LambdaContextualRung.appT (.var .zero) (.var (.succ (.succ .zero)))))))

def identity {Γ : Ctx Target.sig} : Term Target.sig Γ .term :=
  LambdaContextualRung.lamT (.var .zero)

def supplyIdentity : Sub Target.sig [.term] []
  | _, .zero => identity

def closedIntoOpen : Ren Target.sig [] [.term] := fun _ impossible => nomatch impossible

theorem nested_binders_and_live_dependency :
    lower nested.source = LambdaContextualRung.lamT (LambdaContextualRung.lamT
      (LambdaContextualRung.appT (.var (.succ .zero))
        (LambdaContextualRung.appT (.var .zero) (.var (.succ (.succ .zero)))))) := rfl

theorem substitution_keeps_nested_locals :
    lower (nested.substitute supplyIdentity).source =
      LambdaContextualRung.lamT (LambdaContextualRung.lamT
        (LambdaContextualRung.appT (.var (.succ .zero))
          (LambdaContextualRung.appT (.var .zero) identity))) := rfl

theorem free_dependency_is_observable :
    lower nested.source ≠ lower ((nested.substitute supplyIdentity).renamed closedIntoOpen).source := by
  intro equal
  have sizes := congrArg termSize equal
  change 7 = 8 at sizes
  omega

/-- Deliberately wrong: an extra scope captures the value's ambient names.
The independently scoped body keeps its own parameter through the lift. -/
def capturingOperation {Γ : Ctx sig} {s : sig.Srt} (op : sig.Op s)
    (args : FamilyArgs sig (Term Target.sig) (sig.arity op) Γ) : Term Target.sig Γ s :=
  match op with
  | .baseApp => operation (BindingCloneAlgebra.terms Target.sig) .baseApp args
  | .baseLam => operation (BindingCloneAlgebra.terms Target.sig) .baseLam args
  | .lambda => operation (BindingCloneAlgebra.terms Target.sig) .lambda args
  | .result => operation (BindingCloneAlgebra.terms Target.sig) .result args
  | .whereBinding => LambdaContextualRung.lamT
      (LambdaContextualRung.appT
        (LambdaContextualRung.lamT (rename
          (liftRen (Srt := LambdaContextualRung.Srt)
            (fun _ x => Var.succ x) [LambdaContextualRung.Srt.term])
          (argumentHead (argumentTail args))))
        (bind (fun sort _ => match sort with | .term => .var .zero) (argumentHead args)))

def capturingRawModel : FreeBindingTerms.Algebra sig where
  Carrier := Term Target.sig
  injectVar := fun x => Term.var (S := Target.sig) x
  operation := capturingOperation

def capturingLower {Γ : Ctx sig} {s : sig.Srt} (term : Term sig Γ s) : Term Target.sig Γ s :=
  fold capturingRawModel term

def whereOpen : Term sig [.term] .term := whereBinding (.var .zero) (.var .zero)

def sourceSupplyIdentity : Sub sig [.term] []
  | _, .zero => embed identity

/-- This actual alternative fold fails the general substitution square;
the negative is not merely failure to construct an interface instance. -/
theorem capturing_interpretation_breaks_substitution :
    capturingLower (bind sourceSupplyIdentity whereOpen) ≠
      bind (fun s x => capturingLower (sourceSupplyIdentity s x)) (capturingLower whereOpen) := by
  intro equal
  have sizes := congrArg termSize equal
  change 6 = 5 at sizes
  omega

theorem result_erasure_changes_source :
    result (Term.var (S := sig)
      (.zero : Var [LambdaContextualRung.Srt.term] LambdaContextualRung.Srt.term)) ≠ .var .zero := by
  intro equal
  cases equal

theorem result_erasure_keeps_target :
    lower (result (Term.var (S := sig)
      (.zero : Var [LambdaContextualRung.Srt.term] LambdaContextualRung.Srt.term))) = lower (.var .zero) :=
  lower_result _

theorem where_advances_and_preserves_denotation :
    Step whereOpen (.var .zero) ∧
      LambdaContextualRung.Step [.term] (lower whereOpen) (.var .zero) ∧
      lower whereOpen ≠ (.var .zero : Term Target.sig [.term] .term) ∧
      BetaModel.denote whereOpen = BetaModel.denote (.var .zero) := by
  refine ⟨Step.whereBeta _ _, where_lower_step _ _, ?_, BetaModel.denote_where_beta _ _⟩
  intro equal
  cases equal

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Controls

namespace Mettapedia.OSLF.Binding.SignatureSortReindexingControls

inductive Operator : Option Bool → Type where
  | useName : Operator (some false)
  | binder : Operator (some false)
  | undeclared : Operator (some false)

def source : Signature where
  Srt := Option Bool
  Op := Operator
  arity
    | .useName => [([], some true)]
    | .binder => [([some true], some false)]
    | .undeclared => [([none], some false)]

def selected : Signature := source.reindexSorts some

theorem decodeSound (sort : Option Bool) (index : Bool) (decoded : sort = some index) :
    some index = sort := decoded.symm

def nameUse : selected.Op false := ⟨.useName, [([], true)], rfl⟩
def nameBinder : selected.Op false := ⟨.binder, [([true], false)], rfl⟩

def localTerm : Term selected [] false :=
  .op nameBinder (.cons (.op nameUse (.cons (.var .zero) .nil)) .nil)

def original : Term source [] (some false) :=
  .op .binder (.cons (.op .useName (.cons (.var .zero) .nil)) .nil)

theorem literal_scope_retained : (source.reindexProjection some).onTerm localTerm = original := rfl

theorem actual_binding_operator_lifted :
    source.reindexOperator? some id decodeSound .binder = some nameBinder := rfl

theorem unavailable_binding_sort_refused :
    source.reindexOperator? some id decodeSound .undeclared = none := rfl

theorem constructor_identity_retained : nameUse ≠ nameBinder := by
  intro same
  have different := congrArg ReindexedOperator.original same
  cases different

#guard (source.reindexOperator? some id decodeSound .binder).isSome
#guard (source.reindexOperator? some id decodeSound .useName).isSome
#guard (source.reindexOperator? some id decodeSound .undeclared).isNone
#guard (SortArityDecoder.decodeArity id ([some true], some false)).isSome
#guard (SortArityDecoder.decodeArity id ([none], some false)).isNone
#guard (SortArityDecoder.decodeArity id ([some true], none)).isNone

local instance : DecidableEq (source.reindexSorts (some : Bool → Option Bool)).Srt :=
  inferInstanceAs (DecidableEq Bool)

abbrev projection := source.reindexProjection some

def reader : projection.OperatorReader := source.reindexOperatorReader some id decodeSound

theorem binder_reader_roundtrip :
    source.reindexTerm? some id decodeSound (context := []) (sort := false) original = some localTerm := rfl

def unsupportedBinder : Term source [some true] (some false) :=
  .op .undeclared (.cons (.op .useName (.cons (.var (.succ .zero)) .nil)) .nil)

theorem term_with_undeclared_binding_sort_refused :
    source.reindexTerm? some id decodeSound (context := [true]) unsupportedBinder = none := rfl

def nestedOuter : Term source [] (some false) :=
  .op .binder (.cons (.op .binder
    (.cons (.op .useName (.cons (.var (.succ .zero)) .nil)) .nil)) .nil)

def nestedInner : Term source [] (some false) :=
  .op .binder (.cons (.op .binder
    (.cons (.op .useName (.cons (.var .zero) .nil)) .nil)) .nil)

theorem distinct_binding_positions_retained :
    source.reindexTerm? some id decodeSound (context := []) (sort := false) nestedOuter ≠
      source.reindexTerm? some id decodeSound (context := []) (sort := false) nestedInner := by
  intro same
  cases same

def schemaMetas : List (MetaArity selected) := [([true], false), ([], true)]

def dependentSchema : Term (withMetas selected schemaMetas) [true] false :=
  .op (.inl nameBinder) (.cons
    (.op (.inr (.mk ⟨0, by decide⟩)) (.cons (.var (.succ .zero)) .nil)) .nil)

def schemaReader := reader.withMetas projection schemaMetas

theorem dependent_schema_roundtrip :
    SigMor.OperatorReader.readTerm (projection.withMetas schemaMetas) schemaReader
      ((projection.withMetas schemaMetas).onTerm dependentSchema) = some dependentSchema := by
  exact SigMor.OperatorReader.readWithMetas_roundtrip projection reader
    (source.reindexOperator?_roundtrip some id decodeSound (fun _ => rfl)) schemaMetas dependentSchema

#guard (source.reindexTerm? some id decodeSound (context := []) (sort := false) original).isSome
#guard (source.reindexTerm? some id decodeSound (context := [true]) unsupportedBinder).isNone
#guard (source.reindexTerm? some id decodeSound (context := []) (sort := false) nestedOuter).isSome
#guard (source.reindexTerm? some id decodeSound (context := []) (sort := false) nestedInner).isSome
#guard (SigMor.OperatorReader.readTermWithFuel projection reader 0 (context := []) (sort := false) original).isNone
#guard (SigMor.OperatorReader.readTermWithFuel projection reader 1 (context := []) (sort := false) original).isNone
#guard (SigMor.OperatorReader.readTermWithFuel projection reader 32 (context := []) (sort := false) original).isSome
#guard (SigMor.OperatorReader.readTerm (projection.withMetas schemaMetas) schemaReader
  ((projection.withMetas schemaMetas).onTerm dependentSchema)).isSome


end Mettapedia.OSLF.Binding.SignatureSortReindexingControls


namespace Mettapedia.OSLF.Binding.SignatureReaderBoundaryControls

open RedexPositionWitness

def collapsingReader : SortCollapse.collapse.OperatorReader where
  read {sort} operator := match sort, operator with
    | .pr, .out => some .out
    | .pr, .aName => none
    | .nm, .out => none
    | .nm, .aName => some .aName
  projects original selected found := by
    cases selected with
    | out =>
        cases original with
        | out => rfl
        | aName => cases found
    | aName =>
        cases original with
        | out => cases found
        | aName => rfl

def collapsedWrongSort : Term SortCollapse.osig [SortCollapse.OneSrt.all] .all := .var .zero

theorem collapsing_sorts_does_not_give_source_coverage :
    SigMor.OperatorReader.readTerm SortCollapse.collapse collapsingReader
      (context := [Srt.nm]) (sort := Srt.pr) collapsedWrongSort = none := rfl

theorem collapsing_sorts_keeps_an_actual_image_variable :
    SigMor.OperatorReader.readTerm SortCollapse.collapse collapsingReader
      (context := [Srt.nm]) (sort := Srt.nm) collapsedWrongSort = some (.var .zero) := rfl

def mergingReader : ConstantMerge.merge.OperatorReader where
  read _ := some .a
  projects original selected found := by
    cases original
    cases Option.some.inj found
    rfl

theorem merged_constructor_does_not_roundtrip_second_source :
    SigMor.OperatorReader.readTerm ConstantMerge.merge mergingReader
      (ConstantMerge.merge.onTerm ConstantMerge.tb) = some ConstantMerge.ta := rfl

#guard (SigMor.OperatorReader.readTerm SortCollapse.collapse collapsingReader
  (context := [Srt.nm]) (sort := Srt.pr) collapsedWrongSort).isNone
#guard (SigMor.OperatorReader.readTerm SortCollapse.collapse collapsingReader
  (context := [Srt.nm]) (sort := Srt.nm) collapsedWrongSort).isSome
#guard (SigMor.OperatorReader.readTerm ConstantMerge.merge mergingReader
  (ConstantMerge.merge.onTerm ConstantMerge.tb)).map ConstantMerge.isA == some true

end Mettapedia.OSLF.Binding.SignatureReaderBoundaryControls
