import Mettapedia.Algorithms.Compression.ScopedTemplates
import Mettapedia.OSLF.Syntax.BindingWireCodec

/-!
# Finite operator-table instance of the shared scoped wire

Rows retain names, result sorts, and every field's binder sorts. Their
positions, not name lookup or hashes, identify operators. Terms and arguments
are exactly the existing Binding.Term/Args and WireCodec constructions.
This is a finite signature instance, not another term or binding calculus.

The ordinary MeTTa instance uses Wire:Atom/Wire:Pair for WireCodec.Data,
base operator ordinals, and a zero/one-tagged base/parameter sum in schemas.
Public registration additionally checks its declared-sort inventory and
parameter-role metadata. These laws do not certify the host implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ScopedTemplateWire

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec

structure Declaration (Label : Type) where
  name : String
  result : Label
  slots : List (List Label × Label)
  deriving DecidableEq, Repr

variable {Label : Type}

abbrev signature (rows : List (Declaration Label)) : Signature where
  Srt := Label
  Op sort := {index : Fin rows.length // (rows.get index).result = sort}
  arity operator := (rows.get operator.val).slots

def operatorPosition (rows : List (Declaration Label)) :
    (Σ sort, (signature rows).Op sort) ≃ Fin rows.length where
  toFun value := value.2.val
  invFun index := ⟨(rows.get index).result, ⟨index, rfl⟩⟩
  left_inv := by
    rintro ⟨sort, index, same⟩
    cases same
    rfl
  right_inv _ := rfl

def operatorCodec (rows : List (Declaration Label)) :
    Codec (Σ sort, (signature rows).Op sort) :=
  (Codec.fin rows.length).ofEquiv (operatorPosition rows)

def schemaOperatorPut (rows : List (Declaration Label)) (metas : List (MetaArity (signature rows))) :
    (Σ sort, (withMetas (signature rows) metas).Op sort) → Data
  | ⟨_, .inl operator⟩ => .pair (.atom 0) ((operatorCodec rows).put ⟨_, operator⟩)
  | ⟨_, .inr (.mk index)⟩ => .pair (.atom 1) ((Codec.fin metas.length).put index)

def schemaOperatorGet (rows : List (Declaration Label)) (metas : List (MetaArity (signature rows))) :
    Data → Option (Σ sort, (withMetas (signature rows) metas).Op sort)
  | .pair (.atom 0) wire => do
      let ⟨sort, operator⟩ ← (operatorCodec rows).get wire
      pure ⟨sort, .inl operator⟩
  | .pair (.atom 1) wire => do
      let index ← (Codec.fin metas.length).get wire
      pure ⟨(metas.get index).2, .inr (.mk index)⟩
  | _ => none

theorem schemaOperatorGet_put (rows : List (Declaration Label))
    (metas : List (MetaArity (signature rows))) :
    ∀ operator : Σ sort, (withMetas (signature rows) metas).Op sort,
      schemaOperatorGet rows metas (schemaOperatorPut rows metas operator) = some operator
  | ⟨_, .inl operator⟩ => by
      simp only [schemaOperatorPut, schemaOperatorGet, (operatorCodec rows).get_put]
      rfl
  | ⟨_, .inr (.mk index)⟩ => by
      simp only [schemaOperatorPut, schemaOperatorGet, (Codec.fin metas.length).get_put]
      rfl

def schemaOperatorCodec (rows : List (Declaration Label)) (metas : List (MetaArity (signature rows))) :
    Codec (Σ sort, (withMetas (signature rows) metas).Op sort) :=
  ⟨schemaOperatorPut rows metas, schemaOperatorGet rows metas, schemaOperatorGet_put rows metas⟩

instance operatorEquality (rows : List (Declaration Label)) :
    ∀ sort, DecidableEq ((signature rows).Op sort) :=
  fun sort => inferInstanceAs (DecidableEq {i : Fin rows.length // (rows.get i).result = sort})

instance schemaOperatorEquality (rows : List (Declaration Label))
    (metas : List (MetaArity (signature rows))) :
    ∀ sort, DecidableEq ((withMetas (signature rows) metas).Op sort) := by
  intro sort left right
  let encode := fun operator : (withMetas (signature rows) metas).Op sort =>
    (schemaOperatorCodec rows metas).put ⟨sort, operator⟩
  have injective : Function.Injective encode := by
    intro first second same
    have equal := (schemaOperatorCodec rows metas).put_injective same
    exact eq_of_heq (Sigma.mk.inj equal).2
  exact decidable_of_iff (encode left = encode right) injective.eq_iff

variable [DecidableEq Label]

def sourceCodec (rows : List (Declaration Label)) (context : List Label) (sort : Label) :
    Codec (Term (signature rows) context sort) :=
  WireCodec.term (operatorCodec rows) context sort

def schemaCodec (rows : List (Declaration Label)) (metas : List (MetaArity (signature rows)))
    (ordinary : List Label) (sort : Label) :
    Codec (Term (withMetas (signature rows) metas) ordinary sort) :=
  WireCodec.term (schemaOperatorCodec rows metas) ordinary sort

/-- Decode typed inputs, run the existing matcher, expand its actual partial
captures independently, then re-encode the reconstructed source. -/
def matchExpand (rows : List (Declaration Label)) (metas : List (MetaArity (signature rows)))
    (ordinary : List Label) (sort : Label) (patternWire sourceWire : Data) : Option Data := do
  let pattern ← (schemaCodec rows metas ordinary sort).get patternWire
  let source ← (sourceCodec rows [] sort).get sourceWire
  let captures ← smatchT emptyMAcc pattern source
  let restored ← ScopedTemplates.expandAtT [] captures pattern
  pure ((sourceCodec rows [] sort).put restored)

theorem matchExpand_reconstructs (rows : List (Declaration Label))
    (metas : List (MetaArity (signature rows))) (ordinary : List Label) (sort : Label)
    (pattern : Term (withMetas (signature rows) metas) ordinary sort)
    (source : Term (signature rows) [] sort)
    (captures : MAcc (signature rows) metas ordinary)
    (matched : smatchT emptyMAcc pattern source = some captures) :
    matchExpand rows metas ordinary sort
      ((schemaCodec rows metas ordinary sort).put pattern) ((sourceCodec rows [] sort).put source) =
      some ((sourceCodec rows [] sort).put source) := by
  simp only [matchExpand, (schemaCodec rows metas ordinary sort).get_put,
    Bind.bind, Option.bind, (sourceCodec rows [] sort).get_put, matched,
    ScopedTemplates.matched_expands pattern source captures matched]
  rfl

theorem source_wire_injective (rows : List (Declaration Label)) (context : List Label) (sort : Label) :
    Function.Injective (sourceCodec rows context sort).put :=
  (sourceCodec rows context sort).put_injective

theorem schema_wire_injective (rows : List (Declaration Label)) (metas : List (MetaArity (signature rows)))
    (ordinary : List Label) (sort : Label) :
    Function.Injective (schemaCodec rows metas ordinary sort).put :=
  (schemaCodec rows metas ordinary sort).put_injective

end Mettapedia.Algorithms.Compression.ScopedTemplateWire
