import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
import Mettapedia.OSLF.MeTTaIL.GeneralEquationReverseBounds

/-!
# Whole-language finite carriers for typed occurrence execution

The finite universe is calculated from the actual authored snapshot, source
and provider rows. Every equation representative, including those reached
against an edge's orientation, belongs to that universe. Raw binder display
metadata is erased through the earned typed alpha presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

def Request.fromSnapshot (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) : Request :=
  ⟨compile snapshot permissions, bound, expected, source⟩

theorem Request.root_sorted (request : Request)
    (typed : HasType request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.source request.expected)
    (object : isObjectPattern request.source = true)
    (scopeSafe : request.source.isWellScopedAt request.bound.length = true) :
    OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root :=
  GeneralEquationCanonical.open_typed_erase typed object scopeSafe

theorem Request.root_in_universe (request : Request)
    (typed : HasType request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.source request.expected)
    (object : isObjectPattern request.source = true)
    (scopeSafe : request.source.isWellScopedAt request.bound.length = true) :
    request.root ∈ request.universe :=
  sourceUniverse_contains_source _ _ _ _ _ _ (request.root_sorted typed object scopeSafe)

theorem Request.start_unresolved (request : Request)
    (typed : OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root) :
    (start request).unresolved = request.plan.obligations.map Obligation.admission := by
  simp only [start, checkOpenPatternWellSorted_complete typed, ↓reduceIte]

theorem Request.start_pending (request : Request)
    (typed : OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root) : (start request).agenda ≠ [] := by
  simp only [start, checkOpenPatternWellSorted_complete typed, ↓reduceIte]
  exact List.cons_ne_nil _ _

theorem Request.start_incomplete (request : Request)
    (typed : OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root) : complete request (start request) = false :=
  pending_not_complete request (start request) (request.start_pending typed)

theorem representative_in_universe {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (accepted : (compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) (scopeSafe : source.isWellScopedAt bound.length = true)
    (representative : Representative (Request.fromSnapshot snapshot permissions bound expected source)) :
    representative.pattern ∈ (Request.fromSnapshot snapshot permissions bound expected source).universe := by
  have root := (Request.fromSnapshot snapshot permissions bound expected source).root_in_universe typed object scopeSafe
  have comparison := GeneralEquationReverseBounds.compiled_equivalence_universe_iff
    (root := source.eraseBinderMetadata)
    (Request.fromSnapshot snapshot permissions bound expected source).providerTerms
    accepted representative.justified.equivalent
  exact comparison.mp root

theorem every_equivalent_representative {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source representative : Pattern}
    (accepted : (compile snapshot permissions).complete = true)
    (typed : HasType snapshot.language snapshot.free bound source expected)
    (object : isObjectPattern source = true) (scopeSafe : source.isWellScopedAt bound.length = true)
    (equivalent : Relation.EqvGen (Equation (compile snapshot permissions) bound expected)
      source.eraseBinderMetadata representative) :
    representative ∈ (Request.fromSnapshot snapshot permissions bound expected source).universe := by
  have root := (Request.fromSnapshot snapshot permissions bound expected source).root_in_universe typed object scopeSafe
  exact (GeneralEquationReverseBounds.compiled_equivalence_universe_iff
    (root := source.eraseBinderMetadata)
    (Request.fromSnapshot snapshot permissions bound expected source).providerTerms accepted equivalent).mp root

theorem forward_edge_in_universe {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (accepted : (compile snapshot permissions).complete = true)
    (edge : Edge (Request.fromSnapshot snapshot permissions bound expected source))
    (within : edge.source ∈ (Request.fromSnapshot snapshot permissions bound expected source).universe) :
    edge.receipt.target ∈ (Request.fromSnapshot snapshot permissions bound expected source).universe :=
  GeneralEquationJobs.compiled_completion_universe_closed accepted edge.valid within

theorem reverse_edge_in_universe {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (accepted : (compile snapshot permissions).complete = true)
    (edge : Edge (Request.fromSnapshot snapshot permissions bound expected source))
    (within : edge.receipt.target ∈ (Request.fromSnapshot snapshot permissions bound expected source).universe) :
    edge.source ∈ (Request.fromSnapshot snapshot permissions bound expected source).universe :=
  GeneralEquationReverseBounds.compiled_reverse_universe_closed accepted edge.valid within

theorem universe_member_typed (request : Request) (pattern : Pattern) (within : pattern ∈ request.universe) :
    OpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free request.bound request.expected pattern :=
  (typedUniverse_sound _ _ _ _ _ _ _ _ within).2

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
