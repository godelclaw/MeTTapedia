import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.SchemaJudgmentCode

/-!
# Interpreting actual source schema-table citations

A template retains its raw source row, parameter carriers, annotated readings
and HOL equality proof. An entry identifies that row at an actual table
address. The existing decoder checks permission and arity before an assignment
is interpreted. Receipts retain the decoded row and lookup evidence; the
resulting proof is constructed by substitution, not supplied by the caller.
Source judgment/context checking remains the separate admission gate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
namespace Roots
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

abbrev SourceRow (Head : Type) := (arity : Nat) × (Tm Head arity × Tm Head arity)

structure Template (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const))
    (decls : DeclName → Option (CTm Head 0)) where
  parameters : HOL.Ctx Base
  carrier : HOL.Ty Base
  rawLeft : Tm Head parameters.length
  rawRight : Tm Head parameters.length
  leftCode : HOL.Term Const parameters carrier
  rightCode : HOL.Term Const parameters carrier
  leftRead : Reads lex (elabLeft decls rawLeft) leftCode
  rightRead : Reads lex (elabRight decls rawLeft rawRight) rightCode
  proof : HOL.ProofSyntax Const (assumptions closed parameters) (.eq leftCode rightCode)

namespace Template
variable {lex : LexicalReading Head Base Const} {closed : List (HOL.ClosedFormula Const)}
  {decls : DeclName → Option (CTm Head 0)} (template : Template lex closed decls)

def sourceRow : SourceRow Head := ⟨template.parameters.length, template.rawLeft, template.rawRight⟩
def equality : EqualityAt lex closed template.parameters
    (elabLeft decls template.rawLeft) (elabRight decls template.rawLeft template.rawRight) template.carrier :=
  ⟨template.leftCode, template.rightCode, template.leftRead, template.rightRead, template.proof⟩
end Template

structure Entry (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const))
    (decls : DeclName → Option (CTm Head 0)) (table : AlgebraicSchema.SchemaTable Head)
    (address : Fin table.length) where
  template : Template lex closed decls
  binding : table.get address = template.sourceRow

variable {lex : LexicalReading Head Base Const} {closed : List (HOL.ClosedFormula Const)}
  {decls : DeclName → Option (CTm Head 0)} {table : AlgebraicSchema.SchemaTable Head}
  {enabled : Fin table.length → Bool} {Γ : HOL.Ctx Base}

def reindex {first second : SourceRow Head} (same : first = second) {n : Nat}
    (assignment : CSub Head first.1 n) : CSub Head second.1 n :=
  fun position => assignment (Fin.cast (congrArg Sigma.fst same).symm position)

theorem left_reindex {first second : SourceRow Head} (same : first = second) {n : Nat}
    (assignment : CSub Head first.1 n) :
    (elabLeft decls first.2.1).subst assignment = (elabLeft decls second.2.1).subst (reindex same assignment) := by
  cases same
  rfl

theorem right_reindex {first second : SourceRow Head} (same : first = second) {n : Nat}
    (assignment : CSub Head first.1 n) :
    (elabRight decls first.2.1 first.2.2).subst assignment =
      (elabRight decls second.2.1 second.2.2).subst (reindex same assignment) := by
  cases same
  rfl

abbrev Table (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const))
    (decls : DeclName → Option (CTm Head 0)) (table : AlgebraicSchema.SchemaTable Head) :=
  (address : Fin table.length) → Option (Entry lex closed decls table address)

structure Receipt (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (code : SchemaJudgmentCode.Code Head Γ.length) where
  parsed : SchemaJudgmentCode.Instance table enabled Γ.length
  decoded : SchemaJudgmentCode.decodeInstance table enabled code = some parsed
  entry : Entry lex closed decls table parsed.index
  known : entries parsed.index = some entry
  assignment : Reader.Assignment lex entry.template.parameters Γ (reindex entry.binding parsed.substitution)

namespace Receipt
variable {entries : Table lex closed decls table} {code : SchemaJudgmentCode.Code Head Γ.length}
  (receipt : Receipt entries enabled Γ code)

theorem source_decoded : SchemaJudgmentCode.decode decls table enabled code = some (receipt.parsed.result decls) := by
  rw [SchemaJudgmentCode.decode, receipt.decoded]
  rfl

theorem address_exact : receipt.parsed.index.val = code.row := by
  have decoded := receipt.decoded
  unfold SchemaJudgmentCode.decodeInstance at decoded
  split at decoded
  · dsimp only at decoded
    split at decoded
    · split at decoded
      · exact congrArg (fun parsed : SchemaJudgmentCode.Instance table enabled Γ.length => parsed.index.val)
          (Option.some.inj decoded).symm
      · cases decoded
    · cases decoded
  · cases decoded

def equality : EqualityAt lex closed Γ (receipt.parsed.result decls).left
    (receipt.parsed.result decls).right receipt.entry.template.carrier :=
  (receipt.entry.template.equality.substitute (reindex receipt.entry.binding receipt.parsed.substitution)
    receipt.assignment.val receipt.assignment.property).castEndpoints
      (left_reindex receipt.entry.binding receipt.parsed.substitution).symm
      (right_reindex receipt.entry.binding receipt.parsed.substitution).symm

theorem equality_free (free : receipt.entry.template.proof.FunctionExtensionalityFree) :
    receipt.equality.proof.FunctionExtensionalityFree :=
  EqualityAt.castEndpoints_free _ _ _
    (EqualityAt.substitute_free receipt.entry.template.equality
      (reindex receipt.entry.binding receipt.parsed.substitution)
      receipt.assignment.val receipt.assignment.property free)
end Receipt

variable [DecidableEq Base]

def readReceipt? (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (code : SchemaJudgmentCode.Code Head Γ.length) : Option (Receipt entries enabled Γ code) :=
  match decoded : SchemaJudgmentCode.decodeInstance table enabled code with
  | none => none
  | some parsed =>
      match known : entries parsed.index with
      | none => none
      | some entry =>
          (Reader.readAssignment? lex entry.template.parameters Γ (reindex entry.binding parsed.substitution)).map
            (fun assignment => ⟨parsed, decoded, entry, known, assignment⟩)

theorem readReceipt?_complete (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (code : SchemaJudgmentCode.Code Head Γ.length)
    (parsed : SchemaJudgmentCode.Instance table enabled Γ.length)
    (decoded : SchemaJudgmentCode.decodeInstance table enabled code = some parsed)
    (entry : Entry lex closed decls table parsed.index) (known : entries parsed.index = some entry)
    (assignment : Reader.Assignment lex entry.template.parameters Γ (reindex entry.binding parsed.substitution)) :
    readReceipt? entries enabled Γ code = some ⟨parsed, decoded, entry, known, assignment⟩ := by
  simp only [readReceipt?]
  split
  · rename_i refused
    cases refused.symm.trans decoded
  · rename_i received accepted
    cases Option.some.inj (accepted.symm.trans decoded)
    split
    · rename_i refused
      cases refused.symm.trans known
    · rename_i selected found
      cases Option.some.inj (found.symm.trans known)
      rw [Reader.readAssignment?_complete lex _ _ _ assignment.val assignment.property]
      rfl

omit [DecidableEq Base] in
theorem decodeInstance_encode (table : AlgebraicSchema.SchemaTable Head) (enabled : Fin table.length → Bool)
    {n : Nat} (address : Fin table.length) (permitted : enabled address = true)
    (substitution : CSub Head (table.get address).1 n) :
    SchemaJudgmentCode.decodeInstance table enabled (SchemaJudgmentCode.encode table address substitution) =
      some ⟨address, permitted, substitution⟩ := by
  simp [SchemaJudgmentCode.decodeInstance, SchemaJudgmentCode.encode, address.isLt, permitted]

structure Result (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) (code : SchemaJudgmentCode.Code Head Γ.length) where
  receipt : Receipt entries enabled Γ code
  leftExact : (receipt.parsed.result decls).left = source
  rightExact : (receipt.parsed.result decls).right = target

namespace Result
variable {entries : Table lex closed decls table} {source target : CTm Head Γ.length}
  {code : SchemaJudgmentCode.Code Head Γ.length} (result : Result entries enabled Γ source target code)

def equality : EqualityReading lex closed Γ source target :=
  ⟨result.receipt.entry.template.carrier,
    result.receipt.equality.castEndpoints result.leftExact result.rightExact⟩

omit [DecidableEq Base] in
theorem equality_free
    (free : ∀ address entry, entries address = some entry → entry.template.proof.FunctionExtensionalityFree) :
    result.equality.2.proof.FunctionExtensionalityFree :=
  EqualityAt.castEndpoints_free _ _ _ (result.receipt.equality_free (free _ _ result.receipt.known))
end Result

variable [DecidableEq Head]

def read? (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) (code : SchemaJudgmentCode.Code Head Γ.length) :
    Option (Result entries enabled Γ source target code) := do
  let receipt ← readReceipt? entries enabled Γ code
  if left : (receipt.parsed.result decls).left = source then
    if right : (receipt.parsed.result decls).right = target then
      some ⟨receipt, left, right⟩
    else none
  else none

theorem read?_complete (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (source target : CTm Head Γ.length) (code : SchemaJudgmentCode.Code Head Γ.length)
    (result : Result entries enabled Γ source target code)
    (received : readReceipt? entries enabled Γ code = some result.receipt) :
    read? entries enabled Γ source target code = some result := by
  rcases result with ⟨receipt, left, right⟩
  simp [read?, received, left, right]

omit [DecidableEq Head] in
theorem readReceipt?_refuses_decode (entries : Table lex closed decls table) (enabled : Fin table.length → Bool)
    (Γ : HOL.Ctx Base) (code : SchemaJudgmentCode.Code Head Γ.length)
    (refused : SchemaJudgmentCode.decodeInstance table enabled code = none) :
    readReceipt? entries enabled Γ code = none := by
  simp only [readReceipt?]
  split
  · rfl
  · rename_i parsed decoded
    cases decoded.symm.trans refused

#print axioms Receipt.address_exact
#print axioms Receipt.source_decoded
#print axioms Receipt.equality
#print axioms Result.equality_free
#print axioms read?
end Roots
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
