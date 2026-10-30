import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRoots
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateContexts
import Mettapedia.Logic.HOL.ProofSyntaxAppend

/-!
# Extending lexical readings and root-premise contexts

An extension preserves every successful lexical entry and supplies an
explicit target occurrence for each closed premise. Existing proof trees
are transported through that occurrence map. Schema addresses, raw rows,
endpoint codes and assignment values remain unchanged. Extending a table
alone does not interpret any previously absent row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

structure ReadingExtension (source target : LexicalReading Head Base Const)
    (sourceClosed targetClosed : List (HOL.ClosedFormula Const)) where
  lexical : LexicalMap source target (fun head => head)
  hypotheses : HOL.ProofSyntax.OccurrenceMap sourceClosed targetClosed

namespace ReadingExtension
variable {source target : LexicalReading Head Base Const}
  {sourceClosed targetClosed : List (HOL.ClosedFormula Const)}
  (extension : ReadingExtension source target sourceClosed targetClosed)

def atContext (context : HOL.Ctx Base) :
    HOL.ProofSyntax.OccurrenceMap (assumptions sourceClosed context) (assumptions targetClosed context) :=
  extension.hypotheses.map (HOL.weakenCtx context)

def proof {Γ : HOL.Ctx Base} {conclusion : HOL.Formula Const Γ}
    (original : HOL.ProofSyntax Const (assumptions sourceClosed Γ) conclusion) :
    HOL.ProofSyntax Const (assumptions targetClosed Γ) conclusion := original.mono (extension.atContext Γ)

theorem proof_free {Γ : HOL.Ctx Base} {conclusion : HOL.Formula Const Γ}
    (original : HOL.ProofSyntax Const (assumptions sourceClosed Γ) conclusion)
    (free : original.FunctionExtensionalityFree) : (extension.proof original).FunctionExtensionalityFree := by
  simpa only [proof, HOL.ProofSyntax.functionExtensionalityFree_mono] using free

theorem proof_nodeCount {Γ : HOL.Ctx Base} {conclusion : HOL.Formula Const Γ}
    (original : HOL.ProofSyntax Const (assumptions sourceClosed Γ) conclusion) :
    (extension.proof original).nodeCount = original.nodeCount := HOL.ProofSyntax.mono_nodeCount _ _

def equality {Γ : HOL.Ctx Base} {left right : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (original : EqualityAt source sourceClosed Γ left right carrier) :
    EqualityAt target targetClosed Γ left right carrier where
  left := original.left
  right := original.right
  leftRead := by simpa only [CTm.mapHead_id] using original.leftRead.mapLexical extension.lexical
  rightRead := by simpa only [CTm.mapHead_id] using original.rightRead.mapLexical extension.lexical
  proof := extension.proof original.proof

variable {decls : DeclName → Option (CTm Head 0)}

def template (original : Roots.Template source sourceClosed decls) : Roots.Template target targetClosed decls where
  parameters := original.parameters
  carrier := original.carrier
  rawLeft := original.rawLeft
  rawRight := original.rawRight
  leftCode := original.leftCode
  rightCode := original.rightCode
  leftRead := by simpa only [CTm.mapHead_id] using original.leftRead.mapLexical extension.lexical
  rightRead := by simpa only [CTm.mapHead_id] using original.rightRead.mapLexical extension.lexical
  proof := extension.proof original.proof

theorem template_free (original : Roots.Template source sourceClosed decls)
    (free : original.proof.FunctionExtensionalityFree) : (extension.template original).proof.FunctionExtensionalityFree :=
  extension.proof_free original.proof free

theorem template_nodeCount (original : Roots.Template source sourceClosed decls) :
    (extension.template original).proof.nodeCount = original.proof.nodeCount := extension.proof_nodeCount _

variable {table : AlgebraicSchema.SchemaTable Head}

def entry {address : Fin table.length} (original : Roots.Entry source sourceClosed decls table address) :
    Roots.Entry target targetClosed decls table address where
  template := extension.template original.template
  binding := original.binding

def entries (original : Roots.Table source sourceClosed decls table) : Roots.Table target targetClosed decls table :=
  fun address => (original address).map extension.entry

theorem entry_known (original : Roots.Table source sourceClosed decls table) (address : Fin table.length)
    (row : Roots.Entry source sourceClosed decls table address) (known : original address = some row) :
    extension.entries original address = some (extension.entry row) := by simp [entries, known]

theorem absent_iff (original : Roots.Table source sourceClosed decls table) (address : Fin table.length) :
    extension.entries original address = none ↔ original address = none := by simp [entries]

theorem entries_free (original : Roots.Table source sourceClosed decls table)
    (free : ∀ address row, original address = some row → row.template.proof.FunctionExtensionalityFree)
    (address : Fin table.length) (row : Roots.Entry target targetClosed decls table address)
    (known : extension.entries original address = some row) : row.template.proof.FunctionExtensionalityFree := by
  obtain ⟨prior, present, same⟩ := Option.map_eq_some_iff.mp known
  cases same
  exact extension.template_free prior.template (free address prior present)

variable {enabled : Fin table.length → Bool} {Γ : HOL.Ctx Base}
  {code : SchemaJudgmentCode.Code Head Γ.length}

def receipt {original : Roots.Table source sourceClosed decls table}
    (received : Roots.Receipt original enabled Γ code) :
    Roots.Receipt (extension.entries original) enabled Γ code where
  parsed := received.parsed
  decoded := received.decoded
  entry := extension.entry received.entry
  known := extension.entry_known original _ _ received.known
  assignment := ⟨received.assignment.val, by
    intro type index
    simpa only [CTm.mapHead_id] using (received.assignment.property index).mapLexical extension.lexical⟩

theorem receipt_address {original : Roots.Table source sourceClosed decls table}
    (received : Roots.Receipt original enabled Γ code) :
    (extension.receipt received).parsed.index.val = code.row := received.address_exact

end ReadingExtension
#print axioms ReadingExtension.proof_free
#print axioms ReadingExtension.template_nodeCount
#print axioms ReadingExtension.absent_iff
#print axioms ReadingExtension.receipt
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
