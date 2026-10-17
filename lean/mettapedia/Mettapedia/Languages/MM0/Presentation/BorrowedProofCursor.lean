import Mettapedia.Languages.MM0.Presentation.Calculus
import Mettapedia.Languages.MM0.Kernel.BorrowedProofCursor
import Mettapedia.Machines.Cursor.SealedInference

/-!
# One MM0 judgment through authored rules, cursors and protected inference

The actual declaration tables, context and hypotheses determine all three
routes. The direct graph checker and the authored calculus both meet the
existing semantic kernel, without identifying their proof representations.
A protected inference session for that same scope establishes an authored
judgment whenever it delivers a genuine theorem box.

These are logical adequacy and protected-construction results. They do not
extract a certificate from an erased derivation, establish an efficient export
algorithm, validate arbitrary declaration tables or decode textual modules.
The allocation-sensitive MMB profile retains its separate identity laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.BorrowedProofCursor

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

open Mettapedia.Languages.MM0
open Mettapedia.Languages.MeTTa
open Mettapedia.Machines.Cursor

/-- Actual theory contents, rather than a caller-supplied theory label. -/
def scope (theory : Theory) (context : Context) (hypotheses : List Preterm) : Kernel.BorrowedProofCursor.Scope :=
  ⟨theory.termSignature, theory.definitionSignature, theory.theoremSignature,
    context, hypotheses⟩

/-- The finite graph is supplied to the existing independent replay checker.
The cache and root are observed outputs, not trusted proof assumptions. -/
def GraphAccepted (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (expression : Preterm) : Prop :=
  ∃ (nodes : List (Node Preterm Kernel.BorrowedProofCursor.Witness Nat)) (cache : Array Preterm) (root : Nat),
    replay (Kernel.BorrowedProofCursor.interface (scope theory context hypotheses)) nodes = some cache ∧
      cache[root]? = some expression

/-- Native graph presentations and the authored calculus have exactly the
same accepted judgments under the same actual theory and local assumptions. -/
theorem graph_iff_authored (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (expression : Preterm) :
    GraphAccepted theory context hypotheses expression ↔
      (Calculus.mm0 theory).Accepts (Calculus.derivesJ context hypotheses expression) := by
  exact (Kernel.BorrowedProofCursor.original_iff_graph (scope theory context hypotheses) expression).symm.trans
    (Calculus.accepts_iff_derives context hypotheses expression).symm

/-- A successful run over actual stored rows establishes the authored judgment;
no recursively expanded proof tree is required by the cursor execution. -/
theorem stored_root_authored (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (source : Kernel.BorrowedProofCursor.Source) (schedule : List Nat)
    (result : State Preterm)
    (accepted : run (Kernel.BorrowedProofCursor.interface (scope theory context hypotheses)) source
      (start source) schedule = some result)
    (address : Nat) (expression : Preterm) (found : rootAt result address = some expression) :
    (Calculus.mm0 theory).Accepts (Calculus.derivesJ context hypotheses expression) :=
  (Calculus.accepts_iff_derives context hypotheses expression).mpr
    (Kernel.BorrowedProofCursor.stored_root_original (scope theory context hypotheses) source schedule result
      accepted address expression found)

/-- Genuine boxes in a retained session preserve the original MM0 theory and
therefore the authored judgment. The session cannot substitute another rule
interface while retaining its private construction invariant. -/
theorem sealed_judgment_authored (theory : Theory) (context : Context)
    (hypotheses : List Preterm) {kernel brand capability : Nat}
    {original : Seal.Config Preterm}
    (session : SealedInference.Session (Kernel.BorrowedProofCursor.interface (scope theory context hypotheses))
      kernel brand capability original)
    {principal : Nat} {expression : Preterm}
    (held : Seal.Val.box brand (.data expression) ∈ session.state.holds principal) :
    (Calculus.mm0 theory).Accepts (Calculus.derivesJ context hypotheses expression) :=
  (Calculus.accepts_iff_derives context hypotheses expression).mpr
    ((Kernel.BorrowedProofCursor.derives_iff_original (scope theory context hypotheses) expression).mp
      (session.original_derives held))

/-- A delivered checked request meets both the kernel's semantic derivability
and the authored calculus, with the exact same context and theory contents. -/
theorem sealed_request_authored (theory : Theory) (context : Context)
    (hypotheses : List Preterm) {kernel brand capability : Nat}
    {original : Seal.Config Preterm}
    (session : SealedInference.Session (Kernel.BorrowedProofCursor.interface (scope theory context hypotheses))
      kernel brand capability original)
    (request : SealedInference.Request (Kernel.BorrowedProofCursor.interface (scope theory context hypotheses)))
    {premises : List Preterm} {position : Nat}
    {next : SealedInference.Session (Kernel.BorrowedProofCursor.interface (scope theory context hypotheses))
      kernel brand capability original}
    (accepted : session.advance request = some (premises, position, next)) :
    (Calculus.mm0 theory).Accepts
      (Calculus.derivesJ context hypotheses request.conclusion) :=
  (Calculus.accepts_iff_derives context hypotheses request.conclusion).mpr
    ((Kernel.BorrowedProofCursor.derives_iff_original (scope theory context hypotheses) request.conclusion).mp
      (session.advance_sound request accepted).2.2.2)

namespace Controls

def constant : Preterm := .term 0
def declaration : TheoremDecl := ⟨[], [], constant⟩
def withAxiom : Theory :=
  { sorts := [(0, { provable := true })]
    terms := [(0, ⟨[], 0, ∅⟩)]
    theorems := [(0, declaration)] }
def withoutAxiom : Theory := { withAxiom with theorems := [] }

def rows : List (Node Preterm Kernel.BorrowedProofCursor.Witness Nat) :=
  [⟨constant, .theoremApp 0 [], [], 19⟩]

theorem actual_graph_accepts :
    replay (Kernel.BorrowedProofCursor.interface (scope withAxiom [] [])) rows = some #[constant] := by decide

theorem graph_establishes_authored_claim :
    (Calculus.mm0 withAxiom).Accepts (Calculus.derivesJ [] [] constant) :=
  (graph_iff_authored withAxiom [] [] constant).mp
    ⟨rows, #[constant], 0, actual_graph_accepts, rfl⟩

theorem changed_theory_refuses_same_rows :
    replay (Kernel.BorrowedProofCursor.interface (scope withoutAxiom [] [])) rows = none := by decide

private theorem no_derivation {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {expression : Preterm} :
    Kernel.Derives signature definitions (fun _ => none) context [] expression → False
  | .hypothesis member => by cases member
  | .theoremApp lookup _ _ => by cases lookup
  | .conversion _ child => no_derivation child

theorem changed_theory_has_no_alternative_graph :
    ¬ GraphAccepted withoutAxiom [] [] constant := by
  intro accepted
  exact no_derivation ((Kernel.BorrowedProofCursor.original_iff_graph (scope withoutAxiom [] []) constant).mpr accepted)

theorem changed_theory_has_no_authored_certificate :
    ¬ (Calculus.mm0 withoutAxiom).Accepts (Calculus.derivesJ [] [] constant) :=
  fun accepted => changed_theory_has_no_alternative_graph
    ((graph_iff_authored withoutAxiom [] [] constant).mpr accepted)

def initial : Seal.Config Preterm :=
  ⟨fun principal => if principal = 0 then [.cap 0 Seal.Rights.both] else [], 1, 0⟩

theorem initial_valid (theory : Theory) :
    Seal.KernelStart (Kernel.BorrowedProofCursor.Rules (scope theory [] [])) 0 0 initial where
  fresh := by decide
  boxes := by
    intro principal value member
    by_cases same : principal = 0
    · subst same
      simp only [initial, ↓reduceIte, List.mem_singleton] at member
      subst value
      trivial
    · simp [initial, same] at member
  othersCannotSeal := by
    intro principal value other member
    simp [initial, other] at member

/-- The same public request is checked under each actual retained theory.
The client never supplies a replacement rule interface to `advance`. -/
def delivered (theory : Theory) : Option (Option (Seal.Val Preterm)) := do
  let session ← SealedInference.Session.begin
    (Kernel.BorrowedProofCursor.interface (scope theory [] [])) 0 0 0 initial
    (initial_valid theory)
  let (_, position, next) ← session.advance ⟨[], .theoremApp 0 [], constant, 1⟩
  some (next.state.held 1 position)

theorem actual_mm0_request_delivers_sealed_theorem :
    delivered withAxiom = some (some (.box 0 (.data constant))) := by decide

theorem absent_axiom_cannot_mint_same_claim : delivered withoutAxiom = none := by decide

end Controls

end Mettapedia.Languages.MM0.Presentation.BorrowedProofCursor
