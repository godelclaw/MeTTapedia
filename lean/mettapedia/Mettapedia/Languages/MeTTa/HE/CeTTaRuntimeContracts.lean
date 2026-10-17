import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness
import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.Languages.MeTTa.HE.IncrementalTableSemantics
import Mettapedia.Languages.MeTTa.HE.BridgeMatrix
import Mettapedia.Machines.CMemory.EffectStatements
import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.Array
import Mettapedia.Machines.CMemory.ProductiveBlocks
import Mettapedia.Machines.LinkedScopeStack

/-!
# CeTTa runtime contracts and selected instruction projections

The historical cache/tabling contracts remain below. Their variant-key theorem
is explicitly a legacy simpleMatch-interface result, not evidence for the
repaired public faithful query interface.

`InstructionControl` checks exact selected C source blocks and projects their
local operand/frame updates. Its independent source squares preserve saved
syntax, reached bindings, child occurrences and delivery targets. The old
parsed chain block is retained as a negative control: it computes a different
continuation when the chain binder is already bound.

`InstructionControl.Collapse` proves the completed collector's occurrence and
binding readback, and instantiates the common retained child interface with a
whole saved frame and its older continuation. It requires an independently
complete child enumeration before publishing an aggregate. Scheduler pause,
child completion and cancellation remain distinct. The local `returned` flag
controls one parsed block; it is not a native ownership or sealing theorem.

`CallReturnControl` checks the ordinary raw-return helper and selected refusal,
stopped and typed-callback blocks. The local squares keep the post-argument
invocation, selected demand, reached binding record and physical occurrence.
Producer-completed values have a different source judgment; equal syntax does
not determine this provenance. Terminal publication uses the explicit
full-binding observer. The common retained-child adapter begins after the
actual native push; it neither loads the original argument computation nor
claims a whole native call-loader correspondence. Variant-only materialization,
relay redirection and the callback's independent judgment remain explicit
readback obligations.

`NativeCallFrame` interprets selected parsed field, counter and stack updates
through the existing C memory semantics. Its owned-cell proofs preserve the
saved invocation and older stack, recover the occurrence from the paused
sequencer counter, and recover the selected environment from the RESULT
frame's copied row. The actual ordinary-tail push constructs a retained
readback containing the reached finite storage. Logical layout admission,
allocation, binding/outcome copy, GC and stream preparation, payload decoders,
materializer and relay helper contracts remain explicit. The chosen argument
read order needs native helper/read noninterference. Actual CALLER execution
and relay publication still require their own correspondence; this memory
adapter does not prove them or native exactly-once effects.

`NativeOutcomeMaterialization` executes the parsed variant-only materializer
and its parsed storage and presence helpers in the existing C memory semantics.
For live inline outcomes with null variant storage it earns the stored atom
pointer and preserves arbitrary framed memory. Its `Full` fragment also checks
the complete materializer body and the two bound-value summary helpers. With
zero binding rows and a null frame index, it performs the actual cache write
and closes both automatic local scopes. An already populated live cache is
returned unchanged. The two materializers agree when that cache is initially
null or already equals the stored atom; an arbitrary mismatched cache has no
such law. Other helper branches, native layout and automatic-storage lifetime,
payload decoding and the intervening CALLER remain separate boundaries.

`NativeCallFrame.Copy` earns stored-data readback for selected copy paths.
The scalar stores, successful retained-storage binding branch, separately
reserved variant/goal payload transfers, and actual temporary-to-environment
assignment preserve complete payload coordinates and duplicate entries. The
allocated records remain distinct. The resulting native child-request equation
covers both successful and failed decoding, without a supplied copy equality.
The composite is a stored-data projection at helper boundaries, not execution
of the complete C helpers. Allocation, retain/release and index updates, native
ABI/whole-record memcpy interpretation, cache refresh, materialization, payload
decoder adequacy and actual CALLER execution remain separate obligations.
The binding allocation fallback's copy and count publication are proved
locally; the full fallback branch is not included in the retained fork join.

This is a checked partial projection, not a general C interpreter or a proof of
whole native execution. Calls are interpreted under their stated helper
contracts. Concrete pointer identity, allocation/copy success, GC ownership,
helper implementations, world-changing child execution and complete child
enumeration still require the actual runtime readback. An unsupported
projection branch means this local contract does not cover it; it is not a
runtime error.

## Contracts

### §1: Alpha-Canonicalization (`term_universe.c`, `term_canon.c`)
- Any injective variable renaming gives a safe canonicalization
- Canonical keys preserve match semantics (BEq, co-reference)
- Variant-equivalent queries share canonical keys → cache reuse is sound

### §2: Search Context Rollback (`search_machine.c`)
- Bindings builder with marks: save/rollback is stack-disciplined
- Rollback restores all prior bindings; new bindings after mark are discarded
- Scratch arena rollback is compatible with bindings rollback

### §3: Effect Classification (`runtime_effect_classes.json`)
- Pure operations: cache-safe, reorder-safe
- Space mutations: invalidate cache, preserve-order
- Import/oracle: avoid cache, external boundary
- Profile hierarchy gates which operations are available

### §4: Refactor Risk Map
Each theorem maps to a specific CeTTa refactor risk it reduces.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: Alpha-Canonicalization Contracts

CeTTa's `term_universe_canonicalize_atom()` assigns ordinals to variables
in DFS order. We don't formalize the specific algorithm — we formalize the
PROPERTIES that make any such canonicalization safe for tabling and caching.

The key insight: canonicalization IS an injective VarRenaming applied via
`applyAtomTotal`. All safety properties follow from injectivity. -/

/-- A **canonicalization** is an injective variable renaming.
    CeTTa's `TermUniverseCanonMap` builds one by assigning fresh ordinals. -/
structure Canonicalization where
  ren : VarRenaming
  inj : ren.Injective

namespace Canonicalization

/-- Apply canonicalization to an atom. -/
def apply (c : Canonicalization) (a : Atom) : Atom :=
  applyAtomTotal c.ren a

/-- **Contract 1a**: Canonicalization preserves symbols.
    Risk: refactoring `term_universe_canonicalize_atom` to touch symbol atoms. -/
theorem preserves_symbols (c : Canonicalization) (s : String) :
    c.apply (.symbol s) = .symbol s := by
  unfold apply applyAtomTotal; rfl

/-- **Contract 1b**: Canonicalization preserves grounded values.
    Risk: refactoring canonicalization to touch grounded atoms. -/
theorem preserves_grounded (c : Canonicalization) (g : GroundedValue) :
    c.apply (.grounded g) = .grounded g := by
  unfold apply applyAtomTotal; rfl

/-- **Contract 1c**: Canonicalization distributes over expressions.
    Risk: breaking the recursive structure of canonicalization. -/
theorem distributes_expression (c : Canonicalization) (es : List Atom) :
    c.apply (.expression es) = .expression (es.map c.apply) := by
  simp only [apply]; unfold applyAtomTotal; rfl

/-- **Contract 1d**: Canonicalization is injective on atoms.
    Two different atoms cannot canonicalize to the same form.
    Risk: using a non-injective renaming (e.g., mapping all vars to one name). -/
theorem apply_injective (c : Canonicalization) :
    Function.Injective c.apply :=
  applyAtomTotal_injective c.ren c.inj

/-- **Contract 1e**: Canonicalization preserves BEq results.
    `(canon(a) == canon(b)) = (a == b)` for any atoms a, b.
    Risk: BEq check on canonical atoms disagreeing with original check. -/
theorem preserves_beq (c : Canonicalization) (a b : Atom) :
    (c.apply a == c.apply b) = (a == b) :=
  applyAtomTotal_beq_iff c.ren c.inj a b

/-- **Contract 1f**: Co-reference preservation (faithful encoding).
    Same variable name → same canonical name. Different → different.
    Risk: collapsing distinct variables during canonicalization. -/
theorem faithful_variables (c : Canonicalization) (v₁ v₂ : String) :
    v₁ = v₂ ↔ c.ren.rename v₁ = c.ren.rename v₂ :=
  VarRenaming.faithful_iff c.ren c.inj v₁ v₂

/-- **Contract 1g**: Variant-equivalent queries share canonical RHS atoms on
    the legacy simpleMatch query model. The public faithful query interface still
    needs its own invariant. -/
theorem variant_cache_safe (c : Canonicalization)
    (space : Space) (q : Atom) (fuel : Nat) :
    (variantLegacyQueryEquations space q fuel).map Prod.fst =
    (variantLegacyQueryEquations space (c.apply q) fuel).map Prod.fst := by
  have hvar : VariantEquiv q (c.apply q) := ⟨c.ren, c.inj, rfl⟩
  exact variant_queries_same_rhs space q (c.apply q) hvar fuel

end Canonicalization

/-! ## §2: Search Context Rollback Contracts

CeTTa's `SearchContext` uses mark/rollback for backtracking. The bindings
builder captures a mark (current length); rollback truncates back to it.

We model this as a list-based bindings builder with explicit marks. -/

/-- A **bindings builder mark**: captures the state at save time. -/
structure BindingsMark where
  savedLength : Nat

/-- A minimal assignment-list projection with mark/rollback.  It illustrates
the prefix law used by CeTTa but is not a complete model of the live
`BindingsBuilder`, which also carries constraints, Prime occurrence state,
derived caches, revision clocks, ownership, and region protocol state. -/
structure BindingsBuilder where
  entries : List (String × Atom)

namespace BindingsBuilder

def empty : BindingsBuilder := ⟨[]⟩

/-- Save the current state as a mark. -/
def save (bb : BindingsBuilder) : BindingsMark :=
  ⟨bb.entries.length⟩

/-- Add a binding. -/
def addBinding (bb : BindingsBuilder) (v : String) (a : Atom) : BindingsBuilder :=
  ⟨(v, a) :: bb.entries⟩

/-- Rollback to a saved mark. -/
def rollback (bb : BindingsBuilder) (mark : BindingsMark) : BindingsBuilder :=
  ⟨bb.entries.drop (bb.entries.length - mark.savedLength)⟩

/-- **Contract 2a**: Rollback after save with no intermediate changes is identity.
    Risk: save/rollback cycle corrupting bindings. -/
theorem rollback_save_noop (bb : BindingsBuilder) :
    bb.rollback (bb.save) = bb := by
  simp [rollback, save]

/-- **Contract 2b**: Rollback discards bindings added after mark.
    Risk: rollback failing to undo recent bindings. -/
theorem rollback_discards_new (bb : BindingsBuilder) (v : String) (a : Atom) :
    (bb.addBinding v a).rollback (bb.save) = bb := by
  simp [rollback, save, addBinding]

/-- **Contract 2c**: Rollback preserves bindings from before the mark.
    Risk: rollback accidentally removing pre-existing bindings. -/
theorem rollback_preserves_old (bb : BindingsBuilder)
    (v₁ : String) (a₁ : Atom) (v₂ : String) (a₂ : Atom) :
    ((bb.addBinding v₁ a₁).addBinding v₂ a₂).rollback ((bb.addBinding v₁ a₁).save) =
    bb.addBinding v₁ a₁ := by
  simp [rollback, save, addBinding]

/-- **Contract 2d**: Multiple rollbacks to the same mark are idempotent.
    Risk: double-rollback causing corruption. -/
theorem rollback_idempotent (bb : BindingsBuilder) (mark : BindingsMark) :
    (bb.rollback mark).rollback mark = bb.rollback mark := by
  simp [rollback, List.length_drop]; omega

end BindingsBuilder

/-! ## §3: Effect Classification Contracts

CeTTa classifies operations by their effect class, which determines
caching and scheduling policies. This mirrors `runtime_effect_classes.json`. -/

/-- Effect classes from CeTTa's `runtime_effect_classes.json`. -/
inductive EffectClass where
  | pureValue       -- No side effects, deterministic
  | pureNondet      -- No side effects, nondeterministic (match results)
  | pureControl     -- No side effects, control flow (if, case)
  | spaceRead       -- Reads from space (get-atoms, match)
  | spaceWrite      -- Writes to space (add-atom, remove-atom)
  | stateEffect     -- Modifies state (bind!, new-state)
  | dynamicEval     -- Dynamic evaluation (eval on computed atom)
  | importEffect    -- Import/module loading
  deriving DecidableEq, Repr

/-- Memo policy derived from effect class. -/
inductive MemoPolicy where
  | stableCacheSafe    -- Safe to memoize across revisions
  | snapshotCacheOnly  -- Cache only for matching space revision
  | avoidRuntimeCache  -- Don't cache (effectful)
  deriving DecidableEq, Repr

/-- Scheduler policy derived from effect class. -/
inductive SchedulerPolicy where
  | reorderSafe      -- Can be reordered freely
  | preserveOrder    -- Must respect evaluation order
  | externalBoundary -- Import effects at system boundary
  deriving DecidableEq, Repr

/-- The effect→policy mapping from `runtime_effect_classes.json`. -/
def effectMemoPolicy : EffectClass → MemoPolicy
  | .pureValue => .stableCacheSafe
  | .pureNondet => .stableCacheSafe
  | .pureControl => .stableCacheSafe
  | .spaceRead => .snapshotCacheOnly
  | .spaceWrite => .snapshotCacheOnly
  | .stateEffect => .avoidRuntimeCache
  | .dynamicEval => .avoidRuntimeCache
  | .importEffect => .avoidRuntimeCache

def effectSchedulerPolicy : EffectClass → SchedulerPolicy
  | .pureValue => .reorderSafe
  | .pureNondet => .reorderSafe
  | .pureControl => .reorderSafe
  | .spaceRead => .preserveOrder
  | .spaceWrite => .preserveOrder
  | .stateEffect => .preserveOrder
  | .dynamicEval => .preserveOrder
  | .importEffect => .externalBoundary

/-- **Contract 3a**: Pure operations are always cache-safe.
    Risk: marking a pure operation as uncacheable (performance loss). -/
theorem pure_is_cache_safe :
    effectMemoPolicy .pureValue = .stableCacheSafe ∧
    effectMemoPolicy .pureNondet = .stableCacheSafe ∧
    effectMemoPolicy .pureControl = .stableCacheSafe :=
  ⟨rfl, rfl, rfl⟩

/-- **Contract 3b**: Pure operations are reorder-safe.
    Risk: unnecessarily serializing pure computations. -/
theorem pure_is_reorder_safe :
    effectSchedulerPolicy .pureValue = .reorderSafe ∧
    effectSchedulerPolicy .pureNondet = .reorderSafe ∧
    effectSchedulerPolicy .pureControl = .reorderSafe :=
  ⟨rfl, rfl, rfl⟩

/-- **Contract 3c**: Space writes require snapshot-only caching.
    Risk: caching space-write results across revisions (stale data). -/
theorem space_write_is_snapshot_only :
    effectMemoPolicy .spaceWrite = .snapshotCacheOnly :=
  rfl

/-- **Contract 3d**: Import effects avoid all caching.
    Risk: caching import side-effects (module loaded twice or not at all). -/
theorem import_avoids_cache :
    effectMemoPolicy .importEffect = .avoidRuntimeCache :=
  rfl

/-- **Contract 3e**: Import effects are external boundaries.
    Risk: reordering imports (module dependencies violated). -/
theorem import_is_external_boundary :
    effectSchedulerPolicy .importEffect = .externalBoundary :=
  rfl

/-- An operation is **eligible for aggressive lowering** iff it's cache-safe. -/
def isLoweringEligible (e : EffectClass) : Bool :=
  effectMemoPolicy e == .stableCacheSafe

/-- **Contract 3f**: Only pure operations are lowering-eligible.
    Risk: aggressively lowering effectful operations. -/
theorem lowering_eligible_iff_pure (e : EffectClass) :
    isLoweringEligible e = true ↔
    (e = .pureValue ∨ e = .pureNondet ∨ e = .pureControl) := by
  cases e <;> simp [isLoweringEligible, effectMemoPolicy]

/-! ## §4: Profile Hierarchy Contracts

CeTTa profiles gate which operations are available. -/

/-- CeTTa profile levels (from `session.h`). -/
inductive ProfileLevel where
  | heCompat     -- HE-compatible public interface
  | heExtended   -- HE-compatible + CeTTa extensions
  | hePrime      -- Extended + dependent telescope
  deriving DecidableEq, Repr

/-- Profile expressiveness ordering. -/
def ProfileLevel.rank : ProfileLevel → Nat
  | .heCompat => 0
  | .heExtended => 1
  | .hePrime => 2

/-- **Contract 4a**: Profile hierarchy is a total order.
    Risk: adding a profile that isn't comparable to existing ones. -/
theorem profile_total_order (p₁ p₂ : ProfileLevel) :
    p₁.rank ≤ p₂.rank ∨ p₂.rank ≤ p₁.rank := by
  omega

/-- A feature requires at minimum a given profile level. -/
def featureAvailable (required : ProfileLevel) (active : ProfileLevel) : Bool :=
  required.rank ≤ active.rank

/-- **Contract 4b**: HE-compat features are available in all profiles.
    Risk: breaking HE compatibility in extended profiles. -/
theorem he_compat_always_available (p : ProfileLevel) :
    featureAvailable .heCompat p = true := by
  cases p <;> simp [featureAvailable, ProfileLevel.rank]

/-- **Contract 4c**: HE-prime features require HE-prime profile.
    Risk: exposing dependent telescope in HE-compat mode. -/
theorem he_prime_requires_prime :
    featureAvailable .hePrime .heCompat = false ∧
    featureAvailable .hePrime .heExtended = false ∧
    featureAvailable .hePrime .hePrime = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## §5: Refactor Risk Map

Each contract reduces a specific refactor risk:

| Contract | C File | Risk Reduced |
|----------|--------|-------------|
| 1a: preserves_symbols | term_canon.c | Canon touching symbols |
| 1b: preserves_grounded | term_canon.c | Canon touching grounded |
| 1d: apply_injective | term_universe.c | Non-injective canon map |
| 1e: preserves_beq | term_canon.c | BEq mismatch after canon |
| 1f: faithful_variables | term_canon.c | Variable collapsing |
| 1g: variant_cache_safe | table_store.c | Wrong RHS from variant cache |
| 2a: rollback_save_noop | search_machine.c | Save/rollback cycle corruption |
| 2b: rollback_discards_new | search_machine.c | Rollback not undoing bindings |
| 2c: rollback_preserves_old | search_machine.c | Rollback removing too much |
| 2d: rollback_idempotent | search_machine.c | Double-rollback corruption |
| 3a: pure_is_cache_safe | eval.c | Pure op marked uncacheable |
| 3c: space_write_snapshot | table_store.c | Cross-revision stale cache |
| 3d: import_avoids_cache | eval.c | Caching import side-effects |
| 3f: lowering_eligible | mm2_lower.c | Lowering effectful ops |
| 4b: he_compat_available | session.c | Breaking HE compat |
| 4c: he_prime_requires | session.c | Leaking prime features |
-/

end Mettapedia.Languages.MeTTa.HE


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Minimal
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev identifier (name : String) : CExpr := .identifier name.toList
abbrev field (base : CExpr) (name : String) (pointer : Bool := true) : CExpr :=
  .field base name.toList pointer
abbrev call (name : String) (arguments : List CExpr) : CExpr := .call name.toList arguments
abbrev address (value : CExpr) : CExpr := .unary .address value

def types : TypeNames := ["Atom".toList, "bool".toList]
def frameAtom : CExpr := field (identifier "frame") "atom"
def itemEnv : CExpr := address (field (identifier "item") "env")
def savedTemplate : CExpr := call "expr_arg" [frameAtom, .decimal 2]
def savedBinder : CExpr := field (call "expr_arg" [frameAtom, .decimal 1]) "var_id"
def substitution (template : CExpr) : CExpr := call "instantiate_template_variable_once"
  [identifier "a", template, savedBinder, identifier "result"]
def pushBody : CStatement := .effect (call "he_instruction_push"
  [identifier "stack", identifier "HE_INSTRUCTION_RUN", identifier "s", identifier "a",
    identifier "body", identifier "child_fuel", itemEnv, identifier "os"])

def chainBefore : List CStatement :=
  [.declare ⟨"Atom".toList, 1⟩ "body".toList
      (call "bindings_apply_if_vars" [itemEnv, identifier "a", savedTemplate]),
    .assign (identifier "body") (substitution (identifier "body")), pushBody, .return none]

def chainAfter : List CStatement :=
  [.declare ⟨"Atom".toList, 1⟩ "body".toList (substitution savedTemplate),
    pushBody, .return none]

def returned : List CStatement :=
  [.effect (call "outcome_set_add" [identifier "os",
    .index (field (field (identifier "result") "expr") "elems" false) (.decimal 1), itemEnv])]

/-- The body declaration precedes the native kind guard. -/
def functionBodyRead : CStatement :=
  .declare ⟨"Atom".toList, 1⟩ "body".toList (call "expr_arg" [identifier "atom", .decimal 0])

def functionBodyGuard : CExpr :=
  .binary .ne (field (identifier "body") "kind") (identifier "ATOM_EXPR")

def functionStep : CExpr :=
  .binary .or
    (.binary .or (call "active_profile_uses_rust_he_compat_semantics" [])
      (call "he_minimal_instruction" [identifier "body"]))
    (.binary .eq (call "atom_head_symbol_id" [identifier "body"])
      (field (identifier "g_builtin_syms") "return_text" false))

/-- The expression-body branch of the current native function entry. The
preceding body read and kind guard are checked separately. The error branch
and the ordinary evaluator call are outside this selected projection. -/
def functionEntry : List CStatement :=
  [.assign (field (identifier "frame") "phase") (identifier "HE_INSTRUCTION_FUNCTION"),
   .declare ⟨"bool".toList, 0⟩ "step".toList functionStep,
   .branch (identifier "step")
     [.effect (call "he_instruction_push" [identifier "stack", identifier "HE_INSTRUCTION_RUN",
       identifier "s", identifier "a", identifier "body", identifier "child_fuel",
       address (field (identifier "frame") "env"), address (field (identifier "frame") "inner")])]
     [.effect (call "eval_for_caller" [identifier "s", identifier "a", .null,
       identifier "body", identifier "child_fuel", address (field (identifier "frame") "env"),
       .bool true, address (field (identifier "frame") "inner")])]]

def chainBeforeSourcePiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem chainBeforeSourcePiece0_lex : chainBeforeSourcePiece0.1.toList.foldl step initial = completed chainBeforeSourcePiece0.2 := by
  decide +kernel

def chainBeforeSourcePiece1 : String × List Token := ("                Atom *body = bindings_apply_if_vars(\n", [.identifier ['A', 't', 'o', 'm'], .punctuation ['*'], .identifier ['b', 'o', 'd', 'y'], .punctuation ['='], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'a', 'p', 'p', 'l', 'y', '_', 'i', 'f', '_', 'v', 'a', 'r', 's'], .punctuation ['(']])
theorem chainBeforeSourcePiece1_lex : chainBeforeSourcePiece1.1.toList.foldl step initial = completed chainBeforeSourcePiece1.2 := by
  decide +kernel

def chainBeforeSourcePiece2 : String × List Token := ("                    &item->env, a, expr_arg(frame->atom, 2));\n", [.punctuation ['&'], .identifier ['i', 't', 'e', 'm'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .identifier ['a'], .punctuation [','], .identifier ['e', 'x', 'p', 'r', '_', 'a', 'r', 'g'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .number ['2'], .punctuation [')'], .punctuation [')'], .punctuation [';']])
theorem chainBeforeSourcePiece2_lex : chainBeforeSourcePiece2.1.toList.foldl step initial = completed chainBeforeSourcePiece2.2 := by
  decide +kernel

def chainBeforeSourcePiece3 : String × List Token := ("                body = instantiate_template_variable_once(a, body,\n", [.identifier ['b', 'o', 'd', 'y'], .punctuation ['='], .identifier ['i', 'n', 's', 't', 'a', 'n', 't', 'i', 'a', 't', 'e', '_', 't', 'e', 'm', 'p', 'l', 'a', 't', 'e', '_', 'v', 'a', 'r', 'i', 'a', 'b', 'l', 'e', '_', 'o', 'n', 'c', 'e'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['b', 'o', 'd', 'y'], .punctuation [',']])
theorem chainBeforeSourcePiece3_lex : chainBeforeSourcePiece3.1.toList.foldl step initial = completed chainBeforeSourcePiece3.2 := by
  decide +kernel

def chainBeforeSourcePiece4 : String × List Token := ("                    expr_arg(frame->atom, 1)->var_id, result);\n", [.identifier ['e', 'x', 'p', 'r', '_', 'a', 'r', 'g'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .number ['1'], .punctuation [')'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', '_', 'i', 'd'], .punctuation [','], .identifier ['r', 'e', 's', 'u', 'l', 't'], .punctuation [')'], .punctuation [';']])
theorem chainBeforeSourcePiece4_lex : chainBeforeSourcePiece4.1.toList.foldl step initial = completed chainBeforeSourcePiece4.2 := by
  decide +kernel

def chainBeforeSourcePiece5 : String × List Token := ("                he_instruction_push(stack, HE_INSTRUCTION_RUN, s, a,\n", [.identifier ['h', 'e', '_', 'i', 'n', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n', '_', 'p', 'u', 's', 'h'], .punctuation ['('], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation [','], .identifier ['H', 'E', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', '_', 'R', 'U', 'N'], .punctuation [','], .identifier ['s'], .punctuation [','], .identifier ['a'], .punctuation [',']])
theorem chainBeforeSourcePiece5_lex : chainBeforeSourcePiece5.1.toList.foldl step initial = completed chainBeforeSourcePiece5.2 := by
  decide +kernel

def chainBeforeSourcePiece6 : String × List Token := ("                    body, child_fuel, &item->env, os);\n", [.identifier ['b', 'o', 'd', 'y'], .punctuation [','], .identifier ['c', 'h', 'i', 'l', 'd', '_', 'f', 'u', 'e', 'l'], .punctuation [','], .punctuation ['&'], .identifier ['i', 't', 'e', 'm'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .identifier ['o', 's'], .punctuation [')'], .punctuation [';']])
theorem chainBeforeSourcePiece6_lex : chainBeforeSourcePiece6.1.toList.foldl step initial = completed chainBeforeSourcePiece6.2 := by
  decide +kernel

def chainBeforeSourcePiece7 : String × List Token := ("                return;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .punctuation [';']])
theorem chainBeforeSourcePiece7_lex : chainBeforeSourcePiece7.1.toList.foldl step initial = completed chainBeforeSourcePiece7.2 := by
  decide +kernel

def chainBeforeSourcePiece8 : String × List Token := ("            }", [.punctuation ['}']])
theorem chainBeforeSourcePiece8_lex : chainBeforeSourcePiece8.1.toList.foldl step initial = completed chainBeforeSourcePiece8.2 := by
  decide +kernel

def chainBeforeSourcePieces : List (String × List Token) := [chainBeforeSourcePiece0, chainBeforeSourcePiece1, chainBeforeSourcePiece2, chainBeforeSourcePiece3, chainBeforeSourcePiece4, chainBeforeSourcePiece5, chainBeforeSourcePiece6, chainBeforeSourcePiece7, chainBeforeSourcePiece8]
def chainBeforeSource : String := String.join (chainBeforeSourcePieces.map Prod.fst)
def chainBeforeSourceTokens : List Token := chainBeforeSourcePieces.flatMap Prod.snd
theorem chainBeforeSource_lex : lex chainBeforeSource.toList = .ok chainBeforeSourceTokens := by
  apply lex_completed_string_pieces
  simp only [chainBeforeSourcePieces, List.forall_cons]
  exact ⟨chainBeforeSourcePiece0_lex, chainBeforeSourcePiece1_lex, chainBeforeSourcePiece2_lex, chainBeforeSourcePiece3_lex, chainBeforeSourcePiece4_lex, chainBeforeSourcePiece5_lex, chainBeforeSourcePiece6_lex, chainBeforeSourcePiece7_lex, chainBeforeSourcePiece8_lex, trivial⟩

def chainAfterSourcePiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem chainAfterSourcePiece0_lex : chainAfterSourcePiece0.1.toList.foldl step initial = completed chainAfterSourcePiece0.2 := by
  decide +kernel

def chainAfterSourcePiece1 : String × List Token := ("                Atom *body = instantiate_template_variable_once(a,\n", [.identifier ['A', 't', 'o', 'm'], .punctuation ['*'], .identifier ['b', 'o', 'd', 'y'], .punctuation ['='], .identifier ['i', 'n', 's', 't', 'a', 'n', 't', 'i', 'a', 't', 'e', '_', 't', 'e', 'm', 'p', 'l', 'a', 't', 'e', '_', 'v', 'a', 'r', 'i', 'a', 'b', 'l', 'e', '_', 'o', 'n', 'c', 'e'], .punctuation ['('], .identifier ['a'], .punctuation [',']])
theorem chainAfterSourcePiece1_lex : chainAfterSourcePiece1.1.toList.foldl step initial = completed chainAfterSourcePiece1.2 := by
  decide +kernel

def chainAfterSourcePiece2 : String × List Token := ("                    expr_arg(frame->atom, 2),\n", [.identifier ['e', 'x', 'p', 'r', '_', 'a', 'r', 'g'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .number ['2'], .punctuation [')'], .punctuation [',']])
theorem chainAfterSourcePiece2_lex : chainAfterSourcePiece2.1.toList.foldl step initial = completed chainAfterSourcePiece2.2 := by
  decide +kernel

def chainAfterSourcePiece3 : String × List Token := ("                    expr_arg(frame->atom, 1)->var_id, result);\n", [.identifier ['e', 'x', 'p', 'r', '_', 'a', 'r', 'g'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .number ['1'], .punctuation [')'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', '_', 'i', 'd'], .punctuation [','], .identifier ['r', 'e', 's', 'u', 'l', 't'], .punctuation [')'], .punctuation [';']])
theorem chainAfterSourcePiece3_lex : chainAfterSourcePiece3.1.toList.foldl step initial = completed chainAfterSourcePiece3.2 := by
  decide +kernel

def chainAfterSourcePiece4 : String × List Token := ("                he_instruction_push(stack, HE_INSTRUCTION_RUN, s, a,\n", [.identifier ['h', 'e', '_', 'i', 'n', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n', '_', 'p', 'u', 's', 'h'], .punctuation ['('], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation [','], .identifier ['H', 'E', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', '_', 'R', 'U', 'N'], .punctuation [','], .identifier ['s'], .punctuation [','], .identifier ['a'], .punctuation [',']])
theorem chainAfterSourcePiece4_lex : chainAfterSourcePiece4.1.toList.foldl step initial = completed chainAfterSourcePiece4.2 := by
  decide +kernel

def chainAfterSourcePiece5 : String × List Token := ("                    body, child_fuel, &item->env, os);\n", [.identifier ['b', 'o', 'd', 'y'], .punctuation [','], .identifier ['c', 'h', 'i', 'l', 'd', '_', 'f', 'u', 'e', 'l'], .punctuation [','], .punctuation ['&'], .identifier ['i', 't', 'e', 'm'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .identifier ['o', 's'], .punctuation [')'], .punctuation [';']])
theorem chainAfterSourcePiece5_lex : chainAfterSourcePiece5.1.toList.foldl step initial = completed chainAfterSourcePiece5.2 := by
  decide +kernel

def chainAfterSourcePiece6 : String × List Token := ("                return;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .punctuation [';']])
theorem chainAfterSourcePiece6_lex : chainAfterSourcePiece6.1.toList.foldl step initial = completed chainAfterSourcePiece6.2 := by
  decide +kernel

def chainAfterSourcePiece7 : String × List Token := ("            }", [.punctuation ['}']])
theorem chainAfterSourcePiece7_lex : chainAfterSourcePiece7.1.toList.foldl step initial = completed chainAfterSourcePiece7.2 := by
  decide +kernel

def chainAfterSourcePieces : List (String × List Token) := [chainAfterSourcePiece0, chainAfterSourcePiece1, chainAfterSourcePiece2, chainAfterSourcePiece3, chainAfterSourcePiece4, chainAfterSourcePiece5, chainAfterSourcePiece6, chainAfterSourcePiece7]
def chainAfterSource : String := String.join (chainAfterSourcePieces.map Prod.fst)
def chainAfterSourceTokens : List Token := chainAfterSourcePieces.flatMap Prod.snd
theorem chainAfterSource_lex : lex chainAfterSource.toList = .ok chainAfterSourceTokens := by
  apply lex_completed_string_pieces
  simp only [chainAfterSourcePieces, List.forall_cons]
  exact ⟨chainAfterSourcePiece0_lex, chainAfterSourcePiece1_lex, chainAfterSourcePiece2_lex, chainAfterSourcePiece3_lex, chainAfterSourcePiece4_lex, chainAfterSourcePiece5_lex, chainAfterSourcePiece6_lex, chainAfterSourcePiece7_lex, trivial⟩

def returnSourcePiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem returnSourcePiece0_lex : returnSourcePiece0.1.toList.foldl step initial = completed returnSourcePiece0.2 := by
  decide +kernel

def returnSourcePiece1 : String × List Token := ("                outcome_set_add(os, result->expr.elems[1], &item->env);\n", [.identifier ['o', 'u', 't', 'c', 'o', 'm', 'e', '_', 's', 'e', 't', '_', 'a', 'd', 'd'], .punctuation ['('], .identifier ['o', 's'], .punctuation [','], .identifier ['r', 'e', 's', 'u', 'l', 't'], .punctuation ['-', '>'], .identifier ['e', 'x', 'p', 'r'], .punctuation ['.'], .identifier ['e', 'l', 'e', 'm', 's'], .punctuation ['['], .number ['1'], .punctuation [']'], .punctuation [','], .punctuation ['&'], .identifier ['i', 't', 'e', 'm'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [')'], .punctuation [';']])
theorem returnSourcePiece1_lex : returnSourcePiece1.1.toList.foldl step initial = completed returnSourcePiece1.2 := by
  decide +kernel

def returnSourcePiece2 : String × List Token := ("            }", [.punctuation ['}']])
theorem returnSourcePiece2_lex : returnSourcePiece2.1.toList.foldl step initial = completed returnSourcePiece2.2 := by
  decide +kernel

def returnSourcePieces : List (String × List Token) := [returnSourcePiece0, returnSourcePiece1, returnSourcePiece2]
def returnSource : String := String.join (returnSourcePieces.map Prod.fst)
def returnSourceTokens : List Token := returnSourcePieces.flatMap Prod.snd
theorem returnSource_lex : lex returnSource.toList = .ok returnSourceTokens := by
  apply lex_completed_string_pieces
  simp only [returnSourcePieces, List.forall_cons]
  exact ⟨returnSourcePiece0_lex, returnSourcePiece1_lex, returnSourcePiece2_lex, trivial⟩

def functionEntrySourcePiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem functionEntrySourcePiece0_lex : functionEntrySourcePiece0.1.toList.foldl step initial = completed functionEntrySourcePiece0.2 := by
  decide +kernel

def functionEntrySourcePiece1 : String × List Token := ("            frame->phase = HE_INSTRUCTION_FUNCTION;\n", [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['p', 'h', 'a', 's', 'e'], .punctuation ['='], .identifier ['H', 'E', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', '_', 'F', 'U', 'N', 'C', 'T', 'I', 'O', 'N'], .punctuation [';']])
theorem functionEntrySourcePiece1_lex : functionEntrySourcePiece1.1.toList.foldl step initial = completed functionEntrySourcePiece1.2 := by
  decide +kernel

def functionEntrySourcePiece2 : String × List Token := ("            /* He-compat steps the body. Embedded operations run; a return\n             * expression stays data until function_ret unwraps its payload.\n             * Any other body is not evaluated. */\n", [])
theorem functionEntrySourcePiece2_lex : functionEntrySourcePiece2.1.toList.foldl step initial = completed functionEntrySourcePiece2.2 := by
  decide +kernel

def functionEntrySourcePiece3 : String × List Token := ("            bool step = active_profile_uses_rust_he_compat_semantics() ||\n", [.identifier ['b', 'o', 'o', 'l'], .identifier ['s', 't', 'e', 'p'], .punctuation ['='], .identifier ['a', 'c', 't', 'i', 'v', 'e', '_', 'p', 'r', 'o', 'f', 'i', 'l', 'e', '_', 'u', 's', 'e', 's', '_', 'r', 'u', 's', 't', '_', 'h', 'e', '_', 'c', 'o', 'm', 'p', 'a', 't', '_', 's', 'e', 'm', 'a', 'n', 't', 'i', 'c', 's'], .punctuation ['('], .punctuation [')'], .punctuation ['|', '|']])
theorem functionEntrySourcePiece3_lex : functionEntrySourcePiece3.1.toList.foldl step initial = completed functionEntrySourcePiece3.2 := by
  decide +kernel

def functionEntrySourcePiece4 : String × List Token := ("                he_minimal_instruction(body) ||\n", [.identifier ['h', 'e', '_', 'm', 'i', 'n', 'i', 'm', 'a', 'l', '_', 'i', 'n', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n'], .punctuation ['('], .identifier ['b', 'o', 'd', 'y'], .punctuation [')'], .punctuation ['|', '|']])
theorem functionEntrySourcePiece4_lex : functionEntrySourcePiece4.1.toList.foldl step initial = completed functionEntrySourcePiece4.2 := by
  decide +kernel

def functionEntrySourcePiece5 : String × List Token := ("                atom_head_symbol_id(body) == g_builtin_syms.return_text;\n", [.identifier ['a', 't', 'o', 'm', '_', 'h', 'e', 'a', 'd', '_', 's', 'y', 'm', 'b', 'o', 'l', '_', 'i', 'd'], .punctuation ['('], .identifier ['b', 'o', 'd', 'y'], .punctuation [')'], .punctuation ['=', '='], .identifier ['g', '_', 'b', 'u', 'i', 'l', 't', 'i', 'n', '_', 's', 'y', 'm', 's'], .punctuation ['.'], .identifier ['r', 'e', 't', 'u', 'r', 'n', '_', 't', 'e', 'x', 't'], .punctuation [';']])
theorem functionEntrySourcePiece5_lex : functionEntrySourcePiece5.1.toList.foldl step initial = completed functionEntrySourcePiece5.2 := by
  decide +kernel

def functionEntrySourcePiece6 : String × List Token := ("            if (step)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['s', 't', 'e', 'p'], .punctuation [')']])
theorem functionEntrySourcePiece6_lex : functionEntrySourcePiece6.1.toList.foldl step initial = completed functionEntrySourcePiece6.2 := by
  decide +kernel

def functionEntrySourcePiece7 : String × List Token := ("                he_instruction_push(stack, HE_INSTRUCTION_RUN, s, a,\n", [.identifier ['h', 'e', '_', 'i', 'n', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n', '_', 'p', 'u', 's', 'h'], .punctuation ['('], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation [','], .identifier ['H', 'E', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', '_', 'R', 'U', 'N'], .punctuation [','], .identifier ['s'], .punctuation [','], .identifier ['a'], .punctuation [',']])
theorem functionEntrySourcePiece7_lex : functionEntrySourcePiece7.1.toList.foldl step initial = completed functionEntrySourcePiece7.2 := by
  decide +kernel

def functionEntrySourcePiece8 : String × List Token := ("                    body, child_fuel, &frame->env, &frame->inner);\n", [.identifier ['b', 'o', 'd', 'y'], .punctuation [','], .identifier ['c', 'h', 'i', 'l', 'd', '_', 'f', 'u', 'e', 'l'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['i', 'n', 'n', 'e', 'r'], .punctuation [')'], .punctuation [';']])
theorem functionEntrySourcePiece8_lex : functionEntrySourcePiece8.1.toList.foldl step initial = completed functionEntrySourcePiece8.2 := by
  decide +kernel

def functionEntrySourcePiece9 : String × List Token := ("            else\n", [.identifier ['e', 'l', 's', 'e']])
theorem functionEntrySourcePiece9_lex : functionEntrySourcePiece9.1.toList.foldl step initial = completed functionEntrySourcePiece9.2 := by
  decide +kernel

def functionEntrySourcePiece10 : String × List Token := ("                eval_for_caller(s, a, NULL, body, child_fuel,\n", [.identifier ['e', 'v', 'a', 'l', '_', 'f', 'o', 'r', '_', 'c', 'a', 'l', 'l', 'e', 'r'], .punctuation ['('], .identifier ['s'], .punctuation [','], .identifier ['a'], .punctuation [','], .identifier ['N', 'U', 'L', 'L'], .punctuation [','], .identifier ['b', 'o', 'd', 'y'], .punctuation [','], .identifier ['c', 'h', 'i', 'l', 'd', '_', 'f', 'u', 'e', 'l'], .punctuation [',']])
theorem functionEntrySourcePiece10_lex : functionEntrySourcePiece10.1.toList.foldl step initial = completed functionEntrySourcePiece10.2 := by
  decide +kernel

def functionEntrySourcePiece11 : String × List Token := ("                    &frame->env, true, &frame->inner);\n", [.punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .identifier ['t', 'r', 'u', 'e'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['i', 'n', 'n', 'e', 'r'], .punctuation [')'], .punctuation [';']])
theorem functionEntrySourcePiece11_lex : functionEntrySourcePiece11.1.toList.foldl step initial = completed functionEntrySourcePiece11.2 := by
  decide +kernel

def functionEntrySourcePiece12 : String × List Token := ("        }", [.punctuation ['}']])
theorem functionEntrySourcePiece12_lex : functionEntrySourcePiece12.1.toList.foldl step initial = completed functionEntrySourcePiece12.2 := by
  decide +kernel

def functionEntrySourcePieces : List (String × List Token) := [functionEntrySourcePiece0, functionEntrySourcePiece1, functionEntrySourcePiece2, functionEntrySourcePiece3, functionEntrySourcePiece4, functionEntrySourcePiece5, functionEntrySourcePiece6, functionEntrySourcePiece7, functionEntrySourcePiece8, functionEntrySourcePiece9, functionEntrySourcePiece10, functionEntrySourcePiece11, functionEntrySourcePiece12]

def functionEntrySource : String := String.join (functionEntrySourcePieces.map Prod.fst)
def functionEntrySourceTokens : List Token := functionEntrySourcePieces.flatMap Prod.snd
theorem functionEntrySource_lex : lex functionEntrySource.toList = .ok functionEntrySourceTokens := by
  apply lex_completed_string_pieces
  simp only [functionEntrySourcePieces, List.forall_cons]
  exact ⟨functionEntrySourcePiece0_lex, functionEntrySourcePiece1_lex, functionEntrySourcePiece2_lex, functionEntrySourcePiece3_lex, functionEntrySourcePiece4_lex, functionEntrySourcePiece5_lex, functionEntrySourcePiece6_lex, functionEntrySourcePiece7_lex, functionEntrySourcePiece8_lex, functionEntrySourcePiece9_lex, functionEntrySourcePiece10_lex, functionEntrySourcePiece11_lex, functionEntrySourcePiece12_lex, trivial⟩

def functionBodyReadSourcePiece : String × List Token := ("Atom *body = expr_arg(atom, 0);", [.identifier ['A', 't', 'o', 'm'], .punctuation ['*'], .identifier ['b', 'o', 'd', 'y'], .punctuation ['='], .identifier ['e', 'x', 'p', 'r', '_', 'a', 'r', 'g'], .punctuation ['('], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .number ['0'], .punctuation [')'], .punctuation [';']])
theorem functionBodyReadSourcePiece_lex : functionBodyReadSourcePiece.1.toList.foldl step initial = completed functionBodyReadSourcePiece.2 := by
  decide +kernel

def functionBodyGuardSourcePiece : String × List Token := ("body->kind != ATOM_EXPR", [.identifier ['b', 'o', 'd', 'y'], .punctuation ['-', '>'], .identifier ['k', 'i', 'n', 'd'], .punctuation ['!', '='], .identifier ['A', 'T', 'O', 'M', '_', 'E', 'X', 'P', 'R']])
theorem functionBodyGuardSourcePiece_lex :
    lex functionBodyGuardSourcePiece.1.toList = .ok functionBodyGuardSourcePiece.2 := by
  decide +kernel

theorem function_body_read_parsed :
    blockText? types ("{" ++ functionBodyReadSourcePiece.1 ++ "}").toList =
      some [functionBodyRead] := by
  let pieces : List (String × List Token) :=
    [("{", [.punctuation ['{']]), functionBodyReadSourcePiece, ("}", [.punctuation ['}']])]
  have scanned : lex (String.join (pieces.map Prod.fst)).toList =
      .ok (pieces.flatMap Prod.snd) := by
    apply lex_completed_string_pieces
    simp only [pieces, List.forall_cons]
    exact ⟨by decide +kernel, functionBodyReadSourcePiece_lex, by decide +kernel, trivial⟩
  exact block_text_of_parts types _ (pieces.flatMap Prod.snd) [functionBodyRead]
    scanned (by rfl)

theorem function_body_guard_parsed :
    expressionText? types functionBodyGuardSourcePiece.1.toList = some functionBodyGuard := by
  unfold expressionText?
  rw [functionBodyGuardSourcePiece_lex]
  change completeExpression? types functionBodyGuardSourcePiece.2 = some functionBodyGuard
  rfl

theorem chain_before_parsed : blockText? types chainBeforeSource.toList = some chainBefore := by
  exact block_text_of_parts types chainBeforeSource.toList chainBeforeSourceTokens chainBefore chainBeforeSource_lex (by rfl)

theorem chain_after_parsed : blockText? types chainAfterSource.toList = some chainAfter := by
  exact block_text_of_parts types chainAfterSource.toList chainAfterSourceTokens chainAfter chainAfterSource_lex (by rfl)

theorem return_parsed : blockText? types returnSource.toList = some returned := by
  exact block_text_of_parts types returnSource.toList returnSourceTokens returned returnSource_lex (by rfl)

theorem function_entry_parsed : blockText? types functionEntrySource.toList = some functionEntry := by
  exact block_text_of_parts types functionEntrySource.toList functionEntrySourceTokens functionEntry
    functionEntrySource_lex (by rfl)

inductive Kind where
  | run | raw
  deriving DecidableEq, Repr

inductive Phase where
  | enter | done | chain | function | collapse | rawReturns
  deriving DecidableEq, Repr

/-- Logical fields read from one native instruction frame. Arena and target
identities are opaque; this structure asserts no physical heap realization. -/
structure Frame where
  kind : Kind
  phase : Phase
  space : Space
  arena : Nat
  atom : Atom
  env : Bindings
  inner : ResultSet
  index : Nat
  fuel : Int
  target : Nat
  /-- Opaque identity of this frame's retained outcome collection. -/
  innerTarget : Nat := 0

/-- The selected outcome has already advanced the parent's cursor. `stack`
is the complete instruction stack, with the current frame at its head before
a local push and the new child above it afterward. -/
structure LocalState where
  frame : Frame
  selected : ResultPair
  materialized : Atom
  locals : List (Name × Atom) := []
  stack : List Frame
  publications : List (Nat × ResultPair)
  returned : Bool := false
  /-- Identity supplied by the actual child-frame allocation. -/
  freshInnerTarget : Nat := 0
  /-- The flag read from the selected native profile; no default-profile claim. -/
  nativeCompatibility : Bool := false
  boolLocals : List (Name × Bool) := []

abbrev Materializer := Bindings → Atom → Atom

def childFuel (fuel : Int) : Int := if 0 < fuel then fuel - 1 else fuel

def isIdentifier (expression : CExpr) (name : String) : Bool :=
  match expression with
  | .identifier actual => actual == name.toList
  | _ => false

def atomArgument? (atom : Atom) (index : Nat) : Option Atom :=
  match atom with
  | .expression atoms => atoms[index + 1]?
  | _ => none

def bindingOperand? (state : LocalState) : CExpr → Option Bindings
  | .unary .address (.field (.identifier owner) member true) =>
      if member = "env".toList then
        if owner = "item".toList then some state.selected.2
        else if owner = "frame".toList then some state.frame.env else none
      else none
  | _ => none

def atomOperand? (materialize : Materializer) (state : LocalState) : CExpr → Option Atom
  | .identifier name =>
      if name = "result".toList then some state.materialized
      else if name = "atom".toList then some state.frame.atom
      else (state.locals.find? (fun entry => entry.1 == name)).map Prod.snd
  | .field (.identifier owner) member true =>
      if owner = "frame".toList ∧ member = "atom".toList then some state.frame.atom else none
  | .index (.field (.field base expr true) elems false) (.decimal index) => do
      if expr != "expr".toList || elems != "elems".toList then none else
        match ← atomOperand? materialize state base with
        | .expression atoms => atoms[index]?
        | _ => none
  | .call name [base, .decimal index] =>
      if name = "expr_arg".toList then
        (atomOperand? materialize state base).bind (fun atom => atomArgument? atom index)
      else none
  | .call name [bindings, arena, template] => do
      if name != "bindings_apply_if_vars".toList || !isIdentifier arena "a" then none else
        let bindings ← bindingOperand? state bindings
        let template ← atomOperand? materialize state template
        some (materialize bindings template)
  | .call name [arena, template, .field binder member true, replacement] => do
      if name != "instantiate_template_variable_once".toList ||
          !isIdentifier arena "a" || member != "var_id".toList then none else
        let template ← atomOperand? materialize state template
        let binder ← atomOperand? materialize state binder
        let replacement ← atomOperand? materialize state replacement
        match binder with
        | .var name => some (substituteName name replacement template)
        | _ => none
  | _ => none

def setLocal (state : LocalState) (name : Name) (value : Atom) : LocalState :=
  { state with locals := (name, value) :: state.locals.filter (fun entry => entry.1 != name) }

def setBoolLocal (state : LocalState) (name : Name) (value : Bool) : LocalState :=
  { state with boolLocals := (name, value) :: state.boolLocals.filter (fun entry => entry.1 != name) }

def expressionAtom (atom : Atom) : Bool :=
  match atom with
  | .expression _ => true
  | _ => false

/-- The selected source helper recognizes these exact instruction heads.
Its concrete symbol-table representation is a separate native readback law. -/
def minimalHead (atom : Atom) : Bool :=
  match atom with
  | .expression (.symbol head :: _) =>
      head ∈ ["eval", "evalc", "chain", "function", "unify", "metta", "context-space",
        "call-native", "cons-atom", "decons-atom", "collapse-bind", "superpose-bind"]
  | _ => false

def returnHead (atom : Atom) : Bool :=
  match atom with
  | .expression (.symbol head :: _) => head == "return"
  | _ => false

def condition? (materialize : Materializer) (state : LocalState) : CExpr → Option Bool
  | .bool value => some value
  | .identifier name => (state.boolLocals.find? (fun entry => entry.1 == name)).map Prod.snd
  | .unary .not operand => (condition? materialize state operand).map Bool.not
  | .binary .and left right => do
      let first ← condition? materialize state left
      if first then condition? materialize state right else some false
  | .binary .or left right => do
      let first ← condition? materialize state left
      if first then some true else condition? materialize state right
  | .call name [] =>
      if name = "active_profile_uses_rust_he_compat_semantics".toList then
        some state.nativeCompatibility else none
  | .call name [value] =>
      if name = "he_minimal_instruction".toList then
        (atomOperand? materialize state value).map minimalHead else none
  | .binary .eq (.call name [value]) (.field (.identifier owner) member false) =>
      if name = "atom_head_symbol_id".toList ∧ owner = "g_builtin_syms".toList ∧
          member = "return_text".toList then
        (atomOperand? materialize state value).map returnHead else none
  | .binary .ne (.call name [value]) (.field (.identifier owner) member false) =>
      if name = "atom_head_symbol_id".toList ∧ owner = "g_builtin_syms".toList ∧
          member = "return_text".toList then
        (atomOperand? materialize state value).map (fun atom => !(returnHead atom)) else none
  | .binary .ne (.field base member true) (.identifier tag) =>
      if member = "kind".toList ∧ tag = "ATOM_EXPR".toList then
        (atomOperand? materialize state base).map (fun atom => !(expressionAtom atom)) else none
  | _ => none

def targetOperand? (state : LocalState) : CExpr → Option Nat
  | .identifier name => if name = "os".toList then some state.frame.target else none
  | .unary .address (.field (.identifier owner) member true) =>
      if owner = "frame".toList ∧ member = "inner".toList then some state.frame.innerTarget else none
  | _ => none

def phaseOperand? : CExpr → Option Phase
  | .identifier name =>
      if name = "HE_INSTRUCTION_FUNCTION".toList then some .function
      else if name = "HE_INSTRUCTION_CHAIN".toList then some .chain
      else if name = "HE_INSTRUCTION_COLLAPSE".toList then some .collapse
      else none
  | _ => none

def setPhase? (state : LocalState) (phase : Phase) : Option LocalState :=
  match state.stack with
  | [] => none
  | first :: rest =>
      let current : Frame := { state.frame with phase := phase }
      let head : Frame := { first with phase := phase }
      some { state with frame := current, stack := head :: rest }

/-! Checked partial projection of selected parsed statement blocks. Supported
calls use explicit mathematical helper contracts; other syntax is outside
this projection. This is not general NativeOps or ISO C execution. -/
mutual
def executeStatement? (materialize : Materializer) (state : LocalState) :
    CStatement → Option LocalState
  | .declare type name value => do
      if type = ⟨"Atom".toList, 1⟩ then
        some (setLocal state name (← atomOperand? materialize state value))
      else if type = ⟨"bool".toList, 0⟩ then
        some (setBoolLocal state name (← condition? materialize state value))
      else none
  | .assign (.field (.identifier owner) member true) value => do
      if owner != "frame".toList || member != "phase".toList then none else
        setPhase? state (← phaseOperand? value)
  | .assign (.identifier name) value =>
      (atomOperand? materialize state value).map (setLocal state name)
  | .effect (.call name [stack, kind, space, arena, value, fuel, bindings, target]) => do
      if name != "he_instruction_push".toList || !isIdentifier stack "stack" ||
          !isIdentifier kind "HE_INSTRUCTION_RUN" || !isIdentifier space "s" ||
          !isIdentifier arena "a" || !isIdentifier fuel "child_fuel" then none else
        let atom ← atomOperand? materialize state value
        let env ← bindingOperand? state bindings
        let target ← targetOperand? state target
        let child : Frame := ⟨.run, .enter, state.frame.space, state.frame.arena, atom,
          env, [], 0, childFuel state.frame.fuel, target, state.freshInnerTarget⟩
        some { state with stack := child :: state.stack }
  | .effect (.call name [target, value, bindings]) => do
      if name != "outcome_set_add".toList || !isIdentifier target "os" then none else
        let value ← atomOperand? materialize state value
        let bindings ← bindingOperand? state bindings
        some { state with publications := state.publications ++ [(state.frame.target, (value, bindings))] }
  | .branch condition whenTrue whenFalse => do
      let selected ← condition? materialize state condition
      if selected then executeBlock? materialize state whenTrue
      else executeBlock? materialize state whenFalse
  | .return none => some { state with returned := true }
  | _ => none

def executeBlock? (materialize : Materializer) (state : LocalState) :
    List CStatement → Option LocalState
  | [] => some state
  | statement :: rest =>
      if state.returned then some state else
        (executeStatement? materialize state statement).bind (fun next => executeBlock? materialize next rest)

end

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Minimal
open Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- An actual push keeps the selected child's reached binding record and the
parent's target. The parent frame and pending suffix remain beneath it. -/
def childFrame (state : LocalState) (body : Atom) (bindings : Bindings) : Frame :=
  ⟨.run, .enter, state.frame.space, state.frame.arena, body, bindings, [], 0,
    childFuel state.frame.fuel, state.frame.target, state.freshInnerTarget⟩

def afterChain (state : LocalState) (body : Atom) : LocalState :=
  { setLocal state "body".toList body with
    stack := childFrame state body state.selected.2 :: state.stack
    returned := true }

theorem execute_chain_after (materialize : Materializer) (state : LocalState)
    (nested : Atom) (binder : String) (template : Atom)
    (shape : state.frame.atom = .expression [.symbol "chain", nested, .var binder, template])
    (running : state.returned = false) :
    executeBlock? materialize state chainAfter =
      some (afterChain state (substituteName binder state.materialized template)) := by
  simp [executeBlock?, executeStatement?, chainAfter, substitution, savedTemplate, savedBinder,
    pushBody, frameAtom, itemEnv, atomOperand?, bindingOperand?, targetOperand?, isIdentifier,
    atomArgument?, setLocal, shape, running, afterChain, childFrame]

theorem execute_chain_before (materialize : Materializer) (state : LocalState)
    (nested : Atom) (binder : String) (template : Atom)
    (shape : state.frame.atom = .expression [.symbol "chain", nested, .var binder, template])
    (running : state.returned = false) :
    executeBlock? materialize state chainBefore =
      some (afterChain state
        (substituteName binder state.materialized (materialize state.selected.2 template))) := by
  simp [executeBlock?, executeStatement?, chainBefore, substitution, savedTemplate, savedBinder,
    pushBody, frameAtom, itemEnv, atomOperand?, bindingOperand?, targetOperand?, isIdentifier,
    atomArgument?, setLocal, shape, running, afterChain, childFrame]

theorem execute_return (materialize : Materializer) (state : LocalState) (value : Atom)
    (shape : state.materialized = .expression [.symbol "return", value])
    (running : state.returned = false) :
    executeBlock? materialize state returned = some { state with
      publications := state.publications ++ [(state.frame.target, (value, state.selected.2))] } := by
  simp [executeBlock?, executeStatement?, returned, atomOperand?, bindingOperand?,
    isIdentifier, itemEnv, shape, running]

/-- The loop increments its cursor before dispatching the selected outcome.
An exhausted child list has no selected branch; it is not an empty outcome. -/
def selectedState? (materialize : Materializer) (frame : Frame) (parents : List Frame)
    (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat) : Option LocalState := do
  let selected ← frame.inner[frame.index]?
  let advanced := { frame with index := frame.index + 1 }
  some ⟨advanced, selected, materialize selected.2 selected.1, [],
    advanced :: parents, publications, false, freshInnerTarget, false, []⟩

def resumeChain? (materialize : Materializer) (frame : Frame) (parents : List Frame)
    (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat)
    (unwinding : Bool := false) : Option LocalState := do
  if unwinding || frame.phase != .chain then none else
    let state ← selectedState? materialize frame parents publications freshInnerTarget
    executeBlock? materialize state chainAfter

theorem resume_chain_exact (materialize : Materializer) (frame : Frame)
    (parents : List Frame) (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat)
    (nested : Atom) (binder : String) (template : Atom) (selected : ResultPair)
    (phase : frame.phase = .chain)
    (shape : frame.atom = .expression [.symbol "chain", nested, .var binder, template])
    (present : frame.inner[frame.index]? = some selected) :
    let advanced := { frame with index := frame.index + 1 }
    let state : LocalState := ⟨advanced, selected, materialize selected.2 selected.1, [],
      advanced :: parents, publications, false, freshInnerTarget, false, []⟩
    resumeChain? materialize frame parents publications freshInnerTarget =
      some (afterChain state (substituteName binder state.materialized template)) := by
  have gate : (frame.phase != Phase.chain) = false := by simp [phase]
  have executed := execute_chain_after materialize
    (⟨{ frame with index := frame.index + 1 }, selected,
      materialize selected.2 selected.1, [], { frame with index := frame.index + 1 } :: parents,
      publications, false, freshInnerTarget, false, []⟩ : LocalState) nested binder template shape rfl
  simpa [resumeChain?, gate, selectedState?, present] using executed

/-- The selected C continuation constructs the same source step from the
independent child derivation and independent materialization witness. Neither
an empty caller nor a fixed saved template is required. -/
theorem chain_source_step (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (typing : EvalTypeService) (live : List Atom) (caller : Option Atom)
    (nested : Atom) (binder : String) (template : Atom) (incoming : BindingFrame)
    (selected : FrameResult) (value : Atom)
    (child : CoreRunRel space dispatch
      (.expression [.symbol "chain", nested, .var binder, template] :: live)
      nested incoming selected (typing := typing)
      (caller := some (.expression [.symbol "chain", nested, .var binder, template])))
    (materialized : selected.2.Materialization selected.1 value) :
    CoreStepRel space dispatch live (typing := typing) (caller := caller)
      (.expression [.symbol "chain", nested, .var binder, template]) incoming
      (substituteName binder value template, selected.2) :=
  .chain space nested binder template incoming selected value child materialized

/-- Completing the constructed child joins to the existing independent run
relation. This is a local continuation theorem, not a native-C adequacy axiom. -/
theorem chain_source_completed (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (typing : EvalTypeService) (live : List Atom) (caller : Option Atom)
    (nested : Atom) (binder : String) (template : Atom) (incoming : BindingFrame)
    (selected result : FrameResult) (value : Atom)
    (child : CoreRunRel space dispatch
      (.expression [.symbol "chain", nested, .var binder, template] :: live)
      nested incoming selected (typing := typing)
      (caller := some (.expression [.symbol "chain", nested, .var binder, template])))
    (materialized : selected.2.Materialization selected.1 value)
    (continuation : CoreRunRel space dispatch live (typing := typing) (caller := caller)
      (substituteName binder value template) selected.2 result) :
    CoreRunRel space dispatch live (typing := typing) (caller := caller)
      (.expression [.symbol "chain", nested, .var binder, template]) incoming result := by
  exact .chain space _ incoming _ result ⟨_, rfl⟩
    (chain_source_step space dispatch typing live caller nested binder template incoming
      selected value child materialized) continuation

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl

/-! Logical readback of CeTTa's completed minimal-instruction collector.
The child-completion boundary is separate from the array scan. -/
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Minimal

/-- Materialization may return no atom. Its absence is distinct from the
binding snapshot, which remains present for every physical array row. -/
structure MaterializedOutcome where
  value : Option Atom
  bindings : Bindings
  deriving DecidableEq, Repr

def MaterializedOutcome.kept (row : MaterializedOutcome) : Option ResultPair :=
  match row.value with
  | none => none
  | some value => if value == Atom.empty then none else some (value, row.bindings)

/-- The independent array observer preserves every surviving physical row. -/
def results (rows : List MaterializedOutcome) : ResultSet :=
  rows.filterMap MaterializedOutcome.kept

/-- The collector's array loop, including its existing prefix of pair cells. -/
def scan (services : Services) : List MaterializedOutcome → List Atom → List Atom
  | [], pairs => pairs
  | row :: rest, pairs =>
      match row.kept with
      | none => scan services rest pairs
      | some result => scan services rest (pairs ++ [encodeResult services result])

theorem scan_exact (services : Services) (rows : List MaterializedOutcome)
    (pairs : List Atom) :
    scan services rows pairs = pairs ++ (results rows).map (encodeResult services) := by
  induction rows generalizing pairs with
  | nil => simp [scan, results]
  | cons row rows ih =>
      cases found : row.kept <;> simp [scan, results, found, ih, List.append_assoc]

def pack (services : Services) (rows : List MaterializedOutcome) : Atom :=
  .expression (scan services rows [])

theorem pack_exact (services : Services) (rows : List MaterializedOutcome) :
    pack services rows = encodeResults services (results rows) := by
  simp [pack, scan_exact, encodeResults]

/-- Reordering child alternatives transports to a permutation of the collected
occurrences; it does not erase multiplicity or choose one global MeTTa order. -/
theorem results_perm {left right : List MaterializedOutcome} (permutation : left.Perm right) :
    (results left).Perm (results right) :=
  permutation.filterMap MaterializedOutcome.kept

theorem scan_perm (services : Services) {left right : List MaterializedOutcome}
    (permutation : (results left).Perm (results right)) :
    (scan services left []).Perm (scan services right []) := by
  simpa only [scan_exact, List.nil_append] using permutation.map (encodeResult services)

theorem scan_prefix (services : Services) (rows : List MaterializedOutcome)
    (pairs : List Atom) : pairs.IsPrefix (scan services rows pairs) := by
  rw [scan_exact]
  exact List.prefix_append _ _

theorem scan_length (services : Services) (rows : List MaterializedOutcome)
    (pairs : List Atom) :
    (scan services rows pairs).length = pairs.length + (results rows).length := by
  simp [scan_exact]

theorem kept_nonempty (rows : List MaterializedOutcome) (pair : ResultPair)
    (member : pair ∈ results rows) : pair.1 ≠ Atom.empty := by
  simp only [results, List.mem_filterMap] at member
  obtain ⟨row, _, kept⟩ := member
  rcases row with ⟨value, bindings⟩
  cases value with
  | none => simp [MaterializedOutcome.kept] at kept
  | some value =>
      simp only [MaterializedOutcome.kept] at kept
      split at kept
      · cases kept
      · cases kept
        simpa using ‹¬ (value == Atom.empty) = true›

theorem encodeResult_injective (services : Services) (laws : ServiceLaws services) :
    Function.Injective (encodeResult services) := by
  rintro ⟨left, leftBindings⟩ ⟨right, rightBindings⟩ equal
  simp only [encodeResult, Atom.expression.injEq, List.cons.injEq,
    Atom.grounded.injEq, and_true] at equal
  exact Prod.ext equal.1 (laws.bindingPayload_injective equal.2)

theorem pack_eq_iff (services : Services) (laws : ServiceLaws services)
    (left right : List MaterializedOutcome) :
    pack services left = pack services right ↔ results left = results right := by
  simp only [pack_exact, encodeResults, Atom.expression.injEq]
  exact (List.map_injective_iff.mpr (encodeResult_injective services laws)).eq_iff

/-- List equality here observes occurrences and bindings; equal values are
not deduplicated by the encoding. -/
theorem duplicate_retained (services : Services) (value : Atom) (bindings : Bindings)
    (nonempty : value ≠ Atom.empty) :
    pack services [⟨some value, bindings⟩, ⟨some value, bindings⟩] =
      .expression [encodeResult services (value, bindings),
        encodeResult services (value, bindings)] := by
  simp [pack_exact, results, MaterializedOutcome.kept, nonempty, encodeResults]

/-- This local closing square uses an independently supplied *complete*
child enumeration. Mere support or a partial child prefix is insufficient. -/
theorem completed_core_step (services : Services) (enumeration : Enumeration)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (space : Space) (body : Atom) (caller : Bindings) (rows : List MaterializedOutcome)
    (host : dispatch.minimal = some ⟨services, enumeration⟩)
    (child : enumeration.minimalResults space body caller (results rows)) :
    CoreStepRel space dispatch live (typing := typing)
      (.expression [.symbol "collapse-bind", body]) caller
      (pack services rows, caller) := by
  rw [pack_exact]
  exact .collapseBind space body caller (results rows) services enumeration host rfl child

/-- The existing may-level law checks support, while the collector's list
itself continues to supply the additional order and multiplicity observation. -/
theorem completed_support (services : Services) (enumeration : Enumeration)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (laws : MinimalEnumerationLaws services dispatch live typing enumeration)
    (space : Space) (body : Atom) (caller : Bindings) (rows : List MaterializedOutcome)
    (child : enumeration.minimalResults space body caller (results rows))
    (pair : ResultPair) :
    pair ∈ results rows ↔
      MinimalResultRel services dispatch live typing enumeration space body caller pair :=
  laws.support_exact space body caller (results rows) child pair

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Spec.Eval Spec.Eval.Minimal

/-- A completed child owns its reached world and full outcome array. -/
structure Completed (World : Type) where
  world : World
  rows : List MaterializedOutcome
  deriving DecidableEq, Repr

/-- The caller parameter is the complete saved instruction frame, including
its delivery target and any surrounding continuation. -/
inductive Parent (Caller World Failure : Type) where
  | enter (caller : Caller)
  | waiting (caller : Caller)
  | returned (caller : Caller) (reply : Reply (Completed World) Failure)

inductive Event (Caller World Receipt Failure : Type) where
  | entered (caller : Caller)
  | child (receipt : Receipt)
  | replied (reply : Reply (Completed World) Failure)

/-- Closing a collector is different from cancellation or a child's failure.
Neither stopped outcome carries a fabricated aggregate. -/
inductive Verdict (Caller World Failure : Type) where
  | aggregate (caller : Caller) (world : World) (result : ResultPair)
  | failed (caller : Caller) (failure : Failure)
  | cancelled (caller : Caller)

variable {Caller World Receipt Failure Child External : Type}

def Parent.caller : Parent Caller World Failure → Caller
  | .enter caller | .waiting caller | .returned caller _ => caller

def parent (services : Services) (bindings : Caller → Bindings) :
    Machine (Parent Caller World Failure) (Event Caller World Receipt Failure)
      (Verdict Caller World Failure) Caller where
  step
    | .enter caller => some (.call caller (.waiting caller))
    | .waiting _ => none
    | .returned caller (.returned done) =>
        some (.finish (.aggregate caller done.world (pack services done.rows, bindings caller)))
    | .returned caller (.faulted failure) => some (.finish (.failed caller failure))
    | .returned caller .cancelled => some (.finish (.cancelled caller))

def callback : Callback (Parent Caller World Failure)
    (Event Caller World Receipt Failure) Caller (Completed World) Failure where
  callEvent := Event.entered
  replyEvent := Event.replied
  resume saved reply := .returned saved.caller reply

def handled (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) :
    Machine (HandledState (Parent Caller World Failure) Child Caller)
      (Event Caller World Receipt Failure) (Verdict Caller World Failure) External :=
  (parent services bindings).handle callback
    (child.relabel Event.child id id) load

/-- A whole child configuration, rather than its already received answers,
is the retained service state. -/
def active (caller : Caller) (child : Child) :
    HandledState (Parent Caller World Failure) Child Caller :=
  .handling caller (.waiting caller) child

theorem before_reply (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (fuel : Nat) (caller : Caller) (state : Child)
    (events : List Receipt) (outcome : Outcome Child (Reply (Completed World) Failure) External)
    (ran : child.run fuel state = (events, outcome))
    (unfinished : ∀ reply, outcome ≠ .finished reply) :
    (handled services bindings child load).run fuel (active caller state) =
      (events.map Event.child,
        Machine.handlerOutcome (callback (Receipt := Receipt)) caller (.waiting caller) outcome) := by
  have lifted := child.run_relabel
    (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id fuel state
  rw [ran] at lifted
  have run' : (child.relabel
      (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id).run fuel state =
      (events.map Event.child, outcome) := by
    simpa only [Outcome.relabel_id] using lifted
  exact (parent services bindings).handle_run_of_no_reply callback
    (child.relabel Event.child id id) load fuel caller (.waiting caller)
      state _ outcome run' unfinished

theorem paused_child_exact (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (fuel : Nat) (caller : Caller) (state residual : Child)
    (events : List Receipt)
    (ran : child.run fuel state = (events, .exhausted residual)) :
    (handled services bindings child load).run fuel (active caller state) =
      (events.map Event.child, .exhausted (active caller residual)) := by
  exact before_reply services bindings child load fuel caller state events
    (.exhausted residual) ran (by intro reply; simp)

/-- Even an empty or duplicate-filled partial array cannot close the parent:
a completed reply, followed by the collector's own closing step, is required. -/
theorem complete_after_child (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (fuel : Nat) (caller : Caller) (state : Child)
    (events : List Receipt) (done : Completed World)
    (ran : child.run fuel state = (events, .finished (.returned done))) :
    ∃ used ≤ fuel + 1,
      (handled services bindings child load).run used (active caller state) =
        (events.map Event.child ++ [Event.replied (.returned done)],
          .finished (.aggregate caller done.world (pack services done.rows, bindings caller))) := by
  have lifted := child.run_relabel
    (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id fuel state
  rw [ran] at lifted
  obtain ⟨used, bound, reached⟩ := (parent services bindings).handle_run_of_reply callback
    (child.relabel Event.child id id) load fuel caller (.waiting caller) state
      (events.map Event.child) (.returned done) lifted
  refine ⟨used + 1, Nat.add_le_add_right bound 1, ?_⟩
  change (handled services bindings child load).run (used + 1)
    (.handling caller (.waiting caller) state) = _
  rw [Machine.run_add]
  change (handled services bindings child load).continueRun 1
    ((parent services bindings).handle callback (child.relabel Event.child id id) load |>.run used
      (.handling caller (.waiting caller) state)) = _
  rw [reached]
  simp [Machine.continueRun, Machine.run, handled, Machine.handle, parent, callback, Parent.caller]

/-- The same retained interface supplies exact scheduler resumption; this
law does not grant permission to restart a cancelled native owner. -/
theorem resume_after_prefix (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (first second : Nat)
    (state residual : HandledState (Parent Caller World Failure) Child Caller)
    (events : List (Event Caller World Receipt Failure))
    (paused : (handled services bindings child load).run first state =
      (events, .exhausted residual)) :
    (handled services bindings child load).run (first + second) state =
      (events ++ ((handled services bindings child load).run second residual).1,
        ((handled services bindings child load).run second residual).2) :=
  (handled services bindings child load).established_and_pending first second state residual events paused

/-- A cancelled reply closes with its explicit interruption verdict. -/
theorem cancellation_no_aggregate (services : Services) (bindings : Caller → Bindings)
    (caller : Caller) :
    (parent (World := World) (Receipt := Receipt) (Failure := Failure) services bindings).step
      (.returned caller .cancelled) = some (.finish (.cancelled caller)) := rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse

/-! Logical state projection for the actual COLLAPSE continuation. The C
allocation, moving roots, materializer and array-memory interpretation remain
separate representation obligations; this is not a whole-C refinement. -/
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Spec.Eval Spec.Eval.Minimal

/-- Each raw child outcome keeps its own binding snapshot, even if its value
materializer returns no atom. -/
def projectedRows (materialize : ResultPair → Option Atom) (frame : Frame) :
    List MaterializedOutcome :=
  frame.inner.map fun row => ⟨materialize row, row.2⟩

/-- The current stack head owns closing. A child above its parent must return
before the parent can execute this phase. The returned flag prevents repeated
execution of the same local C return block. -/
def closeProjected? (services : Services) (materialize : ResultPair → Option Atom)
    (state : LocalState) : Option LocalState :=
  if state.returned then none else
    match state.stack with
    | [] => none
    | frame :: parents =>
        if frame.phase == .collapse then
          some { state with
            frame := frame
            stack := parents
            publications := state.publications ++
              [(frame.target, (pack services (projectedRows materialize frame), frame.env))],
            returned := true }
        else none

theorem close_current (services : Services) (materialize : ResultPair → Option Atom)
    (state : LocalState) (frame : Frame) (parents : List Frame)
    (active : state.returned = false) (current : state.stack = frame :: parents)
    (phase : frame.phase = .collapse) :
    closeProjected? services materialize state =
      some { state with
        frame := frame
        stack := parents
        publications := state.publications ++
          [(frame.target, (pack services (projectedRows materialize frame), frame.env))],
        returned := true } := by
  simp [closeProjected?, active, current, phase]

theorem active_child_not_closed (services : Services)
    (materialize : ResultPair → Option Atom) (state : LocalState)
    (child : Frame) (parents : List Frame)
    (current : state.stack = child :: parents) (phase : child.phase ≠ .collapse) :
    closeProjected? services materialize state = none := by
  simp [closeProjected?, current, phase]

theorem returned_not_replayed (services : Services)
    (materialize : ResultPair → Option Atom) (state : LocalState)
    (returned : state.returned = true) :
    closeProjected? services materialize state = none := by
  simp [closeProjected?, returned]

theorem closes_once (services : Services) (materialize : ResultPair → Option Atom)
    (state next : LocalState) (closed : closeProjected? services materialize state = some next) :
    closeProjected? services materialize next = none := by
  unfold closeProjected? at closed
  split at closed
  · cases closed
  · split at closed
    · cases closed
    · split at closed
      · cases closed
        exact returned_not_replayed services materialize _ rfl
      · cases closed

/-- Closing an inner collector restores its parent as the stack head; it
cannot also close that parent or publish to that parent's target. -/
theorem nested_close_one_frame (services : Services)
    (materialize : ResultPair → Option Atom) (state : LocalState)
    (child parent : Frame) (parents : List Frame)
    (active : state.returned = false)
    (current : state.stack = child :: parent :: parents)
    (phase : child.phase = .collapse) :
    ∃ next, closeProjected? services materialize state = some next ∧
      next.stack = parent :: parents ∧
      next.publications = state.publications ++
        [(child.target, (pack services (projectedRows materialize child), child.env))] := by
  refine ⟨_, close_current services materialize state child (parent :: parents) active current phase,
    rfl, rfl⟩

/-- The local native collector square consumes the independently enumerated
complete child list. It does not infer completeness from its current array. -/
theorem projected_core_step (services : Services) (enumeration : Enumeration)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (materialize : ResultPair → Option Atom) (frame : Frame) (body : Atom)
    (shape : frame.atom = .expression [.symbol "collapse-bind", body])
    (host : dispatch.minimal = some ⟨services, enumeration⟩)
    (child : enumeration.minimalResults frame.space body frame.env
      (results (projectedRows materialize frame))) :
    CoreStepRel frame.space dispatch live (typing := typing) frame.atom frame.env
      (pack services (projectedRows materialize frame), frame.env) := by
  rw [shape]
  exact completed_core_step services enumeration dispatch live typing frame.space body
    frame.env (projectedRows materialize frame) host child

/-- The common retained handler keeps the whole native caller projection and
all older frames, rather than rebuilding them from collected answers. -/
abbrev owner {World Receipt Failure Child External : Type}
    (services : Services)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Frame × List Frame → Child) :=
  handled services (fun caller : Frame × List Frame => caller.1.env) child load

/-- A retained child that has actually completed can close this exact frame.
The independent enumeration is a separate semantic boundary: the machine run
supplies its world and receipts, while the enumeration supplies the complete
source alternatives. Extra scheduler budget does not repeat the run. -/
theorem owner_completed_source {World Receipt Failure Child External : Type}
    (services : Services) (enumeration : Enumeration)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Frame × List Frame → Child)
    (frame : Frame) (parents : List Frame) (body : Atom)
    (state : Child) (fuel : Nat) (events : List Receipt) (done : Completed World)
    (ran : child.run fuel state = (events, .finished (.returned done)))
    (shape : frame.atom = .expression [.symbol "collapse-bind", body])
    (host : dispatch.minimal = some ⟨services, enumeration⟩)
    (enumerated : enumeration.minimalResults frame.space body frame.env (results done.rows)) :
    (∃ used ≤ fuel + 1, ∀ extra,
      (owner services child load).run (used + extra) (active (frame, parents) state) =
        (events.map Event.child ++ [Event.replied (.returned done)],
          .finished (.aggregate (frame, parents) done.world (pack services done.rows, frame.env)))) ∧
    CoreStepRel frame.space dispatch live (typing := typing) frame.atom frame.env
      (pack services done.rows, frame.env) := by
  constructor
  · obtain ⟨used, bound, closed⟩ := complete_after_child services
      (fun caller : Frame × List Frame => caller.1.env) child load fuel
      (frame, parents) state events done ran
    refine ⟨used, bound, fun extra => ?_⟩
    have stable := (owner services child load).run_stable used extra
      (active (frame, parents) state) (by
        intro residual
        rw [closed]
        simp)
    exact stable.trans closed
  · rw [shape]
    exact completed_core_step services enumeration dispatch live typing frame.space body
      frame.env done.rows host enumerated

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- The actual entry block changes the parent phase before pushing a child
whose destination is that parent's retained collection. -/
def entry : List CStatement :=
  [.assign (field (identifier "frame") "phase") (identifier "HE_INSTRUCTION_COLLAPSE"),
   .effect (call "he_instruction_push" [identifier "stack", identifier "HE_INSTRUCTION_RUN",
     identifier "s", identifier "a", call "expr_arg" [identifier "atom", .decimal 0],
     identifier "child_fuel", address (field (identifier "frame") "env"),
     address (field (identifier "frame") "inner")])]

def entrySource : String := "{\n        frame->phase = HE_INSTRUCTION_COLLAPSE;\n        he_instruction_push(stack, HE_INSTRUCTION_RUN, s, a,\n            expr_arg(atom, 0), child_fuel, &frame->env, &frame->inner);\n    }"

def entrySourceTokens : List Token := [.punctuation ['{'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['p', 'h', 'a', 's', 'e'], .punctuation ['='], .identifier ['H', 'E', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', '_', 'C', 'O', 'L', 'L', 'A', 'P', 'S', 'E'], .punctuation [';'], .identifier ['h', 'e', '_', 'i', 'n', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n', '_', 'p', 'u', 's', 'h'], .punctuation ['('], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation [','], .identifier ['H', 'E', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', '_', 'R', 'U', 'N'], .punctuation [','], .identifier ['s'], .punctuation [','], .identifier ['a'], .punctuation [','], .identifier ['e', 'x', 'p', 'r', '_', 'a', 'r', 'g'], .punctuation ['('], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .number ['0'], .punctuation [')'], .punctuation [','], .identifier ['c', 'h', 'i', 'l', 'd', '_', 'f', 'u', 'e', 'l'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['i', 'n', 'n', 'e', 'r'], .punctuation [')'], .punctuation [';'], .punctuation ['}']]

theorem entry_lexed : lex entrySource.toList = .ok entrySourceTokens := by
  decide +kernel

theorem entry_parsed : blockText? types entrySource.toList = some entry := by
  exact block_text_of_parts types entrySource.toList entrySourceTokens entry entry_lexed (by rfl)

/-- The native push keeps the complete caller and directs the new child's
results to its parent's collection, not to the parent's external destination. -/
theorem entry_executes (materialize : Materializer) (state : LocalState)
    (parents : List Frame) (body : Atom)
    (current : state.stack = state.frame :: parents)
    (active : state.returned = false)
    (shape : state.frame.atom = .expression [.symbol "collapse-bind", body]) :
    executeBlock? materialize state entry =
      some { state with
        frame := { state.frame with phase := .collapse }
        stack :=
          { kind := .run, phase := .enter, space := state.frame.space,
            arena := state.frame.arena, atom := body, env := state.frame.env,
            inner := [], index := 0, fuel := childFuel state.frame.fuel,
            target := state.frame.innerTarget, innerTarget := state.freshInnerTarget } ::
          { state.frame with phase := .collapse } :: parents } := by
  simp [entry, executeBlock?, executeStatement?, phaseOperand?, setPhase?,
    atomOperand?, atomArgument?, bindingOperand?, targetOperand?, isIdentifier,
    identifier, field, call, address, current, active, shape]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Spec.Eval Spec.Eval.Minimal

private def services : Services where
  bindingPayload bindings := .custom "Bindings" (reprStr bindings)
  contextPayload _ := .custom "Context" "test"
  nativeCall _ _ _ _ _ := False

private def original (caller : Nat) : Bindings :=
  ⟨[("caller", .grounded (.int caller))], []⟩
private def captured : Bindings := ⟨[("x", .symbol "A")], []⟩
private def rows : List MaterializedOutcome :=
  [⟨some (.symbol "token"), captured⟩, ⟨none, {}⟩,
   ⟨some Atom.empty, {}⟩, ⟨some (.symbol "token"), captured⟩]

/-- This control child commits before its retained administrative step. -/
private def child : Machine (Nat × Nat) Nat (Reply (Completed Nat) Empty) Empty where
  step state := some <| match state.1 with
    | 0 => .publish [state.2 + 1] (1, state.2 + 1)
    | 1 => .silent (2, state.2)
    | _ => .finish (.returned ⟨state.2, rows⟩)

private def machine := handled services original child (fun _ => (0, 0))

example : machine.run 1 (active 7 (0, 0)) =
    ([Event.child 1], .exhausted (active 7 (1, 1))) := by rfl

example : machine.run 2 (active 7 (0, 0)) =
    ([Event.child 1], .exhausted (active 7 (2, 1))) := by rfl

example : machine.run 3 (active 7 (0, 0)) =
    ([Event.child 1, Event.replied (.returned ⟨1, rows⟩)],
      .exhausted (.running (.returned 7 (.returned ⟨1, rows⟩)))) := by rfl

example : machine.run 4 (active 7 (0, 0)) =
    ([Event.child 1, Event.replied (.returned ⟨1, rows⟩)],
      .finished (.aggregate 7 1 (pack services rows, original 7))) := by rfl

#guard (results rows).length == 2
#guard (results rows).map Prod.snd == [captured, captured]
#guard pack services rows != pack services [⟨some (.symbol "token"), captured⟩]
#guard pack services rows != pack services [⟨some (.symbol "token"), {}⟩,
  ⟨some (.symbol "token"), {}⟩]

/-- Restarting the child from its reached world repeats the effect. -/
example : machine.run 1 (active 7 (0, 1)) =
    ([Event.child 2], .exhausted (active 7 (1, 2))) := by rfl

/- Deleting pending work admits an empty aggregate in the raw state, which
is observably different from the actual finished child. Such a state is not
reachable by the retained execution above. -/
#guard pack services [] != pack services rows

private def stalled : Machine Nat Nat (Reply (Completed Nat) Empty) Empty where
  step n := some (.silent (n + 1))

example : (handled services original stalled id).run 12 (active 7 0) =
    ([], .exhausted (active 7 12)) := by rfl

private def cancelled : Machine Nat Nat (Reply (Completed Nat) Empty) Empty where
  step _ := some (.finish .cancelled)

example : (handled services original cancelled id).run 2 (active 7 0) =
    ([Event.replied .cancelled], .finished (.cancelled 7)) := by rfl

/-- A collector can itself be a retained child of another collector. -/
private def outerChild := machine.relabel id
  (fun verdict => (match verdict with
    | .aggregate _ world result =>
        Reply.returned (Completed.mk world [⟨some result.1, result.2⟩])
    | .failed _ impossible => nomatch impossible
    | .cancelled _ => Reply.cancelled : Reply (Completed Nat) Empty)) id
private def nested := handled services original outerChild (fun _ => active 7 (0, 0))

example : nested.run 1 (active 9 (active 7 (0, 0))) =
    ([Event.child (Event.child 1)], .exhausted (active 9 (active 7 (1, 1)))) := by rfl

example : nested.run 5 (active 9 (active 7 (0, 0))) =
    ([Event.child (Event.child 1),
      Event.child (Event.replied (.returned ⟨1, rows⟩)),
      Event.replied (.returned ⟨1, [⟨some (pack services rows), original 7⟩]⟩)],
      .finished (.aggregate 9 1
        (pack services [⟨some (pack services rows), original 7⟩], original 9))) := by rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Collapse.Controls


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Minimal
open Spec.Type.Presentation.BindingTheory

/-- The phase/cursor branch, parsed body, and independent continuation commute.
The saved parent remains below the new child, including its pending suffix and
original target. The materialization hypothesis is the child-result boundary;
no saved-template materialization or empty-caller hypothesis is used. -/
theorem resume_chain_source_square (materialize : Materializer) (frame : Frame)
    (parents : List Frame) (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat)
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService)
    (live : List Atom) (caller : Option Atom)
    (nested : Atom) (binder : String) (template : Atom) (selected : ResultPair)
    (inputReadout : BindingReadout frame.env) (selectedReadout : BindingReadout selected.2)
    (phase : frame.phase = .chain)
    (shape : frame.atom = .expression [.symbol "chain", nested, .var binder, template])
    (present : frame.inner[frame.index]? = some selected)
    (child : CoreRunRel frame.space dispatch (frame.atom :: live) nested
      ⟨frame.env, inputReadout⟩ (selected.1, ⟨selected.2, selectedReadout⟩)
      (typing := typing) (caller := some frame.atom))
    (materialized : (BindingFrame.mk selected.2 selectedReadout).Materialization selected.1
      (materialize selected.2 selected.1)) :
    let advanced := { frame with index := frame.index + 1 }
    let state : LocalState := ⟨advanced, selected, materialize selected.2 selected.1, [],
      advanced :: parents, publications, false, freshInnerTarget, false, []⟩
    let body := substituteName binder state.materialized template
    resumeChain? materialize frame parents publications freshInnerTarget = some (afterChain state body) ∧
      CoreStepRel frame.space dispatch live frame.atom ⟨frame.env, inputReadout⟩
        (body, ⟨selected.2, selectedReadout⟩) (typing := typing) (caller := caller) := by
  refine ⟨resume_chain_exact materialize frame parents publications freshInnerTarget
    nested binder template selected phase shape present, ?_⟩
  rw [shape] at child ⊢
  exact chain_source_step frame.space dispatch typing live caller nested binder template
    ⟨frame.env, inputReadout⟩ (selected.1, ⟨selected.2, selectedReadout⟩) _ child materialized


theorem condition_disjunction (materialize : Materializer) (state : LocalState)
    (left right : Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.CExpr) :
    condition? materialize state (.binary .or left right) =
      (condition? materialize state left).bind
        (fun first => if first then some true else condition? materialize state right) := by rfl

/-- The selected native branch reads the profile flag before considering the
body's instruction head. The boolean local records that decision. -/
theorem function_step_condition (materialize : Materializer) (state : LocalState) (body : Atom) :
    condition? materialize (setLocal state "body".toList body) functionStep =
      some ((state.nativeCompatibility || minimalHead body) || returnHead body) := by
  have profile : condition? materialize (setLocal state "body".toList body)
      (call "active_profile_uses_rust_he_compat_semantics" []) =
      some state.nativeCompatibility := by rfl
  have instruction : condition? materialize (setLocal state "body".toList body)
      (call "he_minimal_instruction" [identifier "body"]) = some (minimalHead body) := by rfl
  have returned : condition? materialize (setLocal state "body".toList body)
      (.binary .eq (call "atom_head_symbol_id" [identifier "body"])
        (field (identifier "g_builtin_syms") "return_text" false)) = some (returnHead body) := by rfl
  rw [functionStep, condition_disjunction, condition_disjunction, profile, instruction, returned]
  cases state.nativeCompatibility <;> cases minimalHead body <;> cases returnHead body <;> rfl

theorem function_body_guard_expression (materialize : Materializer) (state : LocalState)
    (atoms : List Atom) :
    condition? materialize (setLocal state "body".toList (.expression atoms)) functionBodyGuard =
      some false := by
  simp [functionBodyGuard, condition?, field, identifier, atomOperand?, setLocal, expressionAtom]

/-- Entry retains the original environment and pending parent stack. Its new
child publishes to the parent's private collection, not to the public target. -/
def afterFunctionEntry (state : LocalState) (parents : List Frame) (body : Atom) : LocalState :=
  let bodyState := setLocal state "body".toList body
  let parent := { state.frame with phase := Phase.function }
  let prepared := setBoolLocal { bodyState with frame := parent, stack := parent :: parents }
    "step".toList true
  let child : Frame := ⟨.run, .enter, parent.space, parent.arena, body, parent.env, [], 0,
    childFuel parent.fuel, parent.innerTarget, state.freshInnerTarget⟩
  { prepared with stack := child :: prepared.stack }

theorem execute_function_entry_selected (materialize : Materializer) (state : LocalState)
    (parents : List Frame) (body : Atom)
    (current : state.stack = state.frame :: parents)
    (shape : state.frame.atom = .expression [.symbol "function", body])
    (running : state.returned = false)
    (selected : state.nativeCompatibility = true ∨ minimalHead body = true ∨ returnHead body = true) :
    executeBlock? materialize state (functionBodyRead :: functionEntry) =
      some (afterFunctionEntry state parents body) := by
  let bodyState := setLocal state "body".toList body
  let parent := { state.frame with phase := Phase.function }
  let parentState : LocalState := { bodyState with frame := parent, stack := parent :: parents }
  let prepared := setBoolLocal parentState "step".toList true
  have bodyStep : executeStatement? materialize state functionBodyRead = some bodyState := by
    simp [functionBodyRead, executeStatement?, atomOperand?, atomArgument?, shape, bodyState, call, identifier]
  have phaseStep : executeStatement? materialize bodyState
      (.assign (field (identifier "frame") "phase") (identifier "HE_INSTRUCTION_FUNCTION")) =
      some parentState := by
    simp [executeStatement?, setPhase?, phaseOperand?, bodyState, setLocal, current,
      parentState, parent]
  have gate : condition? materialize parentState functionStep = some true := by
    have localState : parentState = setLocal { state with frame := parent, stack := parent :: parents }
        "body".toList body := rfl
    rw [localState, function_step_condition]
    rcases selected with selected | selected | selected <;> simp [selected]
  have boolStep : executeStatement? materialize parentState
      (.declare ⟨"bool".toList, 0⟩ "step".toList functionStep) = some prepared := by
    simp [executeStatement?, gate, prepared]
  have pushStep : executeStatement? materialize prepared
      (.effect (call "he_instruction_push" [identifier "stack", identifier "HE_INSTRUCTION_RUN",
        identifier "s", identifier "a", identifier "body", identifier "child_fuel",
        address (field (identifier "frame") "env"), address (field (identifier "frame") "inner")])) =
      some (afterFunctionEntry state parents body) := by
    simp [executeStatement?, atomOperand?, prepared, setBoolLocal, parentState, bodyState,
      setLocal, bindingOperand?, targetOperand?, isIdentifier, afterFunctionEntry, parent]
  have branchStep : executeStatement? materialize prepared
      (.branch (identifier "step")
        [.effect (call "he_instruction_push" [identifier "stack", identifier "HE_INSTRUCTION_RUN",
          identifier "s", identifier "a", identifier "body", identifier "child_fuel",
          address (field (identifier "frame") "env"), address (field (identifier "frame") "inner")])]
        [.effect (call "eval_for_caller" [identifier "s", identifier "a", .null,
          identifier "body", identifier "child_fuel", address (field (identifier "frame") "env"),
          .bool true, address (field (identifier "frame") "inner")])]) =
      some (afterFunctionEntry state parents body) := by
    have branchGate : condition? materialize prepared (identifier "step") = some true := by rfl
    simp only [executeStatement?]
    rw [branchGate]
    change executeBlock? materialize prepared [_] = _
    rw [executeBlock?]
    have active : prepared.returned = false := running
    simp only [active, Bool.false_eq_true, ↓reduceIte]
    rw [pushStep]
    rfl
  change executeBlock? materialize state [functionBodyRead, _, _, _] = _
  rw [executeBlock?]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  rw [bodyStep]
  change executeBlock? materialize bodyState [_, _, _] = _
  rw [executeBlock?]
  have bodyActive : bodyState.returned = false := running
  simp only [bodyActive, Bool.false_eq_true, ↓reduceIte]
  rw [phaseStep]
  change executeBlock? materialize parentState [_, _] = _
  rw [executeBlock?]
  have parentActive : parentState.returned = false := running
  simp only [parentActive, Bool.false_eq_true, ↓reduceIte]
  rw [boolStep]
  change executeBlock? materialize prepared [_] = _
  rw [executeBlock?]
  have preparedActive : prepared.returned = false := running
  simp only [preparedActive, Bool.false_eq_true, ↓reduceIte]
  rw [branchStep]
  rfl

/-- The body read establishes the actual expression-kind branch admission;
the checked entry then pushes the retained child. Error handling is not
identified with failure of this partial projection. -/
theorem function_entry_source_control (materialize : Materializer) (state : LocalState)
    (parents : List Frame) (body : Atom)
    (current : state.stack = state.frame :: parents)
    (shape : state.frame.atom = .expression [.symbol "function", body])
    (bodyExpression : ∃ atoms, body = .expression atoms)
    (running : state.returned = false)
    (selected : state.nativeCompatibility = true ∨ minimalHead body = true ∨ returnHead body = true) :
    condition? materialize (setLocal state "body".toList body) functionBodyGuard = some false ∧
    executeBlock? materialize state (functionBodyRead :: functionEntry) =
      some (afterFunctionEntry state parents body) := by
  refine ⟨?_, execute_function_entry_selected materialize state parents body current shape running selected⟩
  rcases bodyExpression with ⟨atoms, rfl⟩
  exact function_body_guard_expression materialize state atoms

theorem execute_function_entry_minimal (materialize : Materializer) (state : LocalState)
    (parents : List Frame) (body : Atom)
    (current : state.stack = state.frame :: parents)
    (shape : state.frame.atom = .expression [.symbol "function", body])
    (running : state.returned = false)
    (selected : minimalHead body = true ∨ returnHead body = true) :
    executeBlock? materialize state (functionBodyRead :: functionEntry) =
      some (afterFunctionEntry state parents body) :=
  execute_function_entry_selected materialize state parents body current shape running (Or.inr selected)


/-- A returned child closes the independent function delimiter and appends
one result at the actual target. This does not identify diagnostic policies
for non-return terminals. -/
theorem function_return_source_square (materialize : Materializer) (state : LocalState)
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService)
    (live : List Atom) (caller : Option Atom) (body value : Atom)
    (inputReadout : BindingReadout state.frame.env)
    (selectedReadout : BindingReadout state.selected.2)
    (shape : state.frame.atom = .expression [.symbol "function", body])
    (bodyExpression : ∃ atoms, body = .expression atoms)
    (running : state.returned = false)
    (returnedShape : state.materialized = .expression [.symbol "return", value])
    (child : CoreRunRel state.frame.space dispatch (state.frame.atom :: live)
      body ⟨state.frame.env, inputReadout⟩ (state.selected.1, ⟨state.selected.2, selectedReadout⟩)
      (typing := typing) (caller := some state.frame.atom))
    (materialized : (BindingFrame.mk state.selected.2 selectedReadout).Materialization
      state.selected.1 state.materialized) :
    executeBlock? materialize state returned = some { state with
      publications := state.publications ++ [(state.frame.target, (value, state.selected.2))] } ∧
      CoreStepRel state.frame.space dispatch live state.frame.atom ⟨state.frame.env, inputReadout⟩
        (value, ⟨state.selected.2, selectedReadout⟩) (typing := typing) (caller := caller) := by
  refine ⟨execute_return materialize state value returnedShape running, ?_⟩
  rw [shape] at child ⊢
  apply CoreStepRel.functionReturn _ body value _ _ bodyExpression
  apply CoreFunctionBodyRel.terminal _ body _
    (state.selected.1, ⟨state.selected.2, selectedReadout⟩) _ child
  · simpa only [returnedShape] using materialized
  · simp [embeddedInstruction]

/-- Matching alone does not choose the successful primitive branch. Refusing
all independently normalized constraint merges rules out every logical common
model; the else branch retains the original frame. -/
theorem unify_merge_refusal_selects_else (target pattern yes no : Atom) (incoming : Bindings)
    (refused : ∀ matched output,
      Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic target pattern matched →
      ¬Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic
        (Spec.Type.Presentation.BindingTheory.aliasConstraints matched)
        (Spec.Type.Presentation.BindingTheory.aliasConstraints incoming) output) :
    Spec.Eval.Steps.UnifyStep target pattern yes no incoming no incoming := by
  apply Spec.Eval.Steps.UnifyStep.noMatch
  rintro output ⟨matched, matchedSource, merged⟩
  obtain ⟨normalized, normalizedMerge, _logical, _shape, _loopFree⟩ :=
    Spec.Match.Completeness.exists_alias_specMerge_of_common_model merged.common_model
  exact refused matched normalized matchedSource normalizedMerge

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Minimal
open Spec.Type.Presentation.BindingTheory

/-- Partial projection of the function return arm. The cursor is advanced by
selection; a non-return terminal belongs to another arm, not semantic failure. -/
def resumeFunctionReturn? (materialize : Materializer) (frame : Frame) (parents : List Frame)
    (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat)
    (unwinding : Bool := false) : Option LocalState := do
  if unwinding || frame.phase != .function then none else
    let state ← selectedState? materialize frame parents publications freshInnerTarget
    match state.materialized with
    | .expression [.symbol "return", _] => executeBlock? materialize state returned
    | _ => none

theorem resume_function_return_exact (materialize : Materializer) (frame : Frame)
    (parents : List Frame) (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat)
    (selected : ResultPair) (value : Atom)
    (phase : frame.phase = .function)
    (present : frame.inner[frame.index]? = some selected)
    (returnedShape : materialize selected.2 selected.1 = .expression [.symbol "return", value]) :
    let advanced := { frame with index := frame.index + 1 }
    let state : LocalState := ⟨advanced, selected, materialize selected.2 selected.1, [],
      advanced :: parents, publications, false, freshInnerTarget, false, []⟩
    resumeFunctionReturn? materialize frame parents publications freshInnerTarget = some { state with
      publications := publications ++ [(frame.target, (value, selected.2))] } := by
  have gate : (frame.phase != Phase.function) = false := by simp [phase]
  have executed := execute_return materialize
    (⟨{ frame with index := frame.index + 1 }, selected,
      materialize selected.2 selected.1, [], { frame with index := frame.index + 1 } :: parents,
      publications, false, freshInnerTarget, false, []⟩ : LocalState) value returnedShape rfl
  simpa [resumeFunctionReturn?, gate, selectedState?, present, returnedShape] using executed

/-- Exact return-arm source square, with the native phase and physical row
selection stated explicitly. The child is independently justified; actual C
child execution remains the separately required refinement. -/
theorem resume_function_return_source_square (materialize : Materializer) (frame : Frame)
    (parents : List Frame) (publications : List (Nat × ResultPair)) (freshInnerTarget : Nat)
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService)
    (live : List Atom) (caller : Option Atom) (body value : Atom) (selected : ResultPair)
    (inputReadout : BindingReadout frame.env) (selectedReadout : BindingReadout selected.2)
    (phase : frame.phase = .function)
    (shape : frame.atom = .expression [.symbol "function", body])
    (bodyExpression : ∃ atoms, body = .expression atoms)
    (present : frame.inner[frame.index]? = some selected)
    (returnedShape : materialize selected.2 selected.1 = .expression [.symbol "return", value])
    (child : CoreRunRel frame.space dispatch (frame.atom :: live)
      body ⟨frame.env, inputReadout⟩ (selected.1, ⟨selected.2, selectedReadout⟩)
      (typing := typing) (caller := some frame.atom))
    (materialized : (BindingFrame.mk selected.2 selectedReadout).Materialization selected.1
      (materialize selected.2 selected.1)) :
    let advanced := { frame with index := frame.index + 1 }
    let state : LocalState := ⟨advanced, selected, materialize selected.2 selected.1, [],
      advanced :: parents, publications, false, freshInnerTarget, false, []⟩
    resumeFunctionReturn? materialize frame parents publications freshInnerTarget = some { state with
      publications := publications ++ [(frame.target, (value, selected.2))] } ∧
      CoreStepRel frame.space dispatch live frame.atom ⟨frame.env, inputReadout⟩
        (value, ⟨selected.2, selectedReadout⟩) (typing := typing) (caller := caller) := by
  refine ⟨resume_function_return_exact materialize frame parents publications freshInnerTarget
    selected value phase present returnedShape, ?_⟩
  rw [shape] at child ⊢
  apply CoreStepRel.functionReturn _ body value _ _ bodyExpression
  apply CoreFunctionBodyRel.terminal _ body _ (selected.1, ⟨selected.2, selectedReadout⟩) _ child
  · simpa only [returnedShape] using materialized
  · simp [embeddedInstruction]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Minimal Spec.Eval.Steps
open Spec.Match.Merge Spec.Match.SolutionTheory
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open LeaTTaBridge

namespace Controls

def boundA : Bindings := Bindings.empty.assign "x" (.symbol "A")
def returnedX : Atom := .expression [.symbol "return", .var "x"]
def returnedB : Atom := .expression [.symbol "return", .symbol "B"]
def bindThenB : Atom := .expression
  [.symbol "unify", .var "x", .symbol "A", .symbol "B", .symbol "refused"]
def chainX : Atom := .expression [.symbol "chain", bindThenB, .var "x", returnedX]

theorem boundA_loop_free : SemanticLoopFree boundA :=
  semanticLoopFree_single_assignment (by intro occurrence; cases occurrence)

theorem boundA_satisfied : HEBindingSatisfied (fun _ => .sym "A") boundA := by
  constructor
  · intro key value member
    have both : key = "x" ∧ value = .symbol "A" := by
      simpa [boundA, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] using member
    rcases both with ⟨rfl, rfl⟩
    simp [applyClassSolution, toLeaTTaAtom]
  · simp [boundA, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]

theorem bind_then_B_candidate :
    UnifyCandidateRel (.var "x") (.symbol "A") Bindings.empty boundA := by
  refine ⟨boundA, .varNonVar rfl boundA_loop_free, ?_⟩
  apply MergeRel.logicalMerge (.mk (List.Perm.refl []) .nil)
  exact ⟨fun _ => .symbol "A", by
    simp [boundA, Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
      Spec.Type.RuntimeRefinement.applyTypeValuation, Bindings.assign,
      Bindings.empty, Bindings.isBound, Bindings.lookup]⟩

theorem bind_then_B : UnifyStep (.var "x") (.symbol "A") (.symbol "B")
    (.symbol "refused") Bindings.empty (.symbol "B") boundA := by
  exact .success ⟨bind_then_B_candidate, by intros; rfl⟩

theorem bindThenB_run (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (caller : Option Atom) :
    CoreRunRel space dispatch live bindThenB Bindings.empty (.symbol "B", boundA)
      (typing := typing) (caller := caller) := by
  apply CoreRunRel.instruction _ _ _ _
  · rfl
  · rintro ⟨tail, equal⟩
    simp [bindThenB] at equal
  · apply CoreStepRel.unifySuccess space (.var "x") (.symbol "A") (.symbol "B")
      (.symbol "refused") (.symbol "B") (BindingFrame.historical Bindings.empty)
      (BindingFrame.historical boundA) bind_then_B_candidate (.historical _ _)
    simpa [boundA, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
      TypeSubst.apply] using
      BindingMaterializationRel.single_assignment "x" (.symbol "A") (.symbol "B")
        (by simp [TypeSubst.typeVars])

theorem chainX_run (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (caller : Option Atom) :
    CoreRunRel space dispatch live chainX Bindings.empty (returnedB, boundA)
      (typing := typing) (caller := caller) := by
  apply chain_source_completed space dispatch typing live caller bindThenB "x" returnedX
    Bindings.empty (.symbol "B", boundA) (returnedB, boundA) (.symbol "B")
  · exact bindThenB_run space dispatch (chainX :: live) typing (some chainX)
  · simpa [boundA, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, TypeSubst.apply] using
      BindingMaterializationRel.single_assignment "x" (.symbol "A") (.symbol "B") (by simp [TypeSubst.typeVars])
  · simpa [returnedX, returnedB, substituteName] using
      (CoreRunRel.data space returnedB boundA rfl (dispatch := dispatch) (live := live)
        (typing := typing) (caller := caller))

/-- The independent function rule derives B even though its reached frame
still binds x to A: the chain binder first replaces its saved template slot. -/
theorem conflicting_slot_function_returns_B (space : Space)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (caller : Option Atom) :
    CoreStepRel space dispatch live (.expression [.symbol "function", chainX]) Bindings.empty
      (.symbol "B", boundA) (typing := typing) (caller := caller) := by
  apply CoreStepRel.functionReturn _ chainX _ _ _ ⟨_, rfl⟩
  apply CoreFunctionBodyRel.terminal _ chainX _ (returnedB, boundA) returnedB
  · exact chainX_run space dispatch (.expression [.symbol "function", chainX] :: live)
      typing (some (.expression [.symbol "function", chainX]))
  · simpa [boundA, returnedB, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, TypeSubst.apply] using
      BindingMaterializationRel.single_assignment "x" (.symbol "A") returnedB (by simp [TypeSubst.typeVars])
  · rfl

/-- This fixture uses its sole assignment as a concrete materializer. It is
not an implementation of general binding resolution. -/
def fixtureMaterializer : Materializer := fun bindings atom =>
  TypeSubst.apply bindings.assignments atom

def fixtureFrame : Frame :=
  ⟨.run, .chain, ⟨[]⟩, 1, chainX, Bindings.empty,
    [(.symbol "B", boundA), (.symbol "B", boundA)], 0, 8, 2, 3⟩

def fixtureState : LocalState :=
  ⟨fixtureFrame, (.symbol "B", boundA), .symbol "B", [], [fixtureFrame], [], false, 4, false, []⟩

theorem old_template_preparation_changes_endpoint :
    executeBlock? fixtureMaterializer fixtureState chainBefore =
      some (afterChain fixtureState (.expression [.symbol "return", .symbol "A"])) := by
  simpa [fixtureState, fixtureFrame, chainX, fixtureMaterializer, boundA,
    returnedX, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
    TypeSubst.apply, TypeSubst.lookup, substituteName] using
    execute_chain_before fixtureMaterializer fixtureState bindThenB "x" returnedX rfl rfl

theorem repaired_template_preparation_keeps_selected_result :
    executeBlock? fixtureMaterializer fixtureState chainAfter =
      some (afterChain fixtureState returnedB) := by
  simpa [fixtureState, fixtureFrame, returnedB, returnedX, substituteName] using
    execute_chain_after fixtureMaterializer fixtureState bindThenB "x" returnedX rfl rfl

theorem old_endpoint_is_not_selected_continuation :
    (.expression [.symbol "return", .symbol "A"] : Atom) ≠
      substituteName "x" (.symbol "B") returnedX := by simp [returnedX, substituteName]

/-- Equal child values are separate physical rows. Selecting the first row
retains the second one in the same parent collection and advances just once. -/
theorem duplicate_children_keep_next_cursor :
    ∃ state, resumeChain? fixtureMaterializer fixtureFrame [] [] 4 = some state ∧
      state.stack.map Frame.index = [0, 1] ∧
      (state.stack[1]?).map Frame.inner = some fixtureFrame.inner ∧
      state.publications = [] := by
  let advanced := { fixtureFrame with index := 1 }
  let selectedState : LocalState :=
    ⟨advanced, (.symbol "B", boundA), .symbol "B", [], [advanced], [], false, 4, false, []⟩
  refine ⟨afterChain selectedState returnedB, ?_, rfl, rfl, rfl⟩
  simpa [fixtureMaterializer, fixtureFrame, TypeSubst.apply, returnedX, returnedB, substituteName, selectedState, advanced] using
    resume_chain_exact fixtureMaterializer fixtureFrame [] [] 4 bindThenB "x" returnedX
      (.symbol "B", boundA) rfl rfl rfl

theorem exhausted_cursor_has_no_selected_branch :
    resumeChain? fixtureMaterializer { fixtureFrame with index := 2 } [] [] 4 = none := by
  simp [resumeChain?, selectedState?, fixtureFrame]

theorem wrong_phase_does_not_run_chain_block :
    resumeChain? fixtureMaterializer { fixtureFrame with phase := .function } [] [] 4 = none := by
  simp [resumeChain?]

/-- Structural chain substitution also reaches repeated same-name syntax;
this is deliberately not a lexical alpha-renaming theorem. -/
theorem repeated_nested_slot_is_structural :
    substituteName "x" (.symbol "C")
      (.expression [.symbol "chain", .symbol "D", .var "x", returnedX]) =
      .expression [.symbol "chain", .symbol "D", .symbol "C",
        .expression [.symbol "return", .symbol "C"]] := by simp [returnedX, substituteName]

/-- The second target still matches syntactically. -/
theorem incompatible_second_target_still_matches :
    MatchRel equalityGroundedSemantic (.var "x") (.symbol "B")
      (Bindings.empty.assign "x" (.symbol "B")) :=
  .varNonVar rfl (semanticLoopFree_single_assignment (by intro occurrence; cases occurrence))

/-- Its result cannot survive the actual incoming constraint x=A. The
independent rule therefore chooses else and keeps the original frame. -/
theorem incompatible_second_binding_selects_else :
    UnifyStep (.var "x") (.symbol "B") (.symbol "accepted") (.symbol "refused")
      boundA (.symbol "refused") boundA := by
  apply UnifyStep.noMatch
  rintro output ⟨matched, hmatch, merged⟩
  obtain ⟨valuation, satisfied⟩ := merged.he_model
  obtain ⟨matchedSatisfied, incomingSatisfied⟩ := (merged.he_solutions valuation).mp satisfied
  have equalsB := (matchRel_solution_iff hmatch valuation).mp matchedSatisfied
  have equalsA := incomingSatisfied.1 "x" (.symbol "A") (by
    simp [boundA, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup])
  simp only [toLeaTTaAtom, applyClassSolution] at equalsA equalsB
  have impossible := equalsA.symm.trans equalsB
  simp at impossible

end Controls
end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl

open OSLFCore (Atom)
open Spec.Eval
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open InstructionControl (identifier field call address isIdentifier types)

def helperBody : List CStatement :=
  [.return (some (.conditional
    (.binary .and (identifier "invocation")
      (call "he_not_reducible" [identifier "raw_result"]))
    (identifier "invocation") (identifier "raw_result")))]


def helperPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])
theorem helperPiece0_lex : helperPiece0.1.toList.foldl step initial =
    completed helperPiece0.2 := by decide +kernel


def helperPiece1 : String × List Token :=
  ("    return invocation && he_not_reducible(raw_result) ? invocation : raw_result;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['i', 'n', 'v', 'o', 'c', 'a', 't', 'i', 'o', 'n'], .punctuation ['&', '&'], .identifier ['h', 'e', '_', 'n', 'o', 't', '_', 'r', 'e', 'd', 'u', 'c', 'i', 'b', 'l', 'e'], .punctuation ['('], .identifier ['r', 'a', 'w', '_', 'r', 'e', 's', 'u', 'l', 't'], .punctuation [')'], .punctuation ['?'], .identifier ['i', 'n', 'v', 'o', 'c', 'a', 't', 'i', 'o', 'n'], .punctuation [':'], .identifier ['r', 'a', 'w', '_', 'r', 'e', 's', 'u', 'l', 't'], .punctuation [';']])
theorem helperPiece1_lex : helperPiece1.1.toList.foldl step initial =
    completed helperPiece1.2 := by decide +kernel


def helperPiece2 : String × List Token :=
  ("}", [.punctuation ['}']])
theorem helperPiece2_lex : helperPiece2.1.toList.foldl step initial =
    completed helperPiece2.2 := by decide +kernel


def helperPieces : List (String × List Token) := [helperPiece0, helperPiece1, helperPiece2]

/-- The deployed helper's body. Pointer nullness is separate from atom syntax. -/
def helperSource : String := String.join (helperPieces.map Prod.fst)

def helperTokens : List Token := helperPieces.flatMap Prod.snd


theorem helper_lex : lex helperSource.toList = .ok helperTokens := by
  apply lex_completed_string_pieces
  simp only [helperPieces, List.forall_cons]
  exact ⟨helperPiece0_lex, helperPiece1_lex, helperPiece2_lex, trivial⟩


theorem helper_parsed : blockText? types helperSource.toList = some helperBody := by
  exact block_text_of_parts types _ helperTokens helperBody helper_lex (by rfl)


mutual
  /-- Only the operand and conditional forms used by this helper are projected.
  Symbol-ID and pointer readback are represented by atoms and `Option`. -/
  def helperAtom? (invocation : Option Atom) (raw : Atom) : CExpr → Option Atom
    | .identifier name =>
        if name = "invocation".toList then invocation
        else if name = "raw_result".toList then some raw else none
    | .conditional test yes no => do
        if ← helperCondition? invocation raw test then helperAtom? invocation raw yes
        else helperAtom? invocation raw no
    | _ => none
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf; all_goals omega

  def helperCondition? (invocation : Option Atom) (raw : Atom) : CExpr → Option Bool
    | .identifier name =>
        if name = "invocation".toList then some invocation.isSome else none
    | .call name [argument] =>
        if name = "he_not_reducible".toList then do
          return (← helperAtom? invocation raw argument) == Atom.notReducible
        else none
    | .binary .and left right => do
        if ← helperCondition? invocation raw left then helperCondition? invocation raw right
        else some false
    | _ => none
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf; all_goals omega
end


def helperBlock? (invocation : Option Atom) (raw : Atom) :
    List CStatement → Option Atom
  | [.return (some expression)] => helperAtom? invocation raw expression
  | _ => none


theorem helper_nonnull (original raw : Atom) :
    helperBlock? (some original) raw helperBody =
      some (if raw = Atom.notReducible then original else raw) := by
  by_cases refused : raw = Atom.notReducible <;>
    simp [helperBlock?, helperBody, helperAtom?, helperCondition?, identifier, call, refused]


theorem helper_null (raw : Atom) : helperBlock? none raw helperBody = some raw := by
  simp [helperBlock?, helperBody, helperAtom?, helperCondition?, identifier, call]

/-- A source callback is needed only for a non-stopped, non-protocol reply.
  This theorem checks the parsed helper's returned operand, not an arbitrary
  C function or the ordinary evaluator that follows it. -/

theorem helper_refusal_square
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (original demand : Atom) (reached : BindingFrame)
    (result : FrameResult) :
    (∃ returned, helperBlock? (some original) Atom.notReducible helperBody = some returned ∧
      result = (returned, reached)) ↔
    CallReturnRel space dispatch live original demand Atom.notReducible reached result
      (typing := typing) := by
  rw [CallReturnRel.notReducible_iff, helper_nonnull]
  simp


inductive Provenance where
  | raw | completed
  deriving DecidableEq, Repr

/-- Equal syntax can have two different return obligations. The producer tag
  cannot be reconstructed by inspecting a value's spelling. This does not
  decide which native producers belong to a given compatibility profile. -/
theorem no_syntax_only_return
    (original : Atom) (different : original ≠ Atom.notReducible) :
    ¬∃ finish : Atom → Atom,
      finish Atom.notReducible = original ∧ finish Atom.notReducible = Atom.notReducible := by
  rintro ⟨finish, raw, completed⟩
  exact different (raw.symm.trans completed)

theorem completed_refusal_is_data
    (space : Space) (typing : EvalTypeService) (reached : Bindings) :
    CompletedNativeReturnRel space typing Atom.notReducible Atom.undefinedType reached
      (Atom.notReducible, reached) :=
  .keep (Or.inr (Or.inl rfl))

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl
open OSLFCore (Atom)
open Spec.Eval
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open InstructionControl (identifier field call address isIdentifier types)

/-- The actual `HE_CANONICAL_RESULT` owner has already evaluated its arguments.
  `caller` can retain its complete surrounding stack, world and argument receipts.
  `row` identifies the selected physical occurrence, even when values coincide.
  This is a readback, not a heap or allocation assertion. -/
structure Invocation (Caller : Type) where
  caller : Caller
  space : Space
  original : Atom
  demand : Atom
  row : Nat
  reached : Bindings
  materialized : Atom
  variantOnly : Atom
  target : Nat
  /-- The actual `he_relay_sink` result; redirection may differ from the
  address of the frame's own child buffer. -/
  relayTarget : Nat
  fuel : Int
  preserveBindings : Bool
  provenance : Provenance

/-- The typed continuation retains the selected environment and demand.
  `input` is the actual variant-only operand handed to the C caller frame. -/
structure Request (Caller : Type) where
  invocation : Invocation Caller
  input : Atom
  demand : Atom
  bindings : Bindings
  target : Nat

structure State (Caller : Type) where
  invocation : Invocation Caller
  phase : Nat := 0
  popped : Bool := false
  returned : Bool := false
  publications : List (Nat × ResultPair) := []
  request : Option (Request Caller) := none

variable {Caller : Type}

def frameAtom : CExpr := field (identifier "frame") "atom"
def frameType : CExpr := field (identifier "frame") "type"
def frameTarget : CExpr := field (identifier "frame") "target"
def framePreserve : CExpr := field (identifier "frame") "preserve_bindings"
def seedEnv : CExpr := address (field (identifier "seed") "env")
def frameChild : CExpr := address (field (identifier "frame") "child")

def refusalBody : List CStatement :=
  [.effect (call "outcome_set_add_prefixed" [identifier "a", frameTarget,
      call "he_call_return_atom" [frameAtom, identifier "candidate"], seedEnv,
      .null, framePreserve]),
    .effect (call "he_canonical_pop" []), .return none]

def stoppedBody : List CStatement :=
  [.effect (call "he_canonical_publish" [identifier "frame",
      address (field (identifier "frame") "work"), .bool false]),
    .effect (call "he_canonical_pop" []), .return none]

def resumePhase : CStatement :=
  .assign (field (identifier "frame") "phase") (.unsignedInteger 1)

def resumePush : CStatement :=
  .effect (call "he_canonical_push" [identifier "HE_CANONICAL_CALLER",
    field (identifier "frame") "space", identifier "a",
    call "outcome_atom_materialize_variant_only" [identifier "a", identifier "seed"],
    frameType, field (identifier "frame") "fuel", seedEnv, framePreserve,
    call "he_relay_sink" [identifier "frame", frameChild]])

def resumedBody : List CStatement := [resumePhase, resumePush]

def refusalPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])
theorem refusalPiece0_lex : refusalPiece0.1.toList.foldl step initial =
    completed refusalPiece0.2 := by decide +kernel

def refusalPiece1 : String × List Token :=
  ("        outcome_set_add_prefixed(a, frame->target,\n", [.identifier ['o', 'u', 't', 'c', 'o', 'm', 'e', '_', 's', 'e', 't', '_', 'a', 'd', 'd', '_', 'p', 'r', 'e', 'f', 'i', 'x', 'e', 'd'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['t', 'a', 'r', 'g', 'e', 't'], .punctuation [',']])
theorem refusalPiece1_lex : refusalPiece1.1.toList.foldl step initial =
    completed refusalPiece1.2 := by decide +kernel

def refusalPiece2 : String × List Token :=
  ("            he_call_return_atom(frame->atom, candidate), &seed->env,\n", [.identifier ['h', 'e', '_', 'c', 'a', 'l', 'l', '_', 'r', 'e', 't', 'u', 'r', 'n', '_', 'a', 't', 'o', 'm'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .identifier ['c', 'a', 'n', 'd', 'i', 'd', 'a', 't', 'e'], .punctuation [')'], .punctuation [','], .punctuation ['&'], .identifier ['s', 'e', 'e', 'd'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [',']])
theorem refusalPiece2_lex : refusalPiece2.1.toList.foldl step initial =
    completed refusalPiece2.2 := by decide +kernel

def refusalPiece3 : String × List Token :=
  ("            NULL, frame->preserve_bindings);\n", [.identifier ['N', 'U', 'L', 'L'], .punctuation [','], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', '_', 'b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation [')'], .punctuation [';']])
theorem refusalPiece3_lex : refusalPiece3.1.toList.foldl step initial =
    completed refusalPiece3.2 := by decide +kernel

def refusalPiece4 : String × List Token :=
  ("        he_canonical_pop();\n", [.identifier ['h', 'e', '_', 'c', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', '_', 'p', 'o', 'p'], .punctuation ['('], .punctuation [')'], .punctuation [';']])
theorem refusalPiece4_lex : refusalPiece4.1.toList.foldl step initial =
    completed refusalPiece4.2 := by decide +kernel

def refusalPiece5 : String × List Token :=
  ("        return;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .punctuation [';']])
theorem refusalPiece5_lex : refusalPiece5.1.toList.foldl step initial =
    completed refusalPiece5.2 := by decide +kernel

def refusalPiece6 : String × List Token :=
  ("    }", [.punctuation ['}']])
theorem refusalPiece6_lex : refusalPiece6.1.toList.foldl step initial =
    completed refusalPiece6.2 := by decide +kernel

def refusalPieces : List (String × List Token) := [refusalPiece0, refusalPiece1, refusalPiece2, refusalPiece3, refusalPiece4, refusalPiece5, refusalPiece6]

def refusalSource : String := String.join (refusalPieces.map Prod.fst)

def refusalTokens : List Token := refusalPieces.flatMap Prod.snd

theorem refusal_lex : lex refusalSource.toList = .ok refusalTokens := by
  apply lex_completed_string_pieces
  simp only [refusalPieces, List.forall_cons]
  exact ⟨refusalPiece0_lex, refusalPiece1_lex, refusalPiece2_lex, refusalPiece3_lex, refusalPiece4_lex, refusalPiece5_lex, refusalPiece6_lex, trivial⟩

theorem refusal_parsed : blockText? types refusalSource.toList = some refusalBody := by
  exact block_text_of_parts types _ refusalTokens refusalBody refusal_lex (by rfl)

def stoppedPiece0 : String × List Token :=
  ("{\n", [.punctuation ['{']])
theorem stoppedPiece0_lex : stoppedPiece0.1.toList.foldl step initial =
    completed stoppedPiece0.2 := by decide +kernel

def stoppedPiece1 : String × List Token :=
  ("        he_canonical_publish(frame, &frame->work, false);\n", [.identifier ['h', 'e', '_', 'c', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', '_', 'p', 'u', 'b', 'l', 'i', 's', 'h'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['w', 'o', 'r', 'k'], .punctuation [','], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [')'], .punctuation [';']])
theorem stoppedPiece1_lex : stoppedPiece1.1.toList.foldl step initial =
    completed stoppedPiece1.2 := by decide +kernel

def stoppedPiece2 : String × List Token :=
  ("        he_canonical_pop();\n", [.identifier ['h', 'e', '_', 'c', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', '_', 'p', 'o', 'p'], .punctuation ['('], .punctuation [')'], .punctuation [';']])
theorem stoppedPiece2_lex : stoppedPiece2.1.toList.foldl step initial =
    completed stoppedPiece2.2 := by decide +kernel

def stoppedPiece3 : String × List Token :=
  ("        return;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .punctuation [';']])
theorem stoppedPiece3_lex : stoppedPiece3.1.toList.foldl step initial =
    completed stoppedPiece3.2 := by decide +kernel

def stoppedPiece4 : String × List Token :=
  ("    }", [.punctuation ['}']])
theorem stoppedPiece4_lex : stoppedPiece4.1.toList.foldl step initial =
    completed stoppedPiece4.2 := by decide +kernel

def stoppedPieces : List (String × List Token) := [stoppedPiece0, stoppedPiece1, stoppedPiece2, stoppedPiece3, stoppedPiece4]

def stoppedSource : String := String.join (stoppedPieces.map Prod.fst)

def stoppedTokens : List Token := stoppedPieces.flatMap Prod.snd

theorem stopped_lex : lex stoppedSource.toList = .ok stoppedTokens := by
  apply lex_completed_string_pieces
  simp only [stoppedPieces, List.forall_cons]
  exact ⟨stoppedPiece0_lex, stoppedPiece1_lex, stoppedPiece2_lex, stoppedPiece3_lex, stoppedPiece4_lex, trivial⟩

theorem stopped_parsed : blockText? types stoppedSource.toList = some stoppedBody := by
  exact block_text_of_parts types _ stoppedTokens stoppedBody stopped_lex (by rfl)

def resumePhasePiece0 : String × List Token :=
  ("frame->phase = 1u;", [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['p', 'h', 'a', 's', 'e'], .punctuation ['='], .number ['1', 'u'], .punctuation [';']])
theorem resumePhasePiece0_lex : resumePhasePiece0.1.toList.foldl step initial =
    completed resumePhasePiece0.2 := by decide +kernel

def resumePhasePieces : List (String × List Token) := [resumePhasePiece0]

def resumePhaseSource : String := String.join (resumePhasePieces.map Prod.fst)

def resumePhaseTokens : List Token := resumePhasePieces.flatMap Prod.snd

theorem resumePhase_lex : lex resumePhaseSource.toList = .ok resumePhaseTokens := by
  apply lex_completed_string_pieces
  simp only [resumePhasePieces, List.forall_cons]
  exact ⟨resumePhasePiece0_lex, trivial⟩

theorem resumePhase_parsed :
    ((lex resumePhaseSource.toList).toOption.bind fun tokens =>
      Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.statement? (2 * tokens.length + 4) types tokens) = some (resumePhase, []) := by
  rw [resumePhase_lex]
  rfl

def resumePushPiece0 : String × List Token :=
  ("he_canonical_push(HE_CANONICAL_CALLER, frame->space, a,\n", [.identifier ['h', 'e', '_', 'c', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', '_', 'p', 'u', 's', 'h'], .punctuation ['('], .identifier ['H', 'E', '_', 'C', 'A', 'N', 'O', 'N', 'I', 'C', 'A', 'L', '_', 'C', 'A', 'L', 'L', 'E', 'R'], .punctuation [','], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'p', 'a', 'c', 'e'], .punctuation [','], .identifier ['a'], .punctuation [',']])
theorem resumePushPiece0_lex : resumePushPiece0.1.toList.foldl step initial =
    completed resumePushPiece0.2 := by decide +kernel

def resumePushPiece1 : String × List Token :=
  ("        outcome_atom_materialize_variant_only(a, seed), frame->type,\n", [.identifier ['o', 'u', 't', 'c', 'o', 'm', 'e', '_', 'a', 't', 'o', 'm', '_', 'm', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', '_', 'v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'o', 'n', 'l', 'y'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['s', 'e', 'e', 'd'], .punctuation [')'], .punctuation [','], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['t', 'y', 'p', 'e'], .punctuation [',']])
theorem resumePushPiece1_lex : resumePushPiece1.1.toList.foldl step initial =
    completed resumePushPiece1.2 := by decide +kernel

def resumePushPiece2 : String × List Token :=
  ("        frame->fuel, &seed->env, frame->preserve_bindings,\n", [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['f', 'u', 'e', 'l'], .punctuation [','], .punctuation ['&'], .identifier ['s', 'e', 'e', 'd'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', '_', 'b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation [',']])
theorem resumePushPiece2_lex : resumePushPiece2.1.toList.foldl step initial =
    completed resumePushPiece2.2 := by decide +kernel

def resumePushPiece3 : String × List Token :=
  ("        he_relay_sink(frame, &frame->child));", [.identifier ['h', 'e', '_', 'r', 'e', 'l', 'a', 'y', '_', 's', 'i', 'n', 'k'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['c', 'h', 'i', 'l', 'd'], .punctuation [')'], .punctuation [')'], .punctuation [';']])
theorem resumePushPiece3_lex : resumePushPiece3.1.toList.foldl step initial =
    completed resumePushPiece3.2 := by decide +kernel

def resumePushPieces : List (String × List Token) := [resumePushPiece0, resumePushPiece1, resumePushPiece2, resumePushPiece3]

def resumePushSource : String := String.join (resumePushPieces.map Prod.fst)

def resumePushTokens : List Token := resumePushPieces.flatMap Prod.snd

theorem resumePush_lex : lex resumePushSource.toList = .ok resumePushTokens := by
  apply lex_completed_string_pieces
  simp only [resumePushPieces, List.forall_cons]
  exact ⟨resumePushPiece0_lex, resumePushPiece1_lex, resumePushPiece2_lex, resumePushPiece3_lex, trivial⟩

theorem resumePush_parsed :
    ((lex resumePushSource.toList).toOption.bind fun tokens =>
      Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.statement? (2 * tokens.length + 4) types tokens) = some (resumePush, []) := by
  rw [resumePush_lex]
  rfl


def atomOperand? (invocation : Invocation Caller) : CExpr → Option Atom
  | .identifier name =>
      if name = "candidate".toList then some invocation.materialized else none
  | .field (.identifier owner) member true =>
      if owner = "frame".toList then
        if member = "atom".toList then some invocation.original
        else if member = "type".toList then some invocation.demand else none
      else none
  | .call name [left, right] =>
      if name = "he_call_return_atom".toList then do
        helperBlock? (some (← atomOperand? invocation left))
          (← atomOperand? invocation right) helperBody
      else if name = "outcome_atom_materialize_variant_only".toList &&
          isIdentifier left "a" && isIdentifier right "seed" then
        some invocation.variantOnly
      else none
  | _ => none
termination_by expression => sizeOf expression
decreasing_by all_goals simp_wf; all_goals omega

/-- Interpret only the selected return-frame effects. Native pointer/collection
  identity, copy success, materialization and relay behavior remain readback
  obligations. Compact publication also applies the environment to the value;
  this full-binding projection therefore declines that observer rather than
  pretending it merely empties a binding list. This is not a replacement C evaluator. -/
def statement? (state : State Caller) : CStatement → Option (State Caller)
  | .assign (.field (.identifier owner) member true) (.unsignedInteger 1) =>
      if owner = "frame".toList && member = "phase".toList then
        some { state with phase := 1 } else none
  | .effect (.call name []) =>
      if name = "he_canonical_pop".toList then
        some { state with popped := true } else none
  | .effect (.call name [.identifier arena,
        .field (.identifier frame) target true, value,
        .unary .address (.field (.identifier seed) env true), .null,
        .field (.identifier preserveFrame) preserve true]) => do
      if name = "outcome_set_add_prefixed".toList && arena = "a".toList &&
          frame = "frame".toList && target = "target".toList &&
          seed = "seed".toList && env = "env".toList &&
          preserveFrame = "frame".toList && preserve = "preserve_bindings".toList &&
          state.invocation.preserveBindings then
        let atom ← atomOperand? state.invocation value
        some { state with publications := state.publications ++
          [(state.invocation.target, (atom, state.invocation.reached))] }
      else none
  | .effect (.call name [.identifier owner,
        .unary .address (.field (.identifier workOwner) work true), .bool false]) =>
      if name = "he_canonical_publish".toList && owner = "frame".toList &&
          workOwner = "frame".toList && work = "work".toList &&
          state.invocation.preserveBindings then
        some { state with publications := state.publications ++
          [(state.invocation.target,
            (state.invocation.materialized, state.invocation.reached))] }
      else none
  | .effect (.call name [.identifier kind,
        .field (.identifier spaceOwner) space true, .identifier arena,
        atom, demand, .field (.identifier fuelOwner) fuel true,
        .unary .address (.field (.identifier seed) env true),
        .field (.identifier preserveOwner) preserve true,
        .call relay [.identifier relayOwner,
          .unary .address (.field (.identifier childOwner) child true)]]) => do
      if name = "he_canonical_push".toList && kind = "HE_CANONICAL_CALLER".toList &&
          spaceOwner = "frame".toList && space = "space".toList && arena = "a".toList &&
          fuelOwner = "frame".toList && fuel = "fuel".toList &&
          seed = "seed".toList && env = "env".toList &&
          preserveOwner = "frame".toList && preserve = "preserve_bindings".toList &&
          relay = "he_relay_sink".toList && relayOwner = "frame".toList &&
          childOwner = "frame".toList && child = "child".toList then
        let input ← atomOperand? state.invocation atom
        let expected ← atomOperand? state.invocation demand
        some { state with request := some ⟨state.invocation, input, expected,
          state.invocation.reached, state.invocation.relayTarget⟩ }
      else none
  | .return none => some { state with returned := true }
  | _ => none

def block? (state : State Caller) : List CStatement → Option (State Caller)
  | [] => some state
  | first :: rest => do
      if state.returned then some state else
        let next ← statement? state first
        block? next rest

def start (invocation : Invocation Caller) (published : List (Nat × ResultPair)) : State Caller :=
  { invocation := invocation, publications := published }

def closed (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (value : Atom) : State Caller :=
  { invocation := invocation, popped := true, returned := true,
    publications := published ++ [(invocation.target, (value, invocation.reached))] }

def requested (invocation : Invocation Caller) (published : List (Nat × ResultPair)) : State Caller :=
  { invocation := invocation, phase := 1, publications := published,
    request := some ⟨invocation, invocation.variantOnly, invocation.demand,
      invocation.reached, invocation.relayTarget⟩ }

theorem refusal_exact (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (preserve : invocation.preserveBindings = true) :
    block? (start invocation published) refusalBody =
      some (closed invocation published
        (if invocation.materialized = Atom.notReducible then invocation.original
         else invocation.materialized)) := by
  simp [block?, statement?, refusalBody, start, closed, atomOperand?,
    frameAtom, frameTarget, framePreserve, seedEnv, identifier, field, call, address,
    helper_nonnull, preserve]

theorem stopped_exact (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (preserve : invocation.preserveBindings = true) :
    block? (start invocation published) stoppedBody =
      some (closed invocation published invocation.materialized) := by
  simp [block?, statement?, stoppedBody, start, closed, identifier, field, call, address, preserve]

theorem resume_exact (invocation : Invocation Caller) (published : List (Nat × ResultPair)) :
    block? (start invocation published) resumedBody = some (requested invocation published) := by
  simp [block?, statement?, resumedBody, resumePhase, resumePush, start, requested,
    atomOperand?, frameType, framePreserve, seedEnv, frameChild, identifier, field, call,
    address, isIdentifier]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl
open OSLFCore (Atom)
open Spec.Eval
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- These are source program points, not a claim that the entire canonical
  dispatcher is covered. `ordinaryTail` is reached only after its function and
  inert-result alternatives have declined or completed their tests. -/
inductive Point where
  | refusal | stopped | ordinaryTail
  deriving DecidableEq, Repr

variable {Caller : Type}

/-- A selected raw result can enter a return block once. Completed producer
  values have a different owner, and a phase-one callback is already pending. -/
def project? (point : Point) (state : State Caller) : Option (State Caller) :=
  if state.invocation.provenance != .raw || state.phase != 0 ||
      state.popped || state.returned then none else
    match point with
    | .refusal =>
        if state.invocation.materialized == Atom.notReducible then
          block? state refusalBody else none
    | .stopped => block? state stoppedBody
    | .ordinaryTail => block? state resumedBody

theorem completed_cannot_enter (invocation : Invocation Caller)
    (point : Point) (published : List (Nat × ResultPair))
    (completed : invocation.provenance = .completed) :
    project? point (start invocation published) = none := by
  simp [project?, start, completed]

theorem popped_cannot_repeat (invocation : Invocation Caller)
    (point : Point) (published : List (Nat × ResultPair)) (value : Atom) :
    project? point (closed invocation published value) = none := by
  simp [project?, closed]

theorem pending_cannot_restart (invocation : Invocation Caller)
    (point : Point) (published : List (Nat × ResultPair)) :
    project? point (requested invocation published) = none := by
  simp [project?, requested]

/-- The physical selected occurrence contributes exactly one new publication.
  Earlier equal publications remain present; no value-based deduplication is
  performed. The full-binding observer requires `preserveBindings`; its frame
  observer also checks the unchanged selected readout, which raw rows alone do
  not reconstruct. -/
theorem refusal_source_square
    (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (readout : BindingReadout invocation.reached)
    (raw : invocation.provenance = .raw)
    (refusal : invocation.materialized = Atom.notReducible)
    (preserve : invocation.preserveBindings = true) (result : FrameResult) :
    project? .refusal (start invocation published) =
      some (closed invocation published invocation.original) ∧
    (((closed invocation published invocation.original).publications =
        published ++ [(invocation.target, BindingFrame.rawResult result)] ∧
          result.2 = ⟨invocation.reached, readout⟩) ↔
      CallReturnRel invocation.space dispatch live invocation.original invocation.demand
        invocation.materialized ⟨invocation.reached, readout⟩ result (typing := typing)) := by
  constructor
  · simpa [project?, start, raw, refusal] using refusal_exact invocation published preserve
  · rw [refusal, CallReturnRel.notReducible_iff]
    rcases result with ⟨value, frame⟩
    simp only [closed, List.append_cancel_left_eq, List.cons.injEq, Prod.mk.injEq, true_and,
      and_true, BindingFrame.rawResult]
    constructor
    · rintro ⟨⟨sameValue, _⟩, rfl⟩
      exact ⟨sameValue.symm, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The native stopped branch is licensed by its actual guard readback:
  preview-Empty or materialized Error. Its helper's singleton publication is
  observed here before the enclosing public Empty filter. -/
theorem stopped_source_square
    (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (readout : BindingReadout invocation.reached)
    (raw : invocation.provenance = .raw)
    (stopped : IsEmptyOrErrorRel invocation.materialized)
    (preserve : invocation.preserveBindings = true) (result : FrameResult) :
    project? .stopped (start invocation published) =
      some (closed invocation published invocation.materialized) ∧
    (((closed invocation published invocation.materialized).publications =
        published ++ [(invocation.target, BindingFrame.rawResult result)] ∧
          result.2 = ⟨invocation.reached, readout⟩) ↔
      CallReturnRel invocation.space dispatch live invocation.original invocation.demand
        invocation.materialized ⟨invocation.reached, readout⟩ result (typing := typing)) := by
  constructor
  · simpa [project?, start, raw] using stopped_exact invocation published preserve
  · rw [CallReturnRel.stopped_iff stopped]
    rcases result with ⟨value, frame⟩
    simp only [closed, List.append_cancel_left_eq, List.cons.injEq, Prod.mk.injEq, true_and,
      and_true, BindingFrame.rawResult]
    constructor
    · rintro ⟨⟨sameValue, _⟩, rfl⟩
      exact ⟨sameValue.symm, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The selected C tail constructs this exact callback request. It does not
  re-enter argument evaluation. Variant-only versus fully materialized input
  remains explicit: `typed` is the independent child interpretation obligation
  for the materialized value, not inferred from a pointer or syntax equality. -/
theorem ordinary_source_square
    (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (readout : BindingReadout invocation.reached)
    (raw : invocation.provenance = .raw)
    (notRefusal : invocation.materialized ≠ Atom.notReducible)
    (notStopped : ¬IsEmptyOrErrorRel invocation.materialized) (result : FrameResult) :
    project? .ordinaryTail (start invocation published) =
      some (requested invocation published) ∧
    (EvalAtomRawRel invocation.space dispatch live invocation.materialized invocation.demand
        ⟨invocation.reached, readout⟩ result (typing := typing) ↔
      CallReturnRel invocation.space dispatch live invocation.original invocation.demand
        invocation.materialized ⟨invocation.reached, readout⟩ result (typing := typing)) := by
  constructor
  · simpa [project?, start, raw] using resume_exact invocation published
  · exact (CallReturnRel.evaluate_iff notRefusal notStopped).symm

/-- When the actual variant-only operand is already materialized, a derivation
  of the concrete callback input directly discharges the child obligation.
  Arbitrary open-input materialization transport is not postulated here. -/
theorem ordinary_callback_source
    (invocation : Invocation Caller) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService)
    (readout : BindingReadout invocation.reached)
    (inputReadback : invocation.variantOnly = invocation.materialized)
    (notRefusal : invocation.materialized ≠ Atom.notReducible)
    (notStopped : ¬IsEmptyOrErrorRel invocation.materialized)
    {result : FrameResult}
    (typed : EvalAtomRawRel invocation.space dispatch live invocation.variantOnly invocation.demand
      ⟨invocation.reached, readout⟩ result (typing := typing)) :
    CallReturnRel invocation.space dispatch live invocation.original invocation.demand
      invocation.materialized ⟨invocation.reached, readout⟩ result (typing := typing) := by
  apply (CallReturnRel.evaluate_iff notRefusal notStopped).mpr
  simpa only [inputReadback] using typed

/-- A caller child returns its whole reached world and physical result list.
  A prefix, cancellation, or fault is not a completed successful list. -/
structure Completion (World : Type) where
  world : World
  results : ResultSet

inductive Parent (Caller World Failure : Type) where
  | waiting (request : Request Caller)
  | replied (request : Request Caller) (reply : Reply (Completion World) Failure)

def Parent.request {World Failure : Type} : Parent Caller World Failure → Request Caller
  | .waiting request | .replied request _ => request

inductive Event (Caller World Receipt Failure : Type) where
  /-- Required by the common callback interface; the already-entered parent
  has no requesting transition, so this adapter does not emit this label. -/
  | requested (request : Request Caller)
  | child (receipt : Receipt)
  | replied (reply : Reply (Completion World) Failure)

variable {World Receipt Failure Child External : Type}

/-- The C push has already happened. There is deliberately no loader from
  an original expression: the next configuration is the actual child residual. -/
def parent : Machine (Parent Caller World Failure) (Event Caller World Receipt Failure)
    (Request Caller × Reply (Completion World) Failure) (Request Caller) where
  step
    | .waiting _ => none
    | .replied request reply => some (.finish (request, reply))

theorem parent_no_new_request (state saved : Parent Caller World Failure)
    (request : Request Caller) :
    (parent (Receipt := Receipt)).step state ≠ some (.call request saved) := by
  cases state <;> simp [parent]

def callback : Callback (Parent Caller World Failure) (Event Caller World Receipt Failure)
    (Request Caller) (Completion World) Failure where
  callEvent := Event.requested
  replyEvent := Event.replied
  resume saved reply := .replied saved.request reply

def handled
    (child : Machine Child Receipt (Reply (Completion World) Failure) External)
    (load : Request Caller → Child) :
    Machine (HandledState (Parent Caller World Failure) Child (Request Caller))
      (Event Caller World Receipt Failure)
      (Request Caller × Reply (Completion World) Failure) External :=
  parent.handle callback (child.relabel Event.child id id) load

def active (request : Request Caller) (state : Child) :
    HandledState (Parent Caller World Failure) Child (Request Caller) :=
  .handling request (.waiting request) state

/-- Exact child resumption keeps the saved invocation, demand, reached input
  bindings, occurrence identity and full caller. In particular it cannot
  replay a prior argument-effect prefix or reload the child from its source.
  This is conditional on the runtime readback supplying the actual residual. -/
theorem child_pause_exact
    (child : Machine Child Receipt (Reply (Completion World) Failure) External)
    (load : Request Caller → Child) (fuel : Nat) (request : Request Caller)
    (state residual : Child) (events : List Receipt)
    (ran : child.run fuel state = (events, .exhausted residual)) :
    (handled child load).run fuel (active request state) =
      (events.map Event.child, .exhausted (active request residual)) := by
  have lifted := child.run_relabel
    (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id fuel state
  rw [ran] at lifted
  exact parent.handle_run_of_no_reply callback (child.relabel Event.child id id)
    load fuel request (.waiting request) state (events.map Event.child)
    (.exhausted residual) (by simpa only [Outcome.relabel] using lifted)
    (by intro reply; simp)

theorem resume_after_prefix
    (child : Machine Child Receipt (Reply (Completion World) Failure) External)
    (load : Request Caller → Child) (first second : Nat)
    (state residual : HandledState (Parent Caller World Failure) Child (Request Caller))
    (events : List (Event Caller World Receipt Failure))
    (paused : (handled child load).run first state = (events, .exhausted residual)) :
    (handled child load).run (first + second) state =
      (events ++ ((handled child load).run second residual).1,
        ((handled child load).run second residual).2) :=
  (handled child load).established_and_pending first second state residual events paused

/-- A completed child, followed by the return continuation's own closing step,
  returns the same request together with the child's reached world and complete
  occurrence list. Completion never reconstructs the saved argument call. -/
theorem child_complete_exact
    (child : Machine Child Receipt (Reply (Completion World) Failure) External)
    (load : Request Caller → Child) (fuel : Nat) (request : Request Caller)
    (state : Child) (events : List Receipt) (done : Completion World)
    (ran : child.run fuel state = (events, .finished (.returned done))) :
    ∃ used ≤ fuel + 1,
      (handled child load).run used (active request state) =
        (events.map Event.child ++ [Event.replied (.returned done)],
          .finished (request, .returned done)) := by
  have lifted := child.run_relabel
    (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id fuel state
  rw [ran] at lifted
  obtain ⟨used, bound, reached⟩ := parent.handle_run_of_reply callback
    (child.relabel Event.child id id) load fuel request (.waiting request) state
      (events.map Event.child) (.returned done) lifted
  refine ⟨used + 1, Nat.add_le_add_right bound 1, ?_⟩
  change (handled child load).run (used + 1) (.handling request (.waiting request) state) = _
  rw [Machine.run_add]
  change (handled child load).continueRun 1
    ((parent.handle callback (child.relabel Event.child id id) load).run used
      (.handling request (.waiting request) state)) = _
  rw [reached]
  simp [Machine.continueRun, Machine.run, handled, Machine.handle, parent, callback,
    Parent.request]

/-- A single framed result list projects to the complete native list. Every
  physical index carries its own independent child derivation, including equal
  duplicate answers; return keeps that occurrence's full reached frame. -/
theorem completed_occurrence_source
    {World : Type} (request : Request Caller) (done : Completion World)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (readout : BindingReadout request.invocation.reached)
    (sourceResults : List FrameResult)
    (readback : sourceResults.map BindingFrame.rawResult = done.results)
    (notRefusal : request.invocation.materialized ≠ Atom.notReducible)
    (notStopped : ¬IsEmptyOrErrorRel request.invocation.materialized)
    (childSound : ∀ result ∈ sourceResults,
      EvalAtomRawRel request.invocation.space dispatch live request.invocation.materialized
        request.invocation.demand ⟨request.invocation.reached, readout⟩ result (typing := typing))
    (index : Nat) (result : FrameResult) (present : sourceResults[index]? = some result) :
    done.results[index]? = some (BindingFrame.rawResult result) ∧
      CallReturnRel request.invocation.space dispatch live request.invocation.original
        request.invocation.demand request.invocation.materialized
        ⟨request.invocation.reached, readout⟩ result (typing := typing) := by
  constructor
  · rw [← readback, List.getElem?_map, present]
    rfl
  · exact (CallReturnRel.evaluate_iff notRefusal notStopped).mpr
      (childSound result (List.mem_of_getElem? present))

/-- Compose the actual parsed callback-tail projection with an already entered
  child run and independent judgments for its complete occurrence list. The
  caller, selected demand, input bindings, row identity and actual relay target
  in the constructed request are shared by all three sides of the square.
  The hypothesis `inputReadback` states the admitted materialization boundary;
  this theorem does not infer it for arbitrary open native outcomes. -/
theorem ordinary_completed_source_square
    {Caller World Receipt Failure Child External : Type}
    (invocation : Invocation Caller) (published : List (Nat × ResultPair))
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (readout : BindingReadout invocation.reached)
    (raw : invocation.provenance = .raw)
    (inputReadback : invocation.variantOnly = invocation.materialized)
    (notRefusal : invocation.materialized ≠ Atom.notReducible)
    (notStopped : ¬IsEmptyOrErrorRel invocation.materialized)
    (child : Machine Child Receipt (Reply (Completion World) Failure) External)
    (load : Request Caller → Child) (fuel : Nat)
    (events : List Receipt) (done : Completion World)
    (sourceResults : List FrameResult)
    (readback : sourceResults.map BindingFrame.rawResult = done.results)
    (ran : child.run fuel (load ⟨invocation, invocation.variantOnly, invocation.demand,
      invocation.reached, invocation.relayTarget⟩) = (events, .finished (.returned done)))
    (childSound : ∀ result ∈ sourceResults,
      EvalAtomRawRel invocation.space dispatch live invocation.variantOnly invocation.demand
        ⟨invocation.reached, readout⟩ result (typing := typing)) :
    let request : Request Caller := ⟨invocation, invocation.variantOnly, invocation.demand,
      invocation.reached, invocation.relayTarget⟩
    project? .ordinaryTail (start invocation published) =
        some (requested invocation published) ∧
      ∃ used ≤ fuel + 1,
        (handled child load).run used (active request (load request)) =
          (events.map Event.child ++ [Event.replied (.returned done)],
            .finished (request, .returned done)) ∧
        ∀ (index : Nat) (result : FrameResult), sourceResults[index]? = some result →
          done.results[index]? = some (BindingFrame.rawResult result) ∧
          CallReturnRel invocation.space dispatch live invocation.original invocation.demand
            invocation.materialized ⟨invocation.reached, readout⟩ result (typing := typing) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa [project?, start, raw] using resume_exact invocation published
  obtain ⟨used, bound, completed⟩ := child_complete_exact child load fuel
    ⟨invocation, invocation.variantOnly, invocation.demand, invocation.reached,
      invocation.relayTarget⟩ (load ⟨invocation, invocation.variantOnly, invocation.demand,
        invocation.reached, invocation.relayTarget⟩) events done ran
  refine ⟨used, bound, completed, ?_⟩
  intro index result present
  constructor
  · rw [← readback, List.getElem?_map, present]
    rfl
  · exact ordinary_callback_source invocation dispatch live typing readout inputReadback
      notRefusal notStopped (childSound result (List.mem_of_getElem? present))


end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl.Controls
open OSLFCore (Atom)
open Spec.Eval

def callAfterArguments : Atom := .expression [.symbol "freeze", .symbol "7"]
def reached : Bindings := ⟨[("kept", .symbol "A")], [("caller", "kept")]⟩

/-- The caller payload records a prior effect receipt and a surrounding frame.
  Neither is recomputed when this invocation's return is resumed. -/
def invocation : Invocation (Nat × List Nat) :=
  { caller := (17, [8, 13]), space := Space.empty, original := callAfterArguments,
    demand := Atom.atomType, row := 4, reached := reached,
    materialized := Atom.notReducible, variantOnly := Atom.notReducible,
    target := 19, relayTarget := 23, fuel := 7, preserveBindings := true,
    provenance := .raw }

theorem raw_refusal_keeps_call_and_bindings
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService) :
    project? .refusal (start invocation []) =
      some (closed invocation [] callAfterArguments) := by
  exact (refusal_source_square invocation [] dispatch []
    typing .historical rfl rfl rfl (callAfterArguments, reached)).1

theorem raw_refusal_independent_source
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService) :
    CallReturnRel Space.empty dispatch live callAfterArguments Atom.atomType
      Atom.notReducible reached (callAfterArguments, reached) (typing := typing) :=
  .notReducible _ _ _

theorem equal_reply_is_another_occurrence :
    (closed invocation [(19, (callAfterArguments, reached))] callAfterArguments).publications =
      [(19, (callAfterArguments, reached)), (19, (callAfterArguments, reached))] := rfl

theorem completed_same_syntax_is_not_raw :
    project? .refusal (start { invocation with provenance := .completed } []) = none :=
  completed_cannot_enter _ _ _ rfl

theorem spelling_cannot_supply_provenance :
    ¬∃ finish : Atom → Atom,
      finish Atom.notReducible = callAfterArguments ∧
      finish Atom.notReducible = Atom.notReducible :=
  no_syntax_only_return _ (by simp [callAfterArguments, Atom.notReducible])

def failedInvocation : Invocation (Nat × List Nat) :=
  { invocation with materialized := .expression [.symbol "Error", .symbol "bad"] }

theorem stopped_reply_preserves_reached_bindings
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService) :
    project? .stopped (start failedInvocation []) =
      some (closed failedInvocation [] failedInvocation.materialized) :=
  (stopped_source_square failedInvocation [] dispatch [] typing .historical rfl
    (Or.inr ⟨[.symbol "bad"], rfl⟩) rfl
    (failedInvocation.materialized, reached)).1

def ordinaryInvocation : Invocation (Nat × List Nat) :=
  { invocation with materialized := .symbol "A", variantOnly := .symbol "A" }

theorem typed_callback_keeps_selected_demand
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService) :
    CallReturnRel Space.empty dispatch live callAfterArguments Atom.atomType
      (.symbol "A") reached (.symbol "A", reached) (typing := typing) := by
  apply ordinary_callback_source ordinaryInvocation dispatch live typing .historical rfl
    (result := (.symbol "A", reached))
  · simp [ordinaryInvocation, Atom.notReducible]
  · simp [ordinaryInvocation, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .typePass _ _ Atom.symbolType _
      (by simp [ordinaryInvocation, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.symbol "A") (Or.inl rfl)

theorem pending_callback_cannot_repeat :
    project? .ordinaryTail (requested ordinaryInvocation []) = none :=
  pending_cannot_restart _ _ _

theorem returned_frame_cannot_publish_twice :
    project? .refusal (closed invocation [] callAfterArguments) = none :=
  popped_cannot_repeat _ _ _ _

/-- The old literal-sentinel outcome violates the repaired raw return judgment. -/
theorem raw_literal_sentinel_refused
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService) :
    ¬CallReturnRel Space.empty dispatch live callAfterArguments Atom.atomType
      Atom.notReducible reached (Atom.notReducible, reached) (typing := typing) := by
  rw [CallReturnRel.notReducible_iff]
  simp [callAfterArguments, Atom.notReducible]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl.Controls

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Controls
open OSLFCore (Atom)
open Spec.Eval Spec.Eval.Minimal
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory

private def aliasBindings : Bindings := ⟨[("x", .var "public")], []⟩
private def aliasTable : TypeSubst := [("x", .var "public")]
private theorem aliasCertificate : ReadoutCertificate aliasBindings aliasTable :=
  .of_fold (single_assignment_presentation "x" (.var "public") (by decide))
private def aliasReadout : BindingReadout aliasBindings := .selected aliasTable aliasCertificate
private def aliasFrame : BindingFrame := ⟨aliasBindings, aliasReadout⟩
private def pairSlot : Atom := .expression [.symbol "Pair", .var "slot", .var "slot"]
private def pairPublic : Atom := .expression [.symbol "Pair", .var "public", .var "public"]
private def aliasChain : Atom := .expression [.symbol "chain", .var "x", .var "slot", pairSlot]
private def nativeAliasFrame : Frame :=
  ⟨.run, .chain, Space.empty, 1, aliasChain, aliasBindings,
    [(.var "x", aliasBindings), (.var "x", aliasBindings)], 1, 9, 19, 23⟩

/-- The physical second duplicate uses the same selected table for both saved
slots. The native projection and independent step share the complete frame. -/
theorem selected_chain_keeps_joint_open_alias
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService) :
    ∃ state, resumeChain? Controls.fixtureMaterializer nativeAliasFrame [] [] 29 = some state ∧
      state.stack.map Frame.index = [0, 2] ∧
      CoreStepRel Space.empty dispatch [] aliasChain aliasFrame (pairPublic, aliasFrame)
        (typing := typing) := by
  have square := resume_chain_source_square Controls.fixtureMaterializer nativeAliasFrame
    [] [] 29 dispatch typing [] none (.var "x") "slot" pairSlot
    (.var "x", aliasBindings) aliasReadout aliasReadout rfl rfl rfl
    (.data _ _ _ rfl) (by rfl)
  let advanced := { nativeAliasFrame with index := 2 }
  let selectedState : LocalState :=
    ⟨advanced, (.var "x", aliasBindings), .var "public", [], [advanced], [], false, 29, false, []⟩
  refine ⟨afterChain selectedState pairPublic, ?_, rfl, ?_⟩
  · simpa [Controls.fixtureMaterializer, nativeAliasFrame, aliasBindings, aliasTable,
      TypeSubst.apply, TypeSubst.lookup, pairSlot, pairPublic, substituteName,
      selectedState, advanced] using square.1
  · simpa [Controls.fixtureMaterializer, nativeAliasFrame, aliasFrame, aliasBindings, aliasTable,
      TypeSubst.apply, TypeSubst.lookup, pairSlot, pairPublic, substituteName] using square.2

private theorem emptyCertificate : ReadoutCertificate Bindings.empty [] :=
  .of_fold (.nil [])
private theorem boundCertificate : ReadoutCertificate Controls.boundA [("x", .symbol "A")] := by
  apply ReadoutCertificate.of_fold
  simpa [Controls.boundA, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] using
    single_assignment_presentation "x" (.symbol "A") (by simp [TypeSubst.typeVars])

/-- An actual successful primitive merge licenses renewal. Neither the input
nor the output is converted into the historical materialization profile. -/
theorem successful_unify_renews_selected_frame
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) :
    CoreStepRel space dispatch live Controls.bindThenB
      (BindingFrame.selected Bindings.empty [] emptyCertificate)
      (.symbol "B", BindingFrame.selected Controls.boundA [("x", .symbol "A")] boundCertificate)
      (typing := typing) := by
  apply CoreStepRel.unifySuccess _ _ _ _ _ _ _ _ Controls.bind_then_B_candidate
    (.selected emptyCertificate boundCertificate)
  change .symbol "B" = TypeSubst.apply _ (.symbol "B")
  rw [TypeSubst.apply]

/-- The raw ABI rows alone do not reconstruct the retained readout profile. -/
theorem raw_rows_do_not_reconstruct_selected_frame :
    BindingFrame.rawResult (.var "public", aliasFrame) =
        BindingFrame.rawResult (.var "public", BindingFrame.historical aliasBindings) ∧
      aliasFrame ≠ BindingFrame.historical aliasBindings := by
  refine ⟨rfl, ?_⟩
  intro same
  cases same


private def returnAlias : Atom := .expression [.symbol "return", .var "x"]
private def nativeFunctionFrame : Frame :=
  { nativeAliasFrame with
    phase := Phase.function
    atom := .expression [.symbol "function", returnAlias]
    inner := [(returnAlias, aliasBindings)]
    index := 0 }

/-- The parsed function-return branch publishes its actual materialized value
while the independent delimiter retains the selected child frame unchanged. -/
theorem selected_function_return_keeps_frame
    (dispatch : Spec.Eval.GroundedDispatch) (typing : EvalTypeService) :
    ∃ state, resumeFunctionReturn? Controls.fixtureMaterializer nativeFunctionFrame [] [] 29 = some state ∧
      state.publications = [(19, (.var "public", aliasBindings))] ∧
      CoreStepRel Space.empty dispatch [] (.expression [.symbol "function", returnAlias])
        aliasFrame (.var "public", aliasFrame) (typing := typing) := by
  have square := resume_function_return_source_square Controls.fixtureMaterializer
    nativeFunctionFrame [] [] 29 dispatch typing [] none returnAlias (.var "public")
    (returnAlias, aliasBindings) aliasReadout aliasReadout rfl rfl ⟨_, rfl⟩ rfl
    (by simp [Controls.fixtureMaterializer, aliasBindings, returnAlias, TypeSubst.apply, TypeSubst.lookup])
    (.data _ _ _ rfl) (by
      simp [BindingFrame.Materialization, Controls.fixtureMaterializer, aliasBindings, aliasReadout, aliasTable, returnAlias,
        TypeSubst.apply, TypeSubst.lookup])
  let advanced := { nativeFunctionFrame with index := 1 }
  let selectedState : LocalState :=
    ⟨advanced, (returnAlias, aliasBindings), .expression [.symbol "return", .var "public"],
      [], [advanced], [], false, 29, false, []⟩
  refine ⟨{ selectedState with publications := [(19, (.var "public", aliasBindings))] }, ?_, rfl, ?_⟩
  · simpa [Controls.fixtureMaterializer, nativeFunctionFrame, nativeAliasFrame,
      aliasBindings, returnAlias, TypeSubst.apply, TypeSubst.lookup, selectedState, advanced]
      using square.1
  · exact square.2

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Controls

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl.Controls
open OSLFCore (Atom)
open Spec.Eval
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory

private theorem selectedCertificate : ReadoutCertificate Bindings.empty [] := .of_fold (.nil [])
private def selectedReadout : BindingReadout Bindings.empty := .selected [] selectedCertificate
private def selectedFrame : BindingFrame := ⟨Bindings.empty, selectedReadout⟩
private def selectedInvocation : Invocation (Nat × List Nat) :=
  { Controls.ordinaryInvocation with reached := Bindings.empty }
private def selectedRequest : Request (Nat × List Nat) :=
  ⟨selectedInvocation, .symbol "A", Atom.atomType, Bindings.empty, 23⟩
private def selectedResult : FrameResult := (.symbol "A", selectedFrame)
private def completedRows : Completion Nat :=
  ⟨17, [(.symbol "A", Bindings.empty), (.symbol "A", Bindings.empty)]⟩

/-- Equal native answers retain two physical positions and their whole source
frames. The second occurrence does not collapse into the first one. -/
theorem completed_duplicate_retains_second_selected_frame
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService) :
    completedRows.results[1]? = some (BindingFrame.rawResult selectedResult) ∧
      CallReturnRel Space.empty dispatch live Controls.callAfterArguments Atom.atomType
        (.symbol "A") selectedFrame selectedResult (typing := typing) := by
  apply completed_occurrence_source selectedRequest completedRows dispatch live typing
    selectedReadout [selectedResult, selectedResult] rfl
  · simp [selectedRequest, selectedInvocation, Controls.ordinaryInvocation, Atom.notReducible]
  · simp [selectedRequest, selectedInvocation, Controls.ordinaryInvocation,
      IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · intro result member
    have same : result = selectedResult := by simpa using member
    subst result
    exact .typePass _ _ Atom.symbolType _
      (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, selectedRequest,
        selectedInvocation, Controls.ordinaryInvocation]) (.symbol "A") (Or.inl rfl)
  · rfl

/-- A shorter source list cannot certify this completed native list. -/
theorem duplicate_erasure_refused :
    [selectedResult].map BindingFrame.rawResult ≠ completedRows.results := by
  intro equal
  have lengths := congrArg List.length equal
  simp [completedRows] at lengths

/-- Refusal restores the assembled call and the exact selected input frame.
A raw record with the historical tag is not that same retained frame. -/
theorem refusal_cannot_erase_selected_readout
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService) :
    ¬CallReturnRel Space.empty dispatch live Controls.callAfterArguments Atom.atomType
      Atom.notReducible selectedFrame
      (Controls.callAfterArguments, BindingFrame.historical Bindings.empty) (typing := typing) := by
  rw [CallReturnRel.notReducible_iff]
  intro equal
  have frames := congrArg Prod.snd equal
  cases frames

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.CallReturnControl.Controls



namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE

def functionEntryState (compatibility : Bool) (body : Atom) : LocalState :=
  let frame := { fixtureFrame with
    phase := .enter
    atom := .expression [.symbol "function", body] }
  { fixtureState with
    frame := frame
    stack := [frame]
    locals := []
    nativeCompatibility := compatibility
    boolLocals := [] }

def ordinaryEffectBody : Atom := .expression [.symbol "println!", .symbol "9"]

/-- Compatibility entry retains an ordinary body as a child instruction. It
does not invoke the ordinary evaluator in this expression branch. -/
theorem compatibility_entry_pushes_ordinary_body :
    executeBlock? fixtureMaterializer (functionEntryState true ordinaryEffectBody)
      (functionBodyRead :: functionEntry) =
      some (afterFunctionEntry (functionEntryState true ordinaryEffectBody) [] ordinaryEffectBody) := by
  apply execute_function_entry_selected <;> first | rfl | exact Or.inl rfl

/-- The selected branch preserves the source environment, pending parent,
private target and the unchanged body. No public publication occurs here. -/
theorem compatibility_entry_retains_parent_and_private_child :
    let initial := functionEntryState true ordinaryEffectBody
    let reached := afterFunctionEntry initial [] ordinaryEffectBody
    reached.stack.map Frame.atom = [ordinaryEffectBody, initial.frame.atom] ∧
    reached.stack.map Frame.env = [initial.frame.env, initial.frame.env] ∧
    reached.stack.map Frame.target = [initial.frame.innerTarget, initial.frame.target] ∧
    reached.publications = initial.publications := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The noncompatibility ordinary-evaluator branch is beyond this partial
projection; refusal is not a claim that native evaluation fails. -/
theorem ordinary_evaluator_branch_is_outside_projection :
    executeBlock? fixtureMaterializer (functionEntryState false ordinaryEffectBody)
      (functionBodyRead :: functionEntry) = none := by
  decide +kernel

/-- An explicit return is pushed under either profile and keeps its payload
as data, including an expression that would have an effect if evaluated. -/
theorem returned_effect_payload_is_retained_raw :
    let body := Atom.expression [.symbol "return", ordinaryEffectBody]
    executeBlock? fixtureMaterializer (functionEntryState false body)
      (functionBodyRead :: functionEntry) =
      some (afterFunctionEntry (functionEntryState false body) [] body) := by
  apply execute_function_entry_minimal <;> first | rfl | exact Or.inr rfl

theorem minimal_body_is_pushed_without_compatibility :
    let body := Atom.expression [.symbol "unify", .symbol "7", .symbol "7", .symbol "1", .symbol "Empty"]
    executeBlock? fixtureMaterializer (functionEntryState false body)
      (functionBodyRead :: functionEntry) =
      some (afterFunctionEntry (functionEntryState false body) [] body) := by
  apply execute_function_entry_minimal <;> first | rfl | exact Or.inl rfl

/-- A nonexpression body takes the guard's error side and cannot be licensed
as the expression-body branch merely by enabling compatibility. -/
theorem nonexpression_body_fails_expression_branch_admission :
    condition? fixtureMaterializer
      (setLocal (functionEntryState true (.symbol "7")) "body".toList (.symbol "7"))
      functionBodyGuard = some true := by
  decide +kernel

theorem disjunction_preserves_short_circuit :
    condition? fixtureMaterializer fixtureState
      (.binary .or (.bool true) (call "unavailable_helper" [])) = some true := by rfl

theorem missing_boolean_local_is_refused :
    condition? fixtureMaterializer fixtureState (identifier "step") = none := by rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.InstructionControl.Controls

/-! ## Native RESULT/CALLER storage and retained readback

The following selected-source adapter uses logical typed C cells. It covers
the successful allocated-frame paths under the stated helper footprints, not
the allocator, native byte ABI, GC roots, cancellation or whole C dispatch.
Native stack assertions and array/header lifetimes are separate admissions.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

open Mettapedia.Machines
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/- The fields are logical typed cells. Their byte offsets and the validity of
the surrounding C objects are separate layout/ownership obligations. -/
def stackLayout : ReadExpressions.Layout := fun name =>
  if name = "top".toList then some ⟨0, .pointer⟩
  else if name = "depth".toList then some ⟨1, .word64⟩
  else if name = "next".toList then some ⟨0, .pointer⟩
  else none

def stackEnvironment (stack frame : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "stack".toList then some (.ptr (some stack))
  else if name = "frame".toList then some (.ptr (some frame)) else none

def pushNext : CStatement := .assign
  (.field (.identifier "frame".toList) "next".toList true)
  (.field (.identifier "stack".toList) "top".toList true)

def pushTop : CStatement := .assign
  (.field (.identifier "stack".toList) "top".toList true)
  (.identifier "frame".toList)

def incrementDepth : CStatement :=
  .effect (.postIncrement (.field (.identifier "stack".toList) "depth".toList true))

def popTop : CStatement := .assign
  (.field (.identifier "stack".toList) "top".toList true)
  (.field (.identifier "frame".toList) "next".toList true)

def clearNext : CStatement := .assign
  (.field (.identifier "frame".toList) "next".toList true) .null

def decrementDepth : CStatement :=
  .effect (.postDecrement (.field (.identifier "stack".toList) "depth".toList true))

def pushBody : List CStatement := [pushNext, pushTop, incrementDepth]
def popBody : List CStatement := [popTop, clearNext, decrementDepth,
  .return (some (.identifier "frame".toList))]

def push_nextSource : String := "{ frame->next = stack->top; }"
def push_nextTokens : List Token := [.punctuation ['{'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['n', 'e', 'x', 't'], .punctuation ['='], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation ['-', '>'], .identifier ['t', 'o', 'p'], .punctuation [';'], .punctuation ['}']]
theorem push_next_lex : lex push_nextSource.toList = .ok push_nextTokens := by
  apply lex_of_completed
  decide +kernel
theorem push_next_parsed : blockText? [] push_nextSource.toList = some [pushNext] :=
  block_text_of_parts [] _ push_nextTokens _ push_next_lex (by rfl)

def push_topSource : String := "{ stack->top = frame; }"
def push_topTokens : List Token := [.punctuation ['{'], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation ['-', '>'], .identifier ['t', 'o', 'p'], .punctuation ['='], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation [';'], .punctuation ['}']]
theorem push_top_lex : lex push_topSource.toList = .ok push_topTokens := by
  apply lex_of_completed
  decide +kernel
theorem push_top_parsed : blockText? [] push_topSource.toList = some [pushTop] :=
  block_text_of_parts [] _ push_topTokens _ push_top_lex (by rfl)

def increment_depthSource : String := "{ stack->depth++; }"
def increment_depthTokens : List Token := [.punctuation ['{'], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation ['-', '>'], .identifier ['d', 'e', 'p', 't', 'h'], .punctuation ['+', '+'], .punctuation [';'], .punctuation ['}']]
theorem increment_depth_lex : lex increment_depthSource.toList = .ok increment_depthTokens := by
  apply lex_of_completed
  decide +kernel
theorem increment_depth_parsed : blockText? [] increment_depthSource.toList = some [incrementDepth] :=
  block_text_of_parts [] _ increment_depthTokens _ increment_depth_lex (by rfl)

def pop_topSource : String := "{ stack->top = frame->next; }"
def pop_topTokens : List Token := [.punctuation ['{'], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation ['-', '>'], .identifier ['t', 'o', 'p'], .punctuation ['='], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['n', 'e', 'x', 't'], .punctuation [';'], .punctuation ['}']]
theorem pop_top_lex : lex pop_topSource.toList = .ok pop_topTokens := by
  apply lex_of_completed
  decide +kernel
theorem pop_top_parsed : blockText? [] pop_topSource.toList = some [popTop] :=
  block_text_of_parts [] _ pop_topTokens _ pop_top_lex (by rfl)

def clear_nextSource : String := "{ frame->next = NULL; }"
def clear_nextTokens : List Token := [.punctuation ['{'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['n', 'e', 'x', 't'], .punctuation ['='], .identifier ['N', 'U', 'L', 'L'], .punctuation [';'], .punctuation ['}']]
theorem clear_next_lex : lex clear_nextSource.toList = .ok clear_nextTokens := by
  apply lex_of_completed
  decide +kernel
theorem clear_next_parsed : blockText? [] clear_nextSource.toList = some [clearNext] :=
  block_text_of_parts [] _ clear_nextTokens _ clear_next_lex (by rfl)

def decrement_depthSource : String := "{ stack->depth--; }"
def decrement_depthTokens : List Token := [.punctuation ['{'], .identifier ['s', 't', 'a', 'c', 'k'], .punctuation ['-', '>'], .identifier ['d', 'e', 'p', 't', 'h'], .punctuation ['-', '-'], .punctuation [';'], .punctuation ['}']]
theorem decrement_depth_lex : lex decrement_depthSource.toList = .ok decrement_depthTokens := by
  apply lex_of_completed
  decide +kernel
theorem decrement_depth_parsed : blockText? [] decrement_depthSource.toList = some [decrementDepth] :=
  block_text_of_parts [] _ decrement_depthTokens _ decrement_depth_lex (by rfl)

/-- The statement provider executes the actual scalar field selected by the
parsed increment/decrement. A missing field or wrong scalar tag is undefined. -/
def depthEffect : StatementBlock.Effect := fun layout environment expression => do
  let (owner, name, increment) ← ReadExpressions.resolved (match expression with
    | .postIncrement (.field owner name true) => some (owner, name, true)
    | .postDecrement (.field owner name true) => some (owner, name, false)
    | _ => none)
  let descriptor ← ReadExpressions.resolved (layout name)
  if descriptor.kind = .word64 then
    let actual ← ReadExpressions.expression layout environment owner
    let address ← ReadExpressions.fieldAddress layout actual name
    let current ← CProg.loadU64 address
    CProg.store address (.u64 (if increment then current + 1 else current - 1))
  else CProg.undefined

def stackServices : StatementBlock.Services where
  effect := depthEffect

/-- The assertions and local `frame = stack->top` preceding these exact source
statements supply the non-null, depth and selected-head preconditions below. -/
def pushProgram (stack frame : Ptr) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith stackServices
    (StatementBlock.fieldAssignment ReadExpressions.expression) stackLayout 0 4
    (stackEnvironment stack frame) pushBody

def popProgram (stack frame : Ptr) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith stackServices
    (StatementBlock.fieldAssignment ReadExpressions.expression) stackLayout 0 5
    (stackEnvironment stack frame) popBody

def pushOperations (stack frame : Ptr) : CProg CVal ReadBlock.Result := do
  let top ← CProg.loadPtr stack
  CProg.store frame (.ptr top)
  CProg.store stack (.ptr (some frame))
  let depth ← CProg.loadU64 (stack + 1)
  CProg.store (stack + 1) (.u64 (depth + 1))
  pure (.finished (.next (stackEnvironment stack frame)))

def popOperations (stack frame : Ptr) : CProg CVal ReadBlock.Result := do
  let next ← CProg.loadPtr frame
  CProg.store stack (.ptr next)
  CProg.store frame (.ptr none)
  let depth ← CProg.loadU64 (stack + 1)
  CProg.store (stack + 1) (.u64 (depth - 1))
  pure (.finished (.returned (stackEnvironment stack frame) (some (.ptr (some frame)))))

theorem push_uses_memory (stack frame : Ptr) :
    pushProgram stack frame = pushOperations stack frame := by
  simp [pushProgram, pushBody, pushNext, pushTop, incrementDepth,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, stackServices, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames, ReadExpressions.field,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.fieldAddress, stackLayout, stackEnvironment, depthEffect,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, pushOperations,
    ptr_add_zero, ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.valueKind]

theorem pop_uses_memory (stack frame : Ptr) :
    popProgram stack frame = popOperations stack frame := by
  simp [popProgram, popBody, popTop, clearNext, decrementDepth,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, stackServices, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames, ReadExpressions.field,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.fieldAddress, stackLayout, stackEnvironment, depthEffect,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, popOperations,
    ptr_add_zero, ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.valueKind]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem push_owned (stack frame : Ptr) (top prior : Option Ptr) (depth : UInt64)
    (rest : Heap L → Prop) :
    CTriple (PointsTo stack (.ptr top) ∗ PointsTo (stack + 1) (.u64 depth) ∗
      PointsTo frame (.ptr prior) ∗ rest) (pushProgram stack frame)
      (fun result heap => result = .finished (.next (stackEnvironment stack frame)) ∧
        (PointsTo stack (.ptr (some frame)) ∗ PointsTo (stack + 1) (.u64 (depth + 1)) ∗
          PointsTo frame (.ptr top) ∗ rest) heap) := by
  rw [push_uses_memory]
  cmem_start heap held
  unfold pushOperations
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  cmem_exact

theorem pop_owned (stack frame : Ptr) (next : Option Ptr) (depth : UInt64)
    (rest : Heap L → Prop) :
    CTriple (PointsTo stack (.ptr (some frame)) ∗ PointsTo (stack + 1) (.u64 depth) ∗
      PointsTo frame (.ptr next) ∗ rest) (popProgram stack frame)
      (fun result heap =>
        result = .finished (.returned (stackEnvironment stack frame) (some (.ptr (some frame)))) ∧
        (PointsTo stack (.ptr next) ∗ PointsTo (stack + 1) (.u64 (depth - 1)) ∗
          PointsTo frame (.ptr none) ∗ rest) heap) := by
  rw [pop_uses_memory]
  cmem_start heap held
  unfold popOperations
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  cmem_exact

/-- The existing intrusive chain represented by physical next-pointer cells.
The rest of each frame is retained separately by the ordinary frame rule. -/
def LinkCells : List Ptr → Heap L → Prop
  | [] => emp
  | frame :: rest => PointsTo frame (.ptr rest.head?) ∗ LinkCells rest

def StackCells (stack : Ptr) (active : List Ptr) : Heap L → Prop :=
  PointsTo stack (.ptr active.head?) ∗
    PointsTo (stack + 1) (.u64 (UInt64.ofNat active.length)) ∗ LinkCells active

def pointerCell (heap : Heap L) (address : Ptr) : Option (Option Ptr) :=
  match read ((heap address.block).2 address.offset) with
  | some (some (.ptr value)) => some value
  | _ => none

def nativeLinks (heap : Heap L) (top : Option Ptr) : LinkedScopeStack Ptr :=
  ⟨top, fun frame => (pointerCell heap frame).join⟩

theorem links_readback (active : List Ptr) (heap : Heap L) (rest : Heap L → Prop)
    (held : (LinkCells active ∗ rest) heap) :
    LinkedScopeStack.MatchesLinks (nativeLinks heap none).parent active := by
  induction active generalizing rest with
  | nil => trivial
  | cons frame frames ih =>
      have splitHeld : (PointsTo frame (.ptr frames.head?) ∗ (LinkCells frames ∗ rest)) heap := by
        simpa only [LinkCells, sepConj_assoc] using held
      have headRead := read_of_pointsTo splitHeld
      refine ⟨?_, ih (PointsTo frame (.ptr frames.head?) ∗ rest) ?_⟩
      · simp [nativeLinks, pointerCell, headRead]
      · simpa only [sepConj_left_comm] using splitHeld

theorem stack_readback (stack : Ptr) (active : List Ptr) (heap : Heap L)
    (rest : Heap L → Prop) (held : (StackCells stack active ∗ rest) heap)
    (distinct : active.Nodup) :
    pointerCell heap stack = some active.head? ∧
      (nativeLinks heap active.head?).Represents active := by
  have splitHeld : (PointsTo stack (.ptr active.head?) ∗
      (PointsTo (stack + 1) (.u64 (UInt64.ofNat active.length)) ∗ LinkCells active ∗ rest)) heap := by
    simpa only [StackCells, sepConj_assoc] using held
  have topRead := read_of_pointsTo splitHeld
  refine ⟨by simp [pointerCell, topRead], rfl, distinct, ?_⟩
  apply links_readback active heap
    (PointsTo stack (.ptr active.head?) ∗
      PointsTo (stack + 1) (.u64 (UInt64.ofNat active.length)) ∗ rest)
  cmem_exact

theorem push_stack_cells (stack frame : Ptr) (active : List Ptr) (prior : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (StackCells stack active ∗ PointsTo frame (.ptr prior) ∗ rest)
      (pushProgram stack frame)
      (fun result heap => result = .finished (.next (stackEnvironment stack frame)) ∧
        (StackCells stack (frame :: active) ∗ rest) heap) := by
  have checked := push_owned stack frame active.head? prior (UInt64.ofNat active.length)
    (LinkCells active ∗ rest)
  apply triple_consequence _ ?_ checked ?_
  · intro heap held
    unfold StackCells at held
    cmem_exact
  · intro result heap held
    refine ⟨held.1, ?_⟩
    have count : UInt64.ofNat (frame :: active).length = UInt64.ofNat active.length + 1 := by
      simp [List.length_cons, UInt64.ofNat_add]
    simp only [StackCells, List.head?_cons, LinkCells, count]
    have stored := held.2
    cmem_exact

theorem pop_stack_cells (stack frame : Ptr) (active : List Ptr) (rest : Heap L → Prop) :
    CTriple (StackCells stack (frame :: active) ∗ rest)
      (popProgram stack frame)
      (fun result heap =>
        result = .finished (.returned (stackEnvironment stack frame) (some (.ptr (some frame)))) ∧
          (StackCells stack active ∗ PointsTo frame (.ptr none) ∗ rest) heap) := by
  have checked := pop_owned stack frame active.head? (UInt64.ofNat (frame :: active).length)
    (LinkCells active ∗ rest)
  apply triple_consequence _ ?_ checked ?_
  · intro heap held
    simp only [StackCells, LinkCells, List.head?_cons] at held
    cmem_exact
  · intro result heap held
    refine ⟨held.1, ?_⟩
    have count : UInt64.ofNat (frame :: active).length - 1 = UInt64.ofNat active.length := by
      simp [List.length_cons, UInt64.ofNat_add]
    simp only [StackCells]
    have stored := held.2
    rw [count] at stored
    cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- Logical scalar-cell offsets supplied by the admitted native record layout.
The intrusive link is the first member. Embedded bindings and outcome storage
are owned outside these scalar cells and are not encoded as scalar pointers. -/
structure FrameOffsets where
  kind : Nat
  phase : Nat
  space : Nat
  arena : Nat
  atom : Nat
  demand : Nat
  fuel : Nat
  target : Nat
  preserve : Nat
  selected : Nat
  index : Nat
  work : Nat
  child : Nat

def frameLayout (offset : FrameOffsets) : ReadExpressions.Layout := fun name =>
  if name = "kind".toList then some ⟨offset.kind, .word⟩
  else if name = "phase".toList then some ⟨offset.phase, .word⟩
  else if name = "space".toList then some ⟨offset.space, .pointer⟩
  else if name = "arena".toList then some ⟨offset.arena, .pointer⟩
  else if name = "atom".toList then some ⟨offset.atom, .pointer⟩
  else if name = "type".toList then some ⟨offset.demand, .pointer⟩
  else if name = "fuel".toList then some ⟨offset.fuel, .signedWord⟩
  else if name = "target".toList then some ⟨offset.target, .pointer⟩
  else if name = "preserve_bindings".toList then some ⟨offset.preserve, .boolean⟩
  else if name = "selected".toList then some ⟨offset.selected, .boolean⟩
  else if name = "index".toList then some ⟨offset.index, .word64⟩
  else if name = "work".toList then some ⟨offset.work, .embedded⟩
  else if name = "child".toList then some ⟨offset.child, .embedded⟩
  else if name = "next".toList then some ⟨0, .pointer⟩
  else none

/-- The actual scalar arguments of `he_canonical_push`, before pointer payloads
are interpreted as source atoms or a binding theory. -/
structure PushArguments where
  kind : UInt32
  space : Option Ptr
  arena : Option Ptr
  atom : Option Ptr
  demand : Option Ptr
  fuel : Int32
  target : Option Ptr
  preserve : Bool
  deriving DecidableEq, Repr

def pushEnvironment (frame : Ptr) (arguments : PushArguments) : ReadExpressions.Environment :=
  fun name =>
    if name = "frame".toList then some (.ptr (some frame))
    else if name = "kind".toList then some (.u32 arguments.kind)
    else if name = "s".toList then some (.ptr arguments.space)
    else if name = "a".toList then some (.ptr arguments.arena)
    else if name = "atom".toList then some (.ptr arguments.atom)
    else if name = "type".toList then some (.ptr arguments.demand)
    else if name = "fuel".toList then some (.i32 arguments.fuel)
    else if name = "target".toList then some (.ptr arguments.target)
    else if name = "preserve".toList then some (.bool arguments.preserve)
    else none

def frameAssignment (field value : String) : CStatement :=
  .assign (.field (.identifier "frame".toList) field.toList true) (.identifier value.toList)

def initializationBody : List CStatement :=
  [frameAssignment "kind" "kind", frameAssignment "space" "s",
   frameAssignment "arena" "a", frameAssignment "atom" "atom",
   frameAssignment "type" "type", frameAssignment "fuel" "fuel",
   frameAssignment "target" "target", frameAssignment "preserve_bindings" "preserve"]

def initializeFields (offset : FrameOffsets) (frame : Ptr) (arguments : PushArguments) :
    CProg CVal ReadBlock.Result :=
  StatementBlock.execute (StatementBlock.fieldAssignment ReadExpressions.expression)
    (frameLayout offset) 0 9 (pushEnvironment frame arguments) initializationBody

def initializationOperations (offset : FrameOffsets) (frame : Ptr) (arguments : PushArguments) :
    CProg CVal ReadBlock.Result := do
  CProg.store (frame + offset.kind) (.u32 arguments.kind)
  CProg.store (frame + offset.space) (.ptr arguments.space)
  CProg.store (frame + offset.arena) (.ptr arguments.arena)
  CProg.store (frame + offset.atom) (.ptr arguments.atom)
  CProg.store (frame + offset.demand) (.ptr arguments.demand)
  CProg.store (frame + offset.fuel) (.i32 arguments.fuel)
  CProg.store (frame + offset.target) (.ptr arguments.target)
  CProg.store (frame + offset.preserve) (.bool arguments.preserve)
  pure (.finished (.next (pushEnvironment frame arguments)))

theorem initialization_uses_memory (offset : FrameOffsets) (frame : Ptr)
    (arguments : PushArguments) :
    initializeFields offset frame arguments = initializationOperations offset frame arguments := by
  simp [initializeFields, initializationBody, frameAssignment,
    StatementBlock.execute, StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames, ReadExpressions.storeField,
    ReadExpressions.pointer, ReadExpressions.resolved, ReadExpressions.valueKind,
    ReadExpressions.fieldAddress,
    frameLayout, pushEnvironment, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_assoc, initializationOperations]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def FrameCells (offset : FrameOffsets) (frame : Ptr) (arguments : PushArguments) :
    Heap L → Prop :=
  PointsTo (frame + offset.kind) (.u32 arguments.kind) ∗
  PointsTo (frame + offset.space) (.ptr arguments.space) ∗
  PointsTo (frame + offset.arena) (.ptr arguments.arena) ∗
  PointsTo (frame + offset.atom) (.ptr arguments.atom) ∗
  PointsTo (frame + offset.demand) (.ptr arguments.demand) ∗
  PointsTo (frame + offset.fuel) (.i32 arguments.fuel) ∗
  PointsTo (frame + offset.target) (.ptr arguments.target) ∗
  PointsTo (frame + offset.preserve) (.bool arguments.preserve)

theorem initialization_owned (offset : FrameOffsets) (frame : Ptr)
    (old arguments : PushArguments) (rest : Heap L → Prop) :
    CTriple (FrameCells offset frame old ∗ rest) (initializeFields offset frame arguments)
      (fun result heap => result = .finished (.next (pushEnvironment frame arguments)) ∧
        (FrameCells offset frame arguments ∗ rest) heap) := by
  rw [initialization_uses_memory]
  cmem_start heap held
  unfold FrameCells at *
  unfold initializationOperations
  cmem_vcgen
  cmem_exact

/-- Read the same actual typed scalar cells; malformed tags and absent storage
are refused before constructing a semantic invocation. -/
def frameArguments? (offset : FrameOffsets) (heap : Heap L) (frame : Ptr) :
    Option PushArguments := do
  let some (.u32 kind) ← read ((heap (frame + offset.kind).block).2 (frame + offset.kind).offset)
    | none
  let space ← pointerCell heap (frame + offset.space)
  let arena ← pointerCell heap (frame + offset.arena)
  let atom ← pointerCell heap (frame + offset.atom)
  let demand ← pointerCell heap (frame + offset.demand)
  let some (.i32 fuel) ← read ((heap (frame + offset.fuel).block).2 (frame + offset.fuel).offset)
    | none
  let target ← pointerCell heap (frame + offset.target)
  let some (.bool preserve) ← read ((heap (frame + offset.preserve).block).2
    (frame + offset.preserve).offset) | none
  pure ⟨kind, space, arena, atom, demand, fuel, target, preserve⟩

theorem owned_fields_readback (offset : FrameOffsets) (frame : Ptr) (arguments : PushArguments)
    (rest : Heap L → Prop) (heap : Heap L) (held : (FrameCells offset frame arguments ∗ rest) heap) :
    frameArguments? offset heap frame = some arguments := by
  unfold FrameCells at held
  have kindRead : Reads (frame + offset.kind) (.u32 arguments.kind) heap := by cmem_fact
  have spaceRead : Reads (frame + offset.space) (.ptr arguments.space) heap := by cmem_fact
  have arenaRead : Reads (frame + offset.arena) (.ptr arguments.arena) heap := by cmem_fact
  have atomRead : Reads (frame + offset.atom) (.ptr arguments.atom) heap := by cmem_fact
  have demandRead : Reads (frame + offset.demand) (.ptr arguments.demand) heap := by cmem_fact
  have fuelRead : Reads (frame + offset.fuel) (.i32 arguments.fuel) heap := by cmem_fact
  have targetRead : Reads (frame + offset.target) (.ptr arguments.target) heap := by cmem_fact
  have preserveRead : Reads (frame + offset.preserve) (.bool arguments.preserve) heap := by cmem_fact
  simp only [Reads] at kindRead spaceRead arenaRead atomRead demandRead fuelRead targetRead preserveRead
  simp only [frameArguments?, pointerCell, kindRead, spaceRead, arenaRead, atomRead, demandRead, fuelRead, targetRead, preserveRead]
  rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open OSLFCore (Atom)

/-- Source payload readback is separate from the C frame's scalar storage.
These partial decoders must be supplied by the actual atom, space and binding
owners. They do not return an Invocation or assert any frame-step simulation. -/
structure PayloadReadback where
  atom : Ptr → Option Atom
  space : Ptr → Option Space
  bindings : Ptr → Option Bindings

def pointerIdentity (address : Ptr) : Nat := Nat.pair address.block address.offset

theorem pointerIdentity_injective : Function.Injective pointerIdentity := by
  intro left right equal
  have components := Nat.pair_eq_pair.mp equal
  cases left
  cases right
  cases components.1
  cases components.2
  rfl

/-- The parent sequencer and its physical row jointly name an occurrence.
Equal payloads never supply this identity. -/
structure NativeCaller where
  frame : Ptr
  parents : List Ptr
  deriving DecidableEq, Repr

/-- Pointer results of the reached materializer and relay calls, plus the
actual inline environment address of the selected outcome. No field here is
an independently asserted source result or evaluation relation. -/
structure PreparedOutcome where
  seed : Ptr
  environment : Ptr
  materialized : Ptr
  variantOnly : Ptr
  relay : Ptr
  row : Nat
  deriving DecidableEq, Repr

def demandReadback (payloads : PayloadReadback) : Option Ptr → Option Atom
  | none => some Atom.undefinedType
  | some address => payloads.atom address

/-- The RESULT control point is an ordinary raw-return owner. Its admitted
entry path supplies that provenance; completed-native owners use another map.
The invocation is constructed from decoded native fields and pointer payloads. -/
def invocationOfFields? (payloads : PayloadReadback) (caller : NativeCaller)
    (arguments : PushArguments) (prepared : PreparedOutcome) :
    Option (CallReturnControl.Invocation NativeCaller) := do
  if arguments.kind != 7 then none else do
    let spaceAddress ← arguments.space
    let space ← payloads.space spaceAddress
    let callAddress ← arguments.atom
    let original ← payloads.atom callAddress
    let demand ← demandReadback payloads arguments.demand
    let reached ← payloads.bindings prepared.environment
    let materialized ← payloads.atom prepared.materialized
    let variantOnly ← payloads.atom prepared.variantOnly
    let target ← arguments.target
    pure {
      caller := caller
      space := space
      original := original
      demand := demand
      row := prepared.row
      reached := reached
      materialized := materialized
      variantOnly := variantOnly
      target := pointerIdentity target
      relayTarget := pointerIdentity prepared.relay
      fuel := arguments.fuel.toInt
      preserveBindings := arguments.preserve
      provenance := .raw }

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def invocationReadback? (offset : FrameOffsets) (payloads : PayloadReadback)
    (heap : Heap L) (caller : NativeCaller) (prepared : PreparedOutcome) :
    Option (CallReturnControl.Invocation NativeCaller) := do
  let arguments ← frameArguments? offset heap caller.frame
  invocationOfFields? payloads caller arguments prepared

theorem invocation_readback_from_owned_fields (offset : FrameOffsets)
    (payloads : PayloadReadback) (caller : NativeCaller) (prepared : PreparedOutcome)
    (arguments : PushArguments) (rest : Heap L → Prop) (heap : Heap L)
    (owned : (FrameCells offset caller.frame arguments ∗ rest) heap) :
    invocationReadback? offset payloads heap caller prepared =
      invocationOfFields? payloads caller arguments prepared := by
  unfold invocationReadback?
  rw [owned_fields_readback offset caller.frame arguments rest heap owned]
  rfl

/-- The semantic environment comes from the selected outcome's environment
address, not the result frame's initially empty `env` member. -/
theorem invocation_environment_is_selected (payloads : PayloadReadback)
    (caller : NativeCaller) (arguments : PushArguments) (prepared : PreparedOutcome)
    (invocation : CallReturnControl.Invocation NativeCaller)
    (decoded : invocationOfFields? payloads caller arguments prepared = some invocation) :
    payloads.bindings prepared.environment = some invocation.reached ∧
      invocation.row = prepared.row ∧ invocation.caller = caller ∧
      invocation.relayTarget = pointerIdentity prepared.relay := by
  unfold invocationOfFields? at decoded
  split at decoded
  · cases decoded
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨spaceAddress, _, space, _, callAddress, _, original, _, demand, _,
      reached, reachedRead, materialized, _, variantOnly, _, target, _, exactInvocation⟩ := decoded
    cases exactInvocation
    exact ⟨reachedRead, rfl, rfl, rfl⟩



def initializeAndLink (offset : FrameOffsets) (stack frame : Ptr)
    (arguments : PushArguments) : CProg CVal ReadBlock.Result := do
  let _ ← initializeFields offset frame arguments
  pushProgram stack frame

theorem initialize_and_link_owned (offset : FrameOffsets) (stack frame : Ptr)
    (active : List Ptr) (old arguments : PushArguments) (prior : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (FrameCells offset frame old ∗ StackCells stack active ∗
      PointsTo frame (.ptr prior) ∗ rest)
      (initializeAndLink offset stack frame arguments)
      (fun result heap => result = .finished (.next (stackEnvironment stack frame)) ∧
        (FrameCells offset frame arguments ∗ StackCells stack (frame :: active) ∗ rest) heap) := by
  unfold initializeAndLink
  refine triple_bind _
    (initialization_owned offset frame old arguments
      (StackCells stack active ∗ PointsTo frame (.ptr prior) ∗ rest)) fun _ => ?_
  apply triple_pure
  intro _
  apply triple_consequence _ ?_
    (push_stack_cells stack frame active prior (FrameCells offset frame arguments ∗ rest)) ?_
  · intro heap held
    cmem_exact
  · intro result heap held
    refine ⟨held.1, ?_⟩
    have stored := held.2
    cmem_exact

theorem initialized_invocation_square (offset : FrameOffsets) (stack : Ptr)
    (caller : NativeCaller) (prepared : PreparedOutcome) (payloads : PayloadReadback)
    (old arguments : PushArguments) (prior : Option Ptr) (rest : Heap L → Prop) :
    CTriple (FrameCells offset caller.frame old ∗ StackCells stack caller.parents ∗
      PointsTo caller.frame (.ptr prior) ∗ rest)
      (initializeAndLink offset stack caller.frame arguments)
      (fun result heap =>
        result = .finished (.next (stackEnvironment stack caller.frame)) ∧
        invocationReadback? offset payloads heap caller prepared =
          invocationOfFields? payloads caller arguments prepared ∧
        (FrameCells offset caller.frame arguments ∗
          StackCells stack (caller.frame :: caller.parents) ∗ rest) heap) := by
  apply triple_post _ (initialize_and_link_owned offset stack caller.frame caller.parents
    old arguments prior rest)
  intro result heap reached
  refine ⟨reached.1, ?_, reached.2⟩
  apply invocation_readback_from_owned_fields offset payloads caller prepared arguments
    (StackCells stack (caller.frame :: caller.parents) ∗ rest) heap
  simpa only [sepConj_assoc] using reached.2

/-- This is the exact phase assignment already parsed from the ordinary
callback tail in the frozen source-square owner. -/
def setResultPhase (offset : FrameOffsets) (frame : Ptr) : CProg CVal ReadBlock.Result :=
  StatementBlock.execute (StatementBlock.fieldAssignment ReadExpressions.expression)
    (frameLayout offset) 0 2 (fun name =>
      if name = "frame".toList then some (.ptr (some frame)) else none)
    [CallReturnControl.resumePhase]

theorem phase_uses_memory (offset : FrameOffsets) (frame : Ptr) :
    setResultPhase offset frame =
      (CProg.store (frame + offset.phase) (.u32 1) >>= fun _ => pure (.finished (.next
        (fun name => if name = "frame".toList then some (.ptr (some frame)) else none)))) := by
  simp [setResultPhase, CallReturnControl.resumePhase, InstructionControl.field,
    InstructionControl.identifier, StatementBlock.execute, StatementBlock.executeWith,
    StatementBlock.executeScopedWith, StatementBlock.Services.scoped,
    StatementBlock.fieldAssignment, ReadExpressions.expression,
    ReadExpressions.expressionWith, ReadExpressions.expressionWithNames,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.valueKind, ReadExpressions.fieldAddress,
    frameLayout, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem phase_owned (offset : FrameOffsets) (frame : Ptr) (phase : UInt32)
    (rest : Heap L → Prop) :
    CTriple (PointsTo (frame + offset.phase) (.u32 phase) ∗ rest)
      (setResultPhase offset frame)
      (fun _ => PointsTo (frame + offset.phase) (.u32 1) ∗ rest) := by
  rw [phase_uses_memory]
  cmem_start heap held
  cmem_vcgen
  cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open OSLFCore (Atom)

/-- Embedded Outcome.env is addressed, never loaded as a pointer cell. -/
def callbackLayout (offset : FrameOffsets) (environmentOffset : Nat) :
    ReadExpressions.Layout := fun name =>
  if name = "env".toList then some ⟨environmentOffset, .embedded⟩ else frameLayout offset name

def callbackEnvironment (frame : Ptr) (arena : Option Ptr) (seed : Ptr) :
    ReadExpressions.Environment := fun name =>
  if name = "HE_CANONICAL_CALLER".toList then some (.u32 3)
  else if name = "frame".toList then some (.ptr (some frame))
  else if name = "a".toList then some (.ptr arena)
  else if name = "seed".toList then some (.ptr (some seed)) else none

/-- Evaluate the operands of the already parsed actual call. The named helper
service remains effectful. It does not receive a semantic request or expected
result. Only the reached ordinary tail, not the preceding dispatch, is covered. -/
def callerOperands (calls : ReadExpressions.Calls) (offset : FrameOffsets)
    (environmentOffset : Nat) (frame : Ptr) (arena : Option Ptr) (seed : Ptr) :
    CProg CVal (List CVal) :=
  match CallReturnControl.resumePush with
  | .effect (.call name arguments) =>
      if name = "he_canonical_push".toList then
        ReadExpressions.argumentsWithNames
          (fun name => ReadExpressions.resolved (callbackEnvironment frame arena seed name))
          calls (callbackLayout offset environmentOffset) arguments
      else CProg.undefined
  | _ => CProg.undefined

/-- The source operands load the retained fields and call each actual helper
once. C's operand-order portability still requires the two helper effects and
these frame reads to commute; this is the existing left-to-right C reader. -/
def callerOperandOperations (calls : ReadExpressions.Calls) (offset : FrameOffsets)
    (environmentOffset : Nat) (frame : Ptr) (arena : Option Ptr) (seed : Ptr) :
    CProg CVal (List CVal) := do
  let space ← CProg.loadPtr (frame + offset.space)
  let input ← calls "outcome_atom_materialize_variant_only".toList
    [.ptr arena, .ptr (some seed)]
  let demand ← CProg.loadPtr (frame + offset.demand)
  let fuel ← CProg.loadI32 (frame + offset.fuel)
  let preserve ← CProg.loadBool (frame + offset.preserve)
  let target ← calls "he_relay_sink".toList
    [.ptr (some frame), .ptr (some (frame + offset.child))]
  pure [.u32 3, .ptr space, .ptr arena, input, .ptr demand, .i32 fuel,
    .ptr (some (seed + environmentOffset)), .bool preserve, target]

theorem caller_operands_use_fields (calls : ReadExpressions.Calls) (offset : FrameOffsets)
    (environmentOffset : Nat) (frame : Ptr) (arena : Option Ptr) (seed : Ptr) :
    callerOperands calls offset environmentOffset frame arena seed =
      callerOperandOperations calls offset environmentOffset frame arena seed := by
  simp [callerOperands, CallReturnControl.resumePush, CallReturnControl.frameType,
    CallReturnControl.seedEnv, CallReturnControl.framePreserve, CallReturnControl.frameChild,
    InstructionControl.identifier, InstructionControl.field, InstructionControl.call,
    InstructionControl.address, callbackEnvironment, callbackLayout, frameLayout,
    ReadExpressions.argumentsWithNames, ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    callerOperandOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

structure CallerArguments where
  scalar : PushArguments
  environment : Ptr
  deriving DecidableEq, Repr

def decodeCallerArguments : List CVal → Option CallerArguments
  | [.u32 kind, .ptr space, .ptr arena, .ptr input, .ptr demand, .i32 fuel,
      .ptr (some environment), .bool preserve, .ptr target] =>
      if kind = 3 then some ⟨⟨kind, space, arena, input, demand, fuel, target, preserve⟩,
        environment⟩ else none
  | _ => none

def callbackArguments (parent : PushArguments) (seed input relay : Ptr)
    (environmentOffset : Nat) : CallerArguments :=
  ⟨⟨3, parent.space, parent.arena, some input, parent.demand, parent.fuel,
    some relay, parent.preserve⟩, seed + environmentOffset⟩

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Helpers own and transform their own storage. Their frame rule preserves
all saved invocation fields while allowing allocation, inflation and relay
metadata to change. No whole native/source correspondence is assumed. -/
theorem caller_operands_owned (calls : ReadExpressions.Calls) (offset : FrameOffsets)
    (environmentOffset : Nat) (frame seed input relay : Ptr) (parent : PushArguments)
    (before middle after : Heap L → Prop)
    (materializer : CTriple before
      (calls "outcome_atom_materialize_variant_only".toList [.ptr parent.arena, .ptr (some seed)])
      (fun value heap => value = .ptr (some input) ∧ middle heap))
    (relaySink : CTriple middle
      (calls "he_relay_sink".toList
        [.ptr (some frame), .ptr (some (frame + offset.child))])
      (fun value heap => value = .ptr (some relay) ∧ after heap)) :
    CTriple (FrameCells offset frame parent ∗ before)
      (callerOperands calls offset environmentOffset frame parent.arena seed)
      (fun values heap =>
        decodeCallerArguments values = some (callbackArguments parent seed input relay environmentOffset) ∧
        (FrameCells offset frame parent ∗ after) heap) := by
  rw [caller_operands_use_fields]
  cmem_start heap held
  unfold callerOperandOperations
  unfold FrameCells at *
  cmem_vcgen
  cmem_call materializer with value heap ⟨rfl, held⟩
  simp only [CProg.loadI32, Prog.bind_eq]
  cmem_vcgen
  cmem_call relaySink with value heap ⟨rfl, held⟩
  constructor
  · rfl
  · cmem_exact

/-- The request is read back from the evaluated physical operands. Its saved
invocation comes from the separately constructed parent-frame readback. -/
def requestOfCaller? (payloads : PayloadReadback)
    (invocation : CallReturnControl.Invocation NativeCaller) (arguments : CallerArguments) :
    Option (CallReturnControl.Request NativeCaller) := do
  let inputAddress ← arguments.scalar.atom
  let input ← payloads.atom inputAddress
  let demand ← demandReadback payloads arguments.scalar.demand
  let bindings ← payloads.bindings arguments.environment
  let target ← arguments.scalar.target
  pure ⟨invocation, input, demand, bindings, pointerIdentity target⟩

/-- Unlike a request oracle, the physical operand decoder requires the input
and environment reached by the actual materializer, and the saved type field. -/
theorem callback_request_fields (payloads : PayloadReadback)
    (invocation : CallReturnControl.Invocation NativeCaller) (parent : PushArguments)
    (seed input relay : Ptr) (environmentOffset : Nat)
    (inputRead : payloads.atom input = some invocation.variantOnly)
    (demandRead : demandReadback payloads parent.demand = some invocation.demand)
    (bindingsRead : payloads.bindings (seed + environmentOffset) = some invocation.reached)
    (targetRead : pointerIdentity relay = invocation.relayTarget) :
    requestOfCaller? payloads invocation
      (callbackArguments parent seed input relay environmentOffset) =
      some ⟨invocation, invocation.variantOnly, invocation.demand,
        invocation.reached, invocation.relayTarget⟩ := by
  simp only [requestOfCaller?, callbackArguments, inputRead, demandRead, bindingsRead,
    targetRead, Option.bind_some, bind]
  rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

structure OutcomeOffsets where
  items : Nat
  len : Nat
  environment : Nat
  extent : Nat

def cursorLayout (frame : FrameOffsets) (outcome : OutcomeOffsets) : ReadExpressions.Layout :=
  fun name => if name = "items".toList then some ⟨outcome.items, .pointer⟩
    else if name = "len".toList then some ⟨outcome.len, .word64⟩
    else frameLayout frame name

def cursorNames (frame : Ptr) : ReadExpressions.NameReads := fun name =>
  ReadExpressions.resolved (if name = "frame".toList then some (.ptr (some frame)) else none)

def cursorObjects : ReadExpressions.ObjectReads := { place := some (fun _ => none) }

def cursorIndex : CExpr := .field (.identifier "frame".toList) "index".toList true
def cursorItems : CExpr := .field
  (.field (.identifier "frame".toList) "work".toList true) "items".toList false
def cursorLength : CExpr := .field
  (.field (.identifier "frame".toList) "work".toList true) "len".toList false

def cursorGuard : CExpr := .binary .ge cursorIndex cursorLength

def cursorSeed : CExpr := .unary .address (.index cursorItems (.postIncrement cursorIndex))

def cursorDeclaration : CStatement :=
  .declare ⟨"Outcome".toList, 1⟩ "seed".toList cursorSeed

/-- The post-index operator returns the old position and advances the actual
counter cell. The aggregate-array stride is supplied by its admitted layout;
ordinary array bounds and native ABI correspondence remain required. -/
def postIndexAddress (extent : Nat) (names : ReadExpressions.NameReads)
    (layout : ReadExpressions.Layout) (objects : ReadExpressions.ObjectReads) :
    CExpr → CProg CVal (Ptr × Nat)
  | .unary .address (.index array (.postIncrement counter@(.field owner field through))) => do
      let arrayValue ← ReadExpressions.expressionWithNames names ReadExpressions.noCalls
        layout array objects
      let arrayAddress ← ReadExpressions.pointer arrayValue >>= ReadExpressions.resolved
      let descriptor ← ReadExpressions.resolved ((objects.fieldLayout layout owner through) field)
      if descriptor.kind = .word64 then
        let counterAddress ← ReadExpressions.placeWithNames names ReadExpressions.noCalls
          layout counter objects
        let index ← CProg.loadU64 counterAddress
        CProg.store counterAddress (.u64 (index + 1))
        pure (arrayAddress + index.toNat * extent, index.toNat)
      else CProg.undefined
  | _ => CProg.undefined

/-- This covers the selected RESULT sequencer branch. Exhaustion returns the
branch tag; the physical pop is composed separately rather than concealed. -/
def selectNext (offset : FrameOffsets) (outcome : OutcomeOffsets) (frame : Ptr) :
    CProg CVal (Option (Ptr × Nat)) := do
  let condition ← ReadExpressions.expressionWithNames (cursorNames frame)
    ReadExpressions.noCalls (cursorLayout offset outcome) cursorGuard cursorObjects
  let exhausted ← ReadExpressions.truth condition
  if exhausted then pure none else do
    let selected ← postIndexAddress outcome.extent (cursorNames frame)
      (cursorLayout offset outcome) cursorObjects cursorSeed
    pure (some selected)

def selectionOperations (offset : FrameOffsets) (outcome : OutcomeOffsets) (frame : Ptr) :
    CProg CVal (Option (Ptr × Nat)) := do
  let index ← CProg.loadU64 (frame + offset.index)
  let length ← CProg.loadU64 ((frame + offset.work) + outcome.len)
  if length ≤ index then pure none else do
    let items ← CProg.loadPtr ((frame + offset.work) + outcome.items)
    let base ← ReadExpressions.resolved items
    let current ← CProg.loadU64 (frame + offset.index)
    CProg.store (frame + offset.index) (.u64 (current + 1))
    pure (some (base + current.toNat * outcome.extent, current.toNat))

theorem selection_uses_cursor_cells (offset : FrameOffsets) (outcome : OutcomeOffsets)
    (frame : Ptr) :
    selectNext offset outcome frame = selectionOperations offset outcome frame := by
  simp [selectNext, cursorGuard, cursorSeed, cursorIndex, cursorItems, cursorLength,
    postIndexAddress, cursorNames, cursorObjects, cursorLayout, frameLayout,
    ReadExpressions.expressionWithNames,
    ReadExpressions.placeWithNames, ReadExpressions.field, ReadExpressions.fieldAddress,
    ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.resolved, ReadExpressions.pointer,
    ReadExpressions.truth, ReadExpressions.binary, ReadExpressions.scalar, ReadExpressions.cell?,
    ScalarRead.numericBinary, ScalarRead.unsigned64Binary,
    selectionOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def CursorCells (offset : FrameOffsets) (outcome : OutcomeOffsets) (frame items : Ptr)
    (index length : UInt64) : Heap L → Prop :=
  PointsTo (frame + offset.index) (.u64 index) ∗
  PointsTo ((frame + offset.work) + outcome.len) (.u64 length) ∗
  PointsTo ((frame + offset.work) + outcome.items) (.ptr (some items))

theorem select_owned (offset : FrameOffsets) (outcome : OutcomeOffsets) (frame items : Ptr)
    (index length : UInt64) (beforeEnd : index < length) (rest : Heap L → Prop) :
    CTriple (CursorCells offset outcome frame items index length ∗ rest)
      (selectNext offset outcome frame)
      (fun selected heap => selected = some (items + index.toNat * outcome.extent, index.toNat) ∧
        (CursorCells offset outcome frame items (index + 1) length ∗ rest) heap) := by
  rw [selection_uses_cursor_cells]
  cmem_start heap held
  unfold selectionOperations CursorCells at *
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  have notEnd : ¬length ≤ index := by
    rw [UInt64.le_iff_toNat_le]
    exact Nat.not_le_of_lt (UInt64.lt_iff_toNat_lt.mp beforeEnd)
  simp only [notEnd, ↓reduceIte]
  cmem_vcgen [ReadExpressions.resolved]
  cmem_exact

theorem exhausted_owned (offset : FrameOffsets) (outcome : OutcomeOffsets) (frame items : Ptr)
    (index length : UInt64) (atEnd : length ≤ index) (rest : Heap L → Prop) :
    CTriple (CursorCells offset outcome frame items index length ∗ rest)
      (selectNext offset outcome frame)
      (fun selected heap => selected = none ∧
        (CursorCells offset outcome frame items index length ∗ rest) heap) := by
  rw [selection_uses_cursor_cells]
  cmem_start heap held
  unfold selectionOperations CursorCells at *
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  simp only [atEnd, ↓reduceIte]
  cmem_exact

theorem selected_counter_does_not_wrap (index length : UInt64) (beforeEnd : index < length) :
    (index + 1).toNat = index.toNat + 1 := by
  rw [UInt64.toNat_add]
  have bound := length.toNat_lt
  have strict := UInt64.lt_iff_toNat_lt.mp beforeEnd
  change (index.toNat + 1) % 18446744073709551616 = index.toNat + 1
  exact Nat.mod_eq_of_lt (by omega)

/-- The selected row is recovered from the paused parent sequencer's advanced
counter. The seed is the RESULT child's copied one-row buffer, not the source
row's address. Materializer and relay outputs remain local helper results. -/
def selectedPreparation? (offset : FrameOffsets) (outcome : OutcomeOffsets)
    (heap : Heap L) (caller : NativeCaller) (materialized variantOnly relay : Ptr) :
    Option PreparedOutcome := do
  let sequencer ← caller.parents.head?
  let some (.u32 kind) ← read ((heap (sequencer + offset.kind).block).2
      (sequencer + offset.kind).offset) | none
  let some (.u32 phase) ← read ((heap (sequencer + offset.phase).block).2
      (sequencer + offset.phase).offset) | none
  let some (.u64 index) ← read ((heap (sequencer + offset.index).block).2
      (sequencer + offset.index).offset) | none
  let some (.u64 length) ← read ((heap ((sequencer + offset.work) + outcome.len).block).2
      ((sequencer + offset.work) + outcome.len).offset) | none
  let items ← pointerCell heap ((caller.frame + offset.work) + outcome.items)
  let seed ← items
  let some (.u64 copiedLength) ← read ((heap ((caller.frame + offset.work) + outcome.len).block).2
      ((caller.frame + offset.work) + outcome.len).offset) | none
  if kind != 7 || phase != 2 || index == 0 || length < index || copiedLength != 1 then none
  else pure ⟨seed, seed + outcome.environment, materialized, variantOnly, relay,
    index.toNat - 1⟩

/-- The native source and copied-buffer identities are owned separately.
`CursorCells` retains the original producer array while the child owns its
single copied row. Payload-copy correctness is a separate component law. -/
def SelectedCells (offset : FrameOffsets) (outcome : OutcomeOffsets)
    (sequencer result sourceItems copiedItems : Ptr) (index length : UInt64) : Heap L → Prop :=
  PointsTo (sequencer + offset.kind) (.u32 7) ∗
  PointsTo (sequencer + offset.phase) (.u32 2) ∗
  CursorCells offset outcome sequencer sourceItems index length ∗
  PointsTo ((result + offset.work) + outcome.items) (.ptr (some copiedItems)) ∗
  PointsTo ((result + offset.work) + outcome.len) (.u64 1)

theorem selected_preparation_of_owned_cursor (offset : FrameOffsets) (outcome : OutcomeOffsets)
    (sequencer result sourceItems copiedItems : Ptr) (older : List Ptr)
    (index length : UInt64) (beforeEnd : index < length)
    (materialized variantOnly relay : Ptr) (rest : Heap L → Prop) (heap : Heap L)
    (owned : (SelectedCells offset outcome sequencer result sourceItems copiedItems
      (index + 1) length ∗ rest) heap) :
    selectedPreparation? offset outcome heap ⟨result, sequencer :: older⟩
      materialized variantOnly relay =
      some ⟨copiedItems, copiedItems + outcome.environment, materialized,
        variantOnly, relay, index.toNat⟩ := by
  unfold SelectedCells CursorCells at owned
  have kindRead : Reads (sequencer + offset.kind) (.u32 7) heap := by cmem_fact
  have phaseRead : Reads (sequencer + offset.phase) (.u32 2) heap := by cmem_fact
  have indexRead : Reads (sequencer + offset.index) (.u64 (index + 1)) heap := by cmem_fact
  have lengthRead : Reads ((sequencer + offset.work) + outcome.len) (.u64 length) heap := by
    cmem_fact
  have itemsRead : Reads ((result + offset.work) + outcome.items) (.ptr (some copiedItems)) heap := by
    cmem_fact
  have copiedRead : Reads ((result + offset.work) + outcome.len) (.u64 1) heap := by cmem_fact
  simp only [Reads] at kindRead phaseRead indexRead lengthRead itemsRead copiedRead
  have noWrap := selected_counter_does_not_wrap index length beforeEnd
  have nonzero : index + 1 ≠ (0 : UInt64) := by
    intro zero
    have equal := congrArg UInt64.toNat zero
    simp only [noWrap] at equal
    change index.toNat + 1 = 0 at equal
    omega
  have within : ¬length < index + 1 := by
    rw [UInt64.lt_iff_toNat_lt, noWrap]
    have earlier := UInt64.lt_iff_toNat_lt.mp beforeEnd
    omega
  simp only [Ptr.add_block, Ptr.add_offset] at kindRead phaseRead indexRead lengthRead itemsRead copiedRead
  simp [selectedPreparation?, pointerCell, kindRead, phaseRead, indexRead, lengthRead,
    itemsRead, copiedRead, nonzero, within, noWrap]

/-- The occurrence is a physical row of one sequencer, independently of equal
payloads. Positive extent makes distinct rows distinct Outcome addresses. -/
theorem selected_addresses_injective (base : Ptr) (extent : Nat) (positive : 0 < extent)
    (left right : Nat) (same : base + left * extent = base + right * extent) : left = right := by
  have offsets := congrArg Ptr.offset same
  simp only [Ptr.add_offset] at offsets
  exact Nat.eq_of_mul_eq_mul_right positive (Nat.add_left_cancel offsets)

/-- The selected embedded environment lies inside the admitted Outcome array.
The cursor law alone does not grant array lifetime or an ABI layout. -/
theorem selected_environment_address_valid (base : Ptr) (extent environmentOffset capacity : Nat)
    (index length : UInt64) (rest : Heap L → Prop) (heap : Heap L)
    (baseStart : base.offset = 0) (environmentInside : environmentOffset < extent)
    (beforeEnd : index < length) (capacityEnough : length.toNat ≤ capacity)
    (arrayLive : (LiveBlock base.block (capacity * extent) ∗ rest) heap) :
    Valid heap ((base + index.toNat * extent) + environmentOffset) := by
  have indexInside := UInt64.lt_iff_toNat_lt.mp beforeEnd
  have capacityStep : (index.toNat + 1) * extent ≤ capacity * extent :=
    Nat.mul_le_mul_right extent (by omega)
  have inside : index.toNat * extent + environmentOffset ≤ capacity * extent := by
    rw [Nat.add_mul, Nat.one_mul] at capacityStep
    omega
  have valid := valid_of_liveBlock arrayLive inside
  cases base with
  | mk block offset =>
      simp only at baseStart
      subst offset
      change Valid heap ⟨block, 0 + index.toNat * extent + environmentOffset⟩
      simpa only [Nat.zero_add] using valid

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open OSLFCore (Atom)

/-- The successful-allocation portion of `he_canonical_push`. The supplied
local preparation is the intervening binding-copy, root-registration and
profile-specific stream-attachment work. It may change its own footprint;
it cannot replace scalar initialization or intrusive linking. -/
def initializePrepareLink (offset : FrameOffsets) (stack child : Ptr)
    (arguments : CallerArguments) (prepare : Ptr → Ptr → CProg CVal Unit) :
    CProg CVal CallerArguments := do
  let _ ← initializeFields offset child arguments.scalar
  prepare child arguments.environment
  let _ ← pushProgram stack child
  pure arguments

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Frame preparation is a local memory obligation; it does not assert source
call adequacy, a whole frame relation, or a successful child evaluation. -/
theorem initialized_prepared_linked (offset : FrameOffsets) (stack child : Ptr)
    (active : List Ptr) (old : PushArguments) (arguments : CallerArguments)
    (prior : Option Ptr) (prepare : Ptr → Ptr → CProg CVal Unit)
    (before after rest : Heap L → Prop)
    (prepared : CTriple before (prepare child arguments.environment) (fun _ => after)) :
    CTriple (FrameCells offset child old ∗ StackCells stack active ∗
      PointsTo child (.ptr prior) ∗ before ∗ rest)
      (initializePrepareLink offset stack child arguments prepare)
      (fun result heap => result = arguments ∧
        (FrameCells offset child arguments.scalar ∗ StackCells stack (child :: active) ∗
          after ∗ rest) heap) := by
  unfold initializePrepareLink
  refine triple_bind _ (initialization_owned offset child old arguments.scalar
    (StackCells stack active ∗ PointsTo child (.ptr prior) ∗ before ∗ rest)) fun _ => ?_
  apply triple_pure
  intro _
  cmem_start heap held
  cmem_norm
  sep_call prepared
  intro result heap held
  cmem_call push_stack_cells stack child active prior
    (FrameCells offset child arguments.scalar ∗ after ∗ rest)
    with result heap ⟨_, held⟩
  cmem_exact

/-- Resume the reached ordinary RESULT tail, then install its actual evaluated
caller operands. The original RESULT frame stays below the child. -/
def enterCaller (calls : ReadExpressions.Calls) (offset : FrameOffsets)
    (environmentOffset : Nat) (stack frame child : Ptr) (arena : Option Ptr)
    (seed : Ptr) (prepare : Ptr → Ptr → CProg CVal Unit) :
    CProg CVal CallerArguments := do
  let _ ← setResultPhase offset frame
  let values ← callerOperands calls offset environmentOffset frame arena seed
  let arguments ← ReadExpressions.resolved (decodeCallerArguments values)
  initializePrepareLink offset stack child arguments prepare

/-- This genuine local path retains the complete parent stack and the reached
seed environment. The loader's successful memory preparation remains a
component obligation; this theorem never supplies child semantics itself. -/
theorem enter_caller_owned (calls : ReadExpressions.Calls) (offset : FrameOffsets)
    (environmentOffset : Nat) (stack frame child seed input relay : Ptr)
    (parents : List Ptr) (parent old : PushArguments) (phase : UInt32) (prior : Option Ptr)
    (prepare : Ptr → Ptr → CProg CVal Unit) (before middle after copied rest : Heap L → Prop)
    (materializer : CTriple before
      (calls "outcome_atom_materialize_variant_only".toList [.ptr parent.arena, .ptr (some seed)])
      (fun value heap => value = .ptr (some input) ∧ middle heap))
    (relaySink : CTriple middle
      (calls "he_relay_sink".toList [.ptr (some frame), .ptr (some (frame + offset.child))])
      (fun value heap => value = .ptr (some relay) ∧ after heap))
    (prepared : CTriple after (prepare child (seed + environmentOffset)) (fun _ => copied)) :
    CTriple (FrameCells offset frame parent ∗ PointsTo (frame + offset.phase) (.u32 phase) ∗
      FrameCells offset child old ∗ StackCells stack (frame :: parents) ∗
      PointsTo child (.ptr prior) ∗ before ∗ rest)
      (enterCaller calls offset environmentOffset stack frame child parent.arena seed prepare)
      (fun result heap => result = callbackArguments parent seed input relay environmentOffset ∧
        (FrameCells offset frame parent ∗ PointsTo (frame + offset.phase) (.u32 1) ∗
          FrameCells offset child result.scalar ∗ StackCells stack (child :: frame :: parents) ∗
          copied ∗ rest) heap) := by
  unfold enterCaller
  apply triple_pre _ (P := PointsTo (frame + offset.phase) (.u32 phase) ∗
    (FrameCells offset frame parent ∗ FrameCells offset child old ∗
      StackCells stack (frame :: parents) ∗ PointsTo child (.ptr prior) ∗ before ∗ rest))
    (fun heap held => by cmem_exact)
  refine triple_bind _ (phase_owned offset frame phase
    (FrameCells offset frame parent ∗ FrameCells offset child old ∗
      StackCells stack (frame :: parents) ∗ PointsTo child (.ptr prior) ∗ before ∗ rest)) fun _ => ?_
  cmem_start heap held
  cmem_norm
  cmem_call caller_operands_owned calls offset environmentOffset frame seed input relay parent
    before middle after materializer relaySink
    with values heap ⟨decoded, held⟩
  simp only [decoded, ReadExpressions.resolved, Prog.pure_eq]
  cmem_norm
  cmem_call initialized_prepared_linked offset stack child (frame :: parents) old
    (callbackArguments parent seed input relay environmentOffset) prior prepare after copied
    (FrameCells offset frame parent ∗ PointsTo (frame + offset.phase) (.u32 1) ∗ rest)
    prepared with result heap ⟨rfl, held⟩
  constructor
  · rfl
  · cmem_exact

/-- Finishing a child uses the actual intrusive pop. The parent frame's scalar
fields and caller continuation remain owned and therefore readable. Release
of the popped frame and delivery/root metadata is a separate component. -/
theorem returned_child_restores_parent (offset : FrameOffsets) (stack frame child : Ptr)
    (parents : List Ptr) (parent childArguments : PushArguments) (rest : Heap L → Prop) :
    CTriple (FrameCells offset frame parent ∗ FrameCells offset child childArguments ∗
      StackCells stack (child :: frame :: parents) ∗ rest)
      (popProgram stack child)
      (fun result heap => result = .finished (.returned (stackEnvironment stack child) (some (.ptr (some child)))) ∧
        (FrameCells offset frame parent ∗ FrameCells offset child childArguments ∗
          PointsTo child (.ptr none) ∗ StackCells stack (frame :: parents) ∗ rest) heap) := by
  apply triple_consequence _ ?_
    (pop_stack_cells stack child (frame :: parents)
      (FrameCells offset frame parent ∗ FrameCells offset child childArguments ∗ rest)) ?_
  · intro heap held
    cmem_exact
  · intro result heap held
    refine ⟨held.1, ?_⟩
    have cells := held.2
    cmem_exact

/-- The second pop removes the RESULT owner, leaving precisely its older
continuation stack. There is no restoration from a reconstructed empty stack. -/
theorem returned_result_restores_older_stack (offset : FrameOffsets) (stack frame : Ptr)
    (parents : List Ptr) (parent : PushArguments) (rest : Heap L → Prop) :
    CTriple (FrameCells offset frame parent ∗ StackCells stack (frame :: parents) ∗ rest)
      (popProgram stack frame)
      (fun result heap => result = .finished (.returned (stackEnvironment stack frame) (some (.ptr (some frame)))) ∧
        (FrameCells offset frame parent ∗ PointsTo frame (.ptr none) ∗
          StackCells stack parents ∗ rest) heap) := by
  apply triple_consequence _ ?_
    (pop_stack_cells stack frame parents (FrameCells offset frame parent ∗ rest)) ?_
  · intro heap held
    cmem_exact
  · intro result heap held
    refine ⟨held.1, ?_⟩
    have cells := held.2
    cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open OSLFCore (Atom)

/-- Parent decoding itself supplies all materialization and request-field
readback equations. No desired callback source relation is an admission field. -/
theorem callback_request_from_native_parent (payloads : PayloadReadback)
    (caller : NativeCaller) (parent : PushArguments) (prepared : PreparedOutcome)
    (invocation : CallReturnControl.Invocation NativeCaller) (environmentOffset : Nat)
    (decoded : invocationOfFields? payloads caller parent prepared = some invocation)
    (environment : prepared.environment = prepared.seed + environmentOffset) :
    requestOfCaller? payloads invocation
      (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay environmentOffset) =
      some ⟨invocation, invocation.variantOnly, invocation.demand,
        invocation.reached, invocation.relayTarget⟩ := by
  unfold invocationOfFields? at decoded
  split at decoded
  · cases decoded
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨spaceAddress, _, space, _, callAddress, _, original, _, demand, demandRead,
      reached, reachedRead, materialized, _, variantOnly, variantRead, target, _, exactInvocation⟩ := decoded
    cases exactInvocation
    apply callback_request_fields
    · exact variantRead
    · exact demandRead
    · simpa only [environment] using reachedRead
    · rfl

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Read both actual frames. The child carries its own copied environment at
an embedded address; the parent carries the saved assembled invocation. -/
def nativeChildRequest? (offset : FrameOffsets) (frameEnvironmentOffset : Nat)
    (payloads : PayloadReadback) (heap : Heap L) (caller : NativeCaller)
    (prepared : PreparedOutcome) (child : Ptr) :
    Option (CallReturnControl.Request NativeCaller) := do
  let invocation ← invocationReadback? offset payloads heap caller prepared
  let scalar ← frameArguments? offset heap child
  if scalar.kind != 3 then none else
    requestOfCaller? payloads invocation ⟨scalar, child + frameEnvironmentOffset⟩

/-- The child request is constructed from scalar ownership and the local
binding-copy readback. It is not supplied as a frame-correspondence premise.
The copy equality is exactly the lower `bindings_copy` representation boundary. -/
theorem native_child_request_of_owned_frames (offset : FrameOffsets)
    (frameEnvironmentOffset outcomeEnvironmentOffset : Nat) (payloads : PayloadReadback)
    (caller : NativeCaller) (prepared : PreparedOutcome) (child : Ptr)
    (parent : PushArguments) (invocation : CallReturnControl.Invocation NativeCaller)
    (rest : Heap L → Prop) (heap : Heap L)
    (owned : (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗ rest) heap)
    (decoded : invocationOfFields? payloads caller parent prepared = some invocation)
    (environment : prepared.environment = prepared.seed + outcomeEnvironmentOffset)
    (copied : payloads.bindings (child + frameEnvironmentOffset) =
      payloads.bindings prepared.environment) :
    nativeChildRequest? offset frameEnvironmentOffset payloads heap caller prepared child =
      some ⟨invocation, invocation.variantOnly, invocation.demand,
        invocation.reached, invocation.relayTarget⟩ := by
  have parentRead := invocation_readback_from_owned_fields offset payloads caller prepared parent
    (FrameCells offset child
      (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
        outcomeEnvironmentOffset).scalar ∗ rest) heap owned
  have childOwned : (FrameCells offset child
      (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
        outcomeEnvironmentOffset).scalar ∗ FrameCells offset caller.frame parent ∗ rest) heap := by
    cmem_exact
  have childRead := owned_fields_readback offset child
    (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
      outcomeEnvironmentOffset).scalar (FrameCells offset caller.frame parent ∗ rest) heap childOwned
  simp only [nativeChildRequest?, parentRead, decoded, childRead]
  have request := callback_request_from_native_parent payloads caller parent prepared invocation
    outcomeEnvironmentOffset decoded environment
  simpa [requestOfCaller?, callbackArguments, copied, environment] using request

/-- The caller readback retains the actual older frames. This theorem derives
both field and link representations from the physically owned state. -/
theorem owned_request_has_actual_stack (offset : FrameOffsets) (stack child : Ptr)
    (caller : NativeCaller) (prepared : PreparedOutcome) (parent : PushArguments)
    (childArguments : CallerArguments) (payloads : PayloadReadback) (rest : Heap L → Prop)
    (heap : Heap L)
    (owned : (FrameCells offset caller.frame parent ∗ FrameCells offset child childArguments.scalar ∗
      StackCells stack (child :: caller.frame :: caller.parents) ∗ rest) heap)
    (distinct : (child :: caller.frame :: caller.parents).Nodup) :
    invocationReadback? offset payloads heap caller prepared =
        invocationOfFields? payloads caller parent prepared ∧
      ∃ top, pointerCell heap stack = some top ∧
        (nativeLinks heap top).Represents (child :: caller.frame :: caller.parents) := by
  constructor
  · exact invocation_readback_from_owned_fields offset payloads caller prepared parent
      (FrameCells offset child childArguments.scalar ∗
        StackCells stack (child :: caller.frame :: caller.parents) ∗ rest) heap owned
  · have stackOwned : (StackCells stack (child :: caller.frame :: caller.parents) ∗
      FrameCells offset caller.frame parent ∗ FrameCells offset child childArguments.scalar ∗ rest) heap := by
      cmem_exact
    exact ⟨_, stack_readback stack (child :: caller.frame :: caller.parents) heap
      (FrameCells offset caller.frame parent ∗ FrameCells offset child childArguments.scalar ∗ rest)
      stackOwned distinct⟩

/-- The retained child is the represented native stack address, its actual
current frame, and the complete finite storage snapshot. This is a readback
carrier, not a new transition machine or a typed-child adequacy assertion. -/
abbrev NativeResidual := Ptr × Ptr × ExecutableStorage.Storage CVal

def retainedFrameReadback? {World Failure : Type} (offset : FrameOffsets)
    (frameEnvironmentOffset : Nat) (payloads : PayloadReadback)
    (storage : ExecutableStorage.Storage CVal) (stack child : Ptr)
    (caller : NativeCaller) (prepared : PreparedOutcome) :
    Option (Mettapedia.GSLT.Distinction.ProductiveBlocks.HandledState
      (CallReturnControl.Parent NativeCaller World Failure) NativeResidual
      (CallReturnControl.Request NativeCaller)) := do
  let top ← pointerCell (ExecutableStorage.heap storage) stack
  if top != some child then none else do
    let request ← nativeChildRequest? offset frameEnvironmentOffset payloads
      (ExecutableStorage.heap storage) caller prepared child
    pure (CallReturnControl.active request (stack, child, storage))

/-- The existing handler configuration is obtained by reading the actual
stack and both owned frames. The child storage is retained in its entirety;
no original expression is reloaded or manufactured as the child state. -/
theorem retained_readback_of_owned_native_entry {World Failure : Type}
    (offset : FrameOffsets) (frameEnvironmentOffset outcomeEnvironmentOffset : Nat)
    (payloads : PayloadReadback) (storage : ExecutableStorage.Storage CVal)
    (stack child : Ptr) (caller : NativeCaller) (prepared : PreparedOutcome)
    (parent : PushArguments) (invocation : CallReturnControl.Invocation NativeCaller)
    (rest : Heap (Excl (Option CVal)) → Prop)
    (owned : (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      StackCells stack (child :: caller.frame :: caller.parents) ∗ rest)
      (ExecutableStorage.heap storage))
    (decoded : invocationOfFields? payloads caller parent prepared = some invocation)
    (environment : prepared.environment = prepared.seed + outcomeEnvironmentOffset)
    (copied : payloads.bindings (child + frameEnvironmentOffset) =
      payloads.bindings prepared.environment)
    (distinct : (child :: caller.frame :: caller.parents).Nodup) :
    retainedFrameReadback? (World := World) (Failure := Failure) offset frameEnvironmentOffset
      payloads storage stack child caller prepared =
      some (CallReturnControl.active
        ⟨invocation, invocation.variantOnly, invocation.demand,
          invocation.reached, invocation.relayTarget⟩ (stack, child, storage)) := by
  have request := native_child_request_of_owned_frames offset frameEnvironmentOffset
    outcomeEnvironmentOffset payloads caller prepared child parent invocation
    (StackCells stack (child :: caller.frame :: caller.parents) ∗ rest)
    (ExecutableStorage.heap storage) owned decoded environment copied
  have stackOwned : (StackCells stack (child :: caller.frame :: caller.parents) ∗
      FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗ rest) (ExecutableStorage.heap storage) := by
    cmem_exact
  have top := (stack_readback stack (child :: caller.frame :: caller.parents)
    (ExecutableStorage.heap storage) _ stackOwned distinct).1
  simp [retainedFrameReadback?, top, request]

/-- The sequenced entry derives the selected physical occurrence and the copied
seed address from storage before reading the request. Only the materializer
and relay pointer results remain inputs from their component implementations. -/
def retainedSequencedReadback? {World Failure : Type} (offset : FrameOffsets)
    (outcome : OutcomeOffsets) (frameEnvironmentOffset : Nat) (payloads : PayloadReadback)
    (storage : ExecutableStorage.Storage CVal) (stack child : Ptr)
    (caller : NativeCaller) (materialized variantOnly relay : Ptr) :
    Option (Mettapedia.GSLT.Distinction.ProductiveBlocks.HandledState
      (CallReturnControl.Parent NativeCaller World Failure) NativeResidual
      (CallReturnControl.Request NativeCaller)) := do
  let prepared ← selectedPreparation? offset outcome (ExecutableStorage.heap storage)
    caller materialized variantOnly relay
  retainedFrameReadback? offset frameEnvironmentOffset payloads storage stack child caller prepared

/-- Physical cursor selection, the actual linked frames and their copied
binding environment determine the retained invocation. Neither a row number
nor the original producer's Outcome pointer is supplied to the readback. -/
theorem retained_sequenced_readback_of_owned_entry {World Failure : Type}
    (offset : FrameOffsets) (outcome : OutcomeOffsets) (frameEnvironmentOffset : Nat)
    (payloads : PayloadReadback) (storage : ExecutableStorage.Storage CVal)
    (stack child result sequencer sourceItems copiedItems : Ptr) (older : List Ptr)
    (index length : UInt64) (beforeEnd : index < length)
    (materialized variantOnly relay : Ptr) (parent : PushArguments)
    (invocation : CallReturnControl.Invocation NativeCaller)
    (rest : Heap (Excl (Option CVal)) → Prop)
    (owned : (FrameCells offset result parent ∗
      FrameCells offset child
        (callbackArguments parent copiedItems variantOnly relay outcome.environment).scalar ∗
      StackCells stack (child :: result :: sequencer :: older) ∗
      SelectedCells offset outcome sequencer result sourceItems copiedItems
        (index + 1) length ∗ rest) (ExecutableStorage.heap storage))
    (decoded : invocationOfFields? payloads ⟨result, sequencer :: older⟩ parent
      ⟨copiedItems, copiedItems + outcome.environment, materialized, variantOnly,
        relay, index.toNat⟩ = some invocation)
    (copied : payloads.bindings (child + frameEnvironmentOffset) =
      payloads.bindings (copiedItems + outcome.environment))
    (distinct : (child :: result :: sequencer :: older).Nodup) :
    retainedSequencedReadback? (World := World) (Failure := Failure) offset outcome
      frameEnvironmentOffset payloads storage stack child ⟨result, sequencer :: older⟩
      materialized variantOnly relay =
      some (CallReturnControl.active
        ⟨invocation, invocation.variantOnly, invocation.demand,
          invocation.reached, invocation.relayTarget⟩ (stack, child, storage)) ∧
      invocation.row = index.toNat ∧ invocation.caller.parents = sequencer :: older := by
  have selectedOwned : (SelectedCells offset outcome sequencer result sourceItems copiedItems
      (index + 1) length ∗ FrameCells offset result parent ∗
      FrameCells offset child
        (callbackArguments parent copiedItems variantOnly relay outcome.environment).scalar ∗
      StackCells stack (child :: result :: sequencer :: older) ∗ rest)
      (ExecutableStorage.heap storage) := by cmem_exact
  have preparation := selected_preparation_of_owned_cursor offset outcome sequencer result
    sourceItems copiedItems older index length beforeEnd materialized variantOnly relay
    _ _ selectedOwned
  have retained := retained_readback_of_owned_native_entry (World := World) (Failure := Failure)
    offset frameEnvironmentOffset outcome.environment payloads storage stack child
    ⟨result, sequencer :: older⟩
    ⟨copiedItems, copiedItems + outcome.environment, materialized, variantOnly, relay, index.toNat⟩
    parent invocation (SelectedCells offset outcome sequencer result sourceItems copiedItems
      (index + 1) length ∗ rest) owned decoded rfl copied distinct
  have fields := invocation_environment_is_selected payloads
    ⟨result, sequencer :: older⟩ parent
    ⟨copiedItems, copiedItems + outcome.environment, materialized, variantOnly, relay, index.toNat⟩
    invocation decoded
  refine ⟨?_, fields.2.1, ?_⟩
  · unfold retainedSequencedReadback?
    rw [preparation]
    exact retained
  · exact congrArg NativeCaller.parents fields.2.2.1

/-- Composing the actual ordinary-tail stores, helper calls and intrusive
push constructs the retained readback at every represented final snapshot.
The snapshot is the reached memory, not a reload of the argument computation.
Helper execution and binding-copy payload correctness remain local contracts. -/
theorem enter_caller_retained_square {World Failure : Type}
    (calls : ReadExpressions.Calls) (offset : FrameOffsets) (outcome : OutcomeOffsets)
    (frameEnvironmentOffset : Nat) (payloads : PayloadReadback)
    (stack result child sequencer sourceItems copiedItems materialized variantOnly relay : Ptr)
    (older : List Ptr) (index length : UInt64) (beforeEnd : index < length)
    (parent old : PushArguments) (prior : Option Ptr)
    (prepare : Ptr → Ptr → CProg CVal Unit)
    (before middle after copied rest : Heap (Excl (Option CVal)) → Prop)
    (materializer : CTriple before
      (calls "outcome_atom_materialize_variant_only".toList
        [.ptr parent.arena, .ptr (some copiedItems)])
      (fun value heap => value = .ptr (some variantOnly) ∧ middle heap))
    (relaySink : CTriple middle
      (calls "he_relay_sink".toList [.ptr (some result), .ptr (some (result + offset.child))])
      (fun value heap => value = .ptr (some relay) ∧ after heap))
    (prepared : CTriple after (prepare child (copiedItems + outcome.environment)) (fun _ => copied))
    (invocation : CallReturnControl.Invocation NativeCaller)
    (decoded : invocationOfFields? payloads ⟨result, sequencer :: older⟩ parent
      ⟨copiedItems, copiedItems + outcome.environment, materialized, variantOnly,
        relay, index.toNat⟩ = some invocation)
    (bindingsCopy : payloads.bindings (child + frameEnvironmentOffset) =
      payloads.bindings (copiedItems + outcome.environment))
    (distinct : (child :: result :: sequencer :: older).Nodup) :
    CTriple (FrameCells offset result parent ∗ PointsTo (result + offset.phase) (.u32 0) ∗
      FrameCells offset child old ∗ StackCells stack (result :: sequencer :: older) ∗
      PointsTo child (.ptr prior) ∗ before ∗
      SelectedCells offset outcome sequencer result sourceItems copiedItems (index + 1) length ∗ rest)
      (enterCaller calls offset outcome.environment stack result child parent.arena copiedItems prepare)
      (fun answer heap =>
        answer = callbackArguments parent copiedItems variantOnly relay outcome.environment ∧
        (FrameCells offset result parent ∗ PointsTo (result + offset.phase) (.u32 1) ∗
          FrameCells offset child answer.scalar ∗
          StackCells stack (child :: result :: sequencer :: older) ∗ copied ∗
          SelectedCells offset outcome sequencer result sourceItems copiedItems
            (index + 1) length ∗ rest) heap ∧
        ∀ storage : ExecutableStorage.Storage CVal, heap = ExecutableStorage.heap storage →
          retainedSequencedReadback? (World := World) (Failure := Failure) offset outcome
            frameEnvironmentOffset payloads storage stack child ⟨result, sequencer :: older⟩
            materialized variantOnly relay =
            some (CallReturnControl.active
              ⟨invocation, invocation.variantOnly, invocation.demand,
                invocation.reached, invocation.relayTarget⟩ (stack, child, storage))) := by
  apply triple_post _ (enter_caller_owned calls offset outcome.environment stack result child
    copiedItems variantOnly relay (sequencer :: older) parent old 0 prior prepare
    before middle after copied
    (SelectedCells offset outcome sequencer result sourceItems copiedItems (index + 1) length ∗ rest)
    materializer relaySink prepared)
  intro answer heap reached
  refine ⟨reached.1, reached.2, ?_⟩
  intro storage represented
  subst heap
  have owned : (FrameCells offset result parent ∗
      FrameCells offset child
        (callbackArguments parent copiedItems variantOnly relay outcome.environment).scalar ∗
      StackCells stack (child :: result :: sequencer :: older) ∗
      SelectedCells offset outcome sequencer result sourceItems copiedItems (index + 1) length ∗
      PointsTo (result + offset.phase) (.u32 1) ∗ copied ∗ rest)
      (ExecutableStorage.heap storage) := by
    have held := reached.2
    rw [reached.1] at held
    cmem_exact
  exact (retained_sequenced_readback_of_owned_entry offset outcome frameEnvironmentOffset
    payloads storage stack child result sequencer sourceItems copiedItems older index length
    beforeEnd materialized variantOnly relay parent invocation
    (PointsTo (result + offset.phase) (.u32 1) ∗ copied ∗ rest)
    owned decoded bindingsCopy distinct).1

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- The actual ordinary-result relay call has two false flags. Raw function
return completion uses a different branch and is not folded into this call. -/
def relayFinishCall : CExpr := .call "he_relay_finish".toList
  [.identifier "frame".toList,
   .unary .address (.field (.identifier "frame".toList) "child".toList true),
   .bool false, .bool false]

def finishRelay (effects : ReadExpressions.CallService Unit) (offset : FrameOffsets)
    (frame : Ptr) : CProg CVal Unit :=
  EffectStatements.invoke ReadExpressions.noCalls effects (frameLayout offset)
    (fun name => if name = "frame".toList then some (.ptr (some frame)) else none) relayFinishCall

theorem relay_finish_actual_arguments (effects : ReadExpressions.CallService Unit)
    (offset : FrameOffsets) (frame : Ptr) :
    finishRelay effects offset frame = effects "he_relay_finish".toList
      [.ptr (some frame), .ptr (some (frame + offset.child)), .bool false, .bool false] := by
  simp [finishRelay, relayFinishCall, EffectStatements.invoke,
    EffectStatements.invokeWithNames, ReadExpressions.argumentsWithNames,
    ReadExpressions.expressionWithNames, ReadExpressions.fieldAddress,
    ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.resolved,
    ReadExpressions.pointer, frameLayout,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- A bounded partial projection of the ordinary RESULT control region.
The phase-zero branch has already passed the actual refusal, stop, function
and inert-result gates. The phase-one branch is admitted only with selected
false. Function delimiters and phase-two sequencers keep their own owners. -/
def ordinaryRegion (calls : ReadExpressions.Calls)
    (effects : ReadExpressions.CallService Unit) (offset : FrameOffsets)
    (environmentOffset : Nat) (stack frame child : Ptr) (arena : Option Ptr)
    (seed : Ptr) (prepare : Ptr → Ptr → CProg CVal Unit) :
    CProg CVal (Option CallerArguments) := do
  let phase ← CProg.loadU32 (frame + offset.phase)
  if phase = 0 then
    let arguments ← enterCaller calls offset environmentOffset stack frame child arena seed prepare
    pure (some arguments)
  else if phase = 1 then
    let selected ← CProg.loadBool (frame + offset.selected)
    if selected then CProg.undefined else do
      finishRelay effects offset frame
      let _ ← popProgram stack frame
      pure none
  else CProg.undefined

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Once the actual child has returned, resumption executes the relay and
physical parent pop; it cannot take the callback-entry arm again. The helper
contract retains the complete delivered payload in `after`, not just values. -/
theorem completed_ordinary_phase_pops (calls : ReadExpressions.Calls)
    (effects : ReadExpressions.CallService Unit) (offset : FrameOffsets)
    (environmentOffset : Nat) (stack frame child seed : Ptr) (arena : Option Ptr)
    (parents : List Ptr) (parent : PushArguments)
    (prepare : Ptr → Ptr → CProg CVal Unit) (before after rest : Heap L → Prop)
    (relay : CTriple before
      (effects "he_relay_finish".toList
        [.ptr (some frame), .ptr (some (frame + offset.child)), .bool false, .bool false])
      (fun _ => after)) :
    CTriple (PointsTo (frame + offset.phase) (.u32 1) ∗
      PointsTo (frame + offset.selected) (.bool false) ∗
      FrameCells offset frame parent ∗ StackCells stack (frame :: parents) ∗ before ∗ rest)
      (ordinaryRegion calls effects offset environmentOffset stack frame child arena seed prepare)
      (fun result heap => result = none ∧
        (PointsTo (frame + offset.phase) (.u32 1) ∗
          PointsTo (frame + offset.selected) (.bool false) ∗
          FrameCells offset frame parent ∗ PointsTo frame (.ptr none) ∗
          StackCells stack parents ∗ after ∗ rest) heap) := by
  cmem_start heap held
  unfold ordinaryRegion
  cmem_vcgen [show (1 : UInt32) ≠ 0 from by decide]
  rw [relay_finish_actual_arguments]
  sep_call relay
  intro result heap held
  cmem_call pop_stack_cells stack frame parents
    (PointsTo (frame + offset.phase) (.u32 1) ∗
      PointsTo (frame + offset.selected) (.bool false) ∗
      FrameCells offset frame parent ∗ after ∗ rest)
    with result heap ⟨_, held⟩
  cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- The source helper forwards parent->atom, not the seed's atom, into the
RESULT frame. Its initially empty frame environment is separate from seed.env. -/
def resultPushCall : CExpr := .call "he_canonical_push".toList
  [.identifier "HE_CANONICAL_RESULT".toList,
   .field (.identifier "parent".toList) "space".toList true,
   .field (.identifier "parent".toList) "arena".toList true,
   .field (.identifier "parent".toList) "atom".toList true,
   .identifier "type".toList,
   .field (.identifier "parent".toList) "fuel".toList true,
   .null,
   .field (.identifier "parent".toList) "preserve_bindings".toList true,
   .identifier "target".toList]

def resultPushDeclaration : CStatement :=
  .declare ⟨"HeCanonicalFrame".toList, 1⟩ "frame".toList resultPushCall

def resultNames (parent : Ptr) (demand target : Option Ptr) : ReadExpressions.NameReads :=
  fun name => ReadExpressions.resolved
    (if name = "HE_CANONICAL_RESULT".toList then some (.u32 7)
    else if name = "parent".toList then some (.ptr (some parent))
    else if name = "type".toList then some (.ptr demand)
    else if name = "target".toList then some (.ptr target) else none)

def resultOperands (offset : FrameOffsets) (parent : Ptr) (demand target : Option Ptr) :
    CProg CVal (List CVal) :=
  match resultPushDeclaration with
  | .declare _ _ (.call name arguments) =>
      if name = "he_canonical_push".toList then
        ReadExpressions.argumentsWithNames (resultNames parent demand target)
          ReadExpressions.noCalls (frameLayout offset) arguments
      else CProg.undefined
  | _ => CProg.undefined

def resultOperandOperations (offset : FrameOffsets) (parent : Ptr) (demand target : Option Ptr) :
    CProg CVal (List CVal) := do
  let space ← CProg.loadPtr (parent + offset.space)
  let arena ← CProg.loadPtr (parent + offset.arena)
  let original ← CProg.loadPtr (parent + offset.atom)
  let fuel ← CProg.loadI32 (parent + offset.fuel)
  let preserve ← CProg.loadBool (parent + offset.preserve)
  pure [.u32 7, .ptr space, .ptr arena, .ptr original, .ptr demand, .i32 fuel,
    .ptr none, .bool preserve, .ptr target]

theorem result_operands_use_saved_call (offset : FrameOffsets) (parent : Ptr)
    (demand target : Option Ptr) :
    resultOperands offset parent demand target =
      resultOperandOperations offset parent demand target := by
  simp [resultOperands, resultPushDeclaration, resultPushCall, resultNames, frameLayout,
    ReadExpressions.argumentsWithNames, ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.resolved, ReadExpressions.pointer,
    resultOperandOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem result_creation_preserves_parent_invocation (offset : FrameOffsets) (parent : Ptr)
    (arguments : PushArguments) (demand target : Option Ptr) (rest : Heap L → Prop) :
    CTriple (FrameCells offset parent arguments ∗ rest)
      (resultOperands offset parent demand target)
      (fun values heap => values =
        [.u32 7, .ptr arguments.space, .ptr arguments.arena, .ptr arguments.atom,
          .ptr demand, .i32 arguments.fuel, .ptr none, .bool arguments.preserve, .ptr target] ∧
        (FrameCells offset parent arguments ∗ rest) heap) := by
  rw [result_operands_use_saved_call]
  cmem_start heap held
  unfold resultOperandOperations FrameCells at *
  simp only [CProg.loadI32, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def init_kindSource : String := "frame->kind = kind;"
def init_kindTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['k', 'i', 'n', 'd'], .punctuation ['='], .identifier ['k', 'i', 'n', 'd'], .punctuation [';']]
theorem init_kind_lex : lex init_kindSource.toList = .ok init_kindTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_kind_parsed :
    ((lex init_kindSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "kind" "kind", []) := by
  rw [init_kind_lex]
  rfl

def init_spaceSource : String := "frame->space = s;"
def init_spaceTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['s', 'p', 'a', 'c', 'e'], .punctuation ['='], .identifier ['s'], .punctuation [';']]
theorem init_space_lex : lex init_spaceSource.toList = .ok init_spaceTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_space_parsed :
    ((lex init_spaceSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "space" "s", []) := by
  rw [init_space_lex]
  rfl

def init_arenaSource : String := "frame->arena = a;"
def init_arenaTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 'r', 'e', 'n', 'a'], .punctuation ['='], .identifier ['a'], .punctuation [';']]
theorem init_arena_lex : lex init_arenaSource.toList = .ok init_arenaTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_arena_parsed :
    ((lex init_arenaSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "arena" "a", []) := by
  rw [init_arena_lex]
  rfl

def init_atomSource : String := "frame->atom = atom;"
def init_atomTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation ['='], .identifier ['a', 't', 'o', 'm'], .punctuation [';']]
theorem init_atom_lex : lex init_atomSource.toList = .ok init_atomTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_atom_parsed :
    ((lex init_atomSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "atom" "atom", []) := by
  rw [init_atom_lex]
  rfl

def init_typeSource : String := "frame->type = type;"
def init_typeTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['t', 'y', 'p', 'e'], .punctuation ['='], .identifier ['t', 'y', 'p', 'e'], .punctuation [';']]
theorem init_type_lex : lex init_typeSource.toList = .ok init_typeTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_type_parsed :
    ((lex init_typeSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "type" "type", []) := by
  rw [init_type_lex]
  rfl

def init_fuelSource : String := "frame->fuel = fuel;"
def init_fuelTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['f', 'u', 'e', 'l'], .punctuation ['='], .identifier ['f', 'u', 'e', 'l'], .punctuation [';']]
theorem init_fuel_lex : lex init_fuelSource.toList = .ok init_fuelTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_fuel_parsed :
    ((lex init_fuelSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "fuel" "fuel", []) := by
  rw [init_fuel_lex]
  rfl

def init_targetSource : String := "frame->target = target;"
def init_targetTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['t', 'a', 'r', 'g', 'e', 't'], .punctuation ['='], .identifier ['t', 'a', 'r', 'g', 'e', 't'], .punctuation [';']]
theorem init_target_lex : lex init_targetSource.toList = .ok init_targetTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_target_parsed :
    ((lex init_targetSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "target" "target", []) := by
  rw [init_target_lex]
  rfl

def init_preserve_bindingsSource : String := "frame->preserve_bindings = preserve;"
def init_preserve_bindingsTokens : List Token := [.identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', '_', 'b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation ['='], .identifier ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e'], .punctuation [';']]
theorem init_preserve_bindings_lex : lex init_preserve_bindingsSource.toList = .ok init_preserve_bindingsTokens := by
  apply lex_of_completed
  decide +kernel
theorem init_preserve_bindings_parsed :
    ((lex init_preserve_bindingsSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (frameAssignment "preserve_bindings" "preserve", []) := by
  rw [init_preserve_bindings_lex]
  rfl

def result_creationSource : String := "HeCanonicalFrame *frame = he_canonical_push(HE_CANONICAL_RESULT,\n        parent->space, parent->arena, parent->atom, type, parent->fuel,\n        NULL, parent->preserve_bindings, target);"
def result_creationTokens : List Token := [.identifier ['H', 'e', 'C', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', 'F', 'r', 'a', 'm', 'e'], .punctuation ['*'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['='], .identifier ['h', 'e', '_', 'c', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', '_', 'p', 'u', 's', 'h'], .punctuation ['('], .identifier ['H', 'E', '_', 'C', 'A', 'N', 'O', 'N', 'I', 'C', 'A', 'L', '_', 'R', 'E', 'S', 'U', 'L', 'T'], .punctuation [','], .identifier ['p', 'a', 'r', 'e', 'n', 't'], .punctuation ['-', '>'], .identifier ['s', 'p', 'a', 'c', 'e'], .punctuation [','], .identifier ['p', 'a', 'r', 'e', 'n', 't'], .punctuation ['-', '>'], .identifier ['a', 'r', 'e', 'n', 'a'], .punctuation [','], .identifier ['p', 'a', 'r', 'e', 'n', 't'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [','], .identifier ['t', 'y', 'p', 'e'], .punctuation [','], .identifier ['p', 'a', 'r', 'e', 'n', 't'], .punctuation ['-', '>'], .identifier ['f', 'u', 'e', 'l'], .punctuation [','], .identifier ['N', 'U', 'L', 'L'], .punctuation [','], .identifier ['p', 'a', 'r', 'e', 'n', 't'], .punctuation ['-', '>'], .identifier ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', '_', 'b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation [','], .identifier ['t', 'a', 'r', 'g', 'e', 't'], .punctuation [')'], .punctuation [';']]
theorem result_creation_lex : lex result_creationSource.toList = .ok result_creationTokens := by
  apply lex_of_completed
  decide +kernel
theorem result_creation_parsed :
    ((lex result_creationSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (resultPushDeclaration, []) := by
  rw [result_creation_lex]
  rfl

def relay_finishSource : String := "he_relay_finish(frame, &frame->child, false, false);"
def relay_finishTokens : List Token := [.identifier ['h', 'e', '_', 'r', 'e', 'l', 'a', 'y', '_', 'f', 'i', 'n', 'i', 's', 'h'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation [','], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['c', 'h', 'i', 'l', 'd'], .punctuation [','], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [','], .identifier ['f', 'a', 'l', 's', 'e'], .punctuation [')'], .punctuation [';']]
theorem relay_finish_lex : lex relay_finishSource.toList = .ok relay_finishTokens := by
  apply lex_of_completed
  decide +kernel
theorem relay_finish_parsed :
    ((lex relay_finishSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some ((.effect relayFinishCall), []) := by
  rw [relay_finish_lex]
  rfl

def cursor_seedSource : String := "Outcome *seed = &frame->work.items[frame->index++];"
def cursor_seedTokens : List Token := [.identifier ['O', 'u', 't', 'c', 'o', 'm', 'e'], .punctuation ['*'], .identifier ['s', 'e', 'e', 'd'], .punctuation ['='], .punctuation ['&'], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['w', 'o', 'r', 'k'], .punctuation ['.'], .identifier ['i', 't', 'e', 'm', 's'], .punctuation ['['], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['+', '+'], .punctuation [']'], .punctuation [';']]
theorem cursor_seed_lex : lex cursor_seedSource.toList = .ok cursor_seedTokens := by
  apply lex_of_completed
  decide +kernel
theorem cursor_seed_parsed :
    ((lex cursor_seedSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some (cursorDeclaration, []) := by
  rw [cursor_seed_lex]
  rfl

def cursor_guardSource : String := "if (frame->index >= frame->work.len)\n                he_canonical_pop();"
def cursor_guardTokens : List Token := [.identifier ['i', 'f'], .punctuation ['('], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['>', '='], .identifier ['f', 'r', 'a', 'm', 'e'], .punctuation ['-', '>'], .identifier ['w', 'o', 'r', 'k'], .punctuation ['.'], .identifier ['l', 'e', 'n'], .punctuation [')'], .identifier ['h', 'e', '_', 'c', 'a', 'n', 'o', 'n', 'i', 'c', 'a', 'l', '_', 'p', 'o', 'p'], .punctuation ['('], .punctuation [')'], .punctuation [';']]
theorem cursor_guard_lex : lex cursor_guardSource.toList = .ok cursor_guardTokens := by
  apply lex_of_completed
  decide +kernel
theorem cursor_guard_parsed :
    ((lex cursor_guardSource.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Outcome".toList, "HeCanonicalFrame".toList] tokens) =
      some ((.branch cursorGuard [.effect (.call "he_canonical_pop".toList [])] []), []) := by
  rw [cursor_guard_lex]
  rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Controls
open Mettapedia.Machines.CMemory
open ExecutableStorage

open Mettapedia.Machines.CMemory.ProductiveBlocks

def offsets : FrameOffsets := ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15⟩
def outcomes : OutcomeOffsets := ⟨0, 1, 2, 4⟩
def stack : Ptr := ⟨1, 0⟩
def frame : Ptr := ⟨2, 0⟩
def child : Ptr := ⟨3, 0⟩
def items : Ptr := ⟨4, 0⟩
def older : Ptr := ⟨5, 0⟩

def arguments : PushArguments :=
  ⟨3, some ⟨10, 0⟩, some ⟨11, 0⟩, some ⟨12, 0⟩, some ⟨13, 0⟩,
    17, some ⟨14, 0⟩, true⟩

def frameBlock (next : Option Ptr) (kind phase : UInt32) (index length : UInt64)
    (buffer : Ptr := items) :
    Block CVal := ⟨true,
  [some (.ptr next), some (.u32 kind), some (.u32 phase),
   some (.ptr (some ⟨10, 0⟩)), some (.ptr (some ⟨11, 0⟩)),
   some (.ptr (some ⟨12, 0⟩)), some (.ptr (some ⟨13, 0⟩)),
   some (.i32 17), some (.ptr (some ⟨14, 0⟩)), some (.bool true),
   some (.bool false), some (.u64 index), some (.ptr (some buffer)), some (.u64 length),
   some (.u64 2), some (.ptr none), some (.u64 0)]⟩

def initial : Storage CVal :=
  [(stack.block, ⟨true, [some (.ptr (some frame)), some (.u64 2)]⟩),
   (frame.block, frameBlock (some older) 7 2 0 2),
   (child.block, frameBlock none 0 0 0 0),
   (older.block, ⟨true, [some (.ptr none)]⟩)]

def result? {Answer : Type} (fuel : Nat) (program : CProg CVal Answer)
    (storage : Storage CVal) : Option (Answer × Storage CVal) :=
  match (machine.run fuel (State.mk program storage [])).2 with
  | .finished (.returned final) => some (final.answer, final.storage)
  | _ => none

def cursorSnapshot (storage : Storage CVal) : Option (Option (Ptr × Nat) × Option CVal) := do
  let (selected, after) ← result? 20 (selectNext offsets outcomes frame) storage
  pure (selected, (after.lookup frame.block).bind (fun block => block.cells[11]?.join))

theorem first_occurrence_advances_once :
    cursorSnapshot initial = some (some (items, 0), some (.u64 1)) := by decide +kernel

theorem equal_payloads_keep_distinct_second_row :
    let second := (frame.block, frameBlock (some older) 7 2 1 2) :: initial
    cursorSnapshot second = some (some (items + 4, 1), some (.u64 2)) := by decide +kernel

theorem exhausted_frontier_preserves_cursor :
    let exhausted := (frame.block, frameBlock (some older) 7 2 2 2) :: initial
    cursorSnapshot exhausted = some (none, some (.u64 2)) := by decide +kernel

def pushAndPop : CProg CVal Unit := do
  let _ ← initializeAndLink offsets stack child arguments
  let _ ← popProgram stack child
  let _ ← popProgram stack frame
  pure ()

def restoredSnapshot : Option (Option Ptr × Option CVal × Option Ptr × Option PushArguments) := do
  let (_, after) ← result? 60 pushAndPop initial
  let top ← pointerCell (heap after) stack
  let depth := (after.lookup stack.block).bind (fun block => block.cells[1]?.join)
  let childLink ← pointerCell (heap after) child
  pure (top, depth, childLink, frameArguments? offsets (heap after) child)

theorem push_then_two_pops_keeps_older_caller :
    restoredSnapshot = some (some older, some (.u64 1), none, some arguments) := by decide +kernel

theorem missing_frame_is_not_an_empty_success :
    result? 60 pushAndPop [(stack.block, ⟨true, [some (.ptr none), some (.u64 0)]⟩)] = none := by
  decide +kernel

theorem wrong_scalar_tag_refuses_readback :
    frameArguments? offsets
      (heap [(child.block, ⟨true, [some (.ptr none), some (.bool true)]⟩)]) child = none := by
  decide +kernel

theorem zero_budget_retains_actual_memory :
    (machine.run 0 (State.mk pushAndPop initial [])).2 =
      .exhausted (State.mk pushAndPop initial []) := rfl

def copiedItems : Ptr := ⟨6, 0⟩

def sequenced (phase : UInt32) (nextIndex copiedLength : UInt64) : Storage CVal :=
  [(frame.block, frameBlock (some older) 7 phase nextIndex 2),
   (child.block, frameBlock (some frame) 7 1 0 copiedLength copiedItems)]

def selectedReadback (phase : UInt32) (nextIndex copiedLength : UInt64) :
    Option PreparedOutcome :=
  selectedPreparation? offsets outcomes (heap (sequenced phase nextIndex copiedLength))
    ⟨child, [frame, older]⟩ ⟨10, 0⟩ ⟨11, 0⟩ ⟨12, 0⟩

theorem selected_row_and_copied_environment_are_read_from_storage :
    selectedReadback 2 1 1 =
      some ⟨copiedItems, copiedItems + 2, ⟨10, 0⟩, ⟨11, 0⟩, ⟨12, 0⟩, 0⟩ := by
  decide +kernel

theorem second_selected_row_has_distinct_origin_after_copy :
    selectedReadback 2 2 1 =
      some ⟨copiedItems, copiedItems + 2, ⟨10, 0⟩, ⟨11, 0⟩, ⟨12, 0⟩, 1⟩ := by
  decide +kernel

theorem unadvanced_cursor_does_not_fabricate_a_row : selectedReadback 2 0 1 = none := by
  decide +kernel

theorem wrong_parent_phase_does_not_supply_occurrence : selectedReadback 1 1 1 = none := by
  decide +kernel

theorem uncopied_result_cannot_be_read_as_an_invocation : selectedReadback 2 1 0 = none := by
  decide +kernel

theorem past_end_cursor_does_not_supply_occurrence : selectedReadback 2 3 1 = none := by
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Controls

/-! ## Native outcome and environment copy readback

These laws follow the selected stored-data operations through the existing
CMemory semantics. Prepared allocations are owned inputs, not assumptions
that their contents already match. Helper control/lifetime and ABI obligations
remain explicit at this projection boundary.
-/

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 7000000
set_option synthInstance.maxSize 256

/-! ### Owned cell readback -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Read every initialized typed cell. This preserves pointer values and all
record coordinates; it neither evaluates atoms nor follows a pointer. -/
def cellsReadback? (heap : Heap L) (base : Ptr) : Nat → Option (List CVal)
  | 0 => some []
  | count + 1 => do
      let value ← (read ((heap base.block).2 base.offset)).join
      let values ← cellsReadback? heap (base + 1) count
      pure (value :: values)

theorem owned_cells_readback (base : Ptr) (values : List CVal) (rest : Heap L → Prop)
    (heap : Heap L) (held : (Cells base (values.map some) ∗ rest) heap) :
    cellsReadback? heap base values.length = some values := by
  induction values generalizing base rest with
  | nil => rfl
  | cons value values ih =>
      rw [List.map_cons, cells_cons] at held
      have splitHeld : (PointsTo base value ∗ Cells (base + 1) (values.map some) ∗ rest) heap := by
        simpa only [PointsTo, sepConj_assoc] using held
      have first := read_of_pointsTo splitHeld
      have tail : (Cells (base + 1) (values.map some) ∗ PointsTo base value ∗ rest) heap := by
        cmem_exact
      have remaining := ih (base + 1) (PointsTo base value ∗ rest) tail
      simp [cellsReadback?, first, remaining]

/-- The existing actual load-before-store aggregate transfer earns equality
of every later pure decoder of the copied record. There is no supplied
source/destination equality premise. -/
theorem copy_cells_earns_readback (source destination : Ptr)
    (old : List (Option CVal)) (values : List CVal) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (Cells source (values.map some) ∗ Cells destination old ∗ rest)
      (CProg.copyCells source destination values.length)
      (fun _ heap =>
        (Cells source (values.map some) ∗ Cells destination (values.map some) ∗ rest) heap ∧
        cellsReadback? heap source values.length = some values ∧
        cellsReadback? heap destination values.length = some values) := by
  have transfer := frame (copy_cells (L := L) source destination old values lengths) rest
  simp only [sepConj_assoc] at transfer
  apply triple_post _ transfer
  intro _ heap copied
  have sourceOwned : (Cells source (values.map some) ∗
      Cells destination (values.map some) ∗ rest) heap := by cmem_exact
  have destinationOwned : (Cells destination (values.map some) ∗
      Cells source (values.map some) ∗ rest) heap := by cmem_exact
  exact ⟨sourceOwned, owned_cells_readback source values _ heap sourceOwned,
    owned_cells_readback destination values _ heap destinationOwned⟩

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Outcome scalar fields -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- Logical layout of every scalar copied by outcome_clone_fields. Embedded
environment, variant and goal-map storage have their own component ownership. -/
structure OutcomeLayout where
  kind : Nat
  resultForm : Nat
  atom : Nat
  cached : Nat
  delayed : Nat
  environment : Nat
  variant : Nat
  answerRef : Nat
  bank : Nat
  reference : Nat
  goalMap : Nat

def outcomeLayout (offset : OutcomeLayout) : ReadExpressions.Layout := fun name =>
  if name = "kind".toList then some ⟨offset.kind, .word⟩
  else if name = "result_form".toList then some ⟨offset.resultForm, .word⟩
  else if name = "atom".toList then some ⟨offset.atom, .pointer⟩
  else if name = "materialized_atom".toList then some ⟨offset.cached, .pointer⟩
  else if name = "delayed".toList then some ⟨offset.delayed, .pointer⟩
  else if name = "env".toList then some ⟨offset.environment, .embedded⟩
  else if name = "variant".toList then some ⟨offset.variant, .embedded⟩
  else if name = "answer_ref".toList then some ⟨offset.answerRef, .embedded⟩
  else if name = "bank".toList then some ⟨offset.bank, .pointer⟩
  else if name = "ref".toList then some ⟨offset.reference, .word64⟩
  else if name = "goal_instantiation".toList then some ⟨offset.goalMap, .embedded⟩
  else none

structure OutcomeScalars where
  kind : UInt32
  resultForm : UInt32
  atom : Option Ptr
  cached : Option Ptr
  delayed : Option Ptr
  bank : Option Ptr
  reference : UInt64
  deriving DecidableEq, Repr

def copyEnvironment (source destination : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "src".toList then some (.ptr (some source))
  else if name = "dst".toList then some (.ptr (some destination)) else none

def copyField (name : String) : CStatement := .assign
  (.field (.identifier "dst".toList) name.toList true)
  (.field (.identifier "src".toList) name.toList true)

def copyAnswerField (name : String) : CStatement := .assign
  (.field (.field (.identifier "dst".toList) "answer_ref".toList true) name.toList false)
  (.field (.field (.identifier "src".toList) "answer_ref".toList true) name.toList false)

def scalarCopyBody : List CStatement :=
  [copyField "kind", copyField "result_form", copyField "atom",
   copyField "materialized_atom", copyField "delayed",
   copyAnswerField "bank", copyAnswerField "ref"]

def embeddedReader : StatementBlock.Reader := fun layout environment expression =>
  ReadExpressions.expressionWithNames (fun name => ReadExpressions.resolved (environment name))
    ReadExpressions.noCalls layout expression cursorObjects

/-- The existing typed-object field writer handles dot through an embedded
record. This adapter admits only physical field stores, so its locals remain
unchanged. It does not approximate a nested object by a scalar pointer field. -/
def embeddedContext (environment : ReadExpressions.Environment) :
    StatementBlock.ObjectBindings.Context := fun name =>
  (environment name).map (fun value =>
    .scalar ⟨"Outcome".toList, 1⟩ (some value))

def embeddedProfile : StatementBlock.ObjectBindings.Profile where
  values := ReadExpressions.noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := fun _ _ => none
  cellExtent := fun _ => none
  byteExtent := fun _ => none
  sizeWidth := .bits64

def embeddedAssignment : StatementBlock.Assignment := fun layout environment statement =>
  match statement with
  | .assign (.field owner name arrow) rhs => do
      let value ← embeddedReader layout environment rhs
      let _ ← StatementBlock.ObjectBindings.writeValue embeddedProfile layout
        (embeddedContext environment) (.field owner name arrow) value
      pure environment
  | _ => CProg.undefined

def copyOutcomeScalars (offset : OutcomeLayout) (source destination : Ptr) :
    CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith { read := embeddedReader }
    embeddedAssignment (outcomeLayout offset) 0 8
    (copyEnvironment source destination) scalarCopyBody

def scalarCopyOperations (offset : OutcomeLayout) (source destination : Ptr) :
    CProg CVal ReadBlock.Result := do
  let kind ← CProg.loadU32 (source + offset.kind)
  CProg.store (destination + offset.kind) (.u32 kind)
  let resultForm ← CProg.loadU32 (source + offset.resultForm)
  CProg.store (destination + offset.resultForm) (.u32 resultForm)
  let atom ← CProg.loadPtr (source + offset.atom)
  CProg.store (destination + offset.atom) (.ptr atom)
  let cached ← CProg.loadPtr (source + offset.cached)
  CProg.store (destination + offset.cached) (.ptr cached)
  let delayed ← CProg.loadPtr (source + offset.delayed)
  CProg.store (destination + offset.delayed) (.ptr delayed)
  let bank ← CProg.loadPtr ((source + offset.answerRef) + offset.bank)
  CProg.store ((destination + offset.answerRef) + offset.bank) (.ptr bank)
  let reference ← CProg.loadU64 ((source + offset.answerRef) + offset.reference)
  CProg.store ((destination + offset.answerRef) + offset.reference) (.u64 reference)
  pure (.finished (.next (copyEnvironment source destination)))

theorem scalar_copy_uses_actual_fields (offset : OutcomeLayout) (source destination : Ptr) :
    copyOutcomeScalars offset source destination = scalarCopyOperations offset source destination := by
  simp [copyOutcomeScalars, scalarCopyBody, copyField, copyAnswerField,
    embeddedReader, cursorObjects, copyEnvironment, outcomeLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values, StatementBlock.ObjectBindings.declared,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    scalarCopyOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def OutcomeScalarCells (offset : OutcomeLayout) (address : Ptr) (value : OutcomeScalars) :
    Heap L → Prop :=
  PointsTo (address + offset.kind) (.u32 value.kind) ∗
  PointsTo (address + offset.resultForm) (.u32 value.resultForm) ∗
  PointsTo (address + offset.atom) (.ptr value.atom) ∗
  PointsTo (address + offset.cached) (.ptr value.cached) ∗
  PointsTo (address + offset.delayed) (.ptr value.delayed) ∗
  PointsTo ((address + offset.answerRef) + offset.bank) (.ptr value.bank) ∗
  PointsTo ((address + offset.answerRef) + offset.reference) (.u64 value.reference)

theorem scalar_copy_owned (offset : OutcomeLayout) (source destination : Ptr)
    (value previous : OutcomeScalars) (rest : Heap L → Prop) :
    CTriple (OutcomeScalarCells offset source value ∗
      OutcomeScalarCells offset destination previous ∗ rest)
      (copyOutcomeScalars offset source destination)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (OutcomeScalarCells offset source value ∗
          OutcomeScalarCells offset destination value ∗ rest) heap) := by
  rw [scalar_copy_uses_actual_fields]
  cmem_start heap held
  unfold scalarCopyOperations OutcomeScalarCells at *
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Full binding descriptor and aggregate assignment -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- The full descriptor, including accelerators and ownership references.
The three bloom bytes occupy three logical cells; native byte layout and
narrow-byte representation remain the separate ABI boundary. -/
structure BindingDescriptor where
  owners : Option Ptr
  entries : Option Ptr
  length : UInt32
  capacity : UInt32
  constraints : Option Ptr
  equalityLength : UInt32
  equalityCapacity : UInt32
  cycle : UInt32
  bloom0 : UInt32
  bloom1 : UInt32
  bloom2 : UInt32
  privateEntries : UInt32
  privateConstraints : UInt32
  lookupIndex : Option Ptr
  frameIndex : Option Ptr
  sharedEntries : Option Ptr
  sharedLength : UInt32
  sharedCapacity : UInt32
  prime : Option Ptr
  deriving DecidableEq, Repr

def BindingDescriptor.cells (value : BindingDescriptor) : List CVal :=
  [.ptr value.owners, .ptr value.entries, .u32 value.length, .u32 value.capacity,
   .ptr value.constraints, .u32 value.equalityLength, .u32 value.equalityCapacity,
   .u32 value.cycle, .u32 value.bloom0, .u32 value.bloom1, .u32 value.bloom2,
   .u32 value.privateEntries, .u32 value.privateConstraints,
   .ptr value.lookupIndex, .ptr value.frameIndex, .ptr value.sharedEntries,
   .u32 value.sharedLength, .u32 value.sharedCapacity, .ptr value.prime]

def BindingDescriptor.ofCells? : List CVal → Option BindingDescriptor
  | [.ptr owners, .ptr entries, .u32 length, .u32 capacity,
     .ptr constraints, .u32 equalityLength, .u32 equalityCapacity,
     .u32 cycle, .u32 bloom0, .u32 bloom1, .u32 bloom2,
     .u32 privateEntries, .u32 privateConstraints,
     .ptr lookupIndex, .ptr frameIndex, .ptr sharedEntries,
     .u32 sharedLength, .u32 sharedCapacity, .ptr prime] =>
      some ⟨owners, entries, length, capacity, constraints, equalityLength,
        equalityCapacity, cycle, bloom0, bloom1, bloom2, privateEntries,
        privateConstraints, lookupIndex, frameIndex, sharedEntries, sharedLength,
        sharedCapacity, prime⟩
  | _ => none

@[simp] theorem BindingDescriptor.cells_length (value : BindingDescriptor) :
    value.cells.length = 19 := rfl

@[simp] theorem BindingDescriptor.read_after_cells (value : BindingDescriptor) :
    BindingDescriptor.ofCells? value.cells = some value := by cases value; rfl

theorem BindingDescriptor.cells_injective : Function.Injective BindingDescriptor.cells := by
  intro left right same
  have read := congrArg BindingDescriptor.ofCells? same
  simpa using read

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def bindingDescriptor? (heap : Heap L) (address : Ptr) : Option BindingDescriptor :=
  cellsReadback? heap address 19 >>= BindingDescriptor.ofCells?

def BindingCells (address : Ptr) (descriptor : BindingDescriptor) : Heap L → Prop :=
  Cells address (descriptor.cells.map some)

theorem owned_binding_descriptor (address : Ptr) (descriptor : BindingDescriptor)
    (rest : Heap L → Prop) (heap : Heap L)
    (owned : (BindingCells address descriptor ∗ rest) heap) :
    bindingDescriptor? heap address = some descriptor := by
  have read := owned_cells_readback address descriptor.cells rest heap owned
  simp only [BindingDescriptor.cells_length] at read
  simp [bindingDescriptor?, read]

/-- Actual aggregate syntax from `bindings_copy` after the successful clone
and destination release. The temporary and destination remain distinct
storage objects; this transfer does not free the temporary's referenced data. -/
def bindingAssignment : CStatement := .assign
  (.unary .dereference (.identifier "dst".toList)) (.identifier "tmp".toList)

def bindingProfile (temporary : Ptr) : StatementBlock.ObjectBindings.Profile where
  values := ReadExpressions.noCalls
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun name => if name = "tmp".toList then some temporary else none
  fieldTypes := fun _ _ => none
  cellExtent := fun type => if type = ⟨"Bindings".toList, 0⟩ then some 19 else none
  recordTypes := [⟨"Bindings".toList, 0⟩]
  byteExtent := fun _ => none
  sizeWidth := .bits64

def bindingContext (temporary destination : Ptr) : StatementBlock.ObjectBindings.Context :=
  fun name => if name = "dst".toList then
    some (.scalar ⟨"Bindings".toList, 1⟩ (some (.ptr (some destination))))
  else if name = "tmp".toList then some (.object ⟨"Bindings".toList, 0⟩ temporary)
  else none

def bindingAssignmentRun (temporary destination : Ptr) :
    CProg CVal StatementBlock.ObjectBindings.Context :=
  StatementBlock.ObjectBindings.assignment (bindingProfile temporary)
    (fun _ => none) (bindingContext temporary destination) bindingAssignment

theorem binding_assignment_is_snapshot (temporary destination : Ptr) :
    bindingAssignmentRun temporary destination =
      (CProg.copyCells temporary destination 19 >>= fun _ =>
        pure (bindingContext temporary destination)) := by
  simp [bindingAssignmentRun, bindingAssignment, bindingProfile, bindingContext,
    StatementBlock.ObjectBindings.Profile.recordExtent,
    StatementBlock.ObjectBindings.assignment, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.types,
    StatementBlock.ObjectBindings.values,
    StatementBlock.ObjectBindings.places, ScalarBytes.typeOf?,
    ReadExpressions.placeWithNames, ReadExpressions.expressionWithNames,
    ReadExpressions.localOrLocated, ReadExpressions.resolved, ReadExpressions.pointer,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- Every descriptor coordinate is transported by the actual record store.
No semantic binding equality is assumed, and equal records do not imply equal
allocation identities. The preceding clone and release are separate steps. -/
theorem binding_assignment_earns_descriptor (temporary destination : Ptr)
    (source previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells temporary source ∗ BindingCells destination previous ∗ rest)
      (bindingAssignmentRun temporary destination)
      (fun result heap => result = bindingContext temporary destination ∧
        (BindingCells temporary source ∗ BindingCells destination source ∗ rest) heap ∧
        bindingDescriptor? heap temporary = some source ∧
        bindingDescriptor? heap destination = some source) := by
  rw [binding_assignment_is_snapshot]
  have copied := copy_cells_earns_readback temporary destination
    (previous.cells.map some) source.cells (by simp) rest
  simp only [BindingDescriptor.cells_length] at copied
  refine triple_bind _ copied (fun _ => ?_)
  apply triple_pre _ (P := fun heap =>
    (BindingCells temporary source ∗ BindingCells destination source ∗ rest) heap ∧
      bindingDescriptor? heap temporary = some source ∧
      bindingDescriptor? heap destination = some source)
  · intro heap reached
    refine ⟨reached.1, ?_, ?_⟩ <;>
      simp [bindingDescriptor?, reached.2.1, reached.2.2]
  · exact triple_pre act (fun _ owned => ⟨rfl, owned⟩)
      (triple_ret act (bindingContext temporary destination) _)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Parsed binding field blocks -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def recordFields (base : Ptr) : List CVal → Heap L → Prop
  | [] => emp
  | value :: rest => PointsTo base value ∗ recordFields (base + 1) rest

theorem cells_recordFields (base : Ptr) (values : List CVal) :
    Cells (L := L) base (values.map some) = recordFields base values := by
  induction values generalizing base with
  | nil => exact cells_nil base
  | cons value rest ih =>
      rw [List.map_cons, cells_cons, ih]
      rfl

def bindingLayout : ReadExpressions.Layout := fun name =>
  if name = "owners".toList then some ⟨0, .pointer⟩
  else if name = "entries".toList then some ⟨1, .pointer⟩
  else if name = "len".toList then some ⟨2, .word⟩
  else if name = "cap".toList then some ⟨3, .word⟩
  else if name = "constraints".toList then some ⟨4, .pointer⟩
  else if name = "eq_len".toList then some ⟨5, .word⟩
  else if name = "eq_cap".toList then some ⟨6, .word⟩
  else if name = "cycle_state".toList then some ⟨7, .word⟩
  else if name = "bloom0".toList then some ⟨8, .word⟩
  else if name = "bloom1".toList then some ⟨9, .word⟩
  else if name = "bloom2".toList then some ⟨10, .word⟩
  else if name = "private_entry_count".toList then some ⟨11, .word⟩
  else if name = "private_constraint_count".toList then some ⟨12, .word⟩
  else if name = "lookup_index".toList then some ⟨13, .pointer⟩
  else if name = "frame_index".toList then some ⟨14, .pointer⟩
  else if name = "shared_entries".toList then some ⟨15, .pointer⟩
  else if name = "shared_len".toList then some ⟨16, .word⟩
  else if name = "shared_cap".toList then some ⟨17, .word⟩
  else if name = "prime_ext".toList then some ⟨18, .pointer⟩
  else none

def bindingFieldAssignment (target source : String) : CStatement := .assign
  (.field (.identifier "dst".toList) target.toList true)
  (.field (.identifier "src".toList) source.toList true)

def bindingFieldBlock (source destination : Ptr) (body : List CStatement) :
    CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith { read := embeddedReader }
    embeddedAssignment bindingLayout 0 (body.length + 1)
    (copyEnvironment source destination) body

def sharedFieldBody : List CStatement :=
  [bindingFieldAssignment "shared_entries" "shared_entries", bindingFieldAssignment "shared_len" "shared_len", bindingFieldAssignment "shared_cap" "shared_cap", bindingFieldAssignment "len" "shared_len"]

def sharedFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with sharedEntries := source.sharedEntries, sharedLength := source.sharedLength, sharedCapacity := source.sharedCapacity, length := source.sharedLength }

def sharedFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadPtr (source + 15)
  CProg.store (destination + 15) (.ptr value0)
  let value1 ← CProg.loadU32 (source + 16)
  CProg.store (destination + 16) (.u32 value1)
  let value2 ← CProg.loadU32 (source + 17)
  CProg.store (destination + 17) (.u32 value2)
  let value3 ← CProg.loadU32 (source + 16)
  CProg.store (destination + 2) (.u32 value3)
  pure (.finished (.next (copyEnvironment source destination)))

theorem shared_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination sharedFieldBody =
      sharedFieldOperations source destination := by
  simp [bindingFieldBlock, sharedFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values, StatementBlock.ObjectBindings.declared,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    sharedFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem shared_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination sharedFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (sharedFieldResult value previous) ∗ rest) heap) := by
  rw [shared_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold sharedFieldOperations sharedFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def exclusiveFieldBody : List CStatement :=
  [bindingFieldAssignment "entries" "entries", bindingFieldAssignment "len" "len", bindingFieldAssignment "cap" "cap"]

def exclusiveFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with entries := source.entries, length := source.length, capacity := source.capacity }

def exclusiveFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadPtr (source + 1)
  CProg.store (destination + 1) (.ptr value0)
  let value1 ← CProg.loadU32 (source + 2)
  CProg.store (destination + 2) (.u32 value1)
  let value2 ← CProg.loadU32 (source + 3)
  CProg.store (destination + 3) (.u32 value2)
  pure (.finished (.next (copyEnvironment source destination)))

theorem exclusive_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination exclusiveFieldBody =
      exclusiveFieldOperations source destination := by
  simp [bindingFieldBlock, exclusiveFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values, StatementBlock.ObjectBindings.declared,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    exclusiveFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem exclusive_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination exclusiveFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (exclusiveFieldResult value previous) ∗ rest) heap) := by
  rw [exclusive_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold exclusiveFieldOperations exclusiveFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def constraintsFieldBody : List CStatement :=
  [bindingFieldAssignment "constraints" "constraints", bindingFieldAssignment "eq_len" "eq_len", bindingFieldAssignment "eq_cap" "eq_cap"]

def constraintsFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with constraints := source.constraints, equalityLength := source.equalityLength, equalityCapacity := source.equalityCapacity }

def constraintsFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadPtr (source + 4)
  CProg.store (destination + 4) (.ptr value0)
  let value1 ← CProg.loadU32 (source + 5)
  CProg.store (destination + 5) (.u32 value1)
  let value2 ← CProg.loadU32 (source + 6)
  CProg.store (destination + 6) (.u32 value2)
  pure (.finished (.next (copyEnvironment source destination)))

theorem constraints_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination constraintsFieldBody =
      constraintsFieldOperations source destination := by
  simp [bindingFieldBlock, constraintsFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values, StatementBlock.ObjectBindings.declared,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    constraintsFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem constraints_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination constraintsFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (constraintsFieldResult value previous) ∗ rest) heap) := by
  rw [constraints_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold constraintsFieldOperations constraintsFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def lookupFieldBody : List CStatement :=
  [bindingFieldAssignment "lookup_index" "lookup_index"]

def lookupFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with lookupIndex := source.lookupIndex }

def lookupFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadPtr (source + 13)
  CProg.store (destination + 13) (.ptr value0)
  pure (.finished (.next (copyEnvironment source destination)))

theorem lookup_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination lookupFieldBody =
      lookupFieldOperations source destination := by
  simp [bindingFieldBlock, lookupFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    lookupFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem lookup_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination lookupFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (lookupFieldResult value previous) ∗ rest) heap) := by
  rw [lookup_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold lookupFieldOperations lookupFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def frameFieldBody : List CStatement :=
  [bindingFieldAssignment "frame_index" "frame_index"]

def frameFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with frameIndex := source.frameIndex }

def frameFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadPtr (source + 14)
  CProg.store (destination + 14) (.ptr value0)
  pure (.finished (.next (copyEnvironment source destination)))

theorem frame_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination frameFieldBody =
      frameFieldOperations source destination := by
  simp [bindingFieldBlock, frameFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    frameFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem frame_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination frameFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (frameFieldResult value previous) ∗ rest) heap) := by
  rw [frame_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold frameFieldOperations frameFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def privateCountsFieldBody : List CStatement :=
  [bindingFieldAssignment "private_entry_count" "private_entry_count", bindingFieldAssignment "private_constraint_count" "private_constraint_count"]

def privateCountsFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with privateEntries := source.privateEntries, privateConstraints := source.privateConstraints }

def privateCountsFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadU32 (source + 11)
  CProg.store (destination + 11) (.u32 value0)
  let value1 ← CProg.loadU32 (source + 12)
  CProg.store (destination + 12) (.u32 value1)
  pure (.finished (.next (copyEnvironment source destination)))

theorem privateCounts_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination privateCountsFieldBody =
      privateCountsFieldOperations source destination := by
  simp [bindingFieldBlock, privateCountsFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values, StatementBlock.ObjectBindings.declared,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    privateCountsFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem privateCounts_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination privateCountsFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (privateCountsFieldResult value previous) ∗ rest) heap) := by
  rw [privateCounts_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold privateCountsFieldOperations privateCountsFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def cycleFieldBody : List CStatement :=
  [bindingFieldAssignment "cycle_state" "cycle_state"]

def cycleFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with cycle := source.cycle }

def cycleFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadU32 (source + 7)
  CProg.store (destination + 7) (.u32 value0)
  pure (.finished (.next (copyEnvironment source destination)))

theorem cycle_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination cycleFieldBody =
      cycleFieldOperations source destination := by
  simp [bindingFieldBlock, cycleFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    cycleFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem cycle_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination cycleFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (cycleFieldResult value previous) ∗ rest) heap) := by
  rw [cycle_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold cycleFieldOperations cycleFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

def ownersFieldBody : List CStatement :=
  [bindingFieldAssignment "owners" "owners"]

def ownersFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with owners := source.owners }

def ownersFieldOperations (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let value0 ← CProg.loadPtr source
  CProg.store destination (.ptr value0)
  pure (.finished (.next (copyEnvironment source destination)))

theorem owners_field_block_operations (source destination : Ptr) :
    bindingFieldBlock source destination ownersFieldBody =
      ownersFieldOperations source destination := by
  simp [bindingFieldBlock, ownersFieldBody, bindingFieldAssignment,
    embeddedReader, cursorObjects, copyEnvironment, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values,
    ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.fieldAddress, ReadExpressions.resolved,
    ReadExpressions.pointer, ReadExpressions.ObjectReads.fieldLayout,
    ReadExpressions.valueKind, ReadExpressions.placeWithNames,
    ownersFieldOperations, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  cases source
  cases destination
  rfl

theorem owners_field_block_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination ownersFieldBody)
      (fun result heap => result = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (ownersFieldResult value previous) ∗ rest) heap) := by
  rw [owners_field_block_operations]
  simp only [BindingCells, cells_recordFields]
  cmem_start heap held
  unfold ownersFieldOperations ownersFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Binding initialization and field guards -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def BindingDescriptor.initial : BindingDescriptor :=
  ⟨none, none, 0, 0, none, 0, 0, 1, 0, 0, 0, 0, 0, none, none, none, 0, 0, none⟩

/-- `bindings_init` stores, in source order. The bloom memset occupies its
three admitted byte cells; it has no padding or pointer reinterpretation. -/
def initializeBinding (destination : Ptr) : CProg CVal Unit := do
  CProg.store destination (.ptr none)
  CProg.store (destination + 1) (.ptr none)
  CProg.store (destination + 2) (.u32 0)
  CProg.store (destination + 3) (.u32 0)
  CProg.store (destination + 4) (.ptr none)
  CProg.store (destination + 5) (.u32 0)
  CProg.store (destination + 6) (.u32 0)
  CProg.store (destination + 11) (.u32 0)
  CProg.store (destination + 12) (.u32 0)
  CProg.store (destination + 7) (.u32 1)
  CProg.store (destination + 8) (.u32 0)
  CProg.store (destination + 9) (.u32 0)
  CProg.store (destination + 10) (.u32 0)
  CProg.store (destination + 13) (.ptr none)
  CProg.store (destination + 14) (.ptr none)
  CProg.store (destination + 15) (.ptr none)
  CProg.store (destination + 16) (.u32 0)
  CProg.store (destination + 17) (.u32 0)
  CProg.store (destination + 18) (.ptr none)

theorem initialize_binding_owned (destination : Ptr) (previous : BindingDescriptor)
    (rest : Heap L → Prop) :
    CTriple (BindingCells destination previous ∗ rest) (initializeBinding destination)
      (fun _ => BindingCells destination .initial ∗ rest) := by
  simp only [BindingCells, cells_recordFields]
  cmem_start heap owned
  unfold initializeBinding BindingDescriptor.initial BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

theorem binding_load_word (source : Ptr) (value : BindingDescriptor) (field : Nat)
    (word : UInt32) (inside : field < 19)
    (selected : (value.cells.map some)[field]? = some (some (.u32 word)))
    (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ rest) (CProg.loadU32 (source + field))
      (fun result heap => result = word ∧ (BindingCells source value ∗ rest) heap) := by
  apply loadU32_rule
  intro heap owned
  have bound : field < (value.cells.map some).length := by simpa using inside
  have atField : (value.cells.map some)[field] = some (.u32 word) := by
    simpa only [List.getElem?_eq_getElem bound, Option.some.injEq] using selected
  exact read_cells bound atField owned

theorem binding_load_pointer (source : Ptr) (value : BindingDescriptor) (field : Nat)
    (pointer : Option Ptr) (inside : field < 19)
    (selected : (value.cells.map some)[field]? = some (some (.ptr pointer)))
    (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ rest) (CProg.loadPtr (source + field))
      (fun result heap => result = pointer ∧ (BindingCells source value ∗ rest) heap) := by
  apply loadPtr_rule
  intro heap owned
  have bound : field < (value.cells.map some).length := by simpa using inside
  have atField : (value.cells.map some)[field] = some (.ptr pointer) := by
    simpa only [List.getElem?_eq_getElem bound, Option.some.injEq] using selected
  exact read_cells bound atField owned

def guardedWordFields (source destination : Ptr) (field : Nat)
    (test : UInt32 → Bool) (body : List CStatement) : CProg CVal ReadBlock.Result := do
  let word ← CProg.loadU32 (source + field)
  if test word then bindingFieldBlock source destination body
  else pure (.finished (.next (copyEnvironment source destination)))

def guardedPointerFields (source destination : Ptr) (field : Nat)
    (body : List CStatement) : CProg CVal ReadBlock.Result := do
  let pointer ← CProg.loadPtr (source + field)
  if pointer.isSome then bindingFieldBlock source destination body
  else pure (.finished (.next (copyEnvironment source destination)))

theorem guarded_word_fields_owned (source destination : Ptr) (field : Nat)
    (test : UInt32 → Bool) (body : List CStatement)
    (result : BindingDescriptor → BindingDescriptor → BindingDescriptor)
    (value previous : BindingDescriptor) (word : UInt32)
    (inside : field < 19)
    (selected : (value.cells.map some)[field]? = some (some (.u32 word)))
    (rest : Heap L → Prop)
    (branch : CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination body)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (result value previous) ∗ rest) heap)) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (guardedWordFields source destination field test body)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗
          BindingCells destination (if test word then result value previous else previous) ∗ rest) heap) := by
  unfold guardedWordFields
  apply triple_bind _ (binding_load_word source value field word inside selected _)
  intro actual
  apply triple_pure
  intro equality
  subst actual
  cases gate : test word with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact triple_pre act (fun _ owned => ⟨rfl, owned⟩) (triple_ret act _ _)
  | true => simpa only [gate, ↓reduceIte] using branch

theorem guarded_pointer_fields_owned (source destination : Ptr) (field : Nat)
    (body : List CStatement)
    (result : BindingDescriptor → BindingDescriptor → BindingDescriptor)
    (value previous : BindingDescriptor) (pointer : Option Ptr)
    (inside : field < 19)
    (selected : (value.cells.map some)[field]? = some (some (.ptr pointer)))
    (rest : Heap L → Prop)
    (branch : CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (bindingFieldBlock source destination body)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination (result value previous) ∗ rest) heap)) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (guardedPointerFields source destination field body)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗
          BindingCells destination (if pointer.isSome then result value previous else previous) ∗ rest) heap) := by
  unfold guardedPointerFields
  apply triple_bind _ (binding_load_pointer source value field pointer inside selected _)
  intro actual
  apply triple_pure
  intro equality
  subst actual
  cases gate : pointer.isSome with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact triple_pre act (fun _ owned => ⟨rfl, owned⟩) (triple_ret act _ _)
  | true => simpa only [gate, ↓reduceIte] using branch

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Retained binding-storage branch -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def guardedExclusiveFields (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let length ← CProg.loadU32 (source + 2)
  let shared ← CProg.loadU32 (source + 16)
  if 0 < length - shared then bindingFieldBlock source destination exclusiveFieldBody
  else pure (.finished (.next (copyEnvironment source destination)))

theorem guarded_exclusive_fields_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (guardedExclusiveFields source destination)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗
          BindingCells destination (if 0 < value.length - value.sharedLength
            then exclusiveFieldResult value previous else previous) ∗ rest) heap) := by
  unfold guardedExclusiveFields
  apply triple_bind _ (binding_load_word source value 2 value.length (by decide)
    (by simp [BindingDescriptor.cells]) _)
  intro actualLength
  apply triple_pure
  intro sameLength
  subst actualLength
  apply triple_bind _ (binding_load_word source value 16 value.sharedLength (by decide)
    (by simp [BindingDescriptor.cells]) _)
  intro actualShared
  apply triple_pure
  intro sameShared
  subst actualShared
  split
  · exact exclusive_field_block_owned source destination value previous rest
  · exact triple_pre act (fun _ owned => ⟨rfl, owned⟩) (triple_ret act _ _)

def bloomFieldResult (source previous : BindingDescriptor) : BindingDescriptor :=
  { previous with bloom0 := source.bloom0, bloom1 := source.bloom1, bloom2 := source.bloom2 }

def copyBloom (source destination : Ptr) : CProg CVal Unit :=
  CProg.copyCells (source + 8) (destination + 8) 3

theorem bloom_copy_owned (source destination : Ptr) (value previous : BindingDescriptor)
    (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (copyBloom source destination)
      (fun _ => BindingCells source value ∗ BindingCells destination (bloomFieldResult value previous) ∗ rest) := by
  simp only [BindingCells, cells_recordFields]
  cmem_start heap owned
  unfold copyBloom bloomFieldResult BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, CProg.copyCells, CProg.loadCells,
    CProg.initializeCells, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind] at *
  cmem_vcgen
  cmem_exact

def BindingDescriptor.afterShared (value : BindingDescriptor) : BindingDescriptor :=
  if 0 < value.sharedLength then sharedFieldResult value .initial else .initial

def BindingDescriptor.afterExclusive (value : BindingDescriptor) : BindingDescriptor :=
  if 0 < value.length - value.sharedLength then exclusiveFieldResult value value.afterShared
  else value.afterShared

def BindingDescriptor.afterConstraints (value : BindingDescriptor) : BindingDescriptor :=
  if 0 < value.equalityLength then constraintsFieldResult value value.afterExclusive
  else value.afterExclusive

def BindingDescriptor.afterLookup (value : BindingDescriptor) : BindingDescriptor :=
  if value.lookupIndex.isSome then lookupFieldResult value value.afterConstraints
  else value.afterConstraints

def BindingDescriptor.afterFrame (value : BindingDescriptor) : BindingDescriptor :=
  if value.frameIndex.isSome then frameFieldResult value value.afterLookup else value.afterLookup

def BindingDescriptor.afterCounts (value : BindingDescriptor) : BindingDescriptor :=
  privateCountsFieldResult value value.afterFrame

def BindingDescriptor.afterCycle (value : BindingDescriptor) : BindingDescriptor :=
  cycleFieldResult value value.afterCounts

def BindingDescriptor.afterBloom (value : BindingDescriptor) : BindingDescriptor :=
  bloomFieldResult value value.afterCycle

def BindingDescriptor.retainedFork (value : BindingDescriptor) : BindingDescriptor :=
  if value.owners.isSome then ownersFieldResult value value.afterBloom else value.afterBloom

/-- Payload-field projection of the successful retain branches in
`bindings_fork_version`. Each length/pointer guard is read from native fields.
Atomic retain, index/owner lifetime, cost counters and the Prime extension
are separate component boundaries; no claim about their C execution is hidden
inside this data projection. Allocation fallback uses the distinct array-copy
branch and must not be identified with this retained-storage path. -/
def retainedForkFields (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  initializeBinding destination
  let _ ← guardedWordFields source destination 16 (fun n => decide (0 < n)) sharedFieldBody
  let _ ← guardedExclusiveFields source destination
  let _ ← guardedWordFields source destination 5 (fun n => decide (0 < n)) constraintsFieldBody
  let _ ← guardedPointerFields source destination 13 lookupFieldBody
  let _ ← guardedPointerFields source destination 14 frameFieldBody
  let _ ← bindingFieldBlock source destination privateCountsFieldBody
  let _ ← bindingFieldBlock source destination cycleFieldBody
  copyBloom source destination
  guardedPointerFields source destination 0 ownersFieldBody

theorem retained_fork_fields_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (retainedForkFields source destination)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination value.retainedFork ∗ rest) heap) := by
  unfold retainedForkFields
  have initialized : CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (initializeBinding destination)
      (fun _ => BindingCells source value ∗ BindingCells destination .initial ∗ rest) := by
    apply triple_consequence _ (fun heap owned => ?_)
      (initialize_binding_owned destination previous (BindingCells source value ∗ rest))
      (fun _ heap owned => ?_) <;> cmem_exact
  apply triple_bind _ initialized
  intro _
  have shared := guarded_word_fields_owned source destination 16 (fun n => decide (0 < n))
    sharedFieldBody sharedFieldResult value .initial value.sharedLength (by decide)
    (by simp [BindingDescriptor.cells]) rest
    (shared_field_block_owned source destination value .initial rest)
  simp only [decide_eq_true_eq] at shared
  apply triple_bind _ (triple_post _ shared (fun _ _ owned => owned.2))
  intro _
  apply triple_bind _ (triple_post _
    (guarded_exclusive_fields_owned source destination value value.afterShared rest)
    (fun _ _ owned => owned.2))
  intro _
  have constraints := guarded_word_fields_owned source destination 5 (fun n => decide (0 < n))
    constraintsFieldBody constraintsFieldResult value value.afterExclusive value.equalityLength
    (by decide) (by simp [BindingDescriptor.cells]) rest
    (constraints_field_block_owned source destination value value.afterExclusive rest)
  simp only [decide_eq_true_eq] at constraints
  apply triple_bind _ (triple_post _ constraints (fun _ _ owned => owned.2))
  intro _
  apply triple_bind _ (triple_post _
    (guarded_pointer_fields_owned source destination 13 lookupFieldBody lookupFieldResult
      value value.afterConstraints value.lookupIndex (by decide)
      (by simp [BindingDescriptor.cells]) rest
      (lookup_field_block_owned source destination value value.afterConstraints rest))
    (fun _ _ owned => owned.2))
  intro _
  apply triple_bind _ (triple_post _
    (guarded_pointer_fields_owned source destination 14 frameFieldBody frameFieldResult
      value value.afterLookup value.frameIndex (by decide)
      (by simp [BindingDescriptor.cells]) rest
      (frame_field_block_owned source destination value value.afterLookup rest))
    (fun _ _ owned => owned.2))
  intro _
  apply triple_bind _ (triple_post _
    (privateCounts_field_block_owned source destination value value.afterFrame rest)
    (fun _ _ owned => owned.2))
  intro _
  apply triple_bind _ (triple_post _
    (cycle_field_block_owned source destination value value.afterCounts rest)
    (fun _ _ owned => owned.2))
  intro _
  apply triple_bind _ (bloom_copy_owned source destination value value.afterCycle rest)
  intro _
  exact guarded_pointer_fields_owned source destination 0 ownersFieldBody ownersFieldResult
    value value.afterBloom value.owners (by decide) (by simp [BindingDescriptor.cells]) rest
    (owners_field_block_owned source destination value value.afterBloom rest)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Owned payload segments -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- These are the three physical data-transfer cases following the native
length/retain/reserve guards. The allocator and atomic retain must justify
selecting a case and supply its owned storage; they do not supply its contents. -/
inductive SegmentTransfer where
  | empty
  | shared (source : Ptr)
  | copied (source destination : Ptr) (previous : List (Option CVal))
  deriving DecidableEq, Repr

def SegmentTransfer.source : SegmentTransfer → Option Ptr
  | .empty => none
  | .shared source | .copied source _ _ => some source

def SegmentTransfer.destination : SegmentTransfer → Option Ptr
  | .empty => none
  | .shared source => some source
  | .copied _ destination _ => some destination

/-- The memcpy path uses the existing typed-cell snapshot. The retained path
performs no payload write; its reference-count change precedes this boundary. -/
def SegmentTransfer.run (transfer : SegmentTransfer) (length : Nat) : CProg CVal (Option Ptr) :=
  match transfer with
  | .empty => pure none
  | .shared source => pure (some source)
  | .copied source destination _ => do
      CProg.copyCells source destination length
      pure (some destination)

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def SegmentTransfer.Before : SegmentTransfer → List CVal → Heap L → Prop
  | .empty, values => fun heap => values = [] ∧ emp heap
  | .shared source, values => Cells source (values.map some)
  | .copied source destination previous, values => fun heap =>
      previous.length = values.length ∧
      (Cells source (values.map some) ∗ Cells destination previous) heap

def SegmentTransfer.After : SegmentTransfer → List CVal → Heap L → Prop
  | .empty, _ => emp
  | .shared source, values => Cells source (values.map some)
  | .copied source destination _, values =>
      Cells source (values.map some) ∗ Cells destination (values.map some)

def segmentReadback? (heap : Heap L) (address : Option Ptr) (length : Nat) :
    Option (List CVal) :=
  if length = 0 then some [] else do
    let address ← address
    cellsReadback? heap address length

theorem owned_nonempty_segment_readback (address : Ptr) (values : List CVal)
    (rest : Heap L → Prop) (heap : Heap L)
    (owned : (Cells address (values.map some) ∗ rest) heap) :
    segmentReadback? heap (some address) values.length = some values := by
  by_cases empty : values.length = 0
  · have zero : values = [] := by simpa using empty
    simp [segmentReadback?, zero]
  · simp [segmentReadback?, empty, owned_cells_readback address values rest heap owned]

/-- Sharing and copying earn the same payload readback while retaining their
physical allocation distinction. No alias normalization or value deduplication
is performed; every cell in the source sequence survives. -/
theorem segment_transfer_earns_readback (transfer : SegmentTransfer) (values : List CVal)
    (rest : Heap L → Prop) :
    CTriple (transfer.Before values ∗ rest) (transfer.run values.length)
      (fun result heap => result = transfer.destination ∧
        (transfer.After values ∗ rest) heap ∧
        segmentReadback? heap transfer.source values.length = some values ∧
        segmentReadback? heap transfer.destination values.length = some values) := by
  cases transfer with
  | empty =>
      refine triple_pre act ?_ (triple_ret act none _)
      intro heap owned
      obtain ⟨left, right, separate, joined, held, restOwned⟩ := owned
      obtain ⟨emptyValues, emptyHeap⟩ := held
      subst values
      refine ⟨rfl, ?_, rfl, rfl⟩
      exact ⟨left, right, separate, joined, emptyHeap, restOwned⟩
  | shared source =>
      refine triple_pre act ?_ (triple_ret act (some source) _)
      intro heap owned
      have read := owned_nonempty_segment_readback source values rest heap owned
      exact ⟨rfl, owned, read, read⟩
  | copied source destination previous =>
      apply triple_pre act (P := fun heap => previous.length = values.length ∧
        (Cells source (values.map some) ∗ Cells destination previous ∗ rest) heap)
      · intro heap owned
        obtain ⟨left, right, separate, joined, held, framed⟩ := owned
        obtain ⟨length, copied⟩ := held
        refine ⟨length, ?_⟩
        have all : ((Cells source (values.map some) ∗ Cells destination previous) ∗ rest) heap :=
          ⟨left, right, separate, joined, copied, framed⟩
        simpa only [sepConj_assoc] using all
      · apply triple_pure
        intro lengths
        have copy := copy_cells_earns_readback source destination previous values lengths rest
        unfold SegmentTransfer.run
        refine triple_bind _ copy (fun _ => ?_)
        refine triple_pre act ?_ (triple_ret act (some destination) _)
        intro heap owned
        have sourceOwned := owned.1
        have destOwned : (Cells destination (values.map some) ∗
            Cells source (values.map some) ∗ rest) heap := by cmem_exact
        refine ⟨rfl, ?_, ?_, ?_⟩
        · simpa only [SegmentTransfer.After, sepConj_assoc] using sourceOwned
        · exact owned_nonempty_segment_readback source values _ heap sourceOwned
        · exact owned_nonempty_segment_readback destination values _ heap destOwned

/-- An absent source with a positive extent is rejected by the reader; a
previous empty prefix is not permission to fabricate initialized cells. -/
theorem missing_nonempty_segment_is_refused (heap : Heap L) (length : Nat)
    (positive : 0 < length) : segmentReadback? heap none length = none := by
  simp [segmentReadback?, Nat.ne_zero_of_lt positive]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Complete binding payload readback -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- Observable native payload, before any interpretation as an HE binding.
Array contents retain every coordinate and duplicate. Storage capacity and
array identities remain in the separately retained descriptors. -/
structure BindingImage where
  sharedRows : List CVal
  exclusiveRows : List CVal
  constraintRows : List CVal
  owners : Option Ptr
  lookupIndex : Option Ptr
  frameIndex : Option Ptr
  cycle : UInt32
  bloom0 : UInt32
  bloom1 : UInt32
  bloom2 : UInt32
  privateEntries : UInt32
  privateConstraints : UInt32
  prime : Option Ptr
  deriving DecidableEq, Repr

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def imageOfDescriptor? (entryExtent constraintExtent : Nat) (heap : Heap L)
    (descriptor : BindingDescriptor) : Option BindingImage := do
  if descriptor.length < descriptor.sharedLength then none else
    let shared ← segmentReadback? heap descriptor.sharedEntries
      (descriptor.sharedLength.toNat * entryExtent)
    let exclusive ← segmentReadback? heap descriptor.entries
      ((descriptor.length.toNat - descriptor.sharedLength.toNat) * entryExtent)
    let constraints ← segmentReadback? heap descriptor.constraints
      (descriptor.equalityLength.toNat * constraintExtent)
    pure ⟨shared, exclusive, constraints, descriptor.owners, descriptor.lookupIndex,
      descriptor.frameIndex, descriptor.cycle, descriptor.bloom0, descriptor.bloom1,
      descriptor.bloom2, descriptor.privateEntries, descriptor.privateConstraints,
      descriptor.prime⟩

def bindingImage? (entryExtent constraintExtent : Nat) (heap : Heap L) (address : Ptr) :
    Option BindingImage := do
  let descriptor ← bindingDescriptor? heap address
  imageOfDescriptor? entryExtent constraintExtent heap descriptor

/-- Exact retained-branch descriptor. Empty ranges need no retained capacity,
so the native fork deliberately clears those inactive allocation coordinates. -/
def BindingDescriptor.retainedView (source : BindingDescriptor) : BindingDescriptor :=
  { source with
    entries := if 0 < source.length - source.sharedLength then source.entries else none
    capacity := if 0 < source.length - source.sharedLength then source.capacity else 0
    constraints := if 0 < source.equalityLength then source.constraints else none
    equalityCapacity := if 0 < source.equalityLength then source.equalityCapacity else 0
    sharedEntries := if 0 < source.sharedLength then source.sharedEntries else none
    sharedCapacity := if 0 < source.sharedLength then source.sharedCapacity else 0
    prime := none }

private theorem word_zero_of_not_positive (value : UInt32) (zero : ¬0 < value) : value = 0 := by
  apply UInt32.toNat_inj.mp
  change value.toNat = 0
  change ¬0 < value.toNat at zero
  omega

private theorem length_from_retained_guards (source : BindingDescriptor)
    (wellFormed : source.sharedLength ≤ source.length) :
    (if 0 < source.length - source.sharedLength then source.length
      else if 0 < source.sharedLength then source.sharedLength else 0) = source.length := by
  by_cases exclusive : 0 < source.length - source.sharedLength
  · simp [exclusive]
  · have difference := word_zero_of_not_positive _ exclusive
    have naturals := congrArg UInt32.toNat difference
    rw [UInt32.toNat_sub_of_le _ _ wellFormed] at naturals
    have lengthNat : source.length.toNat = source.sharedLength.toNat := by
      have ordered := UInt32.le_iff_toNat_le.mp wellFormed
      change source.length.toNat - source.sharedLength.toNat = 0 at naturals
      omega
    have equal : source.length = source.sharedLength := UInt32.toNat_inj.mp lengthNat
    by_cases shared : 0 < source.sharedLength
    · simp [shared, equal]
    · simp [equal, word_zero_of_not_positive _ shared]

theorem retained_fork_descriptor_view (source : BindingDescriptor)
    (wellFormed : source.sharedLength ≤ source.length) :
    source.retainedFork = source.retainedView := by
  have length := length_from_retained_guards source wellFormed
  have shared : (if 0 < source.sharedLength then source.sharedLength else 0) =
      source.sharedLength := by
    by_cases positive : 0 < source.sharedLength
    · simp [positive]
    · simp [word_zero_of_not_positive _ positive]
  have equality : (if 0 < source.equalityLength then source.equalityLength else 0) =
      source.equalityLength := by
    by_cases positive : 0 < source.equalityLength
    · simp [positive]
    · simp [word_zero_of_not_positive _ positive]
  by_cases positiveShared : 0 < source.sharedLength <;>
    by_cases positiveExclusive : 0 < source.length - source.sharedLength <;>
    by_cases positiveEquality : 0 < source.equalityLength <;>
    cases owners : source.owners <;> cases lookup : source.lookupIndex <;>
      cases frame : source.frameIndex <;>
    simp_all [BindingDescriptor.retainedFork, BindingDescriptor.afterBloom,
      BindingDescriptor.afterCycle, BindingDescriptor.afterCounts, BindingDescriptor.afterFrame,
      BindingDescriptor.afterLookup, BindingDescriptor.afterConstraints,
      BindingDescriptor.afterExclusive, BindingDescriptor.afterShared,
      BindingDescriptor.initial, sharedFieldResult, exclusiveFieldResult,
      constraintsFieldResult, lookupFieldResult, frameFieldResult, privateCountsFieldResult,
      cycleFieldResult, bloomFieldResult, ownersFieldResult, BindingDescriptor.retainedView]

theorem segment_masked_readback (heap : Heap L) (pointer : Option Ptr)
    (length : UInt32) (extent count : Nat) (sized : count = length.toNat * extent) :
    segmentReadback? heap (if 0 < length then pointer else none) count =
      segmentReadback? heap pointer count := by
  subst count
  by_cases positive : 0 < length
  · simp [positive]
  · have zero := word_zero_of_not_positive length positive
    simp [zero, segmentReadback?]

/-- The native retained fork clears only inaccessible empty ranges. Its
readback is therefore unchanged for arbitrary open rows and constraints.
This is independent of how a later decoder interprets those cells. -/
theorem retained_fork_image (entryExtent constraintExtent : Nat) (heap : Heap L)
    (source : BindingDescriptor) (wellFormed : source.sharedLength ≤ source.length)
    (heRegion : source.prime = none) :
    imageOfDescriptor? entryExtent constraintExtent heap source.retainedFork =
      imageOfDescriptor? entryExtent constraintExtent heap source := by
  rw [retained_fork_descriptor_view source wellFormed]
  have shared := segment_masked_readback heap source.sharedEntries source.sharedLength
    entryExtent (source.sharedLength.toNat * entryExtent) rfl
  have exclusive := segment_masked_readback heap source.entries
    (source.length - source.sharedLength) entryExtent
    ((source.length.toNat - source.sharedLength.toNat) * entryExtent)
    (by rw [UInt32.toNat_sub_of_le _ _ wellFormed])
  have constraints := segment_masked_readback heap source.constraints source.equalityLength
    constraintExtent (source.equalityLength.toNat * constraintExtent) rfl
  simp only [imageOfDescriptor?, BindingDescriptor.retainedView]
  rw [shared, exclusive, constraints, heRegion]
  rfl

/-- The actual selected field stores earn equality of physical payload
readbacks. No whole-copy equality, valuation equality, or materialization
result is supplied by the caller. -/
theorem retained_fork_earns_binding_image (source destination : Ptr)
    (value previous : BindingDescriptor) (entryExtent constraintExtent : Nat)
    (wellFormed : value.sharedLength ≤ value.length) (heRegion : value.prime = none)
    (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (retainedForkFields source destination)
      (fun answer heap => answer = .finished (.next (copyEnvironment source destination)) ∧
        (BindingCells source value ∗ BindingCells destination value.retainedFork ∗ rest) heap ∧
        bindingImage? entryExtent constraintExtent heap destination =
          bindingImage? entryExtent constraintExtent heap source) := by
  apply triple_post _ (retained_fork_fields_owned source destination value previous rest)
  intro answer heap copied
  have sourceRead := owned_binding_descriptor source value
    (BindingCells destination value.retainedFork ∗ rest) heap copied.2
  have destinationOwned : (BindingCells destination value.retainedFork ∗
      BindingCells source value ∗ rest) heap := by
    have owned := copied.2
    cmem_exact
  have destinationRead := owned_binding_descriptor destination value.retainedFork
    (BindingCells source value ∗ rest) heap destinationOwned
  refine ⟨copied.1, copied.2, ?_⟩
  simp only [bindingImage?, sourceRead, destinationRead, bind, Option.bind_some]
  exact retained_fork_image entryExtent constraintExtent heap value wellFormed heRegion

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Reserved binding-array fallback -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The memcpy payload operation selected after a successful reserve. Its
array addresses are loaded from the actual reached descriptors, rather than
being inferred from equal payloads or supplied as the operation's result. -/
def copyBindingArray (source destination : Ptr) (field count : Nat) : CProg CVal Unit := do
  let destinationArray ← CProg.loadPtr (destination + field)
  let sourceArray ← CProg.loadPtr (source + field)
  let destinationAddress ← ReadExpressions.resolved destinationArray
  let sourceAddress ← ReadExpressions.resolved sourceArray
  CProg.copyCells sourceAddress destinationAddress count

/-- Capacity/allocation admission supplies writable cells, not their copied
contents. The actual load-before-store transfer earns both array readbacks.
This covers the exclusive-entry and constraint fallback payload operations. -/
theorem copy_binding_array_owned (source destination sourceArray destinationArray : Ptr)
    (value previous : BindingDescriptor) (field : Nat) (inside : field < 19)
    (sourceField : (value.cells.map some)[field]? = some (some (.ptr (some sourceArray))))
    (destinationField : (previous.cells.map some)[field]? = some (some (.ptr (some destinationArray))))
    (values : List CVal) (old : List (Option CVal)) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyBindingArray source destination field values.length)
      (fun _ heap =>
        (BindingCells source value ∗ BindingCells destination previous ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) heap ∧
        segmentReadback? heap (some sourceArray) values.length = some values ∧
        segmentReadback? heap (some destinationArray) values.length = some values) := by
  unfold copyBindingArray
  have destinationLoad : CTriple (BindingCells source value ∗ BindingCells destination previous ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (CProg.loadPtr (destination + field))
      (fun pointer heap => pointer = some destinationArray ∧
        (BindingCells source value ∗ BindingCells destination previous ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest) heap) := by
    apply triple_consequence _ (fun heap held => ?_)
      (binding_load_pointer destination previous field (some destinationArray) inside destinationField
        (BindingCells source value ∗ Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest))
      (fun pointer heap reached => ?_)
    · cmem_exact
    · refine ⟨reached.1, ?_⟩
      have held := reached.2
      cmem_exact
  apply triple_bind _ destinationLoad
  intro actualDestination
  apply triple_pure
  intro sameDestination
  subst actualDestination
  apply triple_bind _ (binding_load_pointer source value field (some sourceArray) inside sourceField
    (BindingCells destination previous ∗ Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest))
  intro actualSource
  apply triple_pure
  intro sameSource
  subst actualSource
  simp only [ReadExpressions.resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  apply triple_consequence _ (fun heap held => ?_)
    (copy_cells_earns_readback sourceArray destinationArray old values lengths
      (BindingCells source value ∗ BindingCells destination previous ∗ rest))
    (fun _ heap copied => ?_)
  · cmem_exact
  · have owned := copied.1
    have sourceOwned : (Cells sourceArray (values.map some) ∗
        BindingCells source value ∗ BindingCells destination previous ∗
        Cells destinationArray (values.map some) ∗ rest) heap := by cmem_exact
    have destinationOwned : (Cells destinationArray (values.map some) ∗
        BindingCells source value ∗ BindingCells destination previous ∗
        Cells sourceArray (values.map some) ∗ rest) heap := by cmem_exact
    refine ⟨?_, owned_nonempty_segment_readback sourceArray values _ heap sourceOwned,
      owned_nonempty_segment_readback destinationArray values _ heap destinationOwned⟩
    cmem_exact

/-- A null array is never promoted to a successful memcpy merely because a
capacity field claimed space. The physical pointer load and resolution reject
it before any payload store. -/
theorem null_source_array_is_undefined (destination : Ptr) (field count : Nat) :
    (CProg.loadPtr (destination + field) >>= fun destinationArray =>
      (pure (none : Option Ptr) : CProg CVal (Option Ptr)) >>= fun sourceArray =>
        ReadExpressions.resolved destinationArray >>= fun destinationAddress =>
          ReadExpressions.resolved sourceArray >>= fun sourceAddress =>
            CProg.copyCells sourceAddress destinationAddress count) =
      (CProg.loadPtr (destination + field) >>= fun destinationArray =>
        ReadExpressions.resolved destinationArray >>= fun _ => CProg.undefined) := by
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    show ReadExpressions.resolved (none : Option Ptr) = CProg.undefined from rfl]
  congr 1
  funext destinationArray
  congr 1
  funext destinationAddress
  exact ReadExpressions.undefined_bind _

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Fallback count publication -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def publishExclusiveLength (source destination : Ptr) : CProg CVal Unit := do
  let length ← CProg.loadU32 (source + 2)
  CProg.store (destination + 2) (.u32 length)

def publishConstraintLength (source destination : Ptr) : CProg CVal Unit := do
  let length ← CProg.loadU32 (source + 5)
  CProg.store (destination + 5) (.u32 length)

theorem publish_exclusive_length_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (publishExclusiveLength source destination)
      (fun _ => BindingCells source value ∗
        BindingCells destination { previous with length := value.length } ∗ rest) := by
  simp only [BindingCells, cells_recordFields]
  cmem_start heap owned
  unfold publishExclusiveLength BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

theorem publish_constraint_length_owned (source destination : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗ rest)
      (publishConstraintLength source destination)
      (fun _ => BindingCells source value ∗
        BindingCells destination { previous with equalityLength := value.equalityLength } ∗ rest) := by
  simp only [BindingCells, cells_recordFields]
  cmem_start heap owned
  unfold publishConstraintLength BindingDescriptor.cells at *
  simp only [recordFields, Ptr.add_add, Nat.reduceAdd, Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

/-- The reached allocation-fallback continuation of the actual entry clone:
read the source length and shared prefix, copy only its exclusive suffix,
then publish the total length. Reserved capacity and distinct storage are
already physical resources, never copied-content hypotheses. -/
def copyReservedExclusive (source destination : Ptr) (entryExtent : Nat) : CProg CVal Unit := do
  let length ← CProg.loadU32 (source + 2)
  let shared ← CProg.loadU32 (source + 16)
  copyBindingArray source destination 1 ((length - shared).toNat * entryExtent)
  publishExclusiveLength source destination

theorem copy_reserved_exclusive_owned (source destination sourceArray destinationArray : Ptr)
    (value previous : BindingDescriptor) (entryExtent : Nat)
    (wellFormed : value.sharedLength ≤ value.length)
    (sourceField : value.entries = some sourceArray)
    (destinationField : previous.entries = some destinationArray)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = (value.length.toNat - value.sharedLength.toNat) * entryExtent)
    (lengths : old.length = values.length) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyReservedExclusive source destination entryExtent)
      (fun _ => BindingCells source value ∗
        BindingCells destination { previous with length := value.length } ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) := by
  unfold copyReservedExclusive
  apply triple_bind _ (binding_load_word source value 2 value.length (by decide)
    (by simp [BindingDescriptor.cells]) _)
  intro actualLength
  apply triple_pure
  intro sameLength
  subst actualLength
  apply triple_bind _ (binding_load_word source value 16 value.sharedLength (by decide)
    (by simp [BindingDescriptor.cells]) _)
  intro actualShared
  apply triple_pure
  intro sameShared
  subst actualShared
  rw [UInt32.toNat_sub_of_le _ _ wellFormed, ← sized]
  apply triple_bind _ (triple_post _
    (copy_binding_array_owned source destination sourceArray destinationArray value previous 1
      (by decide) (by simp [BindingDescriptor.cells, sourceField])
      (by simp [BindingDescriptor.cells, destinationField]) values old lengths rest)
    (fun _ _ copied => copied.1))
  intro _
  exact publish_exclusive_length_owned source destination value previous
    (Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest)

def copyReservedConstraints (source destination : Ptr) (entryExtent : Nat) : CProg CVal Unit := do
  let length ← CProg.loadU32 (source + 5)
  copyBindingArray source destination 4 (length.toNat * entryExtent)
  publishConstraintLength source destination

theorem copy_reserved_constraints_owned (source destination sourceArray destinationArray : Ptr)
    (value previous : BindingDescriptor) (entryExtent : Nat)
    (sourceField : value.constraints = some sourceArray)
    (destinationField : previous.constraints = some destinationArray)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = value.equalityLength.toNat * entryExtent)
    (lengths : old.length = values.length) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells destination previous ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyReservedConstraints source destination entryExtent)
      (fun _ => BindingCells source value ∗
        BindingCells destination { previous with equalityLength := value.equalityLength } ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) := by
  unfold copyReservedConstraints
  apply triple_bind _ (binding_load_word source value 5 value.equalityLength (by decide)
    (by simp [BindingDescriptor.cells]) _)
  intro actualLength
  apply triple_pure
  intro sameLength
  subst actualLength
  rw [← sized]
  apply triple_bind _ (triple_post _
    (copy_binding_array_owned source destination sourceArray destinationArray value previous 4
      (by decide) (by simp [BindingDescriptor.cells, sourceField])
      (by simp [BindingDescriptor.cells, destinationField]) values old lengths rest)
    (fun _ _ copied => copied.1))
  intro _
  exact publish_constraint_length_owned source destination value previous
    (Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Counted payload storage -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The actual pointer/count prefix shared by variant storage and goal maps.
Capacity, indexes and lifetime data remain in the framed native storage. -/
def CountedArrayCells (address : Ptr) (items : Option Ptr) (count : UInt32) : Heap L → Prop :=
  PointsTo address (.ptr items) ∗ PointsTo (address + 1) (.u32 count)

def wordCell (heap : Heap L) (address : Ptr) : Option UInt32 := do
  match ← (read ((heap address.block).2 address.offset)).join with
  | .u32 value => some value
  | _ => none

def countedArrayReadback? (extent : Nat) (heap : Heap L) (address : Ptr) : Option (List CVal) := do
  let items ← pointerCell heap address
  let count ← wordCell heap (address + 1)
  segmentReadback? heap items (count.toNat * extent)

theorem owned_counted_header (address : Ptr) (items : Option Ptr) (count : UInt32)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (CountedArrayCells address items count ∗ rest) heap) :
    pointerCell heap address = some items ∧ wordCell heap (address + 1) = some count := by
  have first : (PointsTo address (.ptr items) ∗ PointsTo (address + 1) (.u32 count) ∗ rest) heap := by
    simpa only [CountedArrayCells, sepConj_assoc] using held
  have second : (PointsTo (address + 1) (.u32 count) ∗ PointsTo address (.ptr items) ∗ rest) heap := by
    cmem_exact
  constructor
  · simp [pointerCell, read_of_pointsTo first]
  · unfold wordCell
    rw [read_of_pointsTo second]
    rfl

theorem counted_load_count (address : Ptr) (items : Option Ptr) (count : UInt32)
    (rest : Heap L → Prop) :
    CTriple (CountedArrayCells address items count ∗ rest) (CProg.loadU32 (address + 1))
      (fun result heap => result = count ∧ (CountedArrayCells address items count ∗ rest) heap) := by
  apply loadU32_rule
  intro heap held
  have owned : (PointsTo (address + 1) (.u32 count) ∗ PointsTo address (.ptr items) ∗ rest) heap := by
    unfold CountedArrayCells at held
    cmem_exact
  exact read_of_pointsTo owned

theorem counted_load_pointer (address : Ptr) (items : Option Ptr) (count : UInt32)
    (rest : Heap L → Prop) :
    CTriple (CountedArrayCells address items count ∗ rest) (CProg.loadPtr address)
      (fun result heap => result = items ∧ (CountedArrayCells address items count ∗ rest) heap) := by
  apply loadPtr_rule
  intro heap held
  exact read_of_pointsTo (show (PointsTo address (.ptr items) ∗
    PointsTo (address + 1) (.u32 count) ∗ rest) heap by
      simpa only [CountedArrayCells, sepConj_assoc] using held)

def copyCountedPayload (source destination : Ptr) (extent : Nat) : CProg CVal Unit := do
  let count ← CProg.loadU32 (source + 1)
  if count = 0 then pure () else
    let destinationArray ← CProg.loadPtr destination
    let sourceArray ← CProg.loadPtr source
    let destinationAddress ← ReadExpressions.resolved destinationArray
    let sourceAddress ← ReadExpressions.resolved sourceArray
    CProg.copyCells sourceAddress destinationAddress (count.toNat * extent)

theorem copy_counted_empty_owned (source destination : Ptr) (items : Option Ptr)
    (extent : Nat) (rest : Heap L → Prop) :
    CTriple (CountedArrayCells source items 0 ∗ rest)
      (copyCountedPayload source destination extent)
      (fun _ => CountedArrayCells source items 0 ∗ rest) := by
  unfold copyCountedPayload
  apply triple_bind _ (counted_load_count source items 0 rest)
  intro actual
  apply triple_pure
  intro same
  subst actual
  simp only [↓reduceIte]
  simpa only [Prog.pure_eq] using
    (triple_ret (act (L := L) (V := CVal)) ()
      (fun _ : Unit => CountedArrayCells source items 0 ∗ rest))

/-- The reserve component supplies destination capacity and writable cells.
The copied contents are earned by the actual guarded loads and memcpy. The
source and destination headers, arrays and other fields remain separately owned. -/
theorem copy_counted_nonempty_owned (source destination sourceArray destinationArray : Ptr)
    (count previousCount : UInt32) (positive : count ≠ 0) (extent : Nat)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = count.toNat * extent) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (CountedArrayCells source (some sourceArray) count ∗
      CountedArrayCells destination (some destinationArray) previousCount ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyCountedPayload source destination extent)
      (fun _ => CountedArrayCells source (some sourceArray) count ∗
        CountedArrayCells destination (some destinationArray) previousCount ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) := by
  unfold copyCountedPayload
  apply triple_bind _ (counted_load_count source (some sourceArray) count _)
  intro actualCount
  apply triple_pure
  intro sameCount
  subst actualCount
  simp only [positive, ↓reduceIte]
  have destinationLoad : CTriple (CountedArrayCells source (some sourceArray) count ∗
      CountedArrayCells destination (some destinationArray) previousCount ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (CProg.loadPtr destination)
      (fun pointer heap => pointer = some destinationArray ∧
        (CountedArrayCells source (some sourceArray) count ∗
          CountedArrayCells destination (some destinationArray) previousCount ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest) heap) := by
    apply triple_consequence _ (fun heap held => ?_)
      (counted_load_pointer destination (some destinationArray) previousCount
        (CountedArrayCells source (some sourceArray) count ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest))
      (fun pointer heap reached => ?_)
    · cmem_exact
    · refine ⟨reached.1, ?_⟩
      have held := reached.2
      cmem_exact
  apply triple_bind _ destinationLoad
  intro actualDestination
  apply triple_pure
  intro sameDestination
  subst actualDestination
  apply triple_bind _ (counted_load_pointer source (some sourceArray) count _)
  intro actualSource
  apply triple_pure
  intro sameSource
  subst actualSource
  simp only [ReadExpressions.resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [← sized]
  apply triple_consequence _ (fun heap held => ?_)
    (copy_cells_earns_readback sourceArray destinationArray old values lengths
      (CountedArrayCells source (some sourceArray) count ∗
        CountedArrayCells destination (some destinationArray) previousCount ∗ rest))
    (fun _ heap reached => ?_)
  · cmem_exact
  · have held := reached.1
    cmem_exact

/-- The goal-map clone publishes its length after its payload copy; the
variant reserve has already installed that same count before copying. -/
def publishCopiedCount (source destination : Ptr) : CProg CVal Unit := do
  let count ← CProg.loadU32 (source + 1)
  CProg.store (destination + 1) (.u32 count)

theorem publish_copied_count_owned (source destination : Ptr)
    (sourceArray destinationArray : Option Ptr) (count previousCount : UInt32)
    (rest : Heap L → Prop) :
    CTriple (CountedArrayCells source sourceArray count ∗
      CountedArrayCells destination destinationArray previousCount ∗ rest)
      (publishCopiedCount source destination)
      (fun _ => CountedArrayCells source sourceArray count ∗
        CountedArrayCells destination destinationArray count ∗ rest) := by
  cmem_start heap held
  unfold publishCopiedCount CountedArrayCells at *
  simp only [Prog.bind_eq] at *
  cmem_vcgen
  cmem_exact

theorem owned_counted_readback (address array : Ptr) (count : UInt32)
    (extent : Nat) (values : List CVal) (sized : values.length = count.toNat * extent)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (CountedArrayCells address (some array) count ∗
      Cells array (values.map some) ∗ rest) heap) :
    countedArrayReadback? extent heap address = some values := by
  obtain ⟨pointer, word⟩ := owned_counted_header address (some array) count
    (Cells array (values.map some) ∗ rest) heap held
  have arrayOwned : (Cells array (values.map some) ∗
      CountedArrayCells address (some array) count ∗ rest) heap := by cmem_exact
  simp only [countedArrayReadback?, pointer, word, bind, Option.bind_some]
  rw [← sized]
  exact owned_nonempty_segment_readback array values _ heap arrayOwned

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Reserved variant copying -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def variantReadback? (heap : Heap L) (object : Ptr) : Option (List CVal) := do
  match ← pointerCell heap object with
  | none => some []
  | some storage => countedArrayReadback? 1 heap storage

theorem load_owned_pointer (address : Ptr) (pointer : Option Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo address (.ptr pointer) ∗ rest) (CProg.loadPtr address)
      (fun answer heap => answer = pointer ∧ (PointsTo address (.ptr pointer) ∗ rest) heap) := by
  exact loadPtr_rule (fun _ held => read_of_pointsTo held)

/-- The selected `variant_instance_free(dst)` path is the actual empty
destination guard: outcome_init installed NULL. Other destination lifetimes
require the independent freeing component, not a silent no-op here. -/
def freeEmptyVariant (destination : Ptr) : CProg CVal Unit := do
  let storage ← CProg.loadPtr destination
  match storage with
  | none => pure ()
  | some _ => CProg.undefined

theorem free_empty_variant_owned (destination : Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo destination (.ptr none) ∗ rest) (freeEmptyVariant destination)
      (fun _ => PointsTo destination (.ptr none) ∗ rest) := by
  unfold freeEmptyVariant
  apply triple_bind _ (load_owned_pointer destination none rest)
  intro actual
  apply triple_pure
  intro same
  subst actual
  simpa only [Prog.pure_eq] using
    (triple_ret (act (L := L) (V := CVal)) ()
      (fun _ : Unit => PointsTo destination (.ptr none) ∗ rest))

/-- `*dst = next` after the selected empty-destination free path. This is a
real aggregate snapshot of the one-pointer VariantInstance, not pointer
identification between independently allocated storage objects. -/
def publishVariant (next destination : Ptr) : CProg CVal Unit := do
  freeEmptyVariant destination
  CProg.copyCells next destination 1

theorem publish_variant_owned (next destination : Ptr) (storage : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (PointsTo next (.ptr storage) ∗ PointsTo destination (.ptr none) ∗ rest)
      (publishVariant next destination)
      (fun _ => PointsTo next (.ptr storage) ∗ PointsTo destination (.ptr storage) ∗ rest) := by
  unfold publishVariant
  have free : CTriple (PointsTo next (.ptr storage) ∗ PointsTo destination (.ptr none) ∗ rest)
      (freeEmptyVariant destination)
      (fun _ => PointsTo next (.ptr storage) ∗ PointsTo destination (.ptr none) ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (free_empty_variant_owned destination (PointsTo next (.ptr storage) ∗ rest))
      (fun _ heap held => ?_) <;> cmem_exact
  apply triple_bind _ free
  intro _
  cmem_start heap held
  simp only [CProg.copyCells, CProg.loadCells, CProg.initializeCells,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc] at *
  cmem_vcgen
  cmem_exact

/-- The successfully reserved clone continuation. The storage allocator and
reserve are upstream components; they supply fresh writable cells and the
requested count, never a copied array. Source presence is read from its real
wrapper; slot count and both array pointers are read from the reached storage. -/
def copyReservedVariant (source next destination : Ptr) : CProg CVal Unit := do
  let sourceStorage ← CProg.loadPtr source
  match sourceStorage with
  | none => publishVariant next destination
  | some sourceStorage => do
      let nextStorage ← CProg.loadPtr next
      let nextStorage ← ReadExpressions.resolved nextStorage
      copyCountedPayload sourceStorage nextStorage 1
      publishVariant next destination

theorem copy_reserved_variant_nonempty (source next destination sourceStorage nextStorage
    sourceArray destinationArray : Ptr) (count : UInt32) (positive : count ≠ 0)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = count.toNat) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage (some sourceArray) count ∗
      CountedArrayCells nextStorage (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyReservedVariant source next destination)
      (fun _ => PointsTo source (.ptr (some sourceStorage)) ∗
        PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr (some nextStorage)) ∗
        CountedArrayCells sourceStorage (some sourceArray) count ∗
        CountedArrayCells nextStorage (some destinationArray) count ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) := by
  unfold copyReservedVariant
  apply triple_bind _ (load_owned_pointer source (some sourceStorage) _)
  intro actualSource
  apply triple_pure
  intro sameSource
  subst actualSource
  have nextLoad : CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage (some sourceArray) count ∗
      CountedArrayCells nextStorage (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (CProg.loadPtr next)
      (fun answer heap => answer = some nextStorage ∧
        (PointsTo source (.ptr (some sourceStorage)) ∗
          PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
          CountedArrayCells sourceStorage (some sourceArray) count ∗
          CountedArrayCells nextStorage (some destinationArray) count ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest) heap) := by
    apply loadPtr_rule
    intro heap held
    have selected : (PointsTo next (.ptr (some nextStorage)) ∗
        PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo destination (.ptr none) ∗
        CountedArrayCells sourceStorage (some sourceArray) count ∗
        CountedArrayCells nextStorage (some destinationArray) count ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest) heap := by cmem_exact
    exact read_of_pointsTo selected
  apply triple_bind _ nextLoad
  intro actualNext
  apply triple_pure
  intro sameNext
  subst actualNext
  simp only [ReadExpressions.resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  have copy : CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage (some sourceArray) count ∗
      CountedArrayCells nextStorage (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyCountedPayload sourceStorage nextStorage 1)
      (fun _ => PointsTo source (.ptr (some sourceStorage)) ∗
        PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
        CountedArrayCells sourceStorage (some sourceArray) count ∗
        CountedArrayCells nextStorage (some destinationArray) count ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (copy_counted_nonempty_owned sourceStorage nextStorage sourceArray destinationArray
        count count positive 1 values old (by simpa using sized) lengths
        (PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some nextStorage)) ∗
          PointsTo destination (.ptr none) ∗ rest))
      (fun _ heap held => ?_) <;> cmem_exact
  apply triple_bind _ copy
  intro _
  apply triple_consequence _ (fun heap held => ?_)
    (publish_variant_owned next destination (some nextStorage)
      (PointsTo source (.ptr (some sourceStorage)) ∗
        CountedArrayCells sourceStorage (some sourceArray) count ∗
        CountedArrayCells nextStorage (some destinationArray) count ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest))
    (fun _ heap held => ?_) <;> cmem_exact

theorem copy_reserved_variant_absent (source next destination : Ptr)
    (rest : Heap L → Prop) :
    CTriple (PointsTo source (.ptr none) ∗ PointsTo next (.ptr none) ∗
      PointsTo destination (.ptr none) ∗ rest)
      (copyReservedVariant source next destination)
      (fun _ => PointsTo source (.ptr none) ∗ PointsTo next (.ptr none) ∗
        PointsTo destination (.ptr none) ∗ rest) := by
  unfold copyReservedVariant
  apply triple_bind _ (load_owned_pointer source none _)
  intro actual
  apply triple_pure
  intro same
  subst actual
  apply triple_consequence _ (fun heap held => ?_)
    (publish_variant_owned next destination none (PointsTo source (.ptr none) ∗ rest))
    (fun _ heap held => ?_) <;> cmem_exact

theorem owned_variant_readback (object storage array : Ptr) (count : UInt32)
    (values : List CVal) (sized : values.length = count.toNat)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (PointsTo object (.ptr (some storage)) ∗
      CountedArrayCells storage (some array) count ∗ Cells array (values.map some) ∗ rest) heap) :
    variantReadback? heap object = some values := by
  have pointer : pointerCell heap object = some (some storage) := by
    simp [pointerCell, read_of_pointsTo held]
  have storageOwned : (CountedArrayCells storage (some array) count ∗
      Cells array (values.map some) ∗ PointsTo object (.ptr (some storage)) ∗ rest) heap := by
    cmem_exact
  simp only [variantReadback?, pointer, bind, Option.bind_some]
  exact owned_counted_readback storage array count 1 values (by simpa using sized) _ heap storageOwned

theorem owned_absent_variant_readback (object : Ptr) (rest : Heap L → Prop)
    (heap : Heap L) (held : (PointsTo object (.ptr none) ∗ rest) heap) :
    variantReadback? heap object = some [] := by
  simp [variantReadback?, pointerCell, read_of_pointsTo held]

theorem copy_reserved_variant_empty_storage (source next destination sourceStorage nextStorage : Ptr)
    (sourceItems : Option Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest)
      (copyReservedVariant source next destination)
      (fun _ => PointsTo source (.ptr (some sourceStorage)) ∗
        PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr (some nextStorage)) ∗
        CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest) := by
  unfold copyReservedVariant
  apply triple_bind _ (load_owned_pointer source (some sourceStorage) _)
  intro actualSource
  apply triple_pure
  intro sameSource
  subst actualSource
  have nextLoad : CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest)
      (CProg.loadPtr next)
      (fun answer heap => answer = some nextStorage ∧
        (PointsTo source (.ptr (some sourceStorage)) ∗
          PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
          CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest) heap) := by
    apply loadPtr_rule
    intro heap held
    have selected : (PointsTo next (.ptr (some nextStorage)) ∗
        PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo destination (.ptr none) ∗
        CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest) heap := by
      cmem_exact
    exact read_of_pointsTo selected
  apply triple_bind _ nextLoad
  intro actualNext
  apply triple_pure
  intro sameNext
  subst actualNext
  simp only [ReadExpressions.resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  have copy : CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest)
      (copyCountedPayload sourceStorage nextStorage 1)
      (fun _ => PointsTo source (.ptr (some sourceStorage)) ∗
        PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
        CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells nextStorage none 0 ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (copy_counted_empty_owned sourceStorage nextStorage sourceItems 1
        (PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some nextStorage)) ∗
          PointsTo destination (.ptr none) ∗ CountedArrayCells nextStorage none 0 ∗ rest))
      (fun _ heap held => ?_) <;> cmem_exact
  apply triple_bind _ copy
  intro _
  apply triple_consequence _ (fun heap held => ?_)
    (publish_variant_owned next destination (some nextStorage)
      (PointsTo source (.ptr (some sourceStorage)) ∗ CountedArrayCells sourceStorage sourceItems 0 ∗
        CountedArrayCells nextStorage none 0 ∗ rest))
    (fun _ heap held => ?_) <;> cmem_exact

theorem copy_reserved_variant_earns_readback (source next destination sourceStorage nextStorage
    sourceArray destinationArray : Ptr) (count : UInt32) (positive : count ≠ 0)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = count.toNat) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo source (.ptr (some sourceStorage)) ∗
      PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr none) ∗
      CountedArrayCells sourceStorage (some sourceArray) count ∗
      CountedArrayCells nextStorage (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyReservedVariant source next destination)
      (fun _ heap =>
        (PointsTo source (.ptr (some sourceStorage)) ∗
          PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr (some nextStorage)) ∗
          CountedArrayCells sourceStorage (some sourceArray) count ∗
          CountedArrayCells nextStorage (some destinationArray) count ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) heap ∧
        variantReadback? heap source = some values ∧ variantReadback? heap destination = some values) := by
  apply triple_post _ (copy_reserved_variant_nonempty source next destination sourceStorage nextStorage
    sourceArray destinationArray count positive values old sized lengths rest)
  intro _ heap held
  refine ⟨held, ?_, ?_⟩
  · apply owned_variant_readback source sourceStorage sourceArray count values sized
      (PointsTo next (.ptr (some nextStorage)) ∗ PointsTo destination (.ptr (some nextStorage)) ∗
        CountedArrayCells nextStorage (some destinationArray) count ∗
        Cells destinationArray (values.map some) ∗ rest) heap
    cmem_exact
  · apply owned_variant_readback destination nextStorage destinationArray count values sized
      (PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some nextStorage)) ∗
        CountedArrayCells sourceStorage (some sourceArray) count ∗
        Cells sourceArray (values.map some) ∗ rest) heap
    cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Reserved goal-map copying -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The payload continuation after the nonzero guard and successful reserve
in cetta_var_map_clone. The final index rebuild and its possible failure are
separate from this actual memcpy and length publication; no index success is
inferred merely from having copied rows. -/
def copyReservedGoalMap (source destination : Ptr) (entryExtent : Nat) : CProg CVal Unit := do
  copyCountedPayload source destination entryExtent
  publishCopiedCount source destination

theorem copy_reserved_goal_map_owned (source destination sourceArray destinationArray : Ptr)
    (count : UInt32) (positive : count ≠ 0) (entryExtent : Nat)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = count.toNat * entryExtent) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (CountedArrayCells source (some sourceArray) count ∗
      CountedArrayCells destination (some destinationArray) 0 ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyReservedGoalMap source destination entryExtent)
      (fun _ => CountedArrayCells source (some sourceArray) count ∗
        CountedArrayCells destination (some destinationArray) count ∗
        Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) := by
  unfold copyReservedGoalMap
  apply triple_bind _ (copy_counted_nonempty_owned source destination sourceArray destinationArray
    count 0 positive entryExtent values old sized lengths rest)
  intro _
  exact publish_copied_count_owned source destination (some sourceArray) (some destinationArray)
    count 0 (Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest)

/-- Both physical readbacks are earned, including repeated source identifiers
and repeated mapped pointers. The index fields and spare capacity stay framed
and are not erased or asserted to have been copied. -/
theorem copy_reserved_goal_map_earns_readback (source destination sourceArray destinationArray : Ptr)
    (count : UInt32) (positive : count ≠ 0) (entryExtent : Nat)
    (values : List CVal) (old : List (Option CVal))
    (sized : values.length = count.toNat * entryExtent) (lengths : old.length = values.length)
    (rest : Heap L → Prop) :
    CTriple (CountedArrayCells source (some sourceArray) count ∗
      CountedArrayCells destination (some destinationArray) 0 ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old ∗ rest)
      (copyReservedGoalMap source destination entryExtent)
      (fun _ heap =>
        (CountedArrayCells source (some sourceArray) count ∗
          CountedArrayCells destination (some destinationArray) count ∗
          Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some) ∗ rest) heap ∧
        countedArrayReadback? entryExtent heap source = some values ∧
        countedArrayReadback? entryExtent heap destination = some values) := by
  apply triple_post _ (copy_reserved_goal_map_owned source destination sourceArray destinationArray
    count positive entryExtent values old sized lengths rest)
  intro _ heap held
  refine ⟨held, ?_, ?_⟩
  · apply owned_counted_readback source sourceArray count entryExtent values sized
      (CountedArrayCells destination (some destinationArray) count ∗
        Cells destinationArray (values.map some) ∗ rest) heap
    cmem_exact
  · apply owned_counted_readback destination destinationArray count entryExtent values sized
      (CountedArrayCells source (some sourceArray) count ∗
        Cells sourceArray (values.map some) ∗ rest) heap
    cmem_exact

theorem owned_empty_counted_readback (address : Ptr) (items : Option Ptr)
    (extent : Nat) (rest : Heap L → Prop) (heap : Heap L)
    (held : (CountedArrayCells address items 0 ∗ rest) heap) :
    countedArrayReadback? extent heap address = some [] := by
  obtain ⟨pointer, count⟩ := owned_counted_header address items 0 rest heap held
  simp [countedArrayReadback?, pointer, count, segmentReadback?]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Binding-copy input for native frames -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Bindings are interpreted from their physical payload image. The meaning
of cells, atoms, contextual slots and the authoritative frame index is still
an independent decoder obligation. Copy correctness holds for every such
decoder; it does not assume its source and destination answers are equal. -/
def payloadsFromBindingImage (entryExtent constraintExtent : Nat) (heap : Heap L)
    (base : PayloadReadback) (decode : BindingImage → Option Bindings) : PayloadReadback :=
  { base with bindings := fun address => bindingImage? entryExtent constraintExtent heap address >>= decode }

theorem owned_retained_copy_readback (entryExtent constraintExtent : Nat)
    (heap : Heap L) (base : PayloadReadback) (decode : BindingImage → Option Bindings)
    (source destination : Ptr) (value : BindingDescriptor)
    (wellFormed : value.sharedLength ≤ value.length) (heRegion : value.prime = none)
    (rest : Heap L → Prop)
    (owned : (BindingCells source value ∗ BindingCells destination value.retainedFork ∗ rest) heap) :
    (payloadsFromBindingImage entryExtent constraintExtent heap base decode).bindings destination =
      (payloadsFromBindingImage entryExtent constraintExtent heap base decode).bindings source := by
  have sourceRead := owned_binding_descriptor source value
    (BindingCells destination value.retainedFork ∗ rest) heap owned
  have destinationOwned : (BindingCells destination value.retainedFork ∗
      BindingCells source value ∗ rest) heap := by cmem_exact
  have destinationRead := owned_binding_descriptor destination value.retainedFork
    (BindingCells source value ∗ rest) heap destinationOwned
  simp only [payloadsFromBindingImage, bindingImage?, sourceRead, destinationRead,
    bind, Option.bind_some]
  rw [retained_fork_image entryExtent constraintExtent heap value wellFormed heRegion]

/-- The selected native child request no longer takes binding-copy equality
as a premise on this represented successful-retain path. Its actual descriptor
stores supply that equality. The independent payload decoder and saved parent
readback remain visible representation boundaries. -/
theorem native_child_request_of_owned_retained_copy (offset : FrameOffsets)
    (frameEnvironmentOffset outcomeEnvironmentOffset entryExtent constraintExtent : Nat)
    (base : PayloadReadback) (decode : BindingImage → Option Bindings)
    (caller : NativeCaller) (prepared : PreparedOutcome) (child : Ptr)
    (parent : PushArguments) (invocation : CallReturnControl.Invocation NativeCaller)
    (value : BindingDescriptor) (wellFormed : value.sharedLength ≤ value.length)
    (heRegion : value.prime = none) (rest : Heap L → Prop) (heap : Heap L)
    (owned : (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      BindingCells prepared.environment value ∗
      BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest) heap)
    (decoded : invocationOfFields?
      (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
      caller parent prepared = some invocation)
    (environment : prepared.environment = prepared.seed + outcomeEnvironmentOffset) :
    nativeChildRequest? offset frameEnvironmentOffset
      (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
      heap caller prepared child =
      some ⟨invocation, invocation.variantOnly, invocation.demand,
        invocation.reached, invocation.relayTarget⟩ := by
  apply native_child_request_of_owned_frames offset frameEnvironmentOffset
    outcomeEnvironmentOffset (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
    caller prepared child parent invocation
    (BindingCells prepared.environment value ∗
      BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest)
    heap owned decoded environment
  apply owned_retained_copy_readback entryExtent constraintExtent heap base decode
    prepared.environment (child + frameEnvironmentOffset) value wellFormed heRegion
    (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗ rest)
  cmem_exact

/-- The frame's successful-retain data preparation executes the guarded fork;
root registration, lifetime retention and stream attachment remain separate
native loader components. This is not a replacement native loader. -/
def prepareRetainedBindings (frameEnvironmentOffset : Nat) (child source : Ptr) : CProg CVal Unit := do
  let _ ← retainedForkFields source (child + frameEnvironmentOffset)
  pure ()

theorem prepare_retained_bindings_owned (frameEnvironmentOffset : Nat) (child source : Ptr)
    (value previous : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗
      BindingCells (child + frameEnvironmentOffset) previous ∗ rest)
      (prepareRetainedBindings frameEnvironmentOffset child source)
      (fun _ => BindingCells source value ∗
        BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest) := by
  unfold prepareRetainedBindings
  apply triple_bind _ (triple_post _
    (retained_fork_fields_owned source (child + frameEnvironmentOffset) value previous rest)
    (fun _ _ reached => reached.2))
  intro _
  simpa only [Prog.pure_eq] using (triple_ret (act (L := L) (V := CVal)) ()
    (fun _ : Unit => BindingCells source value ∗
      BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest))

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Temporary-based environment handoff -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Data projection of bindings_copy's successful retained-storage branch:
clone into its distinct local temporary, initialize the already-empty released
destination, then execute the actual aggregate `*dst = tmp`. The empty
destination is the fresh CALLER frame environment. Native retain counters and
the null-release helper guards remain lifetime component obligations. -/
def copyRetainedBindingsViaTemporary (source temporary destination : Ptr) : CProg CVal Unit := do
  let _ ← retainedForkFields source temporary
  initializeBinding destination
  let _ ← bindingAssignmentRun temporary destination
  pure ()

theorem copy_retained_bindings_via_temporary_owned (source temporary destination : Ptr)
    (value previousTemporary : BindingDescriptor) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells temporary previousTemporary ∗
      BindingCells destination .initial ∗ rest)
      (copyRetainedBindingsViaTemporary source temporary destination)
      (fun _ => BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
        BindingCells destination value.retainedFork ∗ rest) := by
  unfold copyRetainedBindingsViaTemporary
  apply triple_bind _ (triple_post _
    (retained_fork_fields_owned source temporary value previousTemporary
      (BindingCells destination .initial ∗ rest)) (fun _ _ reached => reached.2))
  intro _
  have initialized : CTriple (BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
      BindingCells destination .initial ∗ rest) (initializeBinding destination)
      (fun _ => BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
        BindingCells destination .initial ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (initialize_binding_owned destination .initial
        (BindingCells source value ∗ BindingCells temporary value.retainedFork ∗ rest))
      (fun _ heap held => ?_) <;> cmem_exact
  apply triple_bind _ initialized
  intro _
  have assignment : CTriple (BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
      BindingCells destination .initial ∗ rest) (bindingAssignmentRun temporary destination)
      (fun _ => BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
        BindingCells destination value.retainedFork ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (binding_assignment_earns_descriptor temporary destination value.retainedFork .initial
        (BindingCells source value ∗ rest))
      (fun _ heap reached => ?_)
    · cmem_exact
    · have held := reached.2.1
      cmem_exact
  apply triple_bind _ assignment
  intro _
  simpa only [Prog.pure_eq] using
    (triple_ret (act (L := L) (V := CVal)) ()
      (fun _ : Unit => BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
        BindingCells destination value.retainedFork ∗ rest))

/-- The lower copy premise of the native frame adapter is earned from the
actual temporary/store path. This preserves full binding payloads, including
open constraints and authoritative frame indexes, for every cell decoder. -/
theorem copy_retained_bindings_via_temporary_earns_readback
    (source temporary destination : Ptr) (value previousTemporary : BindingDescriptor)
    (entryExtent constraintExtent : Nat) (wellFormed : value.sharedLength ≤ value.length)
    (heRegion : value.prime = none) (base : PayloadReadback)
    (decode : BindingImage → Option Bindings) (rest : Heap L → Prop) :
    CTriple (BindingCells source value ∗ BindingCells temporary previousTemporary ∗
      BindingCells destination .initial ∗ rest)
      (copyRetainedBindingsViaTemporary source temporary destination)
      (fun _ heap =>
        (BindingCells source value ∗ BindingCells temporary value.retainedFork ∗
          BindingCells destination value.retainedFork ∗ rest) heap ∧
        (payloadsFromBindingImage entryExtent constraintExtent heap base decode).bindings destination =
          (payloadsFromBindingImage entryExtent constraintExtent heap base decode).bindings source) := by
  apply triple_post _
    (copy_retained_bindings_via_temporary_owned source temporary destination value previousTemporary rest)
  intro _ heap held
  refine ⟨held, ?_⟩
  apply owned_retained_copy_readback entryExtent constraintExtent heap base decode source destination
    value wellFormed heRegion (BindingCells temporary value.retainedFork ∗ rest)
  cmem_exact

/-- Both successful and failed payload decoding are retained. The actual
child request is computed from owned frames and the copied descriptor;
there is no supplied invocation/copy correspondence premise. -/
theorem native_child_request_after_owned_copy (offset : FrameOffsets)
    (frameEnvironmentOffset outcomeEnvironmentOffset entryExtent constraintExtent : Nat)
    (base : PayloadReadback) (decode : BindingImage → Option Bindings)
    (caller : NativeCaller) (prepared : PreparedOutcome) (child : Ptr) (parent : PushArguments)
    (value : BindingDescriptor) (wellFormed : value.sharedLength ≤ value.length)
    (heRegion : value.prime = none) (rest : Heap L → Prop) (heap : Heap L)
    (owned : (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      BindingCells prepared.environment value ∗
      BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest) heap)
    (environment : prepared.environment = prepared.seed + outcomeEnvironmentOffset) :
    nativeChildRequest? offset frameEnvironmentOffset
      (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
      heap caller prepared child =
      (invocationOfFields? (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
        caller parent prepared).map
        (fun invocation => ⟨invocation, invocation.variantOnly, invocation.demand,
          invocation.reached, invocation.relayTarget⟩) := by
  have parentRead := invocation_readback_from_owned_fields offset
    (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
    caller prepared parent
    (FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      BindingCells prepared.environment value ∗
      BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest) heap owned
  cases decoded : invocationOfFields?
      (payloadsFromBindingImage entryExtent constraintExtent heap base decode) caller parent prepared with
  | none => simp [nativeChildRequest?, parentRead, decoded]
  | some invocation =>
      simpa only [decoded, Option.map_some] using
        native_child_request_of_owned_retained_copy offset frameEnvironmentOffset outcomeEnvironmentOffset
          entryExtent constraintExtent base decode caller prepared child parent invocation value
          wellFormed heRegion rest heap owned decoded environment

theorem copied_child_request_via_actual_temporary (offset : FrameOffsets)
    (frameEnvironmentOffset outcomeEnvironmentOffset entryExtent constraintExtent : Nat)
    (base : PayloadReadback) (decode : BindingImage → Option Bindings)
    (caller : NativeCaller) (prepared : PreparedOutcome) (child temporary : Ptr)
    (parent : PushArguments) (value previousTemporary : BindingDescriptor)
    (wellFormed : value.sharedLength ≤ value.length) (heRegion : value.prime = none)
    (environment : prepared.environment = prepared.seed + outcomeEnvironmentOffset)
    (rest : Heap L → Prop) :
    CTriple (FrameCells offset caller.frame parent ∗
      FrameCells offset child
        (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
          outcomeEnvironmentOffset).scalar ∗
      BindingCells prepared.environment value ∗ BindingCells temporary previousTemporary ∗
      BindingCells (child + frameEnvironmentOffset) .initial ∗ rest)
      (copyRetainedBindingsViaTemporary prepared.environment temporary (child + frameEnvironmentOffset))
      (fun _ heap =>
        (FrameCells offset caller.frame parent ∗
          FrameCells offset child
            (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
              outcomeEnvironmentOffset).scalar ∗
          BindingCells prepared.environment value ∗ BindingCells temporary value.retainedFork ∗
          BindingCells (child + frameEnvironmentOffset) value.retainedFork ∗ rest) heap ∧
        nativeChildRequest? offset frameEnvironmentOffset
          (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
          heap caller prepared child =
          (invocationOfFields? (payloadsFromBindingImage entryExtent constraintExtent heap base decode)
            caller parent prepared).map
            (fun invocation => ⟨invocation, invocation.variantOnly, invocation.demand,
              invocation.reached, invocation.relayTarget⟩)) := by
  apply triple_consequence _ (fun heap held => ?_)
    (copy_retained_bindings_via_temporary_owned prepared.environment temporary (child + frameEnvironmentOffset)
      value previousTemporary
      (FrameCells offset caller.frame parent ∗
        FrameCells offset child
          (callbackArguments parent prepared.seed prepared.variantOnly prepared.relay
            outcomeEnvironmentOffset).scalar ∗ rest))
    (fun _ heap held => ?_)
  · cmem_exact
  · refine ⟨?_, ?_⟩
    · cmem_exact
    · apply native_child_request_after_owned_copy offset frameEnvironmentOffset outcomeEnvironmentOffset
        entryExtent constraintExtent base decode caller prepared child parent value wellFormed heRegion
        (BindingCells temporary value.retainedFork ∗ rest) heap (by cmem_exact) environment

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Whole outcome storage readback -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def word64Cell (heap : Heap L) (address : Ptr) : Option UInt64 :=
  match read ((heap address.block).2 address.offset) with
  | some (some (.u64 value)) => some value
  | _ => none

def outcomeScalarsReadback? (offset : OutcomeLayout) (heap : Heap L) (address : Ptr) :
    Option OutcomeScalars := do
  let kind ← wordCell heap (address + offset.kind)
  let resultForm ← wordCell heap (address + offset.resultForm)
  let atom ← pointerCell heap (address + offset.atom)
  let cached ← pointerCell heap (address + offset.cached)
  let delayed ← pointerCell heap (address + offset.delayed)
  let bank ← pointerCell heap ((address + offset.answerRef) + offset.bank)
  let reference ← word64Cell heap ((address + offset.answerRef) + offset.reference)
  pure ⟨kind, resultForm, atom, cached, delayed, bank, reference⟩

theorem owned_outcome_scalars (offset : OutcomeLayout) (address : Ptr) (value : OutcomeScalars)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (OutcomeScalarCells offset address value ∗ rest) heap) :
    outcomeScalarsReadback? offset heap address = some value := by
  unfold OutcomeScalarCells at held
  have kind : Reads (address + offset.kind) (.u32 value.kind) heap := by cmem_fact
  have form : Reads (address + offset.resultForm) (.u32 value.resultForm) heap := by cmem_fact
  have atom : Reads (address + offset.atom) (.ptr value.atom) heap := by cmem_fact
  have cached : Reads (address + offset.cached) (.ptr value.cached) heap := by cmem_fact
  have delayed : Reads (address + offset.delayed) (.ptr value.delayed) heap := by cmem_fact
  have bank : Reads ((address + offset.answerRef) + offset.bank) (.ptr value.bank) heap := by cmem_fact
  have reference : Reads ((address + offset.answerRef) + offset.reference) (.u64 value.reference) heap := by
    cmem_fact
  simp only [Reads] at kind form atom cached delayed bank reference
  simp only [outcomeScalarsReadback?, wordCell, pointerCell, word64Cell,
    kind, form, atom, cached, delayed, bank, reference]
  rfl

/-- An optional native segment owns its active cells. A NULL pointer can
represent only the empty sequence, not merely a claimed capacity. -/
def PayloadCells : Option Ptr → List CVal → Heap L → Prop
  | none, values => fun heap => values = [] ∧ emp heap
  | some address, values => Cells address (values.map some)

theorem payload_cells_readback (address : Option Ptr) (values : List CVal)
    (rest : Heap L → Prop) (heap : Heap L) (held : (PayloadCells address values ∗ rest) heap) :
    segmentReadback? heap address values.length = some values := by
  cases address with
  | none =>
      obtain ⟨left, right, separate, joined, owned, framed⟩ := held
      have empty := owned.1
      subst values
      rfl
  | some address => exact owned_nonempty_segment_readback address values rest heap held

structure BindingRows where
  shared : List CVal
  exclusive : List CVal
  constraints : List CVal
  deriving DecidableEq, Repr

def BindingRows.image (rows : BindingRows) (value : BindingDescriptor) : BindingImage :=
  ⟨rows.shared, rows.exclusive, rows.constraints, value.owners, value.lookupIndex, value.frameIndex,
    value.cycle, value.bloom0, value.bloom1, value.bloom2, value.privateEntries,
    value.privateConstraints, value.prime⟩

def BindingRows.Sized (rows : BindingRows) (value : BindingDescriptor)
    (entryExtent constraintExtent : Nat) : Prop :=
  rows.shared.length = value.sharedLength.toNat * entryExtent ∧
  rows.exclusive.length = (value.length.toNat - value.sharedLength.toNat) * entryExtent ∧
  rows.constraints.length = value.equalityLength.toNat * constraintExtent

def BindingPayloadCells (value : BindingDescriptor) (rows : BindingRows) : Heap L → Prop :=
  PayloadCells value.sharedEntries rows.shared ∗
  PayloadCells value.entries rows.exclusive ∗ PayloadCells value.constraints rows.constraints

theorem owned_binding_image (address : Ptr) (value : BindingDescriptor) (rows : BindingRows)
    (entryExtent constraintExtent : Nat) (wellFormed : value.sharedLength ≤ value.length)
    (sized : rows.Sized value entryExtent constraintExtent)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (BindingCells address value ∗ BindingPayloadCells value rows ∗ rest) heap) :
    bindingImage? entryExtent constraintExtent heap address = some (rows.image value) := by
  have descriptor := owned_binding_descriptor address value (BindingPayloadCells value rows ∗ rest) heap held
  have sharedOwned : (PayloadCells value.sharedEntries rows.shared ∗ BindingCells address value ∗
      PayloadCells value.entries rows.exclusive ∗ PayloadCells value.constraints rows.constraints ∗ rest) heap := by
    unfold BindingPayloadCells at held
    cmem_exact
  have exclusiveOwned : (PayloadCells value.entries rows.exclusive ∗ BindingCells address value ∗
      PayloadCells value.sharedEntries rows.shared ∗ PayloadCells value.constraints rows.constraints ∗ rest) heap := by
    unfold BindingPayloadCells at held
    cmem_exact
  have constraintOwned : (PayloadCells value.constraints rows.constraints ∗ BindingCells address value ∗
      PayloadCells value.sharedEntries rows.shared ∗ PayloadCells value.entries rows.exclusive ∗ rest) heap := by
    unfold BindingPayloadCells at held
    cmem_exact
  have shared := payload_cells_readback value.sharedEntries rows.shared _ heap sharedOwned
  have exclusive := payload_cells_readback value.entries rows.exclusive _ heap exclusiveOwned
  have constraints := payload_cells_readback value.constraints rows.constraints _ heap constraintOwned
  rw [sized.1] at shared
  rw [sized.2.1] at exclusive
  rw [sized.2.2] at constraints
  have ordered : ¬value.length < value.sharedLength := by
    have orderedNat := UInt32.le_iff_toNat_le.mp wellFormed
    change ¬ value.length.toNat < value.sharedLength.toNat
    omega
  simp [bindingImage?, descriptor, imageOfDescriptor?, ordered, shared, exclusive, constraints,
    BindingRows.image]

/-- Full stored Outcome payload. Provenance, answer references and delayed
payload are included. Cache refresh is a subsequent, explicit operation;
this readback never silently identifies a refreshed record with its source. -/
structure OutcomeImage where
  scalars : OutcomeScalars
  bindings : BindingImage
  variant : List CVal
  goalMap : List CVal
  deriving DecidableEq, Repr

def outcomeImage? (offset : OutcomeLayout) (entryExtent constraintExtent goalEntryExtent : Nat)
    (heap : Heap L) (address : Ptr) : Option OutcomeImage := do
  let scalars ← outcomeScalarsReadback? offset heap address
  let bindings ← bindingImage? entryExtent constraintExtent heap (address + offset.environment)
  let variant ← variantReadback? heap (address + offset.variant)
  let goalMap ← countedArrayReadback? goalEntryExtent heap
    ((address + offset.answerRef) + offset.goalMap)
  pure ⟨scalars, bindings, variant, goalMap⟩

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Allocated variant and goal buffers -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- Physical cases following the real variant allocation/reserve. This data
contains no source judgment or claimed equality between decoder results. -/
inductive VariantBuffers where
  | absent
  | empty (sourceStorage destinationStorage : Ptr) (sourceItems : Option Ptr)
  | slots (sourceStorage destinationStorage sourceArray destinationArray : Ptr)
      (count : UInt32) (values : List CVal) (old : List (Option CVal))

def VariantBuffers.rows : VariantBuffers → List CVal
  | .absent | .empty .. => []
  | .slots _ _ _ _ _ values _ => values

def VariantBuffers.Sized : VariantBuffers → Prop
  | .absent | .empty .. => True
  | .slots _ _ _ _ count values old =>
      count ≠ 0 ∧ values.length = count.toNat ∧ old.length = values.length

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def VariantBuffers.Before (source next destination : Ptr) : VariantBuffers → Heap L → Prop
  | .absent => PointsTo source (.ptr none) ∗ PointsTo next (.ptr none) ∗ PointsTo destination (.ptr none)
  | .empty sourceStorage destinationStorage sourceItems =>
      PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
      PointsTo destination (.ptr none) ∗ CountedArrayCells sourceStorage sourceItems 0 ∗
      CountedArrayCells destinationStorage none 0
  | .slots sourceStorage destinationStorage sourceArray destinationArray count values old =>
      PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
      PointsTo destination (.ptr none) ∗ CountedArrayCells sourceStorage (some sourceArray) count ∗
      CountedArrayCells destinationStorage (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old

def VariantBuffers.After (source next destination : Ptr) : VariantBuffers → Heap L → Prop
  | .absent => PointsTo source (.ptr none) ∗ PointsTo next (.ptr none) ∗ PointsTo destination (.ptr none)
  | .empty sourceStorage destinationStorage sourceItems =>
      PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
      PointsTo destination (.ptr (some destinationStorage)) ∗ CountedArrayCells sourceStorage sourceItems 0 ∗
      CountedArrayCells destinationStorage none 0
  | .slots sourceStorage destinationStorage sourceArray destinationArray count values _ =>
      PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
      PointsTo destination (.ptr (some destinationStorage)) ∗
      CountedArrayCells sourceStorage (some sourceArray) count ∗
      CountedArrayCells destinationStorage (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some)

theorem copy_variant_buffers_owned (source next destination : Ptr) (buffers : VariantBuffers)
    (sized : buffers.Sized) (rest : Heap L → Prop) :
    CTriple (buffers.Before source next destination ∗ rest) (copyReservedVariant source next destination)
      (fun _ => buffers.After source next destination ∗ rest) := by
  cases buffers with
  | absent =>
      simpa only [VariantBuffers.Before, VariantBuffers.After, sepConj_assoc] using
        copy_reserved_variant_absent source next destination rest
  | empty sourceStorage destinationStorage sourceItems =>
      simpa only [VariantBuffers.Before, VariantBuffers.After, sepConj_assoc] using
        copy_reserved_variant_empty_storage source next destination sourceStorage destinationStorage sourceItems rest
  | slots sourceStorage destinationStorage sourceArray destinationArray count values old =>
      simpa only [VariantBuffers.Before, VariantBuffers.After, sepConj_assoc] using
        copy_reserved_variant_nonempty source next destination sourceStorage destinationStorage
          sourceArray destinationArray count sized.1 values old sized.2.1 sized.2.2 rest

theorem variant_buffers_readback (source next destination : Ptr) (buffers : VariantBuffers)
    (sized : buffers.Sized) (rest : Heap L → Prop) (heap : Heap L)
    (held : (buffers.After source next destination ∗ rest) heap) :
    variantReadback? heap source = some buffers.rows ∧
      variantReadback? heap destination = some buffers.rows := by
  cases buffers with
  | absent =>
      simp only [VariantBuffers.After, sepConj_assoc] at held
      constructor
      · exact owned_absent_variant_readback source _ heap held
      · apply owned_absent_variant_readback destination
          (PointsTo source (.ptr none) ∗ PointsTo next (.ptr none) ∗ rest) heap
        cmem_exact
  | empty sourceStorage destinationStorage sourceItems =>
      simp only [VariantBuffers.After, sepConj_assoc] at held
      have sourcePointer : pointerCell heap source = some (some sourceStorage) := by
        simp [pointerCell, read_of_pointsTo held]
      have destinationOwned : (PointsTo destination (.ptr (some destinationStorage)) ∗
          PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
          CountedArrayCells sourceStorage sourceItems 0 ∗ CountedArrayCells destinationStorage none 0 ∗ rest) heap := by
        cmem_exact
      have destinationPointer : pointerCell heap destination = some (some destinationStorage) := by
        simp [pointerCell, read_of_pointsTo destinationOwned]
      have sourceRead : countedArrayReadback? 1 heap sourceStorage = some [] := by
        apply owned_empty_counted_readback sourceStorage sourceItems 1
          (PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
            PointsTo destination (.ptr (some destinationStorage)) ∗ CountedArrayCells destinationStorage none 0 ∗ rest) heap
        cmem_exact
      have destinationRead : countedArrayReadback? 1 heap destinationStorage = some [] := by
        apply owned_empty_counted_readback destinationStorage none 1
          (PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
            PointsTo destination (.ptr (some destinationStorage)) ∗ CountedArrayCells sourceStorage sourceItems 0 ∗ rest) heap
        cmem_exact
      simp [variantReadback?, sourcePointer, destinationPointer, sourceRead, destinationRead, VariantBuffers.rows]
  | slots sourceStorage destinationStorage sourceArray destinationArray count values old =>
      simp only [VariantBuffers.After, sepConj_assoc] at held
      constructor
      · apply owned_variant_readback source sourceStorage sourceArray count values sized.2.1
          (PointsTo next (.ptr (some destinationStorage)) ∗ PointsTo destination (.ptr (some destinationStorage)) ∗
            CountedArrayCells destinationStorage (some destinationArray) count ∗
            Cells destinationArray (values.map some) ∗ rest) heap
        cmem_exact
      · apply owned_variant_readback destination destinationStorage destinationArray count values sized.2.1
          (PointsTo source (.ptr (some sourceStorage)) ∗ PointsTo next (.ptr (some destinationStorage)) ∗
            CountedArrayCells sourceStorage (some sourceArray) count ∗
            Cells sourceArray (values.map some) ∗ rest) heap
        cmem_exact

/-- Physical payload cases at the goal-map copy boundary. The index and
capacity are retained in the caller's footprint; this does not assert that
copying the rows has completed the native index reconstruction. -/
inductive GoalMapBuffers where
  | empty (sourceItems : Option Ptr)
  | entries (sourceArray destinationArray : Ptr) (count : UInt32)
      (values : List CVal) (old : List (Option CVal))

def GoalMapBuffers.rows : GoalMapBuffers → List CVal
  | .empty _ => []
  | .entries _ _ _ values _ => values

def GoalMapBuffers.Sized (extent : Nat) : GoalMapBuffers → Prop
  | .empty _ => True
  | .entries _ _ count values old =>
      count ≠ 0 ∧ values.length = count.toNat * extent ∧ old.length = values.length

def GoalMapBuffers.Before (source destination : Ptr) : GoalMapBuffers → Heap L → Prop
  | .empty sourceItems => CountedArrayCells source sourceItems 0 ∗ CountedArrayCells destination none 0
  | .entries sourceArray destinationArray count values old =>
      CountedArrayCells source (some sourceArray) count ∗ CountedArrayCells destination (some destinationArray) 0 ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray old

def GoalMapBuffers.After (source destination : Ptr) : GoalMapBuffers → Heap L → Prop
  | .empty sourceItems => CountedArrayCells source sourceItems 0 ∗ CountedArrayCells destination none 0
  | .entries sourceArray destinationArray count values _ =>
      CountedArrayCells source (some sourceArray) count ∗ CountedArrayCells destination (some destinationArray) count ∗
      Cells sourceArray (values.map some) ∗ Cells destinationArray (values.map some)

def copyGoalMapData (source destination : Ptr) (entryExtent : Nat) : CProg CVal Unit := do
  let count ← CProg.loadU32 (source + 1)
  if count = 0 then pure () else copyReservedGoalMap source destination entryExtent

theorem copy_goal_map_buffers_owned (source destination : Ptr) (entryExtent : Nat)
    (buffers : GoalMapBuffers) (sized : buffers.Sized entryExtent) (rest : Heap L → Prop) :
    CTriple (buffers.Before source destination ∗ rest) (copyGoalMapData source destination entryExtent)
      (fun _ => buffers.After source destination ∗ rest) := by
  unfold copyGoalMapData
  cases buffers with
  | empty sourceItems =>
      simp only [GoalMapBuffers.Before, GoalMapBuffers.After, sepConj_assoc]
      apply triple_bind _ (counted_load_count source sourceItems 0 _)
      intro actual
      apply triple_pure
      intro same
      subst actual
      simp only [↓reduceIte]
      simpa only [Prog.pure_eq] using (triple_ret (act (L := L) (V := CVal)) ()
        (fun _ : Unit => CountedArrayCells source sourceItems 0 ∗ CountedArrayCells destination none 0 ∗ rest))
  | entries sourceArray destinationArray count values old =>
      simp only [GoalMapBuffers.Before, GoalMapBuffers.After, sepConj_assoc]
      apply triple_bind _ (counted_load_count source (some sourceArray) count _)
      intro actual
      apply triple_pure
      intro same
      subst actual
      simp only [sized.1, ↓reduceIte]
      exact copy_reserved_goal_map_owned source destination sourceArray destinationArray count sized.1
        entryExtent values old sized.2.1 sized.2.2 rest

theorem goal_map_buffers_readback (source destination : Ptr) (entryExtent : Nat)
    (buffers : GoalMapBuffers) (sized : buffers.Sized entryExtent) (rest : Heap L → Prop)
    (heap : Heap L) (held : (buffers.After source destination ∗ rest) heap) :
    countedArrayReadback? entryExtent heap source = some buffers.rows ∧
      countedArrayReadback? entryExtent heap destination = some buffers.rows := by
  cases buffers with
  | empty sourceItems =>
      simp only [GoalMapBuffers.After, sepConj_assoc] at held
      constructor
      · exact owned_empty_counted_readback source sourceItems entryExtent _ heap held
      · apply owned_empty_counted_readback destination none entryExtent
          (CountedArrayCells source sourceItems 0 ∗ rest) heap
        cmem_exact
  | entries sourceArray destinationArray count values old =>
      simp only [GoalMapBuffers.After, sepConj_assoc] at held
      constructor
      · apply owned_counted_readback source sourceArray count entryExtent values sized.2.1
          (CountedArrayCells destination (some destinationArray) count ∗
            Cells destinationArray (values.map some) ∗ rest) heap
        cmem_exact
      · apply owned_counted_readback destination destinationArray count entryExtent values sized.2.1
          (CountedArrayCells source (some sourceArray) count ∗
            Cells sourceArray (values.map some) ∗ rest) heap
        cmem_exact

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Composed outcome stored-data projection -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The stored-data projection of clone_fields, at its successful helper
boundaries. The actual scalar stores and binding fork are followed by the
variant and goal-map payload continuations. Allocation/retain/index helper
effects are separate native components; this projection neither changes their
order nor claims to execute those omitted calls. All prepared storage is
explicitly owned, and none of its destination contents is assumed copied. -/
def copyPreparedOutcomeData (offset : OutcomeLayout) (source destination nextVariant : Ptr)
    (goalEntryExtent : Nat) : CProg CVal Unit := do
  let _ ← copyOutcomeScalars offset source destination
  let _ ← retainedForkFields (source + offset.environment) (destination + offset.environment)
  copyReservedVariant (source + offset.variant) nextVariant (destination + offset.variant)
  copyGoalMapData ((source + offset.answerRef) + offset.goalMap)
    ((destination + offset.answerRef) + offset.goalMap) goalEntryExtent

def PreparedOutcomeData (offset : OutcomeLayout) (source destination nextVariant : Ptr)
    (scalars previousScalars : OutcomeScalars) (bindings previousBindings : BindingDescriptor)
    (rows : BindingRows) (variant : VariantBuffers) (goalMap : GoalMapBuffers) : Heap L → Prop :=
  OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination previousScalars ∗
  BindingCells (source + offset.environment) bindings ∗
  BindingCells (destination + offset.environment) previousBindings ∗
  BindingPayloadCells bindings rows ∗
  variant.Before (source + offset.variant) nextVariant (destination + offset.variant) ∗
  goalMap.Before ((source + offset.answerRef) + offset.goalMap)
    ((destination + offset.answerRef) + offset.goalMap)

def CopiedOutcomeData (offset : OutcomeLayout) (source destination nextVariant : Ptr)
    (scalars : OutcomeScalars) (bindings : BindingDescriptor) (rows : BindingRows)
    (variant : VariantBuffers) (goalMap : GoalMapBuffers) : Heap L → Prop :=
  OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
  BindingCells (source + offset.environment) bindings ∗
  BindingCells (destination + offset.environment) bindings.retainedFork ∗
  BindingPayloadCells bindings rows ∗
  variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗
  goalMap.After ((source + offset.answerRef) + offset.goalMap)
    ((destination + offset.answerRef) + offset.goalMap)

theorem copy_prepared_outcome_data_owned (offset : OutcomeLayout) (source destination nextVariant : Ptr)
    (scalars previousScalars : OutcomeScalars) (bindings previousBindings : BindingDescriptor)
    (rows : BindingRows) (variant : VariantBuffers) (goalMap : GoalMapBuffers)
    (goalEntryExtent : Nat) (variantSized : variant.Sized) (goalSized : goalMap.Sized goalEntryExtent)
    (rest : Heap L → Prop) :
    CTriple (PreparedOutcomeData offset source destination nextVariant scalars previousScalars
      bindings previousBindings rows variant goalMap ∗ rest)
      (copyPreparedOutcomeData offset source destination nextVariant goalEntryExtent)
      (fun _ => CopiedOutcomeData offset source destination nextVariant scalars bindings rows variant goalMap ∗ rest) := by
  simp only [PreparedOutcomeData, CopiedOutcomeData, sepConj_assoc]
  unfold copyPreparedOutcomeData
  apply triple_bind _ (triple_post _
    (scalar_copy_owned offset source destination scalars previousScalars
      (BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) previousBindings ∗ BindingPayloadCells bindings rows ∗
        variant.Before (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.Before ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest))
    (fun _ _ reached => reached.2))
  intro _
  have bindingStep : CTriple
      (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
        BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) previousBindings ∗ BindingPayloadCells bindings rows ∗
        variant.Before (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.Before ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest)
      (retainedForkFields (source + offset.environment) (destination + offset.environment))
      (fun _ => OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
        BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
        variant.Before (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.Before ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (retained_fork_fields_owned (source + offset.environment) (destination + offset.environment)
        bindings previousBindings
        (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
          BindingPayloadCells bindings rows ∗
          variant.Before (source + offset.variant) nextVariant (destination + offset.variant) ∗
          goalMap.Before ((source + offset.answerRef) + offset.goalMap)
            ((destination + offset.answerRef) + offset.goalMap) ∗ rest))
      (fun _ heap reached => ?_)
    · cmem_exact
    · have held := reached.2
      cmem_exact
  apply triple_bind _ bindingStep
  intro _
  have variantStep : CTriple
      (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
        BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
        variant.Before (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.Before ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest)
      (copyReservedVariant (source + offset.variant) nextVariant (destination + offset.variant))
      (fun _ => OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
        BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
        variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.Before ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest) := by
    apply triple_consequence _ (fun heap held => ?_)
      (copy_variant_buffers_owned (source + offset.variant) nextVariant (destination + offset.variant)
        variant variantSized
        (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
          BindingCells (source + offset.environment) bindings ∗
          BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
          goalMap.Before ((source + offset.answerRef) + offset.goalMap)
            ((destination + offset.answerRef) + offset.goalMap) ∗ rest))
      (fun _ heap held => ?_) <;> cmem_exact
  apply triple_bind _ variantStep
  intro _
  apply triple_consequence _ (fun heap held => ?_)
    (copy_goal_map_buffers_owned ((source + offset.answerRef) + offset.goalMap)
      ((destination + offset.answerRef) + offset.goalMap) goalEntryExtent goalMap goalSized
      (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
        BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
        variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗ rest))
    (fun _ heap held => ?_) <;> cmem_exact

/-- Every decoder input is obtained from the reached owned storage. The
variant and goal-map arrays may have different allocation identities, while
their repeated cells and every binding coordinate remain present. -/
theorem copied_outcome_data_readback (offset : OutcomeLayout) (source destination nextVariant : Ptr)
    (scalars : OutcomeScalars) (bindings : BindingDescriptor) (rows : BindingRows)
    (variant : VariantBuffers) (goalMap : GoalMapBuffers)
    (entryExtent constraintExtent goalEntryExtent : Nat)
    (wellFormed : bindings.sharedLength ≤ bindings.length) (heRegion : bindings.prime = none)
    (rowsSized : rows.Sized bindings entryExtent constraintExtent)
    (variantSized : variant.Sized) (goalSized : goalMap.Sized goalEntryExtent)
    (rest : Heap L → Prop) (heap : Heap L)
    (held : (CopiedOutcomeData offset source destination nextVariant scalars bindings rows variant goalMap ∗ rest) heap) :
    outcomeImage? offset entryExtent constraintExtent goalEntryExtent heap source =
        some ⟨scalars, rows.image bindings, variant.rows, goalMap.rows⟩ ∧
      outcomeImage? offset entryExtent constraintExtent goalEntryExtent heap destination =
        some ⟨scalars, rows.image bindings, variant.rows, goalMap.rows⟩ := by
  simp only [CopiedOutcomeData, sepConj_assoc] at held
  have sourceScalar := owned_outcome_scalars offset source scalars _ heap held
  have destinationScalar : outcomeScalarsReadback? offset heap destination = some scalars := by
    apply owned_outcome_scalars offset destination scalars
      (OutcomeScalarCells offset source scalars ∗ BindingCells (source + offset.environment) bindings ∗
        BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
        variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.After ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest) heap
    cmem_exact
  have sourceBinding : bindingImage? entryExtent constraintExtent heap (source + offset.environment) =
      some (rows.image bindings) := by
    apply owned_binding_image (source + offset.environment) bindings rows entryExtent constraintExtent
      wellFormed rowsSized
      (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
        BindingCells (destination + offset.environment) bindings.retainedFork ∗
        variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗
        goalMap.After ((source + offset.answerRef) + offset.goalMap)
          ((destination + offset.answerRef) + offset.goalMap) ∗ rest) heap
    cmem_exact
  have sourceDescriptor := owned_binding_descriptor (source + offset.environment) bindings
    (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
      BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
      variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗
      goalMap.After ((source + offset.answerRef) + offset.goalMap)
        ((destination + offset.answerRef) + offset.goalMap) ∗ rest) heap (by cmem_exact)
  have destinationDescriptor := owned_binding_descriptor (destination + offset.environment) bindings.retainedFork
    (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
      BindingCells (source + offset.environment) bindings ∗ BindingPayloadCells bindings rows ∗
      variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗
      goalMap.After ((source + offset.answerRef) + offset.goalMap)
        ((destination + offset.answerRef) + offset.goalMap) ∗ rest) heap (by cmem_exact)
  have destinationBinding : bindingImage? entryExtent constraintExtent heap (destination + offset.environment) =
      some (rows.image bindings) := by
    simp only [bindingImage?, sourceDescriptor, bind, Option.bind_some] at sourceBinding
    simp only [bindingImage?, destinationDescriptor, bind, Option.bind_some]
    rw [retained_fork_image entryExtent constraintExtent heap bindings wellFormed heRegion]
    exact sourceBinding
  obtain ⟨sourceVariant, destinationVariant⟩ := variant_buffers_readback
    (source + offset.variant) nextVariant (destination + offset.variant) variant variantSized
    (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
      BindingCells (source + offset.environment) bindings ∗
      BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
      goalMap.After ((source + offset.answerRef) + offset.goalMap)
        ((destination + offset.answerRef) + offset.goalMap) ∗ rest) heap (by cmem_exact)
  obtain ⟨sourceGoal, destinationGoal⟩ := goal_map_buffers_readback
    ((source + offset.answerRef) + offset.goalMap) ((destination + offset.answerRef) + offset.goalMap)
    goalEntryExtent goalMap goalSized
    (OutcomeScalarCells offset source scalars ∗ OutcomeScalarCells offset destination scalars ∗
      BindingCells (source + offset.environment) bindings ∗
      BindingCells (destination + offset.environment) bindings.retainedFork ∗ BindingPayloadCells bindings rows ∗
      variant.After (source + offset.variant) nextVariant (destination + offset.variant) ∗ rest) heap (by cmem_exact)
  simp [outcomeImage?, sourceScalar, destinationScalar, sourceBinding, destinationBinding,
    sourceVariant, destinationVariant, sourceGoal, destinationGoal]

theorem copy_prepared_outcome_earns_whole_image (offset : OutcomeLayout) (source destination nextVariant : Ptr)
    (scalars previousScalars : OutcomeScalars) (bindings previousBindings : BindingDescriptor)
    (rows : BindingRows) (variant : VariantBuffers) (goalMap : GoalMapBuffers)
    (entryExtent constraintExtent goalEntryExtent : Nat)
    (wellFormed : bindings.sharedLength ≤ bindings.length) (heRegion : bindings.prime = none)
    (rowsSized : rows.Sized bindings entryExtent constraintExtent)
    (variantSized : variant.Sized) (goalSized : goalMap.Sized goalEntryExtent)
    (rest : Heap L → Prop) :
    CTriple (PreparedOutcomeData offset source destination nextVariant scalars previousScalars
      bindings previousBindings rows variant goalMap ∗ rest)
      (copyPreparedOutcomeData offset source destination nextVariant goalEntryExtent)
      (fun _ heap =>
        (CopiedOutcomeData offset source destination nextVariant scalars bindings rows variant goalMap ∗ rest) heap ∧
        outcomeImage? offset entryExtent constraintExtent goalEntryExtent heap source =
          some ⟨scalars, rows.image bindings, variant.rows, goalMap.rows⟩ ∧
        outcomeImage? offset entryExtent constraintExtent goalEntryExtent heap destination =
          some ⟨scalars, rows.image bindings, variant.rows, goalMap.rows⟩) := by
  apply triple_post _ (copy_prepared_outcome_data_owned offset source destination nextVariant
    scalars previousScalars bindings previousBindings rows variant goalMap goalEntryExtent variantSized goalSized rest)
  intro _ heap held
  exact ⟨held, copied_outcome_data_readback offset source destination nextVariant scalars bindings rows
    variant goalMap entryExtent constraintExtent goalEntryExtent wellFormed heRegion rowsSized variantSized
    goalSized rest heap held⟩

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Checked scalar and binding source fragments -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Source
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def outcome_kindText : String := "dst->kind = src->kind;"
def outcome_kindTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['k', 'i', 'n', 'd'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['k', 'i', 'n', 'd'], .punctuation [';']]
theorem outcome_kind_lex : lex outcome_kindText.toList = .ok outcome_kindTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_kind_parsed :
    ((lex outcome_kindText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyField "kind", []) := by
  rw [outcome_kind_lex]
  rfl

def outcome_result_formText : String := "dst->result_form = src->result_form;"
def outcome_result_formTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['r', 'e', 's', 'u', 'l', 't', '_', 'f', 'o', 'r', 'm'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['r', 'e', 's', 'u', 'l', 't', '_', 'f', 'o', 'r', 'm'], .punctuation [';']]
theorem outcome_result_form_lex : lex outcome_result_formText.toList = .ok outcome_result_formTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_result_form_parsed :
    ((lex outcome_result_formText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyField "result_form", []) := by
  rw [outcome_result_form_lex]
  rfl

def outcome_atomText : String := "dst->atom = src->atom;"
def outcome_atomTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [';']]
theorem outcome_atom_lex : lex outcome_atomText.toList = .ok outcome_atomTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_atom_parsed :
    ((lex outcome_atomText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyField "atom", []) := by
  rw [outcome_atom_lex]
  rfl

def outcome_materialized_atomText : String := "dst->materialized_atom = src->materialized_atom;"
def outcome_materialized_atomTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd', '_', 'a', 't', 'o', 'm'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd', '_', 'a', 't', 'o', 'm'], .punctuation [';']]
theorem outcome_materialized_atom_lex : lex outcome_materialized_atomText.toList = .ok outcome_materialized_atomTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_materialized_atom_parsed :
    ((lex outcome_materialized_atomText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyField "materialized_atom", []) := by
  rw [outcome_materialized_atom_lex]
  rfl

def outcome_delayedText : String := "dst->delayed = src->delayed;"
def outcome_delayedTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['d', 'e', 'l', 'a', 'y', 'e', 'd'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['d', 'e', 'l', 'a', 'y', 'e', 'd'], .punctuation [';']]
theorem outcome_delayed_lex : lex outcome_delayedText.toList = .ok outcome_delayedTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_delayed_parsed :
    ((lex outcome_delayedText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyField "delayed", []) := by
  rw [outcome_delayed_lex]
  rfl

def outcome_bankText : String := "dst->answer_ref.bank = src->answer_ref.bank;"
def outcome_bankTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['a', 'n', 's', 'w', 'e', 'r', '_', 'r', 'e', 'f'], .punctuation ['.'], .identifier ['b', 'a', 'n', 'k'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['a', 'n', 's', 'w', 'e', 'r', '_', 'r', 'e', 'f'], .punctuation ['.'], .identifier ['b', 'a', 'n', 'k'], .punctuation [';']]
theorem outcome_bank_lex : lex outcome_bankText.toList = .ok outcome_bankTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_bank_parsed :
    ((lex outcome_bankText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyAnswerField "bank", []) := by
  rw [outcome_bank_lex]
  rfl

def outcome_refText : String := "dst->answer_ref.ref = src->answer_ref.ref;"
def outcome_refTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['a', 'n', 's', 'w', 'e', 'r', '_', 'r', 'e', 'f'], .punctuation ['.'], .identifier ['r', 'e', 'f'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['a', 'n', 's', 'w', 'e', 'r', '_', 'r', 'e', 'f'], .punctuation ['.'], .identifier ['r', 'e', 'f'], .punctuation [';']]
theorem outcome_ref_lex : lex outcome_refText.toList = .ok outcome_refTokens := by
  apply lex_of_completed
  decide +kernel
theorem outcome_ref_parsed :
    ((lex outcome_refText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (copyAnswerField "ref", []) := by
  rw [outcome_ref_lex]
  rfl

def binding_shared_entries_shared_entriesText : String := "dst->shared_entries = src->shared_entries;"
def binding_shared_entries_shared_entriesTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'e', 'n', 't', 'r', 'i', 'e', 's'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'e', 'n', 't', 'r', 'i', 'e', 's'], .punctuation [';']]
theorem binding_shared_entries_shared_entries_lex : lex binding_shared_entries_shared_entriesText.toList = .ok binding_shared_entries_shared_entriesTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_shared_entries_shared_entries_parsed :
    ((lex binding_shared_entries_shared_entriesText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "shared_entries" "shared_entries", []) := by
  rw [binding_shared_entries_shared_entries_lex]
  rfl

def binding_shared_len_shared_lenText : String := "dst->shared_len = src->shared_len;"
def binding_shared_len_shared_lenTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'l', 'e', 'n'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'l', 'e', 'n'], .punctuation [';']]
theorem binding_shared_len_shared_len_lex : lex binding_shared_len_shared_lenText.toList = .ok binding_shared_len_shared_lenTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_shared_len_shared_len_parsed :
    ((lex binding_shared_len_shared_lenText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "shared_len" "shared_len", []) := by
  rw [binding_shared_len_shared_len_lex]
  rfl

def binding_shared_cap_shared_capText : String := "dst->shared_cap = src->shared_cap;"
def binding_shared_cap_shared_capTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'c', 'a', 'p'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'c', 'a', 'p'], .punctuation [';']]
theorem binding_shared_cap_shared_cap_lex : lex binding_shared_cap_shared_capText.toList = .ok binding_shared_cap_shared_capTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_shared_cap_shared_cap_parsed :
    ((lex binding_shared_cap_shared_capText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "shared_cap" "shared_cap", []) := by
  rw [binding_shared_cap_shared_cap_lex]
  rfl

def binding_len_shared_lenText : String := "dst->len = src->shared_len;"
def binding_len_shared_lenTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['s', 'h', 'a', 'r', 'e', 'd', '_', 'l', 'e', 'n'], .punctuation [';']]
theorem binding_len_shared_len_lex : lex binding_len_shared_lenText.toList = .ok binding_len_shared_lenTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_len_shared_len_parsed :
    ((lex binding_len_shared_lenText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "len" "shared_len", []) := by
  rw [binding_len_shared_len_lex]
  rfl

def binding_entries_entriesText : String := "dst->entries = src->entries;"
def binding_entries_entriesTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['e', 'n', 't', 'r', 'i', 'e', 's'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['e', 'n', 't', 'r', 'i', 'e', 's'], .punctuation [';']]
theorem binding_entries_entries_lex : lex binding_entries_entriesText.toList = .ok binding_entries_entriesTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_entries_entries_parsed :
    ((lex binding_entries_entriesText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "entries" "entries", []) := by
  rw [binding_entries_entries_lex]
  rfl

def binding_len_lenText : String := "dst->len = src->len;"
def binding_len_lenTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation [';']]
theorem binding_len_len_lex : lex binding_len_lenText.toList = .ok binding_len_lenTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_len_len_parsed :
    ((lex binding_len_lenText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "len" "len", []) := by
  rw [binding_len_len_lex]
  rfl

def binding_cap_capText : String := "dst->cap = src->cap;"
def binding_cap_capTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['c', 'a', 'p'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['c', 'a', 'p'], .punctuation [';']]
theorem binding_cap_cap_lex : lex binding_cap_capText.toList = .ok binding_cap_capTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_cap_cap_parsed :
    ((lex binding_cap_capText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "cap" "cap", []) := by
  rw [binding_cap_cap_lex]
  rfl

def binding_constraints_constraintsText : String := "dst->constraints = src->constraints;"
def binding_constraints_constraintsTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', 's'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', 's'], .punctuation [';']]
theorem binding_constraints_constraints_lex : lex binding_constraints_constraintsText.toList = .ok binding_constraints_constraintsTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_constraints_constraints_parsed :
    ((lex binding_constraints_constraintsText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "constraints" "constraints", []) := by
  rw [binding_constraints_constraints_lex]
  rfl

def binding_eq_len_eq_lenText : String := "dst->eq_len = src->eq_len;"
def binding_eq_len_eq_lenTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['e', 'q', '_', 'l', 'e', 'n'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['e', 'q', '_', 'l', 'e', 'n'], .punctuation [';']]
theorem binding_eq_len_eq_len_lex : lex binding_eq_len_eq_lenText.toList = .ok binding_eq_len_eq_lenTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_eq_len_eq_len_parsed :
    ((lex binding_eq_len_eq_lenText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "eq_len" "eq_len", []) := by
  rw [binding_eq_len_eq_len_lex]
  rfl

def binding_eq_cap_eq_capText : String := "dst->eq_cap = src->eq_cap;"
def binding_eq_cap_eq_capTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['e', 'q', '_', 'c', 'a', 'p'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['e', 'q', '_', 'c', 'a', 'p'], .punctuation [';']]
theorem binding_eq_cap_eq_cap_lex : lex binding_eq_cap_eq_capText.toList = .ok binding_eq_cap_eq_capTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_eq_cap_eq_cap_parsed :
    ((lex binding_eq_cap_eq_capText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "eq_cap" "eq_cap", []) := by
  rw [binding_eq_cap_eq_cap_lex]
  rfl

def binding_lookup_index_lookup_indexText : String := "dst->lookup_index = src->lookup_index;"
def binding_lookup_index_lookup_indexTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['l', 'o', 'o', 'k', 'u', 'p', '_', 'i', 'n', 'd', 'e', 'x'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['l', 'o', 'o', 'k', 'u', 'p', '_', 'i', 'n', 'd', 'e', 'x'], .punctuation [';']]
theorem binding_lookup_index_lookup_index_lex : lex binding_lookup_index_lookup_indexText.toList = .ok binding_lookup_index_lookup_indexTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_lookup_index_lookup_index_parsed :
    ((lex binding_lookup_index_lookup_indexText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "lookup_index" "lookup_index", []) := by
  rw [binding_lookup_index_lookup_index_lex]
  rfl

def binding_frame_index_frame_indexText : String := "dst->frame_index = src->frame_index;"
def binding_frame_index_frame_indexTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['f', 'r', 'a', 'm', 'e', '_', 'i', 'n', 'd', 'e', 'x'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['f', 'r', 'a', 'm', 'e', '_', 'i', 'n', 'd', 'e', 'x'], .punctuation [';']]
theorem binding_frame_index_frame_index_lex : lex binding_frame_index_frame_indexText.toList = .ok binding_frame_index_frame_indexTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_frame_index_frame_index_parsed :
    ((lex binding_frame_index_frame_indexText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "frame_index" "frame_index", []) := by
  rw [binding_frame_index_frame_index_lex]
  rfl

def binding_private_entry_count_private_entry_countText : String := "dst->private_entry_count = src->private_entry_count;"
def binding_private_entry_count_private_entry_countTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['p', 'r', 'i', 'v', 'a', 't', 'e', '_', 'e', 'n', 't', 'r', 'y', '_', 'c', 'o', 'u', 'n', 't'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['p', 'r', 'i', 'v', 'a', 't', 'e', '_', 'e', 'n', 't', 'r', 'y', '_', 'c', 'o', 'u', 'n', 't'], .punctuation [';']]
theorem binding_private_entry_count_private_entry_count_lex : lex binding_private_entry_count_private_entry_countText.toList = .ok binding_private_entry_count_private_entry_countTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_private_entry_count_private_entry_count_parsed :
    ((lex binding_private_entry_count_private_entry_countText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "private_entry_count" "private_entry_count", []) := by
  rw [binding_private_entry_count_private_entry_count_lex]
  rfl

def binding_private_constraint_count_private_constraint_countText : String := "dst->private_constraint_count = src->private_constraint_count;"
def binding_private_constraint_count_private_constraint_countTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['p', 'r', 'i', 'v', 'a', 't', 'e', '_', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '_', 'c', 'o', 'u', 'n', 't'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['p', 'r', 'i', 'v', 'a', 't', 'e', '_', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '_', 'c', 'o', 'u', 'n', 't'], .punctuation [';']]
theorem binding_private_constraint_count_private_constraint_count_lex : lex binding_private_constraint_count_private_constraint_countText.toList = .ok binding_private_constraint_count_private_constraint_countTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_private_constraint_count_private_constraint_count_parsed :
    ((lex binding_private_constraint_count_private_constraint_countText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "private_constraint_count" "private_constraint_count", []) := by
  rw [binding_private_constraint_count_private_constraint_count_lex]
  rfl

def binding_cycle_state_cycle_stateText : String := "dst->cycle_state = src->cycle_state;"
def binding_cycle_state_cycle_stateTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['c', 'y', 'c', 'l', 'e', '_', 's', 't', 'a', 't', 'e'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['c', 'y', 'c', 'l', 'e', '_', 's', 't', 'a', 't', 'e'], .punctuation [';']]
theorem binding_cycle_state_cycle_state_lex : lex binding_cycle_state_cycle_stateText.toList = .ok binding_cycle_state_cycle_stateTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_cycle_state_cycle_state_parsed :
    ((lex binding_cycle_state_cycle_stateText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingFieldAssignment "cycle_state" "cycle_state", []) := by
  rw [binding_cycle_state_cycle_state_lex]
  rfl

def binding_ownersText : String := "destination->owners = source->owners;"
def binding_ownersTokens : List Token := [.identifier ['d', 'e', 's', 't', 'i', 'n', 'a', 't', 'i', 'o', 'n'], .punctuation ['-', '>'], .identifier ['o', 'w', 'n', 'e', 'r', 's'], .punctuation ['='], .identifier ['s', 'o', 'u', 'r', 'c', 'e'], .punctuation ['-', '>'], .identifier ['o', 'w', 'n', 'e', 'r', 's'], .punctuation [';']]
theorem binding_owners_lex : lex binding_ownersText.toList = .ok binding_ownersTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_owners_parsed :
    ((lex binding_ownersText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (.assign (.field (.identifier "destination".toList) "owners".toList true) (.field (.identifier "source".toList) "owners".toList true), []) := by
  rw [binding_owners_lex]
  rfl

def binding_assignmentText : String := "*dst = tmp;"
def binding_assignmentTokens : List Token := [.punctuation ['*'], .identifier ['d', 's', 't'], .punctuation ['='], .identifier ['t', 'm', 'p'], .punctuation [';']]
theorem binding_assignment_lex : lex binding_assignmentText.toList = .ok binding_assignmentTokens := by
  apply lex_of_completed
  decide +kernel
theorem binding_assignment_parsed :
    ((lex binding_assignmentText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) [] tokens) =
      some (bindingAssignment, []) := by
  rw [binding_assignment_lex]
  rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Source

end

/-! ### Owner-field helper arguments -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- Actual parameter names in bindings_inherit_owners. -/
def inheritOwnersEnvironment (source destination : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "source".toList then some (.ptr (some source))
  else if name = "destination".toList then some (.ptr (some destination)) else none

def inheritOwnersBody : List CStatement := [.assign
  (.field (.identifier "destination".toList) "owners".toList true)
  (.field (.identifier "source".toList) "owners".toList true)]

/-- The native helper's selected null-destination-owner branch returns to its
caller's local environment. Refcount retention follows this store in C and
remains a distinct lifetime operation. -/
def inheritOwnersFieldCall (source destination : Ptr) : CProg CVal ReadBlock.Result := do
  let _ ← StatementBlock.executeWith { read := embeddedReader }
    embeddedAssignment bindingLayout 0 2 (inheritOwnersEnvironment source destination)
    inheritOwnersBody
  pure (.finished (.next (copyEnvironment source destination)))

theorem inherit_owners_call_uses_actual_parameters (source destination : Ptr) :
    inheritOwnersFieldCall source destination =
      bindingFieldBlock source destination ownersFieldBody := by
  rw [owners_field_block_operations]
  simp [inheritOwnersFieldCall, inheritOwnersBody, inheritOwnersEnvironment,
    embeddedReader, cursorObjects, bindingLayout,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, embeddedAssignment,
    StatementBlock.ObjectBindings.writeValue, embeddedProfile, embeddedContext,
    StatementBlock.ObjectBindings.objects, StatementBlock.ObjectBindings.place,
    StatementBlock.ObjectBindings.values, ReadExpressions.localOrLocated,
    ReadExpressions.expressionWithNames, ReadExpressions.field,
    ReadExpressions.fieldAddress, ReadExpressions.resolved, ReadExpressions.pointer,
    ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.valueKind,
    ReadExpressions.placeWithNames, ownersFieldOperations,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
  cases source
  cases destination
  rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

end

/-! ### Checked array-copy source fragments -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- Exact source syntax for the goal-map byte copy. The checked typed-cell
copy laws below the native interface still require the ABI/record-size and
whole-record memcpy contracts; parsing alone does not discharge them. -/
def goalMemcpyCall : CExpr := .call "memcpy".toList
  [.field (.identifier "dst".toList) "items".toList true,
   .field (.identifier "src".toList) "items".toList true,
   .binary .mul (.sizeOf ⟨"CettaVarMapEntry".toList, 0⟩)
     (.field (.identifier "src".toList) "len".toList true)]

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Source
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def goal_memcpyText : String := "memcpy(dst->items, src->items, sizeof(CettaVarMapEntry) * src->len);"
def goal_memcpyTokens : List Token := [.identifier ['m', 'e', 'm', 'c', 'p', 'y'], .punctuation ['('], .identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['i', 't', 'e', 'm', 's'], .punctuation [','], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['i', 't', 'e', 'm', 's'], .punctuation [','], .identifier ['s', 'i', 'z', 'e', 'o', 'f'], .punctuation ['('], .identifier ['C', 'e', 't', 't', 'a', 'V', 'a', 'r', 'M', 'a', 'p', 'E', 'n', 't', 'r', 'y'], .punctuation [')'], .punctuation ['*'], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation [')'], .punctuation [';']]
theorem goal_memcpy_lex : lex goal_memcpyText.toList = .ok goal_memcpyTokens := by
  apply lex_of_completed
  decide +kernel
theorem goal_memcpy_parsed :
    ((lex goal_memcpyText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.effect goalMemcpyCall, []) := by
  rw [goal_memcpy_lex]
  rfl

def goal_publish_lengthText : String := "dst->len = src->len;"
def goal_publish_lengthTokens : List Token := [.identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation ['='], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation [';']]
theorem goal_publish_length_lex : lex goal_publish_lengthText.toList = .ok goal_publish_lengthTokens := by
  apply lex_of_completed
  decide +kernel
theorem goal_publish_length_parsed :
    ((lex goal_publish_lengthText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (bindingFieldAssignment "len" "len", []) := by
  rw [goal_publish_length_lex]
  rfl

def exclusive_memcpyText : String := "memcpy(dst->entries, src->entries,\n                       sizeof(Binding) * exclusive);"
def exclusive_memcpyTokens : List Token := [.identifier ['m', 'e', 'm', 'c', 'p', 'y'], .punctuation ['('], .identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['e', 'n', 't', 'r', 'i', 'e', 's'], .punctuation [','], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['e', 'n', 't', 'r', 'i', 'e', 's'], .punctuation [','], .identifier ['s', 'i', 'z', 'e', 'o', 'f'], .punctuation ['('], .identifier ['B', 'i', 'n', 'd', 'i', 'n', 'g'], .punctuation [')'], .punctuation ['*'], .identifier ['e', 'x', 'c', 'l', 'u', 's', 'i', 'v', 'e'], .punctuation [')'], .punctuation [';']]
theorem exclusive_memcpy_lex : lex exclusive_memcpyText.toList = .ok exclusive_memcpyTokens := by
  apply lex_of_completed
  decide +kernel
theorem exclusive_memcpy_parsed :
    ((lex exclusive_memcpyText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.effect (.call "memcpy".toList [.field (.identifier "dst".toList) "entries".toList true, .field (.identifier "src".toList) "entries".toList true, .binary .mul (.sizeOf ⟨"Binding".toList, 0⟩) (.identifier "exclusive".toList)]), []) := by
  rw [exclusive_memcpy_lex]
  rfl

def constraints_memcpyText : String := "memcpy(dst->constraints, src->constraints,\n                   sizeof(BindingConstraint) * src->eq_len);"
def constraints_memcpyTokens : List Token := [.identifier ['m', 'e', 'm', 'c', 'p', 'y'], .punctuation ['('], .identifier ['d', 's', 't'], .punctuation ['-', '>'], .identifier ['c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', 's'], .punctuation [','], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', 's'], .punctuation [','], .identifier ['s', 'i', 'z', 'e', 'o', 'f'], .punctuation ['('], .identifier ['B', 'i', 'n', 'd', 'i', 'n', 'g', 'C', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't'], .punctuation [')'], .punctuation ['*'], .identifier ['s', 'r', 'c'], .punctuation ['-', '>'], .identifier ['e', 'q', '_', 'l', 'e', 'n'], .punctuation [')'], .punctuation [';']]
theorem constraints_memcpy_lex : lex constraints_memcpyText.toList = .ok constraints_memcpyTokens := by
  apply lex_of_completed
  decide +kernel
theorem constraints_memcpy_parsed :
    ((lex constraints_memcpyText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.effect (.call "memcpy".toList [.field (.identifier "dst".toList) "constraints".toList true, .field (.identifier "src".toList) "constraints".toList true, .binary .mul (.sizeOf ⟨"BindingConstraint".toList, 0⟩) (.field (.identifier "src".toList) "eq_len".toList true)]), []) := by
  rw [constraints_memcpy_lex]
  rfl

def variant_memcpyText : String := "memcpy(next.storage->slot_vals, src_storage->slot_vals,\n               sizeof(Atom *) * src_storage->slot_count);"
def variant_memcpyTokens : List Token := [.identifier ['m', 'e', 'm', 'c', 'p', 'y'], .punctuation ['('], .identifier ['n', 'e', 'x', 't'], .punctuation ['.'], .identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'v', 'a', 'l', 's'], .punctuation [','], .identifier ['s', 'r', 'c', '_', 's', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'v', 'a', 'l', 's'], .punctuation [','], .identifier ['s', 'i', 'z', 'e', 'o', 'f'], .punctuation ['('], .identifier ['A', 't', 'o', 'm'], .punctuation ['*'], .punctuation [')'], .punctuation ['*'], .identifier ['s', 'r', 'c', '_', 's', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'c', 'o', 'u', 'n', 't'], .punctuation [')'], .punctuation [';']]
theorem variant_memcpy_lex : lex variant_memcpyText.toList = .ok variant_memcpyTokens := by
  apply lex_of_completed
  decide +kernel
theorem variant_memcpy_parsed :
    ((lex variant_memcpyText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.effect (.call "memcpy".toList [.field (.field (.identifier "next".toList) "storage".toList false) "slot_vals".toList true, .field (.identifier "src_storage".toList) "slot_vals".toList true, .binary .mul (.sizeOf ⟨"Atom".toList, 1⟩) (.field (.identifier "src_storage".toList) "slot_count".toList true)]), []) := by
  rw [variant_memcpy_lex]
  rfl

def variant_publishText : String := "*dst = next;"
def variant_publishTokens : List Token := [.punctuation ['*'], .identifier ['d', 's', 't'], .punctuation ['='], .identifier ['n', 'e', 'x', 't'], .punctuation [';']]
theorem variant_publish_lex : lex variant_publishText.toList = .ok variant_publishTokens := by
  apply lex_of_completed
  decide +kernel
theorem variant_publish_parsed :
    ((lex variant_publishText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.assign (.unary .dereference (.identifier "dst".toList)) (.identifier "next".toList), []) := by
  rw [variant_publish_lex]
  rfl

def variant_reserve_itemsText : String := "storage->slot_vals = next;"
def variant_reserve_itemsTokens : List Token := [.identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'v', 'a', 'l', 's'], .punctuation ['='], .identifier ['n', 'e', 'x', 't'], .punctuation [';']]
theorem variant_reserve_items_lex : lex variant_reserve_itemsText.toList = .ok variant_reserve_itemsTokens := by
  apply lex_of_completed
  decide +kernel
theorem variant_reserve_items_parsed :
    ((lex variant_reserve_itemsText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.assign (.field (.identifier "storage".toList) "slot_vals".toList true) (.identifier "next".toList), []) := by
  rw [variant_reserve_items_lex]
  rfl

def variant_reserve_countText : String := "storage->slot_count = needed;"
def variant_reserve_countTokens : List Token := [.identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'c', 'o', 'u', 'n', 't'], .punctuation ['='], .identifier ['n', 'e', 'e', 'd', 'e', 'd'], .punctuation [';']]
theorem variant_reserve_count_lex : lex variant_reserve_countText.toList = .ok variant_reserve_countTokens := by
  apply lex_of_completed
  decide +kernel
theorem variant_reserve_count_parsed :
    ((lex variant_reserve_countText.toList).toOption.bind fun tokens =>
      statement? (2 * tokens.length + 4) ["Binding".toList, "BindingConstraint".toList, "CettaVarMapEntry".toList, "Atom".toList] tokens) =
      some (.assign (.field (.identifier "storage".toList) "slot_count".toList true) (.identifier "needed".toList), []) := by
  rw [variant_reserve_count_lex]
  rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Source

end

/-! ### Copy storage controls -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Controls
open Mettapedia.Machines.CMemory
open ExecutableStorage
open NativeCallFrame.Controls (result?)

def source : Ptr := ⟨1, 0⟩
def destination : Ptr := ⟨2, 0⟩
def exclusive : Ptr := ⟨3, 0⟩
def sharedPrefix : Ptr := ⟨4, 0⟩
def constraints : Ptr := ⟨5, 0⟩
def copiedArray : Ptr := ⟨6, 0⟩

def descriptor : BindingDescriptor :=
  { owners := some ⟨10, 0⟩, entries := some exclusive, length := 3, capacity := 8,
    constraints := some constraints, equalityLength := 2, equalityCapacity := 4,
    cycle := 0, bloom0 := 19, bloom1 := 70, bloom2 := 3,
    privateEntries := 1, privateConstraints := 1,
    lookupIndex := some ⟨11, 0⟩, frameIndex := some ⟨12, 0⟩,
    sharedEntries := some sharedPrefix, sharedLength := 1, sharedCapacity := 2,
    prime := none }

/-- Equal-valued rows are intentionally separate physical entries. -/
def rows : List CVal := [.u64 7, .ptr (some ⟨20, 0⟩), .u64 7, .ptr (some ⟨20, 0⟩)]
def prefixRows : List CVal := [.u64 5, .ptr (some ⟨21, 0⟩)]
def constraintRows : List CVal := [.u64 7, .u64 5, .u64 7, .u64 5]

def initial : Storage CVal :=
  [(source.block, ⟨true, descriptor.cells.map some⟩),
   (destination.block, ⟨true, BindingDescriptor.initial.cells.map some⟩),
   (exclusive.block, ⟨true, rows.map some⟩),
   (sharedPrefix.block, ⟨true, prefixRows.map some⟩),
   (constraints.block, ⟨true, constraintRows.map some⟩),
   (copiedArray.block, ⟨true, List.replicate 4 none⟩)]

def copiedImage : Option (Option BindingImage × Option BindingImage × Option BindingDescriptor) := do
  let (_, final) ← result? 180 (retainedForkFields source destination) initial
  pure (bindingImage? 2 2 (heap final) source, bindingImage? 2 2 (heap final) destination,
    bindingDescriptor? (heap final) destination)

def expectedImage : BindingImage :=
  ⟨prefixRows, rows, constraintRows, descriptor.owners, descriptor.lookupIndex,
    descriptor.frameIndex, 0, 19, 70, 3, 1, 1, none⟩

theorem nonempty_open_payload_and_all_descriptor_coordinates_survive :
    copiedImage = some (some expectedImage, some expectedImage, some descriptor) := by
  decide +kernel

theorem equal_payload_does_not_identify_allocations : source ≠ destination := by decide

def idleCapacity : BindingDescriptor :=
  { descriptor with
    length := 0, capacity := 8, equalityLength := 0, equalityCapacity := 4,
    sharedLength := 0, sharedCapacity := 2 }

def emptyRangeSnapshot : Option BindingDescriptor := do
  let storage := put initial source.block ⟨true, idleCapacity.cells.map some⟩
  let (_, final) ← result? 180 (retainedForkFields source destination) storage
  bindingDescriptor? (heap final) destination

theorem empty_ranges_do_not_claim_old_capacity :
    emptyRangeSnapshot = some
      { idleCapacity with
        entries := none, capacity := 0, constraints := none,
        equalityCapacity := 0, sharedEntries := none, sharedCapacity := 0 } := by
  decide +kernel

def allocated : BindingDescriptor := { BindingDescriptor.initial with entries := some copiedArray, capacity := 4 }

def fallbackSnapshot : Option (Option (List CVal) × Option (List CVal)) := do
  let storage := put initial destination.block ⟨true, allocated.cells.map some⟩
  let (_, final) ← result? 40 (copyBindingArray source destination 1 4) storage
  pure (segmentReadback? (heap final) (some exclusive) 4,
    segmentReadback? (heap final) (some copiedArray) 4)

theorem allocation_fallback_copies_both_equal_occurrences :
    fallbackSnapshot = some (some rows, some rows) := by decide +kernel

def brokenCapacitySnapshot : Option (Unit × Storage CVal) := do
  let storage := put initial destination.block ⟨true, allocated.cells.map some⟩
  let storage := put storage copiedArray.block ⟨true, [none]⟩
  result? 40 (copyBindingArray source destination 1 4) storage

theorem claimed_capacity_without_cells_is_refused : brokenCapacitySnapshot = none := by decide +kernel

def nullSourceSnapshot : Option (Unit × Storage CVal) := do
  let storage := put initial source.block ⟨true, { descriptor with entries := none }.cells.map some⟩
  let storage := put storage destination.block ⟨true, allocated.cells.map some⟩
  result? 40 (copyBindingArray source destination 1 4) storage

theorem nonempty_null_source_is_refused : nullSourceSnapshot = none := by decide +kernel

def uninitializedSnapshot : Option (ReadBlock.Result × Storage CVal) := do
  let storage := put initial source.block ⟨true, (descriptor.cells.map some).set 16 none⟩
  result? 180 (retainedForkFields source destination) storage

theorem uninitialized_guard_is_not_success : uninitializedSnapshot = none := by decide +kernel

def wrongScalarSnapshot : Option (ReadBlock.Result × Storage CVal) := do
  let storage := put initial source.block ⟨true, (descriptor.cells.map some).set 16 (some (.ptr none))⟩
  result? 180 (retainedForkFields source destination) storage

theorem wrong_guard_scalar_tag_is_refused : wrongScalarSnapshot = none := by decide +kernel

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Controls

end

/-! ### Composed copy controls -/

section

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Controls
open Mettapedia.Machines.CMemory
open ExecutableStorage
open NativeCallFrame.Controls (result?)

def outcomeOffsets : OutcomeLayout := ⟨0, 1, 2, 3, 4, 5, 24, 25, 0, 1, 2⟩
def sourceVariantStorage : Ptr := ⟨6, 0⟩
def nextVariant : Ptr := ⟨7, 0⟩
def nextVariantStorage : Ptr := ⟨8, 0⟩
def sourceSlots : Ptr := ⟨9, 0⟩
def destinationSlots : Ptr := ⟨10, 0⟩
def sourceGoalMap : Ptr := ⟨11, 0⟩
def destinationGoalMap : Ptr := ⟨12, 0⟩
def bindingTemporary : Ptr := ⟨13, 0⟩
def childBinding : Ptr := ⟨14, 0⟩

def outcomeScalars : OutcomeScalars :=
  ⟨1, 0, some ⟨30, 0⟩, some ⟨31, 0⟩, some ⟨32, 0⟩, some ⟨33, 0⟩, 42⟩
def repeatedSlots : List CVal := [.ptr (some ⟨35, 0⟩), .ptr (some ⟨35, 0⟩)]
def goalRows : List CVal := [.u64 99, .ptr (some ⟨36, 0⟩), .u64 99, .ptr (some ⟨36, 0⟩)]

def outcomeSourceCells : List CVal :=
  [.u32 outcomeScalars.kind, .u32 outcomeScalars.resultForm, .ptr outcomeScalars.atom,
    .ptr outcomeScalars.cached, .ptr outcomeScalars.delayed] ++ descriptor.cells ++
  [.ptr (some sourceVariantStorage), .ptr outcomeScalars.bank, .u64 outcomeScalars.reference,
    .ptr (some sourceGoalMap), .u32 2,
    .u32 4, .ptr (some ⟨37, 0⟩), .u64 8, .u64 2]

def outcomeDestinationCells : List CVal :=
  [.u32 0, .u32 1, .ptr none, .ptr none, .ptr none] ++ BindingDescriptor.initial.cells ++
  [.ptr none, .ptr none, .u64 0, .ptr (some destinationGoalMap), .u32 0,
    .u32 4, .ptr (some ⟨38, 0⟩), .u64 8, .u64 0]

def wholeStorage : Storage CVal :=
  [(source.block, ⟨true, outcomeSourceCells.map some⟩),
   (destination.block, ⟨true, outcomeDestinationCells.map some⟩),
   (exclusive.block, ⟨true, rows.map some⟩),
   (sharedPrefix.block, ⟨true, prefixRows.map some⟩),
   (constraints.block, ⟨true, constraintRows.map some⟩),
   (sourceVariantStorage.block, ⟨true, [some (.ptr (some sourceSlots)), some (.u32 2)]⟩),
   (nextVariant.block, ⟨true, [some (.ptr (some nextVariantStorage))]⟩),
   (nextVariantStorage.block, ⟨true, [some (.ptr (some destinationSlots)), some (.u32 2)]⟩),
   (sourceSlots.block, ⟨true, repeatedSlots.map some⟩),
   (destinationSlots.block, ⟨true, [none, none]⟩),
   (sourceGoalMap.block, ⟨true, goalRows.map some⟩),
   (destinationGoalMap.block, ⟨true, List.replicate 4 none⟩)]

def wholeSnapshot : Option (Option OutcomeImage × Option OutcomeImage × Option (Option Ptr) ×
    Option (List CVal)) := do
  let (_, final) ← result? 350 (copyPreparedOutcomeData outcomeOffsets source destination nextVariant 2) wholeStorage
  pure (outcomeImage? outcomeOffsets 2 2 2 (heap final) source,
    outcomeImage? outcomeOffsets 2 2 2 (heap final) destination,
    pointerCell (heap final) (destination + 24), cellsReadback? (heap final) (destination + 29) 4)

theorem whole_copy_preserves_protocol_payload_duplicates_and_physical_index_fields :
    wholeSnapshot = some
      (some ⟨outcomeScalars, expectedImage, repeatedSlots, goalRows⟩,
       some ⟨outcomeScalars, expectedImage, repeatedSlots, goalRows⟩,
       some (some nextVariantStorage), some [.u32 4, .ptr (some ⟨38, 0⟩), .u64 8, .u64 0]) := by
  decide +kernel

theorem equal_variant_payload_keeps_distinct_storage :
    sourceVariantStorage ≠ nextVariantStorage ∧ sourceSlots ≠ destinationSlots := by decide

def exhaustedVariantStorage : Storage CVal := put wholeStorage destinationSlots.block ⟨true, [none]⟩
theorem full_row_copy_refuses_insufficient_variant_cells :
    result? 350 (copyPreparedOutcomeData outcomeOffsets source destination nextVariant 2)
      exhaustedVariantStorage = none := by decide +kernel

def exhaustedGoalStorage : Storage CVal := put wholeStorage destinationGoalMap.block ⟨true, [none]⟩
theorem full_row_copy_refuses_insufficient_goal_cells :
    result? 350 (copyPreparedOutcomeData outcomeOffsets source destination nextVariant 2)
      exhaustedGoalStorage = none := by decide +kernel

def absentVariantStorage : Storage CVal :=
  put wholeStorage nextVariant.block ⟨true, [some (.ptr none)]⟩
theorem present_source_requires_actual_reserved_variant_storage :
    result? 350 (copyPreparedOutcomeData outcomeOffsets source destination nextVariant 2)
      absentVariantStorage = none := by decide +kernel

def temporaryStorage : Storage CVal :=
  put (put initial bindingTemporary.block ⟨true, descriptor.cells.map some⟩)
    childBinding.block ⟨true, BindingDescriptor.initial.cells.map some⟩
def temporarySnapshot : Option (Option BindingImage × Option BindingImage × Option BindingDescriptor) := do
  let (_, final) ← result? 300 (copyRetainedBindingsViaTemporary source bindingTemporary childBinding) temporaryStorage
  pure (bindingImage? 2 2 (heap final) source, bindingImage? 2 2 (heap final) childBinding,
    bindingDescriptor? (heap final) bindingTemporary)

theorem actual_temporary_assignment_preserves_open_binding_payload :
    temporarySnapshot = some (some expectedImage, some expectedImage, some descriptor) := by decide +kernel

def fallbackFinished : Option (Option BindingDescriptor × Option (List CVal)) := do
  let storage := put initial destination.block ⟨true, allocated.cells.map some⟩
  let (_, final) ← result? 70 (copyReservedExclusive source destination 2) storage
  pure (bindingDescriptor? (heap final) destination,
    segmentReadback? (heap final) (some copiedArray) 4)

theorem actual_fallback_publishes_total_length_after_exclusive_copy :
    fallbackFinished = some (some { allocated with length := 3 }, some rows) := by decide +kernel

def emptyVariants : Storage CVal :=
  [(source.block, ⟨true, [some (.ptr (some sourceVariantStorage))]⟩),
   (nextVariant.block, ⟨true, [some (.ptr (some nextVariantStorage))]⟩),
   (destination.block, ⟨true, [some (.ptr none)]⟩),
   (sourceVariantStorage.block, ⟨true, [some (.ptr (some sourceSlots)), some (.u32 0)]⟩),
   (nextVariantStorage.block, ⟨true, [some (.ptr none), some (.u32 0)]⟩)]
def emptyVariantSnapshot : Option (Option (List CVal) × Option (List CVal) × Option (Option Ptr)) := do
  let (_, final) ← result? 40 (copyReservedVariant source nextVariant destination) emptyVariants
  pure (variantReadback? (heap final) source, variantReadback? (heap final) destination,
    pointerCell (heap final) destination)

theorem allocated_empty_variant_retains_storage_distinction_without_reading_slots :
    emptyVariantSnapshot = some (some [], some [], some (some nextVariantStorage)) := by decide +kernel

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeCallFrame.Copy.Controls

end

end

section

set_option autoImplicit false
set_option maxRecDepth 14000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

structure Offsets where
  kind : Nat
  atom : Nat
  variant : Nat
  storage : Nat
  slotCount : Nat

def layout (offset : Offsets) : ReadExpressions.Layout := fun name =>
  if name = "kind".toList then some ⟨offset.kind, .word⟩
  else if name = "atom".toList then some ⟨offset.atom, .pointer⟩
  else if name = "variant".toList then some ⟨offset.variant, .embedded⟩
  else if name = "storage".toList then some ⟨offset.storage, .pointer⟩
  else if name = "slot_count".toList then some ⟨offset.slotCount, .word⟩
  else none

def storageExpression : CExpr :=
  .conditional (.identifier "instance".toList)
    (.field (.identifier "instance".toList) "storage".toList true) .null

def storage (offset : Offsets) (handle : Option Ptr) : CProg CVal CVal :=
  ReadExpressions.expression (layout offset)
    (fun name => if name = "instance".toList then some (.ptr handle) else none)
    storageExpression

def presentExpression : CExpr :=
  .binary .and (.identifier "storage".toList)
    (.binary .gt (.field (.identifier "storage".toList) "slot_count".toList true)
      (.decimal 0))

def present (offset : Offsets) (handle : Option Ptr) : CProg CVal CVal := do
  let result ← storage offset handle
  ReadExpressions.expression (layout offset)
    (fun name => if name = "storage".toList then some result else none)
    presentExpression

def calls (offset : Offsets) (external : ReadExpressions.Calls) : ReadExpressions.Calls :=
  fun name arguments =>
    if name = "variant_instance_present".toList then match arguments with
      | [.ptr handle] => present offset handle
      | _ => CProg.undefined
    else external name arguments

def environment (arena out : Option Ptr) : ReadExpressions.Environment := fun name =>
  if name = "out".toList then some (.ptr out)
  else if name = "a".toList then some (.ptr arena)
  else if name = "CETTA_OUTCOME_ANSWER_REF".toList then some (.u32 1)
  else none

def variantOnlyBody : List CStatement := [
  .branch (.unary .not (.identifier "out".toList)) [.return (some .null)] [],
  .branch (.binary .and
    (.binary .eq (.field (.identifier "out".toList) "kind".toList true)
      (.identifier "CETTA_OUTCOME_ANSWER_REF".toList))
    (.unary .not (.call "outcome_inflate_answer_ref".toList
      [.identifier "a".toList, .identifier "out".toList]))) [.return (some .null)] [],
  .branch (.unary .not (.call "variant_instance_present".toList
    [.unary .address (.field (.identifier "out".toList) "variant".toList true)]))
    [.return (some (.field (.identifier "out".toList) "atom".toList true))] [],
  .return (some (.call "variant_instance_materialize".toList
    [.identifier "a".toList, .field (.identifier "out".toList) "atom".toList true,
      .unary .address (.field (.identifier "out".toList) "variant".toList true)]))]

def materializerPiece0 : String × List Token :=
  ("{\n    if (!out)\n        return NULL;\n    if (out->kind == ", [.punctuation ['{'], .identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['o', 'u', 't'], .punctuation [')'], .identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';'], .identifier ['i', 'f'], .punctuation ['('], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['k', 'i', 'n', 'd'], .punctuation ['=', '=']])
theorem materializerPiece0_lex : materializerPiece0.1.toList.foldl step initial =
    completed materializerPiece0.2 := by decide +kernel

def materializerPiece1 : String × List Token :=
  ("CETTA_OUTCOME_ANSWER_REF && !outcome_inflate_answer_ref(a, ", [.identifier ['C', 'E', 'T', 'T', 'A', '_', 'O', 'U', 'T', 'C', 'O', 'M', 'E', '_', 'A', 'N', 'S', 'W', 'E', 'R', '_', 'R', 'E', 'F'], .punctuation ['&', '&'], .punctuation ['!'], .identifier ['o', 'u', 't', 'c', 'o', 'm', 'e', '_', 'i', 'n', 'f', 'l', 'a', 't', 'e', '_', 'a', 'n', 's', 'w', 'e', 'r', '_', 'r', 'e', 'f'], .punctuation ['('], .identifier ['a'], .punctuation [',']])
theorem materializerPiece1_lex : materializerPiece1.1.toList.foldl step initial =
    completed materializerPiece1.2 := by decide +kernel

def materializerPiece2 : String × List Token :=
  ("out))\n        return NULL;\n    if ", [.identifier ['o', 'u', 't'], .punctuation [')'], .punctuation [')'], .identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';'], .identifier ['i', 'f']])
theorem materializerPiece2_lex : materializerPiece2.1.toList.foldl step initial =
    completed materializerPiece2.2 := by decide +kernel

def materializerPiece3 : String × List Token :=
  ("(!variant_instance_present(&out->variant))\n        return ", [.punctuation ['('], .punctuation ['!'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'p', 'r', 'e', 's', 'e', 'n', 't'], .punctuation ['('], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't'], .punctuation [')'], .punctuation [')'], .identifier ['r', 'e', 't', 'u', 'r', 'n']])
theorem materializerPiece3_lex : materializerPiece3.1.toList.foldl step initial =
    completed materializerPiece3.2 := by decide +kernel

def materializerPiece4 : String × List Token :=
  ("out->atom;\n    return variant_instance_materialize(a, out->atom, ", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [';'], .identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'm', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [',']])
theorem materializerPiece4_lex : materializerPiece4.1.toList.foldl step initial =
    completed materializerPiece4.2 := by decide +kernel

def materializerPiece5 : String × List Token :=
  ("&out->variant);\n}", [.punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't'], .punctuation [')'], .punctuation [';'], .punctuation ['}']])
theorem materializerPiece5_lex : materializerPiece5.1.toList.foldl step initial =
    completed materializerPiece5.2 := by decide +kernel

def materializerPieces : List (String × List Token) := [materializerPiece0, materializerPiece1, materializerPiece2, materializerPiece3, materializerPiece4, materializerPiece5]

def variantOnlySource : String := String.join (materializerPieces.map Prod.fst)
def variantOnlyTokens : List Token := materializerPieces.flatMap Prod.snd

theorem variantOnly_lex : lex variantOnlySource.toList = .ok variantOnlyTokens := by
  apply lex_completed_string_pieces
  simp only [materializerPieces, List.forall_cons]
  exact ⟨materializerPiece0_lex, materializerPiece1_lex, materializerPiece2_lex, materializerPiece3_lex, materializerPiece4_lex, materializerPiece5_lex, trivial⟩

theorem variantOnly_parsed :
    blockText? [] variantOnlySource.toList = some variantOnlyBody :=
  block_text_of_parts [] _ variantOnlyTokens _ variantOnly_lex (by rfl)

def variantOnly (offset : Offsets) (external : ReadExpressions.Calls)
    (arena out : Option Ptr) : CProg CVal ReadBlock.Result :=
  let read : StatementBlock.Reader := fun fields names expression =>
    ReadExpressions.expressionWithNames (fun name => ReadExpressions.resolved (names name))
      (calls offset external) fields expression
  StatementBlock.executeWith { read := read } (StatementBlock.fieldAssignment read)
    (layout offset) 0 5 (environment arena out) variantOnlyBody

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def InlineUnfactored (offset : Offsets) (out : Ptr) (atom : Option Ptr) : Heap L → Prop :=
  PointsTo (out + offset.kind) (.u32 0) ∗
  PointsTo (out + offset.atom) (.ptr atom) ∗
  PointsTo ((out + offset.variant) + offset.storage) (.ptr none)


end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 300000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev readExpression (offset : Offsets) (external : ReadExpressions.Calls)
    (arena out : Option Ptr) : CExpr → CProg CVal CVal :=
  ReadExpressions.expressionWith external (layout offset) (environment arena out)

def nullGuard : CExpr := .unary .not (.identifier "out".toList)
def kindField : CExpr := .field (.identifier "out".toList) "kind".toList true
def atomField : CExpr := .field (.identifier "out".toList) "atom".toList true
def kindCondition : CExpr := .binary .eq kindField (.identifier "CETTA_OUTCOME_ANSWER_REF".toList)
def inflationGuard : CExpr := .binary .and kindCondition
  (.unary .not (.call "outcome_inflate_answer_ref".toList
    [.identifier "a".toList, .identifier "out".toList]))
def variantAddress : CExpr := .unary .address
  (.field (.identifier "out".toList) "variant".toList true)
def variantCall : CExpr := .call "variant_instance_present".toList [variantAddress]
def variantGuard : CExpr := .unary .not variantCall

theorem read_null_guard_uses_pointer_comparison (offset : Offsets)
    (external : ReadExpressions.Calls) (arena out : Option Ptr) :
    readExpression offset external arena out nullGuard = (do
      let isNull ← CProg.ptrEq out none
      pure (.bool isNull)) := by
  simp [readExpression, nullGuard, ReadExpressions.expressionWith_equation,
    environment, ReadExpressions.resolved, ReadExpressions.truth,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem read_kind_field_uses_storage (offset : Offsets)
    (external : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr) :
    readExpression offset external arena (some out) kindField = (do
      let kind ← CProg.loadU32 (out + offset.kind)
      pure (.u32 kind)) := by
  simp only [readExpression, kindField, ReadExpressions.expressionWith_equation]
  simp only [environment, ↓reduceIte, ReadExpressions.resolved, Prog.bind_eq,
    Prog.pure_eq, Prog.ret_bind]
  exact ReadExpressions.word_field_uses_actual_offset (layout offset) out
    "kind".toList offset.kind (by simp [layout])

theorem read_atom_field_uses_storage (offset : Offsets)
    (external : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr) :
    readExpression offset external arena (some out) atomField = (do
      let atom ← CProg.loadPtr (out + offset.atom)
      pure (.ptr atom)) := by
  simp only [readExpression, atomField, ReadExpressions.expressionWith_equation]
  simp only [environment, ↓reduceIte, ReadExpressions.resolved, Prog.bind_eq,
    Prog.pure_eq, Prog.ret_bind]
  exact ReadExpressions.pointer_field_uses_actual_offset (layout offset) out
    "atom".toList offset.atom (by simp [layout])

theorem read_kind_condition_uses_loaded_kind (offset : Offsets)
    (external : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr) :
    readExpression offset external arena (some out) kindCondition = (do
      let kind ← CProg.loadU32 (out + offset.kind)
      ReadExpressions.binary .eq (.u32 kind) (.u32 1)) := by
  change ReadExpressions.expressionWith _ _ _ (.binary .eq kindField _) = _
  rw [ReadExpressions.expressionWith_equation]
  change (readExpression offset external arena (some out) kindField >>= fun first =>
    readExpression offset external arena (some out)
      (.identifier "CETTA_OUTCOME_ANSWER_REF".toList) >>= fun second =>
      ReadExpressions.binary .eq first second) = _
  rw [read_kind_field_uses_storage]
  have answerRef : readExpression offset external arena (some out)
      (.identifier "CETTA_OUTCOME_ANSWER_REF".toList) = pure (.u32 1) := by
    simp [readExpression, ReadExpressions.expressionWith_equation, environment,
      ReadExpressions.resolved]
  rw [answerRef]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem read_variant_address_uses_offset (offset : Offsets)
    (external : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr) :
    readExpression offset external arena (some out) variantAddress =
      pure (.ptr (some (out + offset.variant))) := by
  simp [readExpression, variantAddress, ReadExpressions.expressionWith_equation,
    environment, ReadExpressions.resolved, ReadExpressions.fieldAddress,
    ReadExpressions.pointer, layout, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem read_variant_call_applies_service (offset : Offsets)
    (helpers : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr) :
    readExpression offset helpers arena (some out) variantCall =
      helpers "variant_instance_present".toList [.ptr (some (out + offset.variant))] := by
  change ReadExpressions.expressionWith _ _ _ (.call _ [variantAddress]) = _
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  rw [ReadExpressions.argumentsWith_equation]
  dsimp only []
  change (readExpression offset helpers arena (some out) variantAddress >>= fun value =>
    ReadExpressions.argumentsWith helpers (layout offset)
      (environment arena (some out)) [] >>= fun remaining =>
      helpers "variant_instance_present".toList (value :: remaining)) = _
  rw [read_variant_address_uses_offset, ReadExpressions.argumentsWith_equation]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem read_variant_call_uses_helper (offset : Offsets)
    (external : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr) :
    readExpression offset (calls offset external) arena (some out) variantCall =
      present offset (some (out + offset.variant)) := by
  rw [read_variant_call_applies_service]
  simp only [calls, ↓reduceIte]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

private theorem bind_exact {α β : Type} (pre : Heap L → Prop)
    (program : CProg CVal α) (next : α → CProg CVal β) (value : α)
    (post : β → Heap L → Prop)
    (first : CTriple pre program (fun actual heap => actual = value ∧ pre heap))
    (second : CTriple pre (next value) post) :
    CTriple pre (program >>= next) post := by
  apply triple_bind _ first
  intro actual heap held
  rcases held with ⟨rfl, held⟩
  exact second heap held

private theorem pure_exact {α : Type} (pre : Heap L → Prop) (value : α) :
    CTriple pre (pure value : CProg CVal α) (fun actual heap => actual = value ∧ pre heap) := by
  refine triple_pre _ (P := fun heap => value = value ∧ pre heap) ?_
    (triple_ret _ value (fun actual heap => actual = value ∧ pre heap))
  intro heap held
  exact ⟨rfl, held⟩

def OwnedInline (offset : Offsets) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) : Heap L → Prop :=
  fun heap => WellFormed heap ∧ (InlineUnfactored offset out atom ∗ rest) heap

theorem null_guard_false_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (readExpression offset external arena (some out) nullGuard)
      (fun actual heap => actual = .bool false ∧ OwnedInline offset out atom rest heap) := by
  rw [read_null_guard_uses_pointer_comparison]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_step
  exact ⟨wf, held⟩

theorem kind_condition_false_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (readExpression offset external arena (some out) kindCondition)
      (fun actual heap => actual = .bool false ∧ OwnedInline offset out atom rest heap) := by
  rw [read_kind_condition_uses_loaded_kind]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_step
  cmem_norm [ReadExpressions.binary, ReadExpressions.equal, ReadExpressions.scalar,
    ReadExpressions.resolved, ScalarRead.equal?]
  exact ⟨rfl, wf, held⟩


theorem inflation_guard_false_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (readExpression offset external arena (some out) inflationGuard)
      (fun actual heap => actual = .bool false ∧ OwnedInline offset out atom rest heap) := by
  unfold inflationGuard readExpression
  rw [ReadExpressions.expressionWith_equation]
  apply bind_exact _ _ _ (.bool false) _
    (kind_condition_false_owned offset external arena out atom rest)
  simpa only [ReadExpressions.truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, if_false] using
    (pure_exact (OwnedInline offset out atom rest) (CVal.bool false))

theorem storage_null_owned (offset : Offsets) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest) (storage offset (some (out + offset.variant)))
      (fun actual heap => actual = .ptr none ∧ OwnedInline offset out atom rest heap) := by
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_norm [storage, storageExpression, ReadExpressions.expression,
    ReadExpressions.expressionWith_equation, ReadExpressions.resolved, ReadExpressions.truth]
  cmem_step
  cmem_norm [ReadExpressions.field, ReadExpressions.pointer, layout]
  simp only [show "storage".toList ≠ "kind".toList from by decide,
    show "storage".toList ≠ "atom".toList from by decide,
    show "storage".toList ≠ "variant".toList from by decide, ↓reduceIte]
  cmem_step
  exact ⟨wf, held⟩

theorem present_false_from_null_storage (offset : Offsets) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest) (present offset (some (out + offset.variant)))
      (fun actual heap => actual = .bool false ∧ OwnedInline offset out atom rest heap) := by
  unfold present
  apply bind_exact _ _ _ (.ptr none) _ (storage_null_owned offset out atom rest)
  change CTriple _ (ReadExpressions.expressionWith _ _ _ (.binary .and _ _)) _
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  have first : ReadExpressions.expressionWith ReadExpressions.noCalls (layout offset)
      (fun name => if name = "storage".toList then some (.ptr none) else none)
      (.identifier "storage".toList) = pure (.ptr none) := rfl
  rw [first]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  cmem_start heap held
  cmem_norm [ReadExpressions.truth]
  cmem_step
  exact held

theorem variant_guard_true_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (readExpression offset (calls offset external) arena (some out) variantGuard)
      (fun actual heap => actual = .bool true ∧ OwnedInline offset out atom rest heap) := by
  change CTriple _ (ReadExpressions.expressionWith _ _ _ (.unary .not variantCall)) _
  rw [ReadExpressions.expressionWith_equation]
  change CTriple _ (readExpression offset (calls offset external) arena (some out) variantCall >>= fun value =>
    ReadExpressions.truth value >>= fun selected => pure (CVal.bool (!selected))) _
  rw [read_variant_call_uses_helper]
  apply bind_exact _ _ _ (.bool false) _ (present_false_from_null_storage offset out atom rest)
  simpa only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Bool.not_false] using
    (pure_exact (OwnedInline offset out atom rest) (CVal.bool true))

theorem atom_read_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (readExpression offset external arena (some out) atomField)
      (fun actual heap => actual = .ptr atom ∧ OwnedInline offset out atom rest heap) := by
  rw [read_atom_field_uses_storage]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_step
  exact ⟨wf, held⟩

private theorem execute_false_guard (services : StatementBlock.Services)
    (assign : StatementBlock.Assignment) (fields : ReadExpressions.Layout)
    (loopFuel fuel : Nat) (names : ReadExpressions.Environment)
    (condition : CExpr) (yes tail : List CStatement) (pre : Heap L → Prop)
    (post : ReadBlock.Result → Heap L → Prop)
    (guard : CTriple pre (services.read fields names condition)
      (fun actual heap => actual = .bool false ∧ pre heap))
    (continuation : CTriple pre
      (StatementBlock.executeWith services assign fields loopFuel fuel names tail) post) :
    CTriple pre
      (StatementBlock.executeWith services assign fields loopFuel (fuel + 1) names
        (.branch condition yes [] :: tail)) post := by
  rw [StatementBlock.executeWith_equation]
  apply bind_exact _ _ _ (.bool false) _ guard
  simp only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Bool.false_eq_true, if_false]
  rw [StatementBlock.executeWith_equation]
  simpa only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume] using continuation

private theorem execute_true_return (services : StatementBlock.Services)
    (assign : StatementBlock.Assignment) (fields : ReadExpressions.Layout)
    (loopFuel fuel : Nat) (names : ReadExpressions.Environment)
    (condition expression : CExpr) (no tail : List CStatement)
    (pre : Heap L → Prop) (value : CVal)
    (guard : CTriple pre (services.read fields names condition)
      (fun actual heap => actual = .bool true ∧ pre heap))
    (read : CTriple pre (services.read fields names expression)
      (fun actual heap => actual = value ∧ pre heap)) :
    CTriple pre
      (StatementBlock.executeWith services assign fields loopFuel (fuel + 2) names
        (.branch condition [.return (some expression)] no :: tail))
      (fun actual heap => actual = .finished (.returned names (some value)) ∧ pre heap) := by
  rw [StatementBlock.executeWith_equation]
  apply bind_exact _ _ _ (.bool true) _ guard
  simp only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, ↓reduceIte]
  rw [StatementBlock.executeWith_equation]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, ReadBlock.resume]
  apply bind_exact _ _ _ value _ read
  exact pure_exact pre (ReadBlock.Result.finished (.returned names (some value)))

/-- Actual selected branches of the parsed C body. Neither the inflation nor
variant-materialization callback needs a contract on this storage-null path:
the arbitrary callback service is never reached by the proof. All owned fields
and the unrelated framed heap are retained. Pointer validity is derived from
the live containing block, rather than replaced by a pure Boolean test. -/
theorem variantOnly_storage_null_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (variantOnly offset external arena (some out))
      (fun actual heap => actual = .finished (.returned (environment arena (some out))
        (some (.ptr atom))) ∧ OwnedInline offset out atom rest heap) := by
  unfold variantOnly
  apply execute_false_guard _ _ _ _ _ _ nullGuard _ _ _ _
    (null_guard_false_owned offset (calls offset external) arena out atom rest)
  apply execute_false_guard _ _ _ _ _ _ inflationGuard _ _ _ _
    (inflation_guard_false_owned offset (calls offset external) arena out atom rest)
  exact execute_true_return _ _ _ _ 1 _ variantGuard atomField _ _ _ (.ptr atom)
    (variant_guard_true_owned offset external arena out atom rest)
    (atom_read_owned offset (calls offset external) arena out atom rest)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 700000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def storageBody : List CStatement := [.return (some storageExpression)]
def presentBody : List CStatement := [
  .declare ⟨"VariantInstanceStorage".toList, 1⟩ "storage".toList
    (.call "variant_instance_storage".toList [.identifier "instance".toList]),
  .return (some presentExpression)]

def storagePiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem storagePiece0_lex : storagePiece0.1.toList.foldl step initial = completed storagePiece0.2 := by decide +kernel
def storagePiece1 : String × List Token := ("    return instance ? instance->storage : NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['i', 'n', 's', 't', 'a', 'n', 'c', 'e'], .punctuation ['?'], .identifier ['i', 'n', 's', 't', 'a', 'n', 'c', 'e'], .punctuation ['-', '>'], .identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation [':'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])
theorem storagePiece1_lex : storagePiece1.1.toList.foldl step initial = completed storagePiece1.2 := by decide +kernel
def storagePiece2 : String × List Token := ("}", [.punctuation ['}']])
theorem storagePiece2_lex : storagePiece2.1.toList.foldl step initial = completed storagePiece2.2 := by decide +kernel
def storagePieces : List (String × List Token) := [storagePiece0, storagePiece1, storagePiece2]
def storageSource : String := String.join (storagePieces.map Prod.fst)
def storageTokens : List Token := storagePieces.flatMap Prod.snd
theorem storage_lex : lex storageSource.toList = .ok storageTokens := by
  apply lex_completed_string_pieces
  simp only [storagePieces, List.forall_cons]
  exact ⟨storagePiece0_lex, storagePiece1_lex, storagePiece2_lex, trivial⟩
theorem storage_parsed : blockText? [] storageSource.toList = some storageBody :=
  block_text_of_parts [] _ storageTokens _ storage_lex (by rfl)

def presentPiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem presentPiece0_lex : presentPiece0.1.toList.foldl step initial = completed presentPiece0.2 := by decide +kernel
def presentPiece1 : String × List Token := ("    VariantInstanceStorage *storage = variant_instance_storage(instance);\n", [.identifier ['V', 'a', 'r', 'i', 'a', 'n', 't', 'I', 'n', 's', 't', 'a', 'n', 'c', 'e', 'S', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['*'], .identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['='], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 's', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['('], .identifier ['i', 'n', 's', 't', 'a', 'n', 'c', 'e'], .punctuation [')'], .punctuation [';']])
theorem presentPiece1_lex : presentPiece1.1.toList.foldl step initial = completed presentPiece1.2 := by decide +kernel
def presentPiece2 : String × List Token := ("    return storage && storage->slot_count > 0;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['&', '&'], .identifier ['s', 't', 'o', 'r', 'a', 'g', 'e'], .punctuation ['-', '>'], .identifier ['s', 'l', 'o', 't', '_', 'c', 'o', 'u', 'n', 't'], .punctuation ['>'], .number ['0'], .punctuation [';']])
theorem presentPiece2_lex : presentPiece2.1.toList.foldl step initial = completed presentPiece2.2 := by decide +kernel
def presentPiece3 : String × List Token := ("}", [.punctuation ['}']])
theorem presentPiece3_lex : presentPiece3.1.toList.foldl step initial = completed presentPiece3.2 := by decide +kernel
def presentPieces : List (String × List Token) := [presentPiece0, presentPiece1, presentPiece2, presentPiece3]
def presentSource : String := String.join (presentPieces.map Prod.fst)
def presentTokens : List Token := presentPieces.flatMap Prod.snd
theorem present_lex : lex presentSource.toList = .ok presentTokens := by
  apply lex_completed_string_pieces
  simp only [presentPieces, List.forall_cons]
  exact ⟨presentPiece0_lex, presentPiece1_lex, presentPiece2_lex, presentPiece3_lex, trivial⟩
theorem present_parsed : blockText? ["VariantInstanceStorage".toList] presentSource.toList = some presentBody :=
  block_text_of_parts ["VariantInstanceStorage".toList] _ presentTokens _ present_lex (by rfl)


def helperEnvironment (handle : Option Ptr) : ReadExpressions.Environment := fun name =>
  if name = "instance".toList then some (.ptr handle) else none

/-- Function-reply observation rejects exhaustion and non-return control. -/
def helperReply (program : CProg CVal ReadBlock.Result) : CProg CVal CVal := do
  let result ← program
  ReadExpressions.resolved result.returnedValue?

def storageProgram (offset : Offsets) (handle : Option Ptr) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith {} (StatementBlock.fieldAssignment ReadExpressions.expression)
    (layout offset) 0 1 (helperEnvironment handle) storageBody

theorem storage_program_reply (offset : Offsets) (handle : Option Ptr) :
    helperReply (storageProgram offset handle) = storage offset handle := by
  unfold helperReply storageProgram storageBody
  rw [StatementBlock.executeWith_equation]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    ReadBlock.Result.returnedValue?, ReadExpressions.resolved, Prog.bind_ret]
  rfl

def storageCalls (offset : Offsets) : ReadExpressions.Calls := fun name arguments =>
  if name = "variant_instance_storage".toList then match arguments with
    | [.ptr handle] => helperReply (storageProgram offset handle)
    | _ => CProg.undefined
  else CProg.undefined

def presentProgram (offset : Offsets) (handle : Option Ptr) : CProg CVal ReadBlock.Result :=
  let read : StatementBlock.Reader := ReadExpressions.expressionWith (storageCalls offset)
  StatementBlock.executeWith { read := read, initialValue := StatementBlock.objectInitialValue }
    (StatementBlock.fieldAssignment read) (layout offset) 0 2
    (helperEnvironment handle) presentBody


theorem storage_call_uses_actual_function_reply (offset : Offsets) (handle : Option Ptr) :
    ReadExpressions.expressionWith (storageCalls offset) (layout offset) (helperEnvironment handle)
      (.call "variant_instance_storage".toList [.identifier "instance".toList]) =
      storage offset handle := by
  simp [ReadExpressions.expressionWith_equation, ReadExpressions.argumentsWith_equation,
    helperEnvironment, ReadExpressions.resolved, storageCalls, storage_program_reply,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem present_expression_null_short_circuit (offset : Offsets)
    (helpers : ReadExpressions.Calls) (names : ReadExpressions.Environment)
    (selected : names "storage".toList = some (.ptr none)) (pre : Heap L → Prop) :
    CTriple pre (ReadExpressions.expressionWith helpers (layout offset) names presentExpression)
      (fun result heap => result = .bool false ∧ pre heap) := by
  unfold presentExpression
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  have first : ReadExpressions.expressionWith helpers (layout offset) names
      (.identifier "storage".toList) = pure (.ptr none) := by
    simp only [ReadExpressions.expressionWith_equation, selected, ReadExpressions.resolved]
  rw [first]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  cmem_start heap held
  cmem_norm [ReadExpressions.truth]
  cmem_step
  exact held

theorem present_program_storage_null_owned (offset : Offsets) (out : Ptr)
    (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (presentProgram offset (some (out + offset.variant)))
      (fun result heap => result = .finished (.returned
        (helperEnvironment (some (out + offset.variant))) (some (.bool false))) ∧
        OwnedInline offset out atom rest heap) := by
  unfold presentProgram presentBody
  rw [StatementBlock.executeWith_equation]
  dsimp only []
  rw [storage_call_uses_actual_function_reply]
  apply bind_exact _ _ _ (CVal.ptr none) _ (storage_null_owned offset out atom rest)
  simp only [StatementBlock.objectInitialValue, Nat.zero_lt_succ, ↓reduceIte,
    ReadExpressions.pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [StatementBlock.executeWith_equation]
  dsimp only []
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply bind_exact _ _ _ (CVal.bool false) _
    (present_expression_null_short_circuit offset (storageCalls offset)
      (Function.update (helperEnvironment (some (out + offset.variant))) "storage".toList
        (some (.ptr none))) (by simp) (OwnedInline offset out atom rest))
  simpa only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    ReadBlock.returned_declaration_restores_scope] using
      (pure_exact (OwnedInline offset out atom rest)
        (ReadBlock.Result.finished (.returned
          (helperEnvironment (some (out + offset.variant))) (some (.bool false)))))


/-- The dispatch service executes the parsed helper body before reading its
explicit function reply. Unrecognized external helpers keep their supplied
semantics; the admitted fast path does not invoke them. -/
def sourceCalls (offset : Offsets) (external : ReadExpressions.Calls) : ReadExpressions.Calls :=
  fun name arguments =>
    if name = "variant_instance_present".toList then match arguments with
      | [.ptr handle] => helperReply (presentProgram offset handle)
      | _ => CProg.undefined
    else external name arguments

def variantOnlyFromHelpers (offset : Offsets) (external : ReadExpressions.Calls)
    (arena out : Option Ptr) : CProg CVal ReadBlock.Result :=
  let read : StatementBlock.Reader := ReadExpressions.expressionWith (sourceCalls offset external)
  StatementBlock.executeWith { read := read } (StatementBlock.fieldAssignment read)
    (layout offset) 0 5 (environment arena out) variantOnlyBody

theorem present_source_reply_storage_null_owned (offset : Offsets) (out : Ptr)
    (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (helperReply (presentProgram offset (some (out + offset.variant))))
      (fun result heap => result = .bool false ∧ OwnedInline offset out atom rest heap) := by
  unfold helperReply
  apply bind_exact _ _ _
    (ReadBlock.Result.finished (.returned (helperEnvironment (some (out + offset.variant)))
      (some (.bool false)))) _ (present_program_storage_null_owned offset out atom rest)
  exact pure_exact (OwnedInline offset out atom rest) (CVal.bool false)

theorem source_variant_guard_true_owned (offset : Offsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (readExpression offset (sourceCalls offset external) arena (some out) variantGuard)
      (fun actual heap => actual = .bool true ∧ OwnedInline offset out atom rest heap) := by
  change CTriple _ (ReadExpressions.expressionWith _ _ _ (.unary .not variantCall)) _
  rw [ReadExpressions.expressionWith_equation]
  change CTriple _
    (readExpression offset (sourceCalls offset external) arena (some out) variantCall >>= fun value =>
      ReadExpressions.truth value >>= fun selected => pure (CVal.bool (!selected))) _
  rw [read_variant_call_applies_service]
  simp only [sourceCalls, ↓reduceIte]
  apply bind_exact _ _ _ (CVal.bool false) _
    (present_source_reply_storage_null_owned offset out atom rest)
  simpa only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Bool.not_false] using
    (pure_exact (OwnedInline offset out atom rest) (CVal.bool true))

/-- The actual parsed variant-only body, with its parsed storage/presence
helper bodies composed through explicit returned-value observation. No result
or noninterference premise is supplied for either helper. Native layout and
valid owned storage remain the declared representation boundary. -/
theorem variant_only_source_helpers_storage_null_owned (offset : Offsets)
    (external : ReadExpressions.Calls) (arena : Option Ptr) (out : Ptr)
    (atom : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedInline offset out atom rest)
      (variantOnlyFromHelpers offset external arena (some out))
      (fun actual heap => actual = .finished (.returned (environment arena (some out))
        (some (.ptr atom))) ∧ OwnedInline offset out atom rest heap) := by
  unfold variantOnlyFromHelpers
  apply execute_false_guard _ _ _ _ _ _ nullGuard _ _ _ _
    (null_guard_false_owned offset (sourceCalls offset external) arena out atom rest)
  apply execute_false_guard _ _ _ _ _ _ inflationGuard _ _ _ _
    (inflation_guard_false_owned offset (sourceCalls offset external) arena out atom rest)
  exact execute_true_return _ _ _ _ 1 _ variantGuard atomField _ _ _ (.ptr atom)
    (source_variant_guard_true_owned offset external arena out atom rest)
    (atom_read_owned offset (sourceCalls offset external) arena out atom rest)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Controls

open Mettapedia.Machines.CMemory
open ExecutableStorage
open ProductiveBlocks

def offsets : Offsets := ⟨0, 1, 2, 0, 0⟩
def outcome : Ptr := ⟨1, 0⟩
def atom : Ptr := ⟨2, 0⟩
def untouched : Ptr := ⟨3, 0⟩
def initial : Storage CVal :=
  [(outcome.block, ⟨true, [some (.u32 0), some (.ptr (some atom)), some (.ptr none)]⟩),
   (atom.block, ⟨true, [some (.u64 77)]⟩),
   (untouched.block, ⟨true, [some (.u32 45), none]⟩)]

def snapshot (fuel : Nat) (pointer : Option Ptr) (storage : Storage CVal) :
    Option (Option CVal × Storage CVal × Nat) :=
  let result := machine.run fuel (State.mk
    (variantOnlyFromHelpers offsets ReadExpressions.noCalls none pointer) storage [])
  match result.2 with
  | .finished (.returned final) => some (final.answer.returnedValue?, final.storage, result.1.length)
  | _ => none

theorem inline_storage_null_returns_actual_atom_and_preserves_heap :
    snapshot 32 (some outcome) initial = some (some (.ptr (some atom)), initial, 6) := by
  decide +kernel

theorem null_outcome_returns_null_without_reading_fields :
    snapshot 32 none initial = some (some (.ptr none), initial, 1) := by decide +kernel

def wrongKind : Storage CVal := put initial outcome.block
  ⟨true, [some (.ptr none), some (.ptr (some atom)), some (.ptr none)]⟩
theorem wrong_kind_tag_is_refused : snapshot 32 (some outcome) wrongKind = none := by decide +kernel

def answerReference : Storage CVal := put initial outcome.block
  ⟨true, [some (.u32 1), some (.ptr (some atom)), some (.ptr none)]⟩
theorem answer_reference_needs_its_real_inflation_component :
    snapshot 32 (some outcome) answerReference = none := by decide +kernel

def missingAtom : Storage CVal := put initial outcome.block
  ⟨true, [some (.u32 0), none, some (.ptr none)]⟩
theorem missing_atom_cell_is_refused : snapshot 32 (some outcome) missingAtom = none := by decide +kernel

def deadOutcome : Storage CVal := put initial outcome.block
  ⟨false, [some (.u32 0), some (.ptr (some atom)), some (.ptr none)]⟩
theorem dead_outcome_pointer_is_refused : snapshot 32 (some outcome) deadOutcome = none := by decide +kernel

theorem exhausted_scheduler_is_not_a_return : snapshot 0 (some outcome) initial = none := by decide +kernel


theorem exhausted_scheduler_retains_actual_control_and_storage :
    machine.run 0 (State.mk
      (variantOnlyFromHelpers offsets ReadExpressions.noCalls none (some outcome)) initial []) =
    ([], .exhausted (State.mk
      (variantOnlyFromHelpers offsets ReadExpressions.noCalls none (some outcome)) initial [])) := rfl

def faultStorage (storage : Storage CVal) : Option (Storage CVal) :=
  match (machine.run 32 (State.mk
    (variantOnlyFromHelpers offsets ReadExpressions.noCalls none (some outcome)) storage [])).2 with
  | .finished (.fault saved) => some saved.storage
  | _ => none

theorem invalid_kind_finishes_as_a_retained_fault : faultStorage wrongKind = some wrongKind := by
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Controls

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def ident (name : String) : CExpr := .identifier name.toList
def fld (owner fieldName : String) : CExpr := .field (ident owner) fieldName.toList true
def invoke (name : String) (args : List CExpr) : CExpr := .call name.toList args
def address (value : CExpr) : CExpr := .unary .address value

def frameValueCountBody : List CStatement := [
  .declarePointeeConst ⟨"BindingsFrameIndex".toList, 1⟩ "index".toList
    (.conditional (ident "bindings") (fld "bindings" "frame_index") .null),
  .return (some (.conditional (ident "index") (fld "index" "bound_value_count") (.unsignedInteger 0)))]

def hasBoundValuesBody : List CStatement := [
  .return (some (.binary .and (ident "bindings")
    (.binary .or (.binary .ne (fld "bindings" "len") (.unsignedInteger 0))
      (.binary .ne (invoke "bindings_frame_value_count" [ident "bindings"]) (.unsignedInteger 0)))))]

def variantArm : List CStatement := [
  .effect (invoke "cetta_runtime_stats_inc" [ident "CETTA_RUNTIME_COUNTER_OUTCOME_VARIANT_SLOT_MATERIALIZE"]),
  .branch (.unary .not (invoke "bindings_logically_empty" [address (fld "out" "env")]))
    [.effect (invoke "variant_instance_init" [address (ident "compacted")]),
     .branch (.unary .not (invoke "variant_instance_sink_env"
       [ident "a", address (ident "compacted"), address (fld "out" "variant"), address (fld "out" "env")]))
       [.return (some .null)] [],
     .assign (ident "materialized") (invoke "variant_instance_materialize"
       [ident "a", ident "materialized", address (ident "compacted")]),
     .effect (invoke "variant_instance_free" [address (ident "compacted")])]
    [.assign (ident "materialized") (invoke "variant_instance_materialize"
      [ident "a", ident "materialized", address (fld "out" "variant")])]]

def ordinaryTail : List CStatement := [
  .branch nullGuard [.return (some .null)] [],
  .branch inflationGuard [.return (some .null)] [],
  .branch (fld "out" "materialized_atom") [.return (some (fld "out" "materialized_atom"))] [],
  .assign (ident "materialized") atomField,
  .branch variantCall variantArm
    [.branch (invoke "bindings_has_bound_values" [address (fld "out" "env")])
      [.assign (ident "materialized") (invoke "eval_env_apply"
        [address (fld "out" "env"), ident "a", ident "materialized"])] []],
  .assign (fld "out" "materialized_atom") (ident "materialized"),
  .return (some (ident "materialized"))]

def fullBody : List CStatement :=
  .declareUninitialized ⟨"Atom".toList, 1⟩ "materialized".toList ::
  .declareUninitialized ⟨"VariantInstance".toList, 0⟩ "compacted".toList :: ordinaryTail

def frameCountPiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem frameCountPiece0_lex : frameCountPiece0.1.toList.foldl step initial = completed frameCountPiece0.2 := by decide +kernel
def frameCountPiece1 : String × List Token := ("    const BindingsFrameIndex *index = bindings\n", [.identifier ['c', 'o', 'n', 's', 't'], .identifier ['B', 'i', 'n', 'd', 'i', 'n', 'g', 's', 'F', 'r', 'a', 'm', 'e', 'I', 'n', 'd', 'e', 'x'], .punctuation ['*'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['='], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's']])
theorem frameCountPiece1_lex : frameCountPiece1.1.toList.foldl step initial = completed frameCountPiece1.2 := by decide +kernel
def frameCountPiece2 : String × List Token := ("        ? bindings->frame_index : NULL;\n", [.punctuation ['?'], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation ['-', '>'], .identifier ['f', 'r', 'a', 'm', 'e', '_', 'i', 'n', 'd', 'e', 'x'], .punctuation [':'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])
theorem frameCountPiece2_lex : frameCountPiece2.1.toList.foldl step initial = completed frameCountPiece2.2 := by decide +kernel
def frameCountPiece3 : String × List Token := ("    return index ? index->bound_value_count : 0u;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['?'], .identifier ['i', 'n', 'd', 'e', 'x'], .punctuation ['-', '>'], .identifier ['b', 'o', 'u', 'n', 'd', '_', 'v', 'a', 'l', 'u', 'e', '_', 'c', 'o', 'u', 'n', 't'], .punctuation [':'], .number ['0', 'u'], .punctuation [';']])
theorem frameCountPiece3_lex : frameCountPiece3.1.toList.foldl step initial = completed frameCountPiece3.2 := by decide +kernel
def frameCountPiece4 : String × List Token := ("}", [.punctuation ['}']])
theorem frameCountPiece4_lex : frameCountPiece4.1.toList.foldl step initial = completed frameCountPiece4.2 := by decide +kernel
def frameCountPieces : List (String × List Token) := [frameCountPiece0, frameCountPiece1, frameCountPiece2, frameCountPiece3, frameCountPiece4]
def frameCountSource : String := String.join (frameCountPieces.map Prod.fst)
def frameCountTokens : List Token := frameCountPieces.flatMap Prod.snd
theorem frameCount_lex : lex frameCountSource.toList = .ok frameCountTokens := by
  apply lex_completed_string_pieces
  simp only [frameCountPieces, List.forall_cons]
  exact ⟨frameCountPiece0_lex, frameCountPiece1_lex, frameCountPiece2_lex, frameCountPiece3_lex, frameCountPiece4_lex, trivial⟩
theorem frameCount_parsed : blockText? ["BindingsFrameIndex".toList] frameCountSource.toList = some frameValueCountBody :=
  block_text_of_parts ["BindingsFrameIndex".toList] _ frameCountTokens _ frameCount_lex (by rfl)

def hasValuesPiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem hasValuesPiece0_lex : hasValuesPiece0.1.toList.foldl step initial = completed hasValuesPiece0.2 := by decide +kernel
def hasValuesPiece1 : String × List Token := ("    return bindings &&\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation ['&', '&']])
theorem hasValuesPiece1_lex : hasValuesPiece1.1.toList.foldl step initial = completed hasValuesPiece1.2 := by decide +kernel
def hasValuesPiece2 : String × List Token := ("        (bindings->len != 0u ||\n", [.punctuation ['('], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation ['-', '>'], .identifier ['l', 'e', 'n'], .punctuation ['!', '='], .number ['0', 'u'], .punctuation ['|', '|']])
theorem hasValuesPiece2_lex : hasValuesPiece2.1.toList.foldl step initial = completed hasValuesPiece2.2 := by decide +kernel
def hasValuesPiece3 : String × List Token := ("         bindings_frame_value_count(bindings) != 0u);\n", [.identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'f', 'r', 'a', 'm', 'e', '_', 'v', 'a', 'l', 'u', 'e', '_', 'c', 'o', 'u', 'n', 't'], .punctuation ['('], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's'], .punctuation [')'], .punctuation ['!', '='], .number ['0', 'u'], .punctuation [')'], .punctuation [';']])
theorem hasValuesPiece3_lex : hasValuesPiece3.1.toList.foldl step initial = completed hasValuesPiece3.2 := by decide +kernel
def hasValuesPiece4 : String × List Token := ("}", [.punctuation ['}']])
theorem hasValuesPiece4_lex : hasValuesPiece4.1.toList.foldl step initial = completed hasValuesPiece4.2 := by decide +kernel
def hasValuesPieces : List (String × List Token) := [hasValuesPiece0, hasValuesPiece1, hasValuesPiece2, hasValuesPiece3, hasValuesPiece4]
def hasValuesSource : String := String.join (hasValuesPieces.map Prod.fst)
def hasValuesTokens : List Token := hasValuesPieces.flatMap Prod.snd
theorem hasValues_lex : lex hasValuesSource.toList = .ok hasValuesTokens := by
  apply lex_completed_string_pieces
  simp only [hasValuesPieces, List.forall_cons]
  exact ⟨hasValuesPiece0_lex, hasValuesPiece1_lex, hasValuesPiece2_lex, hasValuesPiece3_lex, hasValuesPiece4_lex, trivial⟩
theorem hasValues_parsed : blockText? [] hasValuesSource.toList = some hasBoundValuesBody :=
  block_text_of_parts [] _ hasValuesTokens _ hasValues_lex (by rfl)

def fullPiece0 : String × List Token := ("{\n", [.punctuation ['{']])
theorem fullPiece0_lex : fullPiece0.1.toList.foldl step initial = completed fullPiece0.2 := by decide +kernel
def fullPiece1 : String × List Token := ("    Atom *materialized;\n", [.identifier ['A', 't', 'o', 'm'], .punctuation ['*'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation [';']])
theorem fullPiece1_lex : fullPiece1.1.toList.foldl step initial = completed fullPiece1.2 := by decide +kernel
def fullPiece2 : String × List Token := ("    VariantInstance compacted;\n", [.identifier ['V', 'a', 'r', 'i', 'a', 'n', 't', 'I', 'n', 's', 't', 'a', 'n', 'c', 'e'], .identifier ['c', 'o', 'm', 'p', 'a', 'c', 't', 'e', 'd'], .punctuation [';']])
theorem fullPiece2_lex : fullPiece2.1.toList.foldl step initial = completed fullPiece2.2 := by decide +kernel
def fullPiece3 : String × List Token := ("    if (!out)\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['o', 'u', 't'], .punctuation [')']])
theorem fullPiece3_lex : fullPiece3.1.toList.foldl step initial = completed fullPiece3.2 := by decide +kernel
def fullPiece4 : String × List Token := ("        return NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])
theorem fullPiece4_lex : fullPiece4.1.toList.foldl step initial = completed fullPiece4.2 := by decide +kernel
def fullPiece5 : String × List Token := ("    if (out->kind == CETTA_OUTCOME_ANSWER_REF && !outcome_inflate_answer_ref(a, out))\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['k', 'i', 'n', 'd'], .punctuation ['=', '='], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'O', 'U', 'T', 'C', 'O', 'M', 'E', '_', 'A', 'N', 'S', 'W', 'E', 'R', '_', 'R', 'E', 'F'], .punctuation ['&', '&'], .punctuation ['!'], .identifier ['o', 'u', 't', 'c', 'o', 'm', 'e', '_', 'i', 'n', 'f', 'l', 'a', 't', 'e', '_', 'a', 'n', 's', 'w', 'e', 'r', '_', 'r', 'e', 'f'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['o', 'u', 't'], .punctuation [')'], .punctuation [')']])
theorem fullPiece5_lex : fullPiece5.1.toList.foldl step initial = completed fullPiece5.2 := by decide +kernel
def fullPiece6 : String × List Token := ("        return NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])
theorem fullPiece6_lex : fullPiece6.1.toList.foldl step initial = completed fullPiece6.2 := by decide +kernel
def fullPiece7 : String × List Token := ("    if (out->materialized_atom)\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd', '_', 'a', 't', 'o', 'm'], .punctuation [')']])
theorem fullPiece7_lex : fullPiece7.1.toList.foldl step initial = completed fullPiece7.2 := by decide +kernel
def fullPiece8 : String × List Token := ("        return out->materialized_atom;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd', '_', 'a', 't', 'o', 'm'], .punctuation [';']])
theorem fullPiece8_lex : fullPiece8.1.toList.foldl step initial = completed fullPiece8.2 := by decide +kernel
def fullPiece9 : String × List Token := ("    materialized = out->atom;\n", [.identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation ['='], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['a', 't', 'o', 'm'], .punctuation [';']])
theorem fullPiece9_lex : fullPiece9.1.toList.foldl step initial = completed fullPiece9.2 := by decide +kernel
def fullPiece10 : String × List Token := ("    if (variant_instance_present(&out->variant)) {\n", [.identifier ['i', 'f'], .punctuation ['('], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'p', 'r', 'e', 's', 'e', 'n', 't'], .punctuation ['('], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't'], .punctuation [')'], .punctuation [')'], .punctuation ['{']])
theorem fullPiece10_lex : fullPiece10.1.toList.foldl step initial = completed fullPiece10.2 := by decide +kernel
def fullPiece11 : String × List Token := ("        cetta_runtime_stats_inc(CETTA_RUNTIME_COUNTER_OUTCOME_VARIANT_SLOT_MATERIALIZE);\n", [.identifier ['c', 'e', 't', 't', 'a', '_', 'r', 'u', 'n', 't', 'i', 'm', 'e', '_', 's', 't', 'a', 't', 's', '_', 'i', 'n', 'c'], .punctuation ['('], .identifier ['C', 'E', 'T', 'T', 'A', '_', 'R', 'U', 'N', 'T', 'I', 'M', 'E', '_', 'C', 'O', 'U', 'N', 'T', 'E', 'R', '_', 'O', 'U', 'T', 'C', 'O', 'M', 'E', '_', 'V', 'A', 'R', 'I', 'A', 'N', 'T', '_', 'S', 'L', 'O', 'T', '_', 'M', 'A', 'T', 'E', 'R', 'I', 'A', 'L', 'I', 'Z', 'E'], .punctuation [')'], .punctuation [';']])
theorem fullPiece11_lex : fullPiece11.1.toList.foldl step initial = completed fullPiece11.2 := by decide +kernel
def fullPiece12 : String × List Token := ("        if (!bindings_logically_empty(&out->env)) {\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'l', 'o', 'g', 'i', 'c', 'a', 'l', 'l', 'y', '_', 'e', 'm', 'p', 't', 'y'], .punctuation ['('], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [')'], .punctuation [')'], .punctuation ['{']])
theorem fullPiece12_lex : fullPiece12.1.toList.foldl step initial = completed fullPiece12.2 := by decide +kernel
def fullPiece13 : String × List Token := ("            variant_instance_init(&compacted);\n", [.identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'i', 'n', 'i', 't'], .punctuation ['('], .punctuation ['&'], .identifier ['c', 'o', 'm', 'p', 'a', 'c', 't', 'e', 'd'], .punctuation [')'], .punctuation [';']])
theorem fullPiece13_lex : fullPiece13.1.toList.foldl step initial = completed fullPiece13.2 := by decide +kernel
def fullPiece14 : String × List Token := ("            if (!variant_instance_sink_env(a, &compacted, &out->variant, &out->env))\n", [.identifier ['i', 'f'], .punctuation ['('], .punctuation ['!'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 's', 'i', 'n', 'k', '_', 'e', 'n', 'v'], .punctuation ['('], .identifier ['a'], .punctuation [','], .punctuation ['&'], .identifier ['c', 'o', 'm', 'p', 'a', 'c', 't', 'e', 'd'], .punctuation [','], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't'], .punctuation [','], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [')'], .punctuation [')']])
theorem fullPiece14_lex : fullPiece14.1.toList.foldl step initial = completed fullPiece14.2 := by decide +kernel
def fullPiece15 : String × List Token := ("                return NULL;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['N', 'U', 'L', 'L'], .punctuation [';']])
theorem fullPiece15_lex : fullPiece15.1.toList.foldl step initial = completed fullPiece15.2 := by decide +kernel
def fullPiece16 : String × List Token := ("            materialized = variant_instance_materialize(a, materialized, &compacted);\n", [.identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation ['='], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'm', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation [','], .punctuation ['&'], .identifier ['c', 'o', 'm', 'p', 'a', 'c', 't', 'e', 'd'], .punctuation [')'], .punctuation [';']])
theorem fullPiece16_lex : fullPiece16.1.toList.foldl step initial = completed fullPiece16.2 := by decide +kernel
def fullPiece17 : String × List Token := ("            variant_instance_free(&compacted);\n", [.identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'f', 'r', 'e', 'e'], .punctuation ['('], .punctuation ['&'], .identifier ['c', 'o', 'm', 'p', 'a', 'c', 't', 'e', 'd'], .punctuation [')'], .punctuation [';']])
theorem fullPiece17_lex : fullPiece17.1.toList.foldl step initial = completed fullPiece17.2 := by decide +kernel
def fullPiece18 : String × List Token := ("        } else {\n", [.punctuation ['}'], .identifier ['e', 'l', 's', 'e'], .punctuation ['{']])
theorem fullPiece18_lex : fullPiece18.1.toList.foldl step initial = completed fullPiece18.2 := by decide +kernel
def fullPiece19 : String × List Token := ("            materialized = variant_instance_materialize(a, materialized, &out->variant);\n", [.identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation ['='], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't', '_', 'i', 'n', 's', 't', 'a', 'n', 'c', 'e', '_', 'm', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e'], .punctuation ['('], .identifier ['a'], .punctuation [','], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation [','], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['v', 'a', 'r', 'i', 'a', 'n', 't'], .punctuation [')'], .punctuation [';']])
theorem fullPiece19_lex : fullPiece19.1.toList.foldl step initial = completed fullPiece19.2 := by decide +kernel
def fullPiece20 : String × List Token := ("        }\n", [.punctuation ['}']])
theorem fullPiece20_lex : fullPiece20.1.toList.foldl step initial = completed fullPiece20.2 := by decide +kernel
def fullPiece21 : String × List Token := ("    } else if (bindings_has_bound_values(&out->env)) {\n", [.punctuation ['}'], .identifier ['e', 'l', 's', 'e'], .identifier ['i', 'f'], .punctuation ['('], .identifier ['b', 'i', 'n', 'd', 'i', 'n', 'g', 's', '_', 'h', 'a', 's', '_', 'b', 'o', 'u', 'n', 'd', '_', 'v', 'a', 'l', 'u', 'e', 's'], .punctuation ['('], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [')'], .punctuation [')'], .punctuation ['{']])
theorem fullPiece21_lex : fullPiece21.1.toList.foldl step initial = completed fullPiece21.2 := by decide +kernel
def fullPiece22 : String × List Token := ("        /* Reading an outcome is a consumer too: in Prime the store reaches\n         * the result through the environment action, which never enters a\n         * quotation in value position (rule 5). */\n", [])
theorem fullPiece22_lex : fullPiece22.1.toList.foldl step initial = completed fullPiece22.2 := by decide +kernel
def fullPiece23 : String × List Token := ("        materialized = eval_env_apply(&out->env, a, materialized);\n", [.identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation ['='], .identifier ['e', 'v', 'a', 'l', '_', 'e', 'n', 'v', '_', 'a', 'p', 'p', 'l', 'y'], .punctuation ['('], .punctuation ['&'], .identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['e', 'n', 'v'], .punctuation [','], .identifier ['a'], .punctuation [','], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation [')'], .punctuation [';']])
theorem fullPiece23_lex : fullPiece23.1.toList.foldl step initial = completed fullPiece23.2 := by decide +kernel
def fullPiece24 : String × List Token := ("    }\n", [.punctuation ['}']])
theorem fullPiece24_lex : fullPiece24.1.toList.foldl step initial = completed fullPiece24.2 := by decide +kernel
def fullPiece25 : String × List Token := ("    out->materialized_atom = materialized;\n", [.identifier ['o', 'u', 't'], .punctuation ['-', '>'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd', '_', 'a', 't', 'o', 'm'], .punctuation ['='], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation [';']])
theorem fullPiece25_lex : fullPiece25.1.toList.foldl step initial = completed fullPiece25.2 := by decide +kernel
def fullPiece26 : String × List Token := ("    return materialized;\n", [.identifier ['r', 'e', 't', 'u', 'r', 'n'], .identifier ['m', 'a', 't', 'e', 'r', 'i', 'a', 'l', 'i', 'z', 'e', 'd'], .punctuation [';']])
theorem fullPiece26_lex : fullPiece26.1.toList.foldl step initial = completed fullPiece26.2 := by decide +kernel
def fullPiece27 : String × List Token := ("}", [.punctuation ['}']])
theorem fullPiece27_lex : fullPiece27.1.toList.foldl step initial = completed fullPiece27.2 := by decide +kernel
def fullPieces : List (String × List Token) := [fullPiece0, fullPiece1, fullPiece2, fullPiece3, fullPiece4, fullPiece5, fullPiece6, fullPiece7, fullPiece8, fullPiece9, fullPiece10, fullPiece11, fullPiece12, fullPiece13, fullPiece14, fullPiece15, fullPiece16, fullPiece17, fullPiece18, fullPiece19, fullPiece20, fullPiece21, fullPiece22, fullPiece23, fullPiece24, fullPiece25, fullPiece26, fullPiece27]
def fullSource : String := String.join (fullPieces.map Prod.fst)
def fullTokens : List Token := fullPieces.flatMap Prod.snd
theorem full_lex : lex fullSource.toList = .ok fullTokens := by
  apply lex_completed_string_pieces
  simp only [fullPieces, List.forall_cons]
  exact ⟨fullPiece0_lex, fullPiece1_lex, fullPiece2_lex, fullPiece3_lex, fullPiece4_lex, fullPiece5_lex, fullPiece6_lex, fullPiece7_lex, fullPiece8_lex, fullPiece9_lex, fullPiece10_lex, fullPiece11_lex, fullPiece12_lex, fullPiece13_lex, fullPiece14_lex, fullPiece15_lex, fullPiece16_lex, fullPiece17_lex, fullPiece18_lex, fullPiece19_lex, fullPiece20_lex, fullPiece21_lex, fullPiece22_lex, fullPiece23_lex, fullPiece24_lex, fullPiece25_lex, fullPiece26_lex, fullPiece27_lex, trivial⟩
theorem full_parsed : blockText? ["Atom".toList, "VariantInstance".toList] fullSource.toList = some fullBody :=
  block_text_of_parts ["Atom".toList, "VariantInstance".toList] _ fullTokens _ full_lex (by rfl)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 900000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

structure FullOffsets extends Offsets where
  cache : Nat
  environment : Nat
  length : Nat
  frameIndex : Nat
  boundValueCount : Nat

def fullLayout (offset : FullOffsets) : ReadExpressions.Layout := fun name =>
  if name = "materialized_atom".toList then some ⟨offset.cache, .pointer⟩
  else if name = "env".toList then some ⟨offset.environment, .embedded⟩
  else if name = "len".toList then some ⟨offset.length, .word⟩
  else if name = "frame_index".toList then some ⟨offset.frameIndex, .pointer⟩
  else if name = "bound_value_count".toList then some ⟨offset.boundValueCount, .word64⟩
  else layout offset.toOffsets name

def bindingNames (bindings : Option Ptr) : ReadExpressions.Environment := fun name =>
  if name = "bindings".toList then some (.ptr bindings) else none

def frameCountProgram (offset : FullOffsets) (bindings : Option Ptr) :
    CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith
    { pointeeConst := true, initialValue := StatementBlock.objectInitialValue }
    (StatementBlock.fieldAssignment ReadExpressions.expression) (fullLayout offset) 0 2
    (bindingNames bindings) frameValueCountBody

/-- This profile explicitly represents native size_t by uint64_t. Its return
conversion is executed after the actual function reply; the zero-valued
unsigned-int literal is not silently given a different runtime tag. -/
def frameCountReply (offset : FullOffsets) (bindings : Option Ptr) : CProg CVal CVal := do
  let value ← helperReply (frameCountProgram offset bindings)
  StatementBlock.objectInitialValue ⟨"uint64_t".toList, 0⟩ value

def bindingCalls (offset : FullOffsets) : ReadExpressions.Calls := fun name arguments =>
  if name = "bindings_frame_value_count".toList then match arguments with
    | [.ptr bindings] => frameCountReply offset bindings
    | _ => CProg.undefined
  else CProg.undefined

def hasValuesProgram (offset : FullOffsets) (bindings : Option Ptr) : CProg CVal ReadBlock.Result :=
  let read : StatementBlock.Reader := ReadExpressions.expressionWith (bindingCalls offset)
  StatementBlock.executeWith { read := read } (StatementBlock.fieldAssignment read)
    (fullLayout offset) 0 1 (bindingNames bindings) hasBoundValuesBody

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def NoValueCells (offset : FullOffsets) (bindings : Ptr) : Heap L → Prop :=
  PointsTo (bindings + offset.length) (.u32 0) ∗
  PointsTo (bindings + offset.frameIndex) (.ptr none)

def OwnedNoValues (offset : FullOffsets) (bindings : Ptr) (rest : Heap L → Prop) : Heap L → Prop :=
  fun heap => WellFormed heap ∧ (NoValueCells offset bindings ∗ rest) heap

theorem frame_initializer_null_owned (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest)
      (ReadExpressions.expression (fullLayout offset) (bindingNames (some bindings))
        (.conditional (ident "bindings") (fld "bindings" "frame_index") .null))
      (fun actual heap => actual = .ptr none ∧ OwnedNoValues offset bindings rest heap) := by
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold NoValueCells at held
  cmem_norm [ReadExpressions.expression, ReadExpressions.expressionWith_equation,
    ident, fld, bindingNames, ReadExpressions.resolved, ReadExpressions.truth]
  cmem_step
  cmem_norm [ReadExpressions.field, ReadExpressions.pointer, fullLayout]
  simp only [show "frame_index".toList ≠ "materialized_atom".toList from by decide,
    show "frame_index".toList ≠ "env".toList from by decide,
    show "frame_index".toList ≠ "len".toList from by decide, ↓reduceIte]
  cmem_step
  exact ⟨wf, held⟩

theorem null_index_count_short_circuit (offset : FullOffsets)
    (names : ReadExpressions.Environment) (known : names "index".toList = some (.ptr none))
    (pre : Heap L → Prop) :
    CTriple pre (ReadExpressions.expression (fullLayout offset) names
      (.conditional (ident "index") (fld "index" "bound_value_count") (.unsignedInteger 0)))
      (fun actual heap => actual = .u32 0 ∧ pre heap) := by
  unfold ReadExpressions.expression
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  have hfirst : ReadExpressions.expressionWith ReadExpressions.noCalls (fullLayout offset) names
      (ident "index") = pure (.ptr none) := by
    simp only [ident, ReadExpressions.expressionWith_equation, known, ReadExpressions.resolved]
  rw [hfirst]
  cmem_start heap held
  cmem_norm [ReadExpressions.truth]
  cmem_step
  cmem_norm [ReadExpressions.expressionWith_equation, ReadExpressions.resolved,
    show (0 : Nat) < 2 ^ 32 from by decide]
  exact ⟨rfl, held⟩

theorem frame_count_program_no_values (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest) (frameCountProgram offset (some bindings))
      (fun actual heap => actual = .finished (.returned (bindingNames (some bindings))
        (some (.u32 0))) ∧ OwnedNoValues offset bindings rest heap) := by
  unfold frameCountProgram frameValueCountBody
  rw [StatementBlock.executeWith_equation]
  dsimp only []
  simp only [and_self, ↓reduceIte]
  apply bind_exact _ _ _ (CVal.ptr none) _ (frame_initializer_null_owned offset bindings rest)
  simp only [StatementBlock.objectInitialValue, Nat.zero_lt_succ, ↓reduceIte,
    ReadExpressions.pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [StatementBlock.executeWith_equation]
  dsimp only []
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply bind_exact _ _ _ (CVal.u32 0) _
    (null_index_count_short_circuit offset
      (Function.update (bindingNames (some bindings)) "index".toList (some (.ptr none)))
      (by simp) (OwnedNoValues offset bindings rest))
  simpa only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    ReadBlock.returned_declaration_restores_scope] using
      (pure_exact (OwnedNoValues offset bindings rest)
        (ReadBlock.Result.finished (.returned (bindingNames (some bindings)) (some (.u32 0)))))

theorem frame_count_reply_no_values (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest) (frameCountReply offset (some bindings))
      (fun actual heap => actual = .u64 0 ∧ OwnedNoValues offset bindings rest heap) := by
  unfold frameCountReply helperReply
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply bind_exact _ _ _
    (ReadBlock.Result.finished (.returned (bindingNames (some bindings)) (some (.u32 0)))) _
    (frame_count_program_no_values offset bindings rest)
  exact pure_exact (OwnedNoValues offset bindings rest) (CVal.u64 0)

def lengthCondition : CExpr := .binary .ne (fld "bindings" "len") (.unsignedInteger 0)
def countCall : CExpr := invoke "bindings_frame_value_count" [ident "bindings"]
def countCondition : CExpr := .binary .ne countCall (.unsignedInteger 0)
def boundValuesExpression : CExpr :=
  .binary .and (ident "bindings") (.binary .or lengthCondition countCondition)

theorem binding_pointer_true_owned (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest) (ReadExpressions.truth (.ptr (some bindings)))
      (fun actual heap => actual = true ∧ OwnedNoValues offset bindings rest heap) := by
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold NoValueCells at held
  cmem_norm [ReadExpressions.truth]
  cmem_step
  exact ⟨wf, held⟩

theorem length_condition_false_owned (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest)
      (ReadExpressions.expressionWith (bindingCalls offset) (fullLayout offset)
        (bindingNames (some bindings)) lengthCondition)
      (fun actual heap => actual = .bool false ∧ OwnedNoValues offset bindings rest heap) := by
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold NoValueCells at held
  cmem_norm [lengthCondition, fld, ident, ReadExpressions.expressionWith_equation,
    bindingNames, ReadExpressions.resolved, ReadExpressions.field,
    ReadExpressions.pointer, fullLayout]
  simp only [show "len".toList ≠ "materialized_atom".toList from by decide,
    show "len".toList ≠ "env".toList from by decide, ↓reduceIte]
  cmem_step
  cmem_norm [ReadExpressions.expressionWith_equation,
    show (0 : Nat) < 2 ^ 32 from by decide, ReadExpressions.binary, ReadExpressions.equal, ReadExpressions.scalar,
    ReadExpressions.resolved, ScalarRead.equal?]
  exact ⟨rfl, wf, held⟩

theorem count_call_enters_actual_helper (offset : FullOffsets) (bindings : Option Ptr) :
    ReadExpressions.expressionWith (bindingCalls offset) (fullLayout offset)
      (bindingNames bindings) countCall = frameCountReply offset bindings := by
  simp [countCall, invoke, ident, ReadExpressions.expressionWith_equation,
    ReadExpressions.argumentsWith_equation, bindingNames, ReadExpressions.resolved,
    bindingCalls, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem count_condition_false_owned (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest)
      (ReadExpressions.expressionWith (bindingCalls offset) (fullLayout offset)
        (bindingNames (some bindings)) countCondition)
      (fun actual heap => actual = .bool false ∧ OwnedNoValues offset bindings rest heap) := by
  unfold countCondition
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  rw [count_call_enters_actual_helper]
  apply bind_exact _ _ _ (CVal.u64 0) _ (frame_count_reply_no_values offset bindings rest)
  simpa [ReadExpressions.expressionWith_equation, ReadExpressions.binary,
    ReadExpressions.equal, ReadExpressions.scalar, ReadExpressions.resolved,
    ScalarRead.equal?, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind] using
    (pure_exact (OwnedNoValues offset bindings rest) (CVal.bool false))

theorem bound_values_expression_false_owned (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest)
      (ReadExpressions.expressionWith (bindingCalls offset) (fullLayout offset)
        (bindingNames (some bindings)) boundValuesExpression)
      (fun actual heap => actual = .bool false ∧ OwnedNoValues offset bindings rest heap) := by
  unfold boundValuesExpression
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  have pointerRead : ReadExpressions.expressionWith (bindingCalls offset) (fullLayout offset)
      (bindingNames (some bindings)) (ident "bindings") = pure (.ptr (some bindings)) := by
    simp [ReadExpressions.expressionWith_equation, ident, bindingNames, ReadExpressions.resolved]
  rw [pointerRead]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  apply bind_exact _ _ _ true _ (binding_pointer_true_owned offset bindings rest)
  simp only [↓reduceIte]
  rw [ReadExpressions.expressionWith_equation]
  dsimp only []
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply bind_exact _ _ _ (CVal.bool false) _ (length_condition_false_owned offset bindings rest)
  simp only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Bool.false_eq_true, ↓reduceIte, Prog.bind_assoc]
  apply bind_exact _ _ _ (CVal.bool false) _ (count_condition_false_owned offset bindings rest)
  exact pure_exact (OwnedNoValues offset bindings rest) (CVal.bool false)

theorem has_values_reply_is_actual_expression (offset : FullOffsets) (bindings : Option Ptr) :
    helperReply (hasValuesProgram offset bindings) =
      ReadExpressions.expressionWith (bindingCalls offset) (fullLayout offset)
        (bindingNames bindings) boundValuesExpression := by
  unfold helperReply hasValuesProgram hasBoundValuesBody
  rw [StatementBlock.executeWith_equation]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    ReadBlock.Result.returnedValue?, ReadExpressions.resolved, Prog.bind_ret]
  rfl

theorem has_values_source_reply_false_owned (offset : FullOffsets) (bindings : Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedNoValues offset bindings rest) (helperReply (hasValuesProgram offset (some bindings)))
      (fun actual heap => actual = .bool false ∧ OwnedNoValues offset bindings rest heap) := by
  rw [has_values_reply_is_actual_expression]
  exact bound_values_expression_false_owned offset bindings rest

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev Context := StatementBlock.ObjectBindings.Context
abbrev ObjectBinding := StatementBlock.ObjectBindings.Binding

def atomType : CType := ⟨"Atom".toList, 1⟩
def outcomeType : CType := ⟨"Outcome".toList, 1⟩
def arenaType : CType := ⟨"Arena".toList, 1⟩
def variantType : CType := ⟨"VariantInstance".toList, 0⟩

def fullSourceCalls (offset : FullOffsets) (external : ReadExpressions.Calls) : ReadExpressions.Calls :=
  fun name arguments =>
    if name = "bindings_has_bound_values".toList then match arguments with
      | [.ptr bindings] => helperReply (hasValuesProgram offset bindings)
      | _ => CProg.undefined
    else sourceCalls offset.toOffsets external name arguments

def nativeFieldTypes : ScalarBytes.FieldTypes := fun type name =>
  if type = ⟨"Outcome".toList, 0⟩ then
    if name = "kind".toList then some ⟨"uint32_t".toList, 0⟩
    else if name = "atom".toList ∨ name = "materialized_atom".toList then some atomType
    else if name = "variant".toList then some variantType
    else if name = "env".toList then some ⟨"Bindings".toList, 0⟩
    else none
  else if type = ⟨"Bindings".toList, 0⟩ then
    if name = "len".toList then some ⟨"uint32_t".toList, 0⟩
    else if name = "frame_index".toList then some ⟨"BindingsFrameIndex".toList, 1⟩
    else none
  else if type = variantType ∧ name = "storage".toList then
    some ⟨"VariantInstanceStorage".toList, 1⟩
  else none

/-- The compacted record has its declared logical cell extent. Actual ABI and
automatic storage lifetime are supplied at the existing region boundary. -/
def materializerProfile (offset : FullOffsets) (external : ReadExpressions.Calls)
    (compactedExtent : Nat) : StatementBlock.ObjectBindings.Profile where
  values := fullSourceCalls offset external
  locations := fun _ => none
  outsideTypes := fun _ => none
  outsidePlaces := fun _ => none
  fieldTypes := nativeFieldTypes
  cellExtent := fun type => if type = variantType then some compactedExtent else none
  recordTypes := [variantType]
  byteExtent := fun _ => none
  sizeWidth := .bits64

@[simp] theorem materializerProfile_recordExtent (offset : FullOffsets)
    (external : ReadExpressions.Calls) (extent : Nat) (type : CType) :
    (materializerProfile offset external extent).recordExtent type =
      if type = variantType then some extent else none := by
  simp [StatementBlock.ObjectBindings.Profile.recordExtent, materializerProfile]

def read (offset : FullOffsets) (external : ReadExpressions.Calls)
    (compactedExtent : Nat) (context : Context) : CExpr → CProg CVal CVal :=
  StatementBlock.ObjectBindings.read (materializerProfile offset external compactedExtent)
    (fullLayout offset) context

def services (offset : FullOffsets) (external : ReadExpressions.Calls)
    (compactedExtent : Nat) (region : StatementBlock.AutomaticRegion Context) :
    StatementBlock.ScopedServices Context :=
  StatementBlock.ObjectBindings.services (materializerProfile offset external compactedExtent)
    region (fun _ _ _ => CProg.undefined)

def program (offset : FullOffsets) (external : ReadExpressions.Calls)
    (compactedExtent : Nat) (region : StatementBlock.AutomaticRegion Context)
    (context : Context) : CProg CVal (ReadBlock.Result Context) :=
  StatementBlock.executeScopedWith (services offset external compactedExtent region)
    (fullLayout offset) 0 12 context fullBody

def pointerLocal (context : Context) (name : String) (type : CType) (value : Option Ptr) : Prop :=
  context name.toList = some (.scalar type (some (.ptr value)))

theorem read_identifier (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (name : String) (type : CType) (value : CVal)
    (known : context name.toList = some (.scalar type (some value))) :
    read offset external extent context (ident name) = pure value :=
  StatementBlock.ObjectBindings.initialized_local_keeps_its_value _ _ _ _ _ _ known

theorem read_pointer_field (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (owner fieldName : String) (type : CType)
    (address : Option Ptr) (known : pointerLocal context owner type address) :
    read offset external extent context (fld owner fieldName) =
      ReadExpressions.field (fullLayout offset) (.ptr address) fieldName.toList := by
  unfold read StatementBlock.ObjectBindings.read fld
  rw [ReadExpressions.expressionWithNames.eq_def]
  change (read offset external extent context (ident owner) >>= fun value =>
    ReadExpressions.field (fullLayout offset) value fieldName.toList) = _
  rw [read_identifier offset external extent context owner type (.ptr address) known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem read_field_address (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (owner fieldName : String) (type : CType)
    (location : Option Ptr) (known : pointerLocal context owner type location) :
    read offset external extent context (address (fld owner fieldName)) =
      (ReadExpressions.fieldAddress (fullLayout offset) (.ptr location) fieldName.toList >>= fun place =>
        pure (.ptr (some place))) := by
  unfold read StatementBlock.ObjectBindings.read address fld
  rw [ReadExpressions.expressionWithNames.eq_def]
  change (read offset external extent context (ident owner) >>= fun value =>
    ReadExpressions.fieldAddress (fullLayout offset) value fieldName.toList >>= fun place =>
      pure (CVal.ptr (some place))) = _
  rw [read_identifier offset external extent context owner type (.ptr location) known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private theorem retained_two_declarations (profile : StatementBlock.ObjectBindings.Profile)
    (region : StatementBlock.AutomaticRegion Context)
    (effect : ReadExpressions.Layout → Context → CExpr → CProg CVal Unit)
    (fields : ReadExpressions.Layout) (context : Context) (body : List CStatement)
    (fuel extent : Nat)
    (scalar : profile.recordExtent atomType = none)
    (record : profile.recordExtent variantType = some extent) :
    StatementBlock.executeScopedWith (StatementBlock.ObjectBindings.services profile region effect)
      fields 0 (fuel + 2) context
      (.declareUninitialized atomType "materialized".toList ::
       .declareUninitialized variantType "compacted".toList :: body) =
      (region "compacted".toList extent (fun place =>
        StatementBlock.executeScopedWith (StatementBlock.ObjectBindings.services profile region effect)
          fields 0 fuel
          (Function.update (Function.update context "materialized".toList
            (some (.scalar atomType none))) "compacted".toList (some (.object variantType place))) body)
       >>= fun result => pure (StatementBlock.ObjectBindings.restore "materialized".toList
         (context "materialized".toList) (StatementBlock.ObjectBindings.restore "compacted".toList
           (context "compacted".toList) result))) := by
  rw [StatementBlock.executeScopedWith.eq_def]
  change (StatementBlock.ObjectBindings.declaration profile region fields context atomType
    "materialized".toList none (fun next =>
      StatementBlock.executeScopedWith (StatementBlock.ObjectBindings.services profile region effect)
        fields 0 (fuel + 1) next (.declareUninitialized variantType "compacted".toList :: body))) = _
  rw [StatementBlock.ObjectBindings.declaration, scalar]
  dsimp only []
  rw [StatementBlock.executeScopedWith.eq_def]
  change ((StatementBlock.ObjectBindings.declaration profile region fields
      (Function.update context "materialized".toList (some (.scalar atomType none)))
      variantType "compacted".toList none (fun next =>
        StatementBlock.executeScopedWith (StatementBlock.ObjectBindings.services profile region effect)
          fields 0 fuel next body)) >>= fun result =>
      pure (StatementBlock.ObjectBindings.restore "materialized".toList
        (context "materialized".toList) result)) = _
  rw [StatementBlock.ObjectBindings.declaration, record]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    Function.update_of_ne (by decide : "compacted".toList ≠ "materialized".toList)]

/-- Both declarations remain in the operation tree, including the record's
live automatic region and the two lexical restorations. -/
theorem full_program_keeps_both_local_scopes (offset : FullOffsets)
    (external : ReadExpressions.Calls) (extent : Nat)
    (region : StatementBlock.AutomaticRegion Context) (context : Context) :
    program offset external extent region context =
      (region "compacted".toList extent (fun place =>
        StatementBlock.executeScopedWith (services offset external extent region)
          (fullLayout offset) 0 10
          (Function.update (Function.update context "materialized".toList
            (some (.scalar atomType none))) "compacted".toList (some (.object variantType place)))
          ordinaryTail) >>= fun result =>
      pure (StatementBlock.ObjectBindings.restore "materialized".toList
        (context "materialized".toList)
        (StatementBlock.ObjectBindings.restore "compacted".toList
          (context "compacted".toList) result))) := by
  have scalar : (materializerProfile offset external extent).recordExtent atomType = none := by
    rw [materializerProfile_recordExtent]
    exact if_neg (by decide)
  have record : (materializerProfile offset external extent).recordExtent variantType = some extent := by
    rw [materializerProfile_recordExtent]
    exact if_pos rfl
  exact retained_two_declarations (materializerProfile offset external extent) region
    (fun _ _ _ => CProg.undefined) (fullLayout offset) context ordinaryTail 10 extent scalar record

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

def OwnedFull (offset : FullOffsets) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) : Heap L → Prop :=
  OwnedInline offset.toOffsets out atom
    (PointsTo (out + offset.cache) (.ptr cache) ∗
      (NoValueCells offset (out + offset.environment) ∗ rest))

theorem owned_full_as_no_values (offset : FullOffsets) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) :
    OwnedFull offset out atom cache rest =
      OwnedNoValues offset (out + offset.environment)
        (InlineUnfactored offset.toOffsets out atom ∗
          (PointsTo (out + offset.cache) (.ptr cache) ∗ rest)) := by
  unfold OwnedFull OwnedInline OwnedNoValues
  rw [sepConj_left_comm (PointsTo _ _) (NoValueCells _ _),
    sepConj_left_comm (InlineUnfactored _ _ _) (NoValueCells _ _)]

theorem source_bound_values_false_from_owned_outcome (offset : FullOffsets)
    (external : ReadExpressions.Calls) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedFull offset out atom cache rest)
      (fullSourceCalls offset external "bindings_has_bound_values".toList
        [.ptr (some (out + offset.environment))])
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  simp only [fullSourceCalls, ↓reduceIte]
  rw [owned_full_as_no_values]
  exact has_values_source_reply_false_owned offset (out + offset.environment) _

theorem source_variant_false_from_owned_outcome (offset : FullOffsets)
    (external : ReadExpressions.Calls) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) :
    CTriple (OwnedFull offset out atom cache rest)
      (fullSourceCalls offset external "variant_instance_present".toList
        [.ptr (some (out + offset.variant))])
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  simp only [fullSourceCalls,
    show "variant_instance_present".toList ≠ "bindings_has_bound_values".toList from by decide,
    ↓reduceIte, sourceCalls]
  exact present_source_reply_storage_null_owned offset.toOffsets out atom _

theorem read_atom_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context atomField)
      (fun actual heap => actual = .ptr atom ∧ OwnedFull offset out atom cache rest heap) := by
  change CTriple _ (read offset external extent context (fld "out" "atom")) _
  rw [read_pointer_field offset external extent context "out" "atom" outcomeType _ known,
    ReadExpressions.pointer_field_uses_actual_offset _ out "atom".toList offset.atom
      (by simp [fullLayout, layout])]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_step
  exact ⟨wf, held⟩

theorem read_cache_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context (fld "out" "materialized_atom"))
      (fun actual heap => actual = .ptr cache ∧ OwnedFull offset out atom cache rest heap) := by
  rw [read_pointer_field offset external extent context "out" "materialized_atom" outcomeType _ known,
    ReadExpressions.pointer_field_uses_actual_offset _ out "materialized_atom".toList offset.cache
      (by simp [fullLayout])]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  cmem_step
  exact ⟨wf, held⟩

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev uintType : CType := ⟨"uint32_t".toList, 0⟩

def initialized (context : Context) (atom : Option Ptr) : Context :=
  Function.update context "materialized".toList (some (.scalar atomType (some (.ptr atom))))

theorem read_null_guard (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Option Ptr)
    (known : pointerLocal context "out" outcomeType out) :
    read offset external extent context nullGuard =
      (CProg.ptrEq out none >>= fun isNull => pure (CVal.bool isNull)) := by
  unfold nullGuard read StatementBlock.ObjectBindings.read
  rw [ReadExpressions.expressionWithNames.eq_def]
  change (read offset external extent context (ident "out") >>= fun value =>
    ReadExpressions.truth value >>= fun selected => pure (CVal.bool (!selected))) = _
  rw [read_identifier offset external extent context "out" outcomeType (.ptr out) known]
  simp only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_assoc, Bool.not_not]

theorem read_kind (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr)
    (known : pointerLocal context "out" outcomeType (some out)) :
    read offset external extent context kindField =
      (CProg.loadU32 (out + offset.kind) >>= fun value => pure (.u32 value)) := by
  change read offset external extent context (fld "out" "kind") = _
  rw [read_pointer_field offset external extent context "out" "kind" outcomeType _ known]
  exact ReadExpressions.word_field_uses_actual_offset _ out "kind".toList offset.kind
    (by simp [fullLayout, layout])

theorem read_kind_condition (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr)
    (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1)))) :
    read offset external extent context kindCondition =
      (CProg.loadU32 (out + offset.kind) >>= fun value =>
        ReadExpressions.binary .eq (.u32 value) (.u32 1)) := by
  unfold kindCondition read StatementBlock.ObjectBindings.read
  rw [ReadExpressions.expressionWithNames.eq_def]
  change (read offset external extent context kindField >>= fun first =>
    read offset external extent context (ident "CETTA_OUTCOME_ANSWER_REF") >>= fun second =>
      ReadExpressions.binary .eq first second) = _
  rw [read_kind offset external extent context out known,
    read_identifier offset external extent context "CETTA_OUTCOME_ANSWER_REF" uintType (.u32 1) tag]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

theorem read_single_field_call (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (name member : String) (displacement : Nat)
    (known : pointerLocal context "out" outcomeType (some out))
    (field : (fullLayout offset) member.toList = some ⟨displacement, .embedded⟩) :
    read offset external extent context (invoke name [address (fld "out" member)]) =
      fullSourceCalls offset external name.toList [.ptr (some (out + displacement))] := by
  unfold read StatementBlock.ObjectBindings.read invoke
  rw [ReadExpressions.expressionWithNames.eq_def]
  dsimp only []
  rw [ReadExpressions.argumentsWithNames.eq_def]
  dsimp only []
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  change (read offset external extent context (address (fld "out" member)) >>= fun first =>
    ReadExpressions.argumentsWithNames _ _ _ [] _ >>= fun rest =>
      fullSourceCalls offset external name.toList (first :: rest)) = _
  rw [read_field_address offset external extent context "out" member outcomeType _ known]
  simp only [ReadExpressions.fieldAddress, ReadExpressions.pointer, field,
    ReadExpressions.argumentsWithNames.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem null_guard_false (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context nullGuard)
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  rw [read_null_guard offset external extent context _ known]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_step
  exact ⟨wf, held⟩

theorem kind_condition_false (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1)))) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context kindCondition)
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  rw [read_kind_condition offset external extent context out known tag]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  unfold InlineUnfactored at held
  cmem_step
  cmem_norm [ReadExpressions.binary, ReadExpressions.equal, ReadExpressions.scalar,
    ReadExpressions.resolved, ScalarRead.equal?]
  exact ⟨rfl, wf, held⟩

theorem inflation_guard_false (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1)))) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context inflationGuard)
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  unfold inflationGuard read StatementBlock.ObjectBindings.read
  rw [ReadExpressions.expressionWithNames.eq_def]
  dsimp only []
  apply bind_exact _ _ _ (.bool false) _ (kind_condition_false offset external extent context out atom cache rest known tag)
  simpa only [ReadExpressions.truth, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Bool.false_eq_true, if_false] using
    (pure_exact (OwnedFull offset out atom cache rest) (.bool false : CVal))

theorem read_variant_false (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context variantCall)
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  change CTriple _ (read offset external extent context
    (invoke "variant_instance_present" [address (fld "out" "variant")])) _
  rw [read_single_field_call offset external extent context out "variant_instance_present" "variant" offset.variant known
    (by simp [fullLayout, layout])]
  exact source_variant_false_from_owned_outcome offset external out atom cache rest

theorem read_bound_values_false (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom cache rest)
      (read offset external extent context
        (invoke "bindings_has_bound_values" [address (fld "out" "env")]))
      (fun actual heap => actual = .bool false ∧ OwnedFull offset out atom cache rest heap) := by
  rw [read_single_field_call offset external extent context out "bindings_has_bound_values" "env" offset.environment known
    (by simp [fullLayout])]
  exact source_bound_values_false_from_owned_outcome offset external out atom cache rest

theorem assign_materialized_local (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (declaredLocal : context "materialized".toList = some (.scalar atomType none)) :
    CTriple (OwnedFull offset out atom cache rest)
      (StatementBlock.ObjectBindings.assignment (materializerProfile offset external extent)
        (fullLayout offset) context (.assign (ident "materialized") atomField))
      (fun actual heap => actual = initialized context atom ∧ OwnedFull offset out atom cache rest heap) := by
  have targetType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (fun _ => none)) (ident "materialized") nativeFieldTypes = some atomType := by
    simp only [ScalarBytes.typeOf?, ident, StatementBlock.ObjectBindings.types, declaredLocal]
  unfold StatementBlock.ObjectBindings.assignment
  simp only [targetType, materializerProfile, ReadExpressions.resolved,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  apply bind_exact _ _ _ (.ptr atom) _ (read_atom_owned offset external extent context out atom cache rest known)
  change CTriple _ (StatementBlock.ObjectBindings.writeValue
    (materializerProfile offset external extent) (fullLayout offset) context
    (.identifier "materialized".toList) (.ptr atom)) _
  rw [StatementBlock.ObjectBindings.local_scalar_write_refines_existing_inventory _ _ context
    "materialized".toList atomType none (.ptr atom) declaredLocal]
  simpa only [StatementBlock.ObjectBindings.scalarInitialValue, materializerProfile,
    Option.getD_none, StatementBlock.objectInitialValue, atomType, ReadExpressions.pointer,
    Nat.zero_lt_succ, ↓reduceIte, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, initialized] using
    (pure_exact (OwnedFull offset out atom cache rest) (initialized context atom))

theorem cache_assignment_retains_store (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom : Option Ptr)
    (known : pointerLocal context "out" outcomeType (some out))
    (declaredLocal : context "materialized".toList = some (.scalar atomType (some (.ptr atom)))) :
    StatementBlock.ObjectBindings.assignment (materializerProfile offset external extent)
      (fullLayout offset) context (.assign (fld "out" "materialized_atom") (ident "materialized")) =
      (CProg.store (out + offset.cache) (.ptr atom) >>= fun _ => pure context) := by
  have targetType : ScalarBytes.typeOf?
      (StatementBlock.ObjectBindings.types context (fun _ => none)) (fld "out" "materialized_atom") nativeFieldTypes = some atomType := by
    change context "out".toList = some (.scalar outcomeType (some (.ptr (some out)))) at known
    simp only [ScalarBytes.typeOf?, fld, ident, StatementBlock.ObjectBindings.types, known,
      outcomeType]
    rfl
  unfold StatementBlock.ObjectBindings.assignment
  simp only [targetType, materializerProfile, ReadExpressions.resolved,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  change (read offset external extent context (ident "materialized") >>= fun value =>
    StatementBlock.ObjectBindings.writeValue (materializerProfile offset external extent)
      (fullLayout offset) context (fld "out" "materialized_atom") value) = _
  rw [read_identifier offset external extent context "materialized" atomType (.ptr atom) declaredLocal]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  change StatementBlock.ObjectBindings.writeValue (materializerProfile offset external extent)
    (fullLayout offset) context (.field (ident "out") "materialized_atom".toList true) (.ptr atom) = _
  rw [StatementBlock.ObjectBindings.scalar_field_write_keeps_place_and_value _ _ context
    (ident "out") "materialized_atom".toList true (.ptr atom) offset.cache (by rfl)]
  unfold StatementBlock.ObjectBindings.place
  rw [ReadExpressions.placeWithNames.eq_def]
  change ((read offset external extent context (ident "out") >>= fun value =>
    ReadExpressions.fieldAddress (fullLayout offset) value "materialized_atom".toList) >>= fun place =>
    CProg.store place (.ptr atom) >>= fun _ => pure context) = _
  rw [read_identifier offset external extent context "out" outcomeType (.ptr (some out)) known]
  simp only [ReadExpressions.fieldAddress, ReadExpressions.pointer, fullLayout, ↓reduceIte, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem cache_assignment_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (declaredLocal : context "materialized".toList = some (.scalar atomType (some (.ptr atom)))) :
    CTriple (OwnedFull offset out atom cache rest)
      (StatementBlock.ObjectBindings.assignment (materializerProfile offset external extent)
        (fullLayout offset) context (.assign (fld "out" "materialized_atom") (ident "materialized")))
      (fun actual heap => actual = context ∧ OwnedFull offset out atom atom rest heap) := by
  rw [cache_assignment_retains_store offset external extent context out atom known declaredLocal]
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  cmem_step
  rw [sepConj_left_comm (PointsTo (out + offset.cache) (CVal.ptr atom))
    (InlineUnfactored offset.toOffsets out atom)] at held
  exact ⟨wf, held⟩


private theorem false_read_has_false_truth (pre : Heap L → Prop) (reader : CProg CVal CVal)
    (reads : CTriple pre reader (fun actual heap => actual = .bool false ∧ pre heap)) :
    CTriple pre (reader >>= ReadExpressions.truth)
      (fun actual heap => actual = false ∧ pre heap) := by
  apply bind_exact _ _ _ (.bool false) _ reads
  exact pure_exact pre false

private theorem scoped_false_branch (engine : StatementBlock.ScopedServices Context)
    (fields : ReadExpressions.Layout) (fuel : Nat) (context : Context)
    (condition : CExpr) (yes no tail : List CStatement) (pre : Heap L → Prop)
    (post : ReadBlock.Result Context → Heap L → Prop)
    (guard : CTriple pre (engine.read fields context condition >>= ReadExpressions.truth)
      (fun actual heap => actual = false ∧ pre heap))
    (selected : CTriple pre (StatementBlock.executeScopedWith engine fields 0 fuel context no)
      (fun actual heap => actual = .finished (.next context) ∧ pre heap))
    (continuation : CTriple pre (StatementBlock.executeScopedWith engine fields 0 fuel context tail) post) :
    CTriple pre (StatementBlock.executeScopedWith engine fields 0 (fuel + 1) context
      (.branch condition yes no :: tail)) post := by
  rw [StatementBlock.executeScopedWith.eq_def]
  simp only [Prog.bind_eq, ← Prog.bind_assoc]
  rw [Prog.bind_assoc]
  apply bind_exact _ _ _ false _ guard
  simp only [Bool.false_eq_true, if_false]
  apply bind_exact _ _ _ (ReadBlock.Result.finished (.next context)) _ selected
  exact continuation

private theorem scoped_false_guard (engine : StatementBlock.ScopedServices Context)
    (fields : ReadExpressions.Layout) (fuel : Nat) (context : Context)
    (condition : CExpr) (yes tail : List CStatement) (pre : Heap L → Prop)
    (post : ReadBlock.Result Context → Heap L → Prop)
    (guard : CTriple pre (engine.read fields context condition >>= ReadExpressions.truth)
      (fun actual heap => actual = false ∧ pre heap))
    (continuation : CTriple pre (StatementBlock.executeScopedWith engine fields 0 fuel context tail) post) :
    CTriple pre (StatementBlock.executeScopedWith engine fields 0 (fuel + 1) context
      (.branch condition yes [] :: tail)) post := by
  apply scoped_false_branch engine fields fuel context condition yes [] tail pre post guard
  · rw [StatementBlock.executeScopedWith.eq_def]
    exact pure_exact pre (ReadBlock.Result.finished (.next context))
  · exact continuation

theorem cache_guard_false (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom none rest)
      (read offset external extent context (fld "out" "materialized_atom") >>= ReadExpressions.truth)
      (fun actual heap => actual = false ∧ OwnedFull offset out atom none rest heap) := by
  apply bind_exact _ _ _ (.ptr none) _ (read_cache_owned offset external extent context out atom none rest known)
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  cmem_norm [ReadExpressions.truth]
  cmem_step
  exact ⟨wf, held⟩

theorem store_and_return (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (region : StatementBlock.AutomaticRegion Context)
    (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (declaredLocal : context "materialized".toList = some (.scalar atomType (some (.ptr atom)))) :
    CTriple (OwnedFull offset out atom cache rest)
      (StatementBlock.executeScopedWith (services offset external extent region) (fullLayout offset) 0 5 context
        [.assign (fld "out" "materialized_atom") (ident "materialized"),
         .return (some (ident "materialized"))])
      (fun actual heap => actual = .finished (.returned context (some (.ptr atom))) ∧
        OwnedFull offset out atom atom rest heap) := by
  rw [StatementBlock.scoped_assignment_keeps_continuation]
  apply triple_bind _ (cache_assignment_owned offset external extent context out atom cache rest known declaredLocal)
  intro reached heap held
  rcases held with ⟨same, held⟩
  subst reached
  have tail : CTriple (OwnedFull offset out atom atom rest)
      (StatementBlock.executeScopedWith (services offset external extent region) (fullLayout offset) 0 4 context
        [.return (some (ident "materialized"))])
      (fun actual heap => actual = .finished (.returned context (some (.ptr atom))) ∧
        OwnedFull offset out atom atom rest heap) := by
    rw [StatementBlock.executeScopedWith.eq_def]
    change CTriple _ (read offset external extent context (ident "materialized") >>= fun value =>
      pure (ReadBlock.Result.finished (.returned context (some value)))) _
    rw [read_identifier offset external extent context "materialized" atomType (.ptr atom) declaredLocal]
    simpa only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind] using
      (pure_exact (OwnedFull offset out atom atom rest)
        (ReadBlock.Result.finished (.returned context (some (.ptr atom)))))
  exact tail heap held

/-- On this path the variant branch and environment application are both
skipped by the actual helper bodies. The cache store still executes. -/
theorem no_values_suffix (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (region : StatementBlock.AutomaticRegion Context)
    (context : Context) (out : Ptr) (atom cache : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (declaredLocal : context "materialized".toList = some (.scalar atomType (some (.ptr atom)))) :
    CTriple (OwnedFull offset out atom cache rest)
      (StatementBlock.executeScopedWith (services offset external extent region) (fullLayout offset) 0 6 context
        [.branch variantCall variantArm
          [.branch (invoke "bindings_has_bound_values" [address (fld "out" "env")])
            [.assign (ident "materialized") (invoke "eval_env_apply"
              [address (fld "out" "env"), ident "a", ident "materialized"])] []],
         .assign (fld "out" "materialized_atom") (ident "materialized"),
         .return (some (ident "materialized"))])
      (fun actual heap => actual = .finished (.returned context (some (.ptr atom))) ∧
        OwnedFull offset out atom atom rest heap) := by
  apply scoped_false_branch _ _ 5 _ variantCall _ _ _ _ _
    (false_read_has_false_truth _ _ (read_variant_false offset external extent context out atom cache rest known))
  · apply scoped_false_guard _ _ 4 _ _ _ _ _ _
      (false_read_has_false_truth _ _ (read_bound_values_false offset external extent context out atom cache rest known))
    exact pure_exact (OwnedFull offset out atom cache rest) (ReadBlock.Result.finished (.next context))
  · exact store_and_return offset external extent region context out atom cache rest known declaredLocal

/-- The parsed full tail returns the stored atom while writing that same
pointer to its actual cache cell. All other owned fields and the frame survive. -/
theorem ordinary_tail_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (region : StatementBlock.AutomaticRegion Context)
    (context : Context) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1))))
    (declaredLocal : context "materialized".toList = some (.scalar atomType none)) :
    CTriple (OwnedFull offset out atom none rest)
      (StatementBlock.executeScopedWith (services offset external extent region) (fullLayout offset) 0 10 context ordinaryTail)
      (fun actual heap => actual = .finished (.returned (initialized context atom) (some (.ptr atom))) ∧
        OwnedFull offset out atom atom rest heap) := by
  unfold ordinaryTail
  apply scoped_false_guard _ _ 9 _ nullGuard _ _ _ _
    (false_read_has_false_truth _ _ (null_guard_false offset external extent context out atom none rest known))
  apply scoped_false_guard _ _ 8 _ inflationGuard _ _ _ _
    (false_read_has_false_truth _ _ (inflation_guard_false offset external extent context out atom none rest known tag))
  apply scoped_false_guard _ _ 7 _ _ _ _ _ _
    (cache_guard_false offset external extent context out atom rest known)
  rw [StatementBlock.scoped_assignment_keeps_continuation]
  apply triple_bind _ (assign_materialized_local offset external extent context out atom none rest known declaredLocal)
  intro reached heap held
  rcases held with ⟨rfl, held⟩
  exact no_values_suffix offset external extent region (initialized context atom) out atom none rest
    (by
      change context "out".toList = _ at known
      change initialized context atom "out".toList = _
      exact (Function.update_of_ne (by decide : "out".toList ≠ "materialized".toList) _ _).trans known)
    (by exact Function.update_self _ _ _) heap held


private theorem scoped_true_return (engine : StatementBlock.ScopedServices Context)
    (fields : ReadExpressions.Layout) (fuel : Nat) (context : Context)
    (condition operand : CExpr) (no tail : List CStatement) (pre : Heap L → Prop) (value : CVal)
    (guard : CTriple pre (engine.read fields context condition >>= ReadExpressions.truth)
      (fun actual heap => actual = true ∧ pre heap))
    (reads : CTriple pre (engine.read fields context operand)
      (fun actual heap => actual = value ∧ pre heap)) :
    CTriple pre (StatementBlock.executeScopedWith engine fields 0 (fuel + 2) context
      (.branch condition [.return (some operand)] no :: tail))
      (fun actual heap => actual = .finished (.returned context (some value)) ∧ pre heap) := by
  rw [StatementBlock.executeScopedWith.eq_def]
  simp only [Prog.bind_eq, ← Prog.bind_assoc]
  rw [Prog.bind_assoc]
  apply bind_exact _ _ _ true _ guard
  simp only [↓reduceIte]
  rw [StatementBlock.executeScopedWith.eq_def]
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  apply bind_exact _ _ _ value _ reads
  exact pure_exact pre (ReadBlock.Result.finished (.returned context (some value)))

theorem cache_guard_true (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (context : Context) (out cache : Ptr) (atom : Option Ptr) (payload : CVal)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out)) :
    CTriple (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest))
      (read offset external extent context (fld "out" "materialized_atom") >>= ReadExpressions.truth)
      (fun actual heap => actual = true ∧
        OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest) heap) := by
  apply bind_exact _ _ _ (.ptr (some cache)) _
    (read_cache_owned offset external extent context out atom (some cache) _ known)
  cmem_start heap held
  rcases held with ⟨wf, held⟩
  cmem_norm [ReadExpressions.truth]
  cmem_step
  exact ⟨wf, held⟩

/-- An already populated live cache is authoritative for the full materializer.
Its returned pointer need not equal the stored atom pointer. -/
theorem populated_cache_tail_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (region : StatementBlock.AutomaticRegion Context)
    (context : Context) (out cache : Ptr) (atom : Option Ptr) (payload : CVal)
    (rest : Heap L → Prop) (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1)))) :
    CTriple (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest))
      (StatementBlock.executeScopedWith (services offset external extent region) (fullLayout offset) 0 10 context ordinaryTail)
      (fun actual heap => actual = .finished (.returned context (some (.ptr (some cache)))) ∧
        OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest) heap) := by
  unfold ordinaryTail
  apply scoped_false_guard _ _ 9 _ nullGuard _ _ _ _
    (false_read_has_false_truth _ _ (null_guard_false offset external extent context out atom (some cache) _ known))
  apply scoped_false_guard _ _ 8 _ inflationGuard _ _ _ _
    (false_read_has_false_truth _ _ (inflation_guard_false offset external extent context out atom (some cache) _ known tag))
  exact scoped_true_return _ _ 6 _ (fld "out" "materialized_atom") (fld "out" "materialized_atom")
    _ _ _ (.ptr (some cache))
    (cache_guard_true offset external extent context out cache atom payload rest known)
    (read_cache_owned offset external extent context out atom (some cache) _ known)

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def scopedContext (context : Context) (place : Ptr) : Context :=
  Function.update (Function.update context "materialized".toList
    (some (.scalar atomType none))) "compacted".toList (some (.object variantType place))

theorem initialization_keeps_the_record_scope (context : Context) (place : Ptr) (atom : Option Ptr) :
    initialized (scopedContext context place) atom =
      Function.update (initialized context atom) "compacted".toList (some (.object variantType place)) := by
  unfold initialized scopedContext
  rw [Function.update_comm (by decide : "compacted".toList ≠ "materialized".toList),
    Function.update_idem]

theorem completed_scope_restores_caller (context : Context) (place : Ptr) (atom : Option Ptr) :
    StatementBlock.ObjectBindings.restore "materialized".toList (context "materialized".toList)
      (StatementBlock.ObjectBindings.restore "compacted".toList (context "compacted".toList)
        (.finished (.returned (initialized (scopedContext context place) atom) (some (CVal.ptr atom))))) =
      .finished (.returned context (some (CVal.ptr atom))) := by
  rw [initialization_keeps_the_record_scope]
  have unchanged : initialized context atom "compacted".toList = context "compacted".toList := by
    exact Function.update_of_ne (by decide : "compacted".toList ≠ "materialized".toList) _ _
  rw [← unchanged, StatementBlock.ObjectBindings.returned_local_restores_previous_binding]
  exact StatementBlock.ObjectBindings.returned_local_restores_previous_binding context
    "materialized".toList (.scalar atomType (some (CVal.ptr atom))) _

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- Full source execution under the existing automatic-region interface.
Only entry and exit own the automatic-storage contract; the actual parsed
body, helper reads, result, cache store and lexical restoration are proved here. -/
theorem full_source_no_values_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) (inside : Ptr → Heap L → Prop)
    (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1))))
    (opened : CTriple (OwnedFull offset out atom none rest)
      (enter "compacted".toList extent)
      (fun place heap => OwnedFull offset out atom none (inside place) heap))
    (closed : ∀ place, CTriple (OwnedFull offset out atom atom (inside place))
      (leave "compacted".toList place extent)
      (fun _ heap => OwnedFull offset out atom atom rest heap)) :
    CTriple (OwnedFull offset out atom none rest)
      (program offset external extent (StatementBlock.AutomaticRegion.bracket enter leave) context)
      (fun actual heap => actual = .finished (.returned context (some (CVal.ptr atom))) ∧
        OwnedFull offset out atom atom rest heap) := by
  rw [full_program_keeps_both_local_scopes]
  unfold StatementBlock.AutomaticRegion.bracket
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply triple_bind _ opened
  intro place heap held
  have body := ordinary_tail_owned offset external extent
    (StatementBlock.AutomaticRegion.bracket enter leave) (scopedContext context place)
    out atom (inside place)
    (by
      change scopedContext context place "out".toList = _
      unfold scopedContext
      rw [Function.update_of_ne (by decide : "out".toList ≠ "compacted".toList),
        Function.update_of_ne (by decide : "out".toList ≠ "materialized".toList)]
      exact known)
    (by
      unfold scopedContext
      rw [Function.update_of_ne (by decide : "CETTA_OUTCOME_ANSWER_REF".toList ≠ "compacted".toList),
        Function.update_of_ne (by decide : "CETTA_OUTCOME_ANSWER_REF".toList ≠ "materialized".toList)]
      exact tag)
    (by
      unfold scopedContext
      rw [Function.update_of_ne (by decide : "materialized".toList ≠ "compacted".toList),
        Function.update_self])
  have continuation : CTriple (OwnedFull offset out atom none (inside place))
      (StatementBlock.executeScopedWith
        (services offset external extent (StatementBlock.AutomaticRegion.bracket enter leave))
        (fullLayout offset) 0 10 (scopedContext context place) ordinaryTail >>= fun result =>
        leave "compacted".toList place extent >>= fun _ =>
        pure (StatementBlock.ObjectBindings.restore "materialized".toList
          (context "materialized".toList)
          (StatementBlock.ObjectBindings.restore "compacted".toList
            (context "compacted".toList) result)))
      (fun actual heap => actual = .finished (.returned context (some (CVal.ptr atom))) ∧
        OwnedFull offset out atom atom rest heap) := by
    apply triple_bind _ body
    intro result after returned
    rcases returned with ⟨rfl, retained⟩
    have exitLaw : CTriple (OwnedFull offset out atom atom (inside place))
        (leave "compacted".toList place extent >>= fun _ =>
          pure (StatementBlock.ObjectBindings.restore "materialized".toList
            (context "materialized".toList)
            (StatementBlock.ObjectBindings.restore "compacted".toList
              (context "compacted".toList)
              (.finished (.returned (initialized (scopedContext context place) atom) (some (CVal.ptr atom)))))))
        (fun actual heap => actual = .finished (.returned context (some (CVal.ptr atom))) ∧
          OwnedFull offset out atom atom rest heap) := by
      rw [completed_scope_restores_caller]
      apply triple_bind _ (closed place)
      intro ignored
      exact pure_exact (OwnedFull offset out atom atom rest)
        (ReadBlock.Result.finished (.returned context (some (CVal.ptr atom))))
    exact exitLaw after retained
  exact continuation heap held

/-- The pointer observation of the actual full function, after both local
scopes have closed, retains the same proved cache update. -/
theorem full_source_reply_no_values_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) (inside : Ptr → Heap L → Prop)
    (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1))))
    (opened : CTriple (OwnedFull offset out atom none rest)
      (enter "compacted".toList extent)
      (fun place heap => OwnedFull offset out atom none (inside place) heap))
    (closed : ∀ place, CTriple (OwnedFull offset out atom atom (inside place))
      (leave "compacted".toList place extent)
      (fun _ heap => OwnedFull offset out atom atom rest heap)) :
    CTriple (OwnedFull offset out atom none rest)
      (program offset external extent (StatementBlock.AutomaticRegion.bracket enter leave) context >>=
        fun result => ReadExpressions.resolved result.returnedValue?)
      (fun actual heap => actual = .ptr atom ∧ OwnedFull offset out atom atom rest heap) := by
  apply triple_bind _ (full_source_no_values_owned offset external extent enter leave
    context out atom rest inside known tag opened closed)
  intro result heap held
  rcases held with ⟨rfl, held⟩
  exact pure_exact (OwnedFull offset out atom atom rest) (CVal.ptr atom : CVal) heap held


/-- The two automatic declarations restore the previous locals even when the
function returns directly from its already populated cache. -/
theorem cached_scope_restores_caller (context : Context) (place : Ptr) (cache : Ptr) :
    StatementBlock.ObjectBindings.restore "materialized".toList (context "materialized".toList)
      (StatementBlock.ObjectBindings.restore "compacted".toList (context "compacted".toList)
        (.finished (.returned (scopedContext context place) (some (CVal.ptr (some cache)))))) =
      .finished (.returned context (some (CVal.ptr (some cache)))) := by
  unfold scopedContext
  have unchanged : Function.update context "materialized".toList
      (some (.scalar atomType none)) "compacted".toList = context "compacted".toList :=
    Function.update_of_ne (by decide : "compacted".toList ≠ "materialized".toList) _ _
  rw [← unchanged, StatementBlock.ObjectBindings.returned_local_restores_previous_binding]
  exact StatementBlock.ObjectBindings.returned_local_restores_previous_binding context
    "materialized".toList (.scalar atomType none) _

/-- A populated cache is read through the actual function and lexical exit.
No equality between that cache and the stored atom is assumed or inferred. -/
theorem full_source_cached_owned (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (out cache : Ptr) (atom : Option Ptr) (payload : CVal)
    (rest : Heap L → Prop) (inside : Ptr → Heap L → Prop)
    (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1))))
    (opened : CTriple (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest))
      (enter "compacted".toList extent)
      (fun place heap => OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ inside place) heap))
    (closed : ∀ place, CTriple
      (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ inside place))
      (leave "compacted".toList place extent)
      (fun _ heap => OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest) heap)) :
    CTriple (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest))
      (program offset external extent (StatementBlock.AutomaticRegion.bracket enter leave) context)
      (fun actual heap => actual = .finished (.returned context (some (CVal.ptr (some cache)))) ∧
        OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest) heap) := by
  rw [full_program_keeps_both_local_scopes]
  unfold StatementBlock.AutomaticRegion.bracket
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply triple_bind _ opened
  intro place heap held
  have body := populated_cache_tail_owned offset external extent
    (StatementBlock.AutomaticRegion.bracket enter leave) (scopedContext context place)
    out cache atom payload (inside place)
    (by
      change scopedContext context place "out".toList = _
      unfold scopedContext
      rw [Function.update_of_ne (by decide : "out".toList ≠ "compacted".toList),
        Function.update_of_ne (by decide : "out".toList ≠ "materialized".toList)]
      exact known)
    (by
      unfold scopedContext
      rw [Function.update_of_ne (by decide : "CETTA_OUTCOME_ANSWER_REF".toList ≠ "compacted".toList),
        Function.update_of_ne (by decide : "CETTA_OUTCOME_ANSWER_REF".toList ≠ "materialized".toList)]
      exact tag)
  have continuation : CTriple
      (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ inside place))
      (StatementBlock.executeScopedWith
        (services offset external extent (StatementBlock.AutomaticRegion.bracket enter leave))
        (fullLayout offset) 0 10 (scopedContext context place) ordinaryTail >>= fun result =>
        leave "compacted".toList place extent >>= fun _ =>
        pure (StatementBlock.ObjectBindings.restore "materialized".toList
          (context "materialized".toList)
          (StatementBlock.ObjectBindings.restore "compacted".toList
            (context "compacted".toList) result)))
      (fun actual heap => actual = .finished (.returned context (some (CVal.ptr (some cache)))) ∧
        OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest) heap) := by
    apply triple_bind _ body
    intro result after returned
    rcases returned with ⟨rfl, retained⟩
    have exitLaw : CTriple
        (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ inside place))
        (leave "compacted".toList place extent >>= fun _ =>
          pure (StatementBlock.ObjectBindings.restore "materialized".toList
            (context "materialized".toList)
            (StatementBlock.ObjectBindings.restore "compacted".toList
              (context "compacted".toList)
              (.finished (.returned (scopedContext context place) (some (CVal.ptr (some cache))))))))
        (fun actual heap => actual = .finished (.returned context (some (CVal.ptr (some cache)))) ∧
          OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest) heap) := by
      rw [cached_scope_restores_caller]
      apply triple_bind _ (closed place)
      intro ignored
      exact pure_exact (OwnedFull offset out atom (some cache) (PointsTo cache payload ∗ rest))
        (ReadBlock.Result.finished (.returned context (some (CVal.ptr (some cache)))))
    exact exitLaw after retained
  exact continuation heap held

/-- Variant-only materialization preserves every additional outcome cell,
including the current cache and binding fields. -/
theorem variant_keeps_full_footprint (offset : FullOffsets) (external : ReadExpressions.Calls)
    (arena : Option Ptr) (out : Ptr) (atom cache : Option Ptr) (rest : Heap L → Prop) :
    CTriple (OwnedFull offset out atom cache rest)
      (variantOnlyFromHelpers offset.toOffsets external arena (some out))
      (fun actual heap =>
        actual = .finished (.returned (environment arena (some out)) (some (CVal.ptr atom))) ∧
        OwnedFull offset out atom cache rest heap) :=
  variant_only_source_helpers_storage_null_owned offset.toOffsets external arena out atom _

/-- Both selected real materializer programs agree after the full helper has
written its null cache. The intervening native caller is a separate component. -/
theorem full_then_variant_null_cache_agree (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (arena : Option Ptr) (out : Ptr) (atom : Option Ptr)
    (rest : Heap L → Prop) (inside : Ptr → Heap L → Prop)
    (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1))))
    (opened : CTriple (OwnedFull offset out atom none rest)
      (enter "compacted".toList extent)
      (fun place heap => OwnedFull offset out atom none (inside place) heap))
    (closed : ∀ place, CTriple (OwnedFull offset out atom atom (inside place))
      (leave "compacted".toList place extent)
      (fun _ heap => OwnedFull offset out atom atom rest heap)) :
    CTriple (OwnedFull offset out atom none rest)
      (program offset external extent (StatementBlock.AutomaticRegion.bracket enter leave) context >>= fun full =>
        variantOnlyFromHelpers offset.toOffsets external arena (some out) >>= fun variant =>
          pure (full.returnedValue?, variant.returnedValue?))
      (fun actual heap => actual = (some (CVal.ptr atom), some (CVal.ptr atom)) ∧
        OwnedFull offset out atom atom rest heap) := by
  apply triple_bind _ (full_source_no_values_owned offset external extent enter leave context
    out atom rest inside known tag opened closed)
  intro full heap held
  rcases held with ⟨rfl, held⟩
  have finish : CTriple (OwnedFull offset out atom atom rest)
      (variantOnlyFromHelpers offset.toOffsets external arena (some out) >>= fun variant =>
        pure (some (CVal.ptr atom), variant.returnedValue?))
      (fun actual heap => actual = (some (CVal.ptr atom), some (CVal.ptr atom)) ∧
        OwnedFull offset out atom atom rest heap) := by
    apply bind_exact _ _ _ _ _
      (variant_keeps_full_footprint offset external arena out atom atom rest)
    exact pure_exact _ (some (CVal.ptr atom), some (CVal.ptr atom))
  exact finish heap held

/-- The second valid cache frontier is an already populated cache equal to
the stored atom, with its live pointer footprint retained. -/
theorem full_then_variant_equal_cache_agree (offset : FullOffsets) (external : ReadExpressions.Calls)
    (extent : Nat) (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit)
    (context : Context) (arena : Option Ptr) (out atom : Ptr) (payload : CVal)
    (rest : Heap L → Prop) (inside : Ptr → Heap L → Prop)
    (known : pointerLocal context "out" outcomeType (some out))
    (tag : context "CETTA_OUTCOME_ANSWER_REF".toList = some (.scalar uintType (some (.u32 1))))
    (opened : CTriple (OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ rest))
      (enter "compacted".toList extent)
      (fun place heap =>
        OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ inside place) heap))
    (closed : ∀ place, CTriple
      (OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ inside place))
      (leave "compacted".toList place extent)
      (fun _ heap => OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ rest) heap)) :
    CTriple (OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ rest))
      (program offset external extent (StatementBlock.AutomaticRegion.bracket enter leave) context >>= fun full =>
        variantOnlyFromHelpers offset.toOffsets external arena (some out) >>= fun variant =>
          pure (full.returnedValue?, variant.returnedValue?))
      (fun actual heap => actual = (some (CVal.ptr (some atom)), some (CVal.ptr (some atom))) ∧
        OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ rest) heap) := by
  apply triple_bind _ (full_source_cached_owned offset external extent enter leave context
    out atom (some atom) payload rest inside known tag opened closed)
  intro full heap held
  rcases held with ⟨rfl, held⟩
  have finish : CTriple (OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ rest))
      (variantOnlyFromHelpers offset.toOffsets external arena (some out) >>= fun variant =>
        pure (some (CVal.ptr (some atom)), variant.returnedValue?))
      (fun actual heap => actual = (some (CVal.ptr (some atom)), some (CVal.ptr (some atom))) ∧
        OwnedFull offset out (some atom) (some atom) (PointsTo atom payload ∗ rest) heap) := by
    apply bind_exact _ _ _ _ _
      (variant_keeps_full_footprint offset external arena out (some atom) (some atom) (PointsTo atom payload ∗ rest))
    exact pure_exact _ (some (CVal.ptr (some atom)), some (CVal.ptr (some atom)))
  exact finish heap held

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full

end

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full.Controls
open Mettapedia.Machines.CMemory
open ExecutableStorage ProductiveBlocks

def offsets : FullOffsets := ⟨⟨0, 1, 2, 0, 0⟩, 3, 4, 0, 1, 0⟩
def outcome : Ptr := ⟨1, 0⟩
def atom : Ptr := ⟨2, 0⟩
def other : Ptr := ⟨4, 0⟩
def fields (cache : Option Ptr) (length : UInt32 := 0) : List (Option CVal) :=
  [some (.u32 0), some (.ptr (some atom)), some (.ptr none), some (.ptr cache),
   some (.u32 length), some (.ptr none)]
def initial : Storage CVal :=
  [(outcome.block, ⟨true, fields none⟩),
   (atom.block, ⟨true, [some (.u64 77)]⟩),
   (3, ⟨true, [some (.u32 45), none]⟩),
   (other.block, ⟨true, [some (.u64 88)]⟩)]
def cached : Storage CVal := put initial outcome.block ⟨true, fields (some atom)⟩
def mismatched : Storage CVal := put initial outcome.block ⟨true, fields (some other)⟩
def needsBindings : Storage CVal := put initial outcome.block ⟨true, fields none 1⟩

def context : Context := fun name =>
  if name = "out".toList then some (.scalar outcomeType (some (.ptr (some outcome))))
  else if name = "a".toList then some (.scalar arenaType (some (.ptr none)))
  else if name = "materialized".toList then some (.scalar atomType none)
  else if name = "CETTA_OUTCOME_ANSWER_REF".toList then some (.scalar uintType (some (.u32 1)))
  else none

/-- The automatic region remains arbitrary: these controls begin at the
proved body boundary, after the actual two declarations have been entered. -/
def state (region : StatementBlock.AutomaticRegion Context) (storage : Storage CVal) :
    State CVal (ReadBlock.Result Context) :=
  ⟨StatementBlock.executeScopedWith (services offsets ReadExpressions.noCalls 1 region)
    (fullLayout offsets) 0 10 context ordinaryTail, storage, []⟩

def endpoint (region : StatementBlock.AutomaticRegion Context) (fuel : Nat) (storage : Storage CVal) :
    Option (Option CVal × Storage CVal) :=
  match (machine.run fuel (state region storage)).2 with
  | .finished (.returned final) => some (final.answer.returnedValue?, final.storage)
  | _ => none

def writes (receipts : List (Receipt CVal)) : Nat :=
  (receipts.filter fun receipt => match receipt.operation with
    | .store _ _ => true
    | _ => false).length

theorem full_tail_returns_actual_pointer_and_updates_cache
    (region : StatementBlock.AutomaticRegion Context) :
    endpoint region 20 initial = some (some (.ptr (some atom)), cached) := by
  rfl

theorem actual_tail_writes_the_cache_once (region : StatementBlock.AutomaticRegion Context) :
    writes (machine.run 20 (state region initial)).1 = 1 := rfl

/-- A storage-level counterexample to unconditional agreement; this does not
assert that an admitted native producer can reach this mismatched cache. -/
theorem a_preexisting_different_cache_is_observable (region : StatementBlock.AutomaticRegion Context) :
    endpoint region 20 mismatched = some (some (.ptr (some other)), mismatched) := by
  rfl

def variantEndpoint (storage : Storage CVal) : Option (Option CVal) :=
  match (machine.run 20 (State.mk
      (variantOnlyFromHelpers offsets.toOffsets ReadExpressions.noCalls none (some outcome)) storage [])).2 with
  | .finished (.returned final) => some final.answer.returnedValue?
  | _ => none

theorem variant_only_ignores_that_distinct_cache :
    variantEndpoint mismatched = some (some (.ptr (some atom))) := by decide +kernel

theorem no_unconditional_cache_agreement (region : StatementBlock.AutomaticRegion Context) :
    (endpoint region 20 mismatched).map Prod.fst ≠ variantEndpoint mismatched := by
  rw [a_preexisting_different_cache_is_observable, variant_only_ignores_that_distinct_cache]
  decide

theorem nonzero_values_require_the_real_binding_component
    (region : StatementBlock.AutomaticRegion Context) :
    endpoint region 20 needsBindings = none := rfl

/-- A missing cache cell is a memory fault, not an empty successful value. -/
theorem missing_cache_cell_refuses (region : StatementBlock.AutomaticRegion Context) :
    endpoint region 20 [(outcome.block, ⟨true,
      [some (.u32 0), some (.ptr (some atom)), some (.ptr none)]⟩),
      (atom.block, ⟨true, [some (.u64 77)]⟩)] = none := rfl

/-- A valid already-equal cache returns without executing a replacement store. -/
theorem equal_cache_is_reused_without_a_store (region : StatementBlock.AutomaticRegion Context) :
    endpoint region 20 cached = some (some (.ptr (some atom)), cached) ∧
      writes (machine.run 20 (state region cached)).1 = 0 := by
  constructor <;> rfl

def pausedSnapshot (region : StatementBlock.AutomaticRegion Context) : Option (Storage CVal × Nat) :=
  let partialRun := machine.run 7 (state region initial)
  match partialRun.2 with
  | .exhausted saved => some (saved.storage, writes partialRun.1)
  | _ => none

theorem pause_before_cache_write_keeps_actual_storage (region : StatementBlock.AutomaticRegion Context) :
    pausedSnapshot region = some (initial, 0) := rfl

theorem resumed_tail_does_not_replay_the_cache_store (region : StatementBlock.AutomaticRegion Context) :
    writes (machine.continueRun 13 (machine.run 7 (state region initial))).1 = 1 := by
  rw [← machine.run_add]
  exact actual_tail_writes_the_cache_once region

theorem zero_budget_retains_the_exact_tail (region : StatementBlock.AutomaticRegion Context) :
    machine.run 0 (state region initial) = ([], .exhausted (state region initial)) := rfl

end Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts.NativeOutcomeMaterialization.Full.Controls

end
