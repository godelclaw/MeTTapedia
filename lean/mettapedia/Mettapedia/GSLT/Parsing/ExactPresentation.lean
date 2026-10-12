import Mathlib.Data.Option.Basic

/-!
# Exact presentations of one sorted abstract syntax

An expansion is partial because a surface can be malformed. A view is total
on the abstract syntax and is a section of expansion. Surface spelling need
not survive a round trip: normalization selects the presentation's own view.
Conversion preserves the abstract syntax tree, including refusal, and composition
does not depend on an intermediate presentation.

The records describe structural interpreters. They do not identify a host
reader with a source lexer, establish native parser correctness, or provide
operational semantics for the represented language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ExactPresentation

universe uSort uAst uSurface uOther uThird uObservation

structure Key where
  name : String
  version : Nat
  deriving DecidableEq, Repr

/-- The sort index belongs to the abstract syntax, independently of the
chosen presentation. The section law is a required obligation, not an axiom. -/
structure Presentation {SortName : Type uSort}
    (Ast : SortName → Type uAst) (Surface : SortName → Type uSurface) where
  key : Key
  expand : {sort : SortName} → Surface sort → Option (Ast sort)
  view : {sort : SortName} → Ast sort → Surface sort
  expand_view : ∀ {sort : SortName} (tree : Ast sort), expand (view tree) = some tree

variable {SortName : Type uSort}
variable {Ast : SortName → Type uAst} {Surface : SortName → Type uSurface}
variable {Other : SortName → Type uOther} {Third : SortName → Type uThird}

def normalize (presentation : Presentation Ast Surface) {sort : SortName}
    (surface : Surface sort) : Option (Surface sort) :=
  (presentation.expand surface).map presentation.view

def convert (source : Presentation Ast Surface)
    (target : Presentation Ast Other) {sort : SortName}
    (surface : Surface sort) : Option (Other sort) :=
  (source.expand surface).map target.view

structure Document {SortName : Type uSort} (Surface : SortName → Type uSurface)
    (sort : SortName) where
  key : Key
  body : Surface sort

/-- A document names its interpreter version. New abbreviations do not
silently change the interpretation of a document naming an older version. -/
def expandDocument (presentation : Presentation Ast Surface) {sort : SortName}
    (document : Document Surface sort) : Option (Ast sort) :=
  if document.key = presentation.key then presentation.expand document.body else none

def viewDocument (presentation : Presentation Ast Surface) {sort : SortName}
    (tree : Ast sort) : Document Surface sort :=
  ⟨presentation.key, presentation.view tree⟩

@[simp] theorem expand_viewDocument (presentation : Presentation Ast Surface)
    {sort : SortName} (tree : Ast sort) :
    expandDocument presentation (viewDocument presentation tree) = some tree := by
  simp [expandDocument, viewDocument, presentation.expand_view]

theorem expandDocument_wrong_key (presentation : Presentation Ast Surface)
    {sort : SortName} (document : Document Surface sort)
    (mismatch : document.key ≠ presentation.key) :
    expandDocument presentation document = none := by
  simp [expandDocument, mismatch]

@[simp] theorem normalize_view (presentation : Presentation Ast Surface)
    {sort : SortName} (tree : Ast sort) :
    normalize presentation (presentation.view tree) = some (presentation.view tree) := by
  simp [normalize, presentation.expand_view]

@[simp] theorem expand_normalize (presentation : Presentation Ast Surface)
    {sort : SortName} (surface : Surface sort) :
    (normalize presentation surface).bind presentation.expand = presentation.expand surface := by
  cases expanded : presentation.expand surface <;>
    simp [normalize, expanded, presentation.expand_view]

theorem normalize_idempotent (presentation : Presentation Ast Surface)
    {sort : SortName} (surface : Surface sort) :
    (normalize presentation surface).bind (normalize presentation) =
      normalize presentation surface := by
  cases expanded : presentation.expand surface <;>
    simp [normalize, expanded, presentation.expand_view]

theorem normalize_of_same_tree (presentation : Presentation Ast Surface)
    {sort : SortName} (first second : Surface sort)
    (same : presentation.expand first = presentation.expand second) :
    normalize presentation first = normalize presentation second := by
  simp only [normalize, same]

@[simp] theorem convert_view (source : Presentation Ast Surface)
    (target : Presentation Ast Other) {sort : SortName} (tree : Ast sort) :
    convert source target (source.view tree) = some (target.view tree) := by
  simp [convert, source.expand_view]

/-- Successful conversion preserves the complete abstract syntax tree; invalid
source forms remain invalid rather than acquiring an invented meaning. -/
@[simp] theorem expand_convert (source : Presentation Ast Surface)
    (target : Presentation Ast Other) {sort : SortName} (surface : Surface sort) :
    (convert source target surface).bind target.expand = source.expand surface := by
  cases expanded : source.expand surface <;>
    simp [convert, expanded, target.expand_view]

theorem convert_comp (source : Presentation Ast Surface)
    (middle : Presentation Ast Other) (target : Presentation Ast Third)
    {sort : SortName} (surface : Surface sort) :
    (convert source middle surface).bind (convert middle target) =
      convert source target surface := by
  cases expanded : source.expand surface <;>
    simp [convert, expanded, middle.expand_view]

/-- Returning to a presentation selects its normal form, not necessarily
the original spelling. -/
theorem convert_back (source : Presentation Ast Surface)
    (target : Presentation Ast Other) {sort : SortName} (surface : Surface sort) :
    (convert source target surface).bind (convert target source) = normalize source surface := by
  simpa only [convert, normalize] using convert_comp source target source surface

theorem convert_refuses_iff (source : Presentation Ast Surface)
    (target : Presentation Ast Other) {sort : SortName} (surface : Surface sort) :
    convert source target surface = none ↔ source.expand surface = none := by
  cases expanded : source.expand surface <;> simp [convert, expanded]

/-- Any separately defined observation of the abstract syntax tree survives
conversion. This does not supply or prove a C execution observation. -/
theorem convert_observation {Observation : Type uObservation}
    (source : Presentation Ast Surface) (target : Presentation Ast Other)
    {sort : SortName} (observe : Ast sort → Observation) (surface : Surface sort) :
    ((convert source target surface).bind target.expand).map observe =
      (source.expand surface).map observe := by
  rw [expand_convert]

/-- An arbitrary abbreviation may be wrong. It is used only after its
expansion is compared with the original abstract syntax tree. -/
def checkedChoice {Tree : Type uAst} {Form : Type uSurface} [DecidableEq Tree]
    (expand : Form → Option Tree) (fallback : Form) (candidate : Option Form)
    (tree : Tree) : Form :=
  match candidate with
  | none => fallback
  | some proposed => if expand proposed = some tree then proposed else fallback

theorem checkedChoice_exact {Tree : Type uAst} {Form : Type uSurface}
    [DecidableEq Tree] (expand : Form → Option Tree) (fallback : Form)
    (candidate : Option Form) (tree : Tree) (exactFallback : expand fallback = some tree) :
    expand (checkedChoice expand fallback candidate tree) = some tree := by
  cases candidate with
  | none => exact exactFallback
  | some proposed =>
      by_cases exactCandidate : expand proposed = some tree
      · simp [checkedChoice, exactCandidate]
      · simpa [checkedChoice, exactCandidate] using exactFallback

theorem checkedChoice_uses_exact {Tree : Type uAst} {Form : Type uSurface}
    [DecidableEq Tree] (expand : Form → Option Tree) (fallback proposed : Form)
    (tree : Tree) (exactCandidate : expand proposed = some tree) :
    checkedChoice expand fallback (some proposed) tree = proposed := by
  simp [checkedChoice, exactCandidate]

theorem checkedChoice_rejects_changed_tree {Tree : Type uAst} {Form : Type uSurface}
    [DecidableEq Tree] (expand : Form → Option Tree) (fallback proposed : Form)
    (tree other : Tree) (changed : tree ≠ other) (expanded : expand proposed = some other) :
    checkedChoice expand fallback (some proposed) tree = fallback := by
  simp [checkedChoice, expanded, Ne.symm changed]

theorem checkedChoice_rejects_invalid {Tree : Type uAst} {Form : Type uSurface}
    [DecidableEq Tree] (expand : Form → Option Tree) (fallback proposed : Form)
    (tree : Tree) (invalid : expand proposed = none) :
    checkedChoice expand fallback (some proposed) tree = fallback := by
  simp [checkedChoice, invalid]

end Mettapedia.GSLT.Parsing.ExactPresentation
