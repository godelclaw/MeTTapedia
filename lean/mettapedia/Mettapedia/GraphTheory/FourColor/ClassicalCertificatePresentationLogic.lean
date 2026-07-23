import Mathlib.Data.List.Basic

/-!
# A reflection kernel for finite unavoidability presentations

The classical unavoidability argument repeatedly splits a local face-size
pattern.  Its leaves are closed either by a reducible configuration, by a
discharging bound, or by symmetry with a pattern already closed earlier in
the same branch.  This file isolates the propositional logic of that
calculation from the concrete representation of patterns.

`PresentationCode` is deliberately small.  All mathematical content lives in
a `Backend`: Boolean checks for leaves, splits, and similarities, together
with proofs that accepted checks have their intended semantics.  The main
soundness theorem then turns an accepted finite presentation into the
nonexistence of a valid hub fitting its root pattern.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationLogic

universe u v w x y

/-- Semantic interpretation of local patterns around candidate hubs. -/
structure Semantics (Hub : Type u) (Pattern : Type v) where
  valid : Hub → Prop
  fits : Hub → Pattern → Prop

namespace Semantics

variable {Hub : Type u} {Pattern : Type v}

/-- No valid hub fits the given pattern. -/
def Successful (semantics : Semantics Hub Pattern) (pattern : Pattern) : Prop :=
  ∀ hub, semantics.valid hub → ¬ semantics.fits hub pattern

/-- Every valid hub fitting `source` also fits `target`. -/
def Forces (semantics : Semantics Hub Pattern)
    (source target : Pattern) : Prop :=
  ∀ hub, semantics.valid hub →
    semantics.fits hub source → semantics.fits hub target

/-- The presentation judgment used by the classical split scripts. -/
def SucceedsIn (semantics : Semantics Hub Pattern)
    (context pattern : Pattern) : Prop :=
  semantics.Forces context pattern → semantics.Successful pattern

/-- Forcing is reflexive. -/
theorem forces_refl (semantics : Semantics Hub Pattern) (pattern : Pattern) :
    semantics.Forces pattern pattern := by
  intro hub hvalid hfits
  exact hfits

/-- Failure of a forced target propagates back to its source. -/
theorem successful_of_forces
    (semantics : Semantics Hub Pattern) {source target : Pattern}
    (hforces : semantics.Forces source target)
    (htarget : semantics.Successful target) :
    semantics.Successful source := by
  intro hub hvalid hsource
  exact htarget hub hvalid (hforces hub hvalid hsource)

/-- A direct successful-pattern proof closes any presentation context. -/
theorem succeedsIn_of_successful
    (semantics : Semantics Hub Pattern) {context pattern : Pattern}
    (hsuccessful : semantics.Successful pattern) :
    semantics.SucceedsIn context pattern := by
  intro _hforces
  exact hsuccessful

/-- Two successful patterns close any pattern covered by their union. -/
theorem successful_of_binary_cover
    (semantics : Semantics Hub Pattern)
    {pattern left right : Pattern}
    (hcover : ∀ hub, semantics.valid hub → semantics.fits hub pattern →
      semantics.fits hub left ∨ semantics.fits hub right)
    (hleft : semantics.Successful left)
    (hright : semantics.Successful right) :
    semantics.Successful pattern := by
  intro hub hvalid hpattern
  rcases hcover hub hvalid hpattern with hfitsLeft | hfitsRight
  · exact hleft hub hvalid hfitsLeft
  · exact hright hub hvalid hfitsRight

end Semantics

/-- The three patterns computed at a split.  The left branch is proved in
`leftContext`; its success is retained while checking the right branch in the
original context. -/
structure SplitResult (Pattern : Type v) where
  leftContext : Pattern
  left : Pattern
  right : Pattern

/-- A compact finite presentation program.  Similarity nodes name a pattern
already proved successful in the current branch. -/
inductive PresentationCode
    (Pattern : Type v) (Leaf : Type w) (Split : Type x)
    (Similarity : Type y) where
  | terminal (leaf : Leaf)
  | similar (depth : Nat) (similarity : Similarity)
  | split (retainLeft : Bool) (split : Split)
      (left right : PresentationCode Pattern Leaf Split Similarity)

/-- Concrete Boolean operations and their semantic correctness theorems. -/
structure Backend
    (Hub : Type u) (Pattern : Type v) (Leaf : Type w) (Split : Type x)
    (Similarity : Type y) where
  semantics : Semantics Hub Pattern
  leafCheck : Leaf → Pattern → Bool
  leaf_sound : ∀ {leaf pattern}, leafCheck leaf pattern = true →
    semantics.Successful pattern
  splitResult : Pattern → Pattern → Split → SplitResult Pattern
  splitCheck : Pattern → Pattern → Split → Bool
  split_cover : ∀ {context pattern split},
    splitCheck context pattern split = true →
      ∀ hub, semantics.valid hub → semantics.fits hub pattern →
        semantics.fits hub (splitResult context pattern split).left ∨
          semantics.fits hub (splitResult context pattern split).right
  split_left_forces : ∀ {context pattern split},
    splitCheck context pattern split = true →
      semantics.Forces context pattern →
        semantics.Forces
          (splitResult context pattern split).leftContext
          (splitResult context pattern split).left
  similarityCheck : Similarity → Pattern → Pattern → Bool
  similarity_sound : ∀ {similarity known pattern},
    similarityCheck similarity known pattern = true →
      semantics.Successful known → semantics.Successful pattern

section Checker

variable {Hub : Type u} {Pattern : Type v} {Leaf : Type w} {Split : Type x}
  {Similarity : Type y}

/-- Execute a presentation in a branch context of already successful
patterns.  A split adds its left context only while checking the right
subtree, matching the dependency discipline of presentation scripts. -/
def check
    (backend : Backend Hub Pattern Leaf Split Similarity)
    (known : List Pattern) (context pattern : Pattern) :
    PresentationCode Pattern Leaf Split Similarity → Bool
  | .terminal leaf => backend.leafCheck leaf pattern
  | .similar depth similarity =>
      match known[depth]? with
      | none => false
      | some previous =>
          backend.similarityCheck similarity previous pattern
  | .split retainLeft split leftCode rightCode =>
      let result := backend.splitResult context pattern split
      backend.splitCheck context pattern split &&
        (check backend known result.leftContext result.left leftCode &&
          check backend (if retainLeft then result.leftContext :: known else known)
            context result.right rightCode)

/-- Soundness of the finite presentation checker. -/
theorem check_sound
    (backend : Backend Hub Pattern Leaf Split Similarity)
    {known : List Pattern} {context pattern : Pattern}
    {code : PresentationCode Pattern Leaf Split Similarity}
    (hknown : ∀ previous, previous ∈ known →
      backend.semantics.Successful previous)
    (hcheck : check backend known context pattern code = true) :
    backend.semantics.SucceedsIn context pattern := by
  induction code generalizing known context pattern with
  | terminal leaf =>
      exact backend.semantics.succeedsIn_of_successful
        (backend.leaf_sound hcheck)
  | similar depth similarity =>
      cases hlookup : known[depth]? with
      | none => simp [check, hlookup] at hcheck
      | some previous =>
          have hsimilar :
              backend.similarityCheck similarity previous pattern = true := by
            simpa [check, hlookup] using hcheck
          have hprevious : backend.semantics.Successful previous := by
            apply hknown previous
            exact List.mem_iff_getElem?.2 ⟨depth, hlookup⟩
          exact backend.semantics.succeedsIn_of_successful
            (backend.similarity_sound hsimilar hprevious)
  | split retainLeft split leftCode rightCode ihLeft ihRight =>
      let result := backend.splitResult context pattern split
      have htriple :
          (backend.splitCheck context pattern split &&
              (check backend known result.leftContext result.left leftCode &&
                check backend
                  (if retainLeft then result.leftContext :: known else known)
                  context result.right rightCode)) = true := by
        simpa [check, result] using hcheck
      rcases Bool.and_eq_true_iff.mp htriple with ⟨hsplit, hchildren⟩
      rcases Bool.and_eq_true_iff.mp hchildren with
        ⟨hleftCheck, hrightCheck⟩
      intro hcontextPattern
      have hleftForces :
          backend.semantics.Forces result.leftContext result.left := by
        exact backend.split_left_forces hsplit hcontextPattern
      have hleftSuccessful : backend.semantics.Successful result.left :=
        (ihLeft hknown hleftCheck) hleftForces
      have hleftContextSuccessful :
          backend.semantics.Successful result.leftContext :=
        backend.semantics.successful_of_forces
          hleftForces hleftSuccessful
      have hknownRight : ∀ previous,
          previous ∈ (if retainLeft then result.leftContext :: known else known) →
            backend.semantics.Successful previous := by
        intro previous hmem
        cases retainLeft
        · exact hknown previous (by simpa using hmem)
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · exact hleftContextSuccessful
          · exact hknown previous hmem
      have hcontextRight :
          backend.semantics.Forces context result.right := by
        intro hub hvalid hcontext
        have hpattern := hcontextPattern hub hvalid hcontext
        rcases backend.split_cover hsplit hub hvalid hpattern with
          hleft | hright
        · exact False.elim (hleftSuccessful hub hvalid hleft)
        · exact hright
      have hrightSuccessful : backend.semantics.Successful result.right :=
        (ihRight hknownRight hrightCheck) hcontextRight
      exact backend.semantics.successful_of_binary_cover
        (backend.split_cover hsplit) hleftSuccessful hrightSuccessful

/-- An accepted root presentation excludes every valid hub matching its root
pattern. -/
theorem successful_of_check_root
    (backend : Backend Hub Pattern Leaf Split Similarity)
    (root : Pattern) (code : PresentationCode Pattern Leaf Split Similarity)
    (hcheck : check backend [] root root code = true) :
    backend.semantics.Successful root := by
  have hknown : ∀ previous, previous ∈ ([] : List Pattern) →
      backend.semantics.Successful previous := by
    intro previous hmem
    exact False.elim (by simpa using hmem)
  exact (check_sound backend hknown hcheck)
    (backend.semantics.forces_refl root)

end Checker

end ClassicalCertificatePresentationLogic

end Mettapedia.GraphTheory.FourColor
