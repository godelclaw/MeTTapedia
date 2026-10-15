import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSource

/-!
# Separating witnesses for call-time choice

Concrete equations and their observed answer lists under the three profiles,
computed by the kernel. Every list keeps order and multiplicity.

* `same pick` with `same x = Pair x x` and `pick = A | B`: call-time choice and
  eager evaluation give the two diagonal pairs; run-time choice gives four.
* `pairOf pick pick`: two argument occurrences are two choices under every
  profile.
* The residual discriminator: `rwOnlyA (A x) = OK x`, otherwise the residual
  `RwOnlyA y` holding the argument `y` itself, and
  `rwKeepChoice x = Pair (rwOnlyA x) x`, applied to producers with the
  alternatives `B 1 | B 2`, `B 1 | B 1 | B 2` and `A 3 | B 1 | B 2`: two,
  three and three answers.
* A lazy field: `mkc = S pick`, `unS (S x) = x`, `both v = Pair (unS v) (unS v)`:
  the field is shared, two answers; resampled, four.
* Laziness: `konst x y = x`. An unused failing argument fails eagerly and is
  ignored lazily; an unused choice multiplies eager answers only.
* Strict positions: under each of the three profiles, a primitive applied to an
  equation parameter (`checkAt x = eq (Wrap Num) x`) answers as the primitive
  applied to the term directly, and an activation of a parameter (`act x = *x`)
  runs the code as a direct activation does. Passing the parameter's suspension
  itself to the primitive, or to the activation, changes the answer.* Ignored divergence: `konst A loop` answers `A` under call-time and run-time
  choice; eager evaluation runs the diverging argument and has no observation
  at all (`konstLoop_value_diverges`, from `selfCall_underivable`).
* Held code: `konst A @loop` answers `A` even eagerly, since a quotation is not
  run; `twice @pick` with `twice c = Pair (*c) (*c)` makes two independent
  choices under every profile, against the shared choice of `same pick`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Witnesses

/-! ## Symbols and functions -/

def symA : Nat := 1
def symB : Nat := 2
def symPair : Nat := 3
def symOK : Nat := 4
def symRwOnlyA : Nat := 5
def symS : Nat := 6
def sym1 : Nat := 7
def sym2 : Nat := 8
def sym3 : Nat := 9

def fnPick : Nat := 1
def fnSame : Nat := 2
def fnPairOf : Nat := 3
def fnRwOnlyA : Nat := 4
def fnRwKeepChoice : Nat := 5
def fnSp1 : Nat := 6
def fnSp2 : Nat := 7
def fnSp3 : Nat := 8
def fnMkc : Nat := 9
def fnUnS : Nat := 10
def fnBoth : Nat := 11
def fnKonst : Nat := 12
def fnCheckAt : Nat := 13
def fnAct : Nat := 14

def symWrap : Nat := 10
def symNum : Nat := 11
def symYes : Nat := 12
def symNo : Nat := 13

/-- A constant constructor. -/
def k0 (c : Nat) : Expr := .con c .nil
/-- A unary constructor. -/
def k1 (c : Nat) (e : Expr) : Expr := .con c (.cons e .nil)
/-- A binary constructor. -/
def k2 (c : Nat) (e f : Expr) : Expr := .con c (.cons e (.cons f .nil))
def call0 (f : Nat) : Expr := .call f .nil
def call1 (f : Nat) (e : Expr) : Expr := .call f (.cons e .nil)
def call2 (f : Nat) (e g : Expr) : Expr := .call f (.cons e (.cons g .nil))

/-- The equations. -/
def program : SProgram :=
  [ ⟨fnPick, 0, k0 symA⟩, ⟨fnPick, 0, k0 symB⟩,
    ⟨fnSame, 1, k2 symPair (.var 0) (.var 0)⟩,
    ⟨fnPairOf, 2, k2 symPair (.var 0) (.var 1)⟩,
    ⟨fnRwOnlyA, 1,
      .case (.var 0) symA 1 (k1 symOK (.var 0)) (k1 symRwOnlyA (.var 1))⟩,
    ⟨fnRwKeepChoice, 1, k2 symPair (call1 fnRwOnlyA (.var 0)) (.var 0)⟩,
    ⟨fnSp1, 0, k1 symB (k0 sym1)⟩, ⟨fnSp1, 0, k1 symB (k0 sym2)⟩,
    ⟨fnSp2, 0, k1 symB (k0 sym1)⟩, ⟨fnSp2, 0, k1 symB (k0 sym1)⟩,
    ⟨fnSp2, 0, k1 symB (k0 sym2)⟩,
    ⟨fnSp3, 0, k1 symA (k0 sym3)⟩, ⟨fnSp3, 0, k1 symB (k0 sym1)⟩,
    ⟨fnSp3, 0, k1 symB (k0 sym2)⟩,
    ⟨fnMkc, 0, k1 symS (call0 fnPick)⟩,
    ⟨fnUnS, 1, .case (.var 0) symS 1 (.var 0) .fail⟩,
    ⟨fnBoth, 1, k2 symPair (call1 fnUnS (.var 0)) (call1 fnUnS (.var 0))⟩,
    ⟨fnKonst, 2, .var 0⟩,
    ⟨fnCheckAt, 1, .prim (.eq symYes symNo) (.cons (k1 symWrap (k0 symNum)) (.cons (.var 0) .nil))⟩,
    ⟨fnAct, 1, .activate (.var 0)⟩ ]

/-! ## Expected answers -/

def vA : Val Nat := term symA []
def vB : Val Nat := term symB []
def pair (x y : Val Nat) : Val Nat := term symPair [x, y]
def num (c : Nat) : Val Nat := term c []
def vBn (c : Nat) : Val Nat := term symB [num c]
def vAn (c : Nat) : Val Nat := term symA [num c]
def residual (x : Val Nat) : Val Nat := term symRwOnlyA [x]
def okv (x : Val Nat) : Val Nat := term symOK [x]

def samePick : Expr := call1 fnSame (call0 fnPick)
def pairPickPick : Expr := call2 fnPairOf (call0 fnPick) (call0 fnPick)
def keep (producer : Nat) : Expr := call1 fnRwKeepChoice (call0 producer)
def bothMkc : Expr := call1 fnBoth (call0 fnMkc)
def konstFail : Expr := call2 fnKonst (k0 symA) .fail
def konstPick : Expr := call2 fnKonst (k0 symA) (call0 fnPick)

/-! ## `same pick` -/

theorem samePick_need :
    sourceValues .need program 60 samePick = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem samePick_value :
    sourceValues .value program 60 samePick = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem samePick_name :
    sourceValues .name program 60 samePick =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

/-! ## Two occurrences are two choices -/

theorem pairPickPick_need :
    sourceValues .need program 60 pairPickPick =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

theorem pairPickPick_value :
    sourceValues .value program 60 pairPickPick =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

/-! ## The residual discriminator: 2, 3 and 3 answers -/

theorem keep1_need :
    sourceValues .need program 80 (keep fnSp1) =
      some [pair (residual (vBn sym1)) (vBn sym1), pair (residual (vBn sym2)) (vBn sym2)] := by
  decide +kernel

theorem keep2_need :
    sourceValues .need program 80 (keep fnSp2) =
      some [pair (residual (vBn sym1)) (vBn sym1), pair (residual (vBn sym1)) (vBn sym1),
        pair (residual (vBn sym2)) (vBn sym2)] := by
  decide +kernel

theorem keep3_need :
    sourceValues .need program 80 (keep fnSp3) =
      some [pair (okv (num sym3)) (vAn sym3), pair (residual (vBn sym1)) (vBn sym1),
        pair (residual (vBn sym2)) (vBn sym2)] := by
  decide +kernel

theorem keep1_value :
    sourceValues .value program 80 (keep fnSp1) =
      some [pair (residual (vBn sym1)) (vBn sym1), pair (residual (vBn sym2)) (vBn sym2)] := by
  decide +kernel

/-- Run-time choice reruns the argument at the match, at the residual's field and
at the pair's second field: eight answers. -/
theorem keep1_name_length :
    (sourceValues .name program 80 (keep fnSp1)).map List.length = some 8 := by
  decide +kernel

/-! ## A lazy field -/

theorem bothMkc_need :
    sourceValues .need program 80 bothMkc = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem bothMkc_name :
    sourceValues .name program 80 bothMkc =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

/-! ## Laziness -/

theorem konstFail_need : sourceValues .need program 40 konstFail = some [vA] := by
  decide +kernel

theorem konstFail_name : sourceValues .name program 40 konstFail = some [vA] := by
  decide +kernel

theorem konstFail_value : sourceValues .value program 40 konstFail = some [] := by
  decide +kernel

theorem konstPick_need : sourceValues .need program 40 konstPick = some [vA] := by
  decide +kernel

theorem konstPick_value : sourceValues .value program 40 konstPick = some [vA, vA] := by
  decide +kernel

/-! ## Strict positions: parameters, direct terms and leaked suspensions -/

def wrapNum : Expr := k1 symWrap (k0 symNum)
def checkAtParam : Expr := call1 fnCheckAt wrapNum
def checkAtDirect : Expr := .prim (.eq symYes symNo) (.cons wrapNum (.cons wrapNum .nil))
def actParam : Expr := call1 fnAct (.quote (k1 symS (k0 symA)))
def actDirect : Expr := .activate (.quote (k1 symS (k0 symA)))

theorem checkAtParam_need :
    sourceValues .need program 60 checkAtParam = some [.sym symYes] := by
  decide +kernel

theorem checkAtDirect_need :
    sourceValues .need program 60 checkAtDirect = some [.sym symYes] := by
  decide +kernel

theorem actParam_need :
    sourceValues .need program 60 actParam = some [term symS [vA]] := by
  decide +kernel

theorem actDirect_need :
    sourceValues .need program 60 actDirect = some [term symS [vA]] := by
  decide +kernel

/-- The same answers when the parameter is bound eagerly or resampled. -/
theorem checkAtParam_value :
    sourceValues .value program 60 checkAtParam = some [.sym symYes] := by
  decide +kernel

theorem checkAtParam_name :
    sourceValues .name program 60 checkAtParam = some [.sym symYes] := by
  decide +kernel

theorem actParam_value :
    sourceValues .value program 60 actParam = some [term symS [vA]] := by
  decide +kernel

theorem actParam_name :
    sourceValues .name program 60 actParam = some [term symS [vA]] := by
  decide +kernel

/-- A primitive that receives the parameter's suspension instead of its normal
form: the head `100` compares the term with its argument as given. -/
def leakyProgram : Program :=
  program.toCore .need ++
    [⟨100, 1, .prim (.eq symYes symNo) [.app (.sym symWrap) (.sym symNum), .var 0]⟩,
     ⟨101, 1, .run (.var 0)⟩]

/-- The argument is passed as a memoized suspension, as an equation call does. -/
def leakyCheckAt : Comp := .need (wrapNum.toCore .need id) (.call 100 [.var 0])
def leakyAct : Comp :=
  .need ((Expr.quote (k1 symS (k0 symA))).toCore .need id) (.call 101 [.var 0])

theorem leakyCheckAt_refutes : observeValues leakyProgram 60 leakyCheckAt = some [.sym symNo] := by
  decide +kernel

/-- Activating the suspension itself leaves a residual instead of running the code. -/
theorem leakyAct_residual :
    observeValues leakyProgram 60 leakyAct ≠ some [term symS [vA]] := by
  decide +kernel


/-! ## A core witness program

The witnesses of the sharing policies and of the transport controls, written
directly in the core: equations with explicit forcing, called with closed
argument computations. -/

namespace Core

def symA : Nat := 1
def symB : Nat := 2
def symPair : Nat := 3
def symOK : Nat := 4
def symResidual : Nat := 5
def sym1 : Nat := 7
def sym2 : Nat := 8
def sym3 : Nat := 9

def fPick : Nat := 1
def fSame : Nat := 2
def fPairOf : Nat := 3
def fRwOnlyA : Nat := 4
def fKeep : Nat := 5
def fSp1 : Nat := 6
def fSp2 : Nat := 7
def fSp3 : Nat := 8
def fTwoWay : Nat := 9

def pairE (a b : VExp) : VExp := .app (.app (.sym symPair) a) b
def taggedE (c n : Nat) : VExp := .app (.sym c) (.sym n)

/-- `pick = A | B`; `same x = Pair x x`; `pairOf x y = Pair x y`; the residual
discriminator `rwOnlyA (A n) = OK n`, otherwise `Residual v` with the forced
argument `v`, and `keep x = Pair (rwOnlyA x) x`, applied to the producers
`B 1 | B 2`, `B 1 | B 1 | B 2` and `A 3 | B 1 | B 2`; `twoWay` has two
candidate equations, `Pair x x` and `Pair x A`. -/
def program : Program :=
  [ ⟨fPick, 0, .ret (.sym symA)⟩, ⟨fPick, 0, .ret (.sym symB)⟩,
    ⟨fSame, 1, .ret (pairE (.var 0) (.var 0))⟩,
    ⟨fPairOf, 2, .ret (pairE (.var 0) (.var 1))⟩,
    ⟨fRwOnlyA, 1, .seq (.force (.var 0))
        (.caseCon (.var 0) symA 1 (.ret (.app (.sym symOK) (.var 0)))
          (.ret (.app (.sym symResidual) (.var 0))))⟩,
    ⟨fKeep, 1, .seq (.call fRwOnlyA [.var 0]) (.ret (pairE (.var 0) (.var 1)))⟩,
    ⟨fSp1, 0, .ret (taggedE symB sym1)⟩, ⟨fSp1, 0, .ret (taggedE symB sym2)⟩,
    ⟨fSp2, 0, .ret (taggedE symB sym1)⟩, ⟨fSp2, 0, .ret (taggedE symB sym1)⟩,
    ⟨fSp2, 0, .ret (taggedE symB sym2)⟩,
    ⟨fSp3, 0, .ret (taggedE symA sym3)⟩, ⟨fSp3, 0, .ret (taggedE symB sym1)⟩,
    ⟨fSp3, 0, .ret (taggedE symB sym2)⟩,
    ⟨fTwoWay, 1, .ret (pairE (.var 0) (.var 0))⟩,
    ⟨fTwoWay, 1, .ret (pairE (.var 0) (.sym symA))⟩ ]

def pickC : Comp := .call fPick []

def vA : Val Nat := .sym symA
def vB : Val Nat := .sym symB
def pair (x y : Val Nat) : Val Nat := .app (.app (.sym symPair) x) y
def tagged (c n : Nat) : Val Nat := .app (.sym c) (.sym n)
def residual (x : Val Nat) : Val Nat := .app (.sym symResidual) x

end Core

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Witnesses

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-- A call whose only equation calls itself again has no derivation, from any
store and environment; neither has a dispatch whose first alternative is that
call.  Derivations are finite, and such a goal can only be derived from
itself. -/
theorem selfCall_underivable {P : Program} {f : Nat}
    (only : candidates P f 0 = [⟨f, 0, .call f []⟩]) :
    ∀ {g : Goal} {L : List Result}, Derives P g L →
      (∀ σ ρ, g ≠ .eval σ ρ (.call f [])) ∧
      (∀ σ ρ rest, g ≠ .alts σ ((.call f [], ρ) :: rest)) := by
  intro g L h
  induction h
  case call σ ρ f' args L' _ _ ih =>
    refine ⟨fun σ' ρ' equal => ?_, fun _ _ _ equal => (by cases equal)⟩
    cases equal
    have := ih.2 σ [] []
    simp [only] at this
  case callNone σ ρ f' args none =>
    refine ⟨fun σ' ρ' equal => ?_, fun _ _ _ equal => (by cases equal)⟩
    cases equal
    simp [only] at none
  case altsCons σ m ρ bs L₁ L₂ _ _ ihHead _ =>
    refine ⟨fun _ _ equal => (by cases equal), fun σ' ρ' rest equal => ?_⟩
    cases equal
    exact ihHead.1 σ ρ rfl
  all_goals exact ⟨fun _ _ equal => (by cases equal), fun _ _ _ equal => (by cases equal)⟩

namespace Witnesses

/-! ## Ignored divergence, held syntax and resampled code -/

def fnLoop : Nat := 15
def fnTwice : Nat := 16

/-- The witness equations with a diverging call `loop = loop` and
`twice c = Pair (*c) (*c)`. -/
def programExt : SProgram :=
  program ++ [⟨fnLoop, 0, call0 fnLoop⟩,
    ⟨fnTwice, 1, k2 symPair (.activate (.var 0)) (.activate (.var 0))⟩]

/-- `konst A loop`: an unused argument that diverges. -/
def konstLoop : Expr := call2 fnKonst (k0 symA) (call0 fnLoop)

/-- `konst A @loop`: the same argument as held code. -/
def konstHeldLoop : Expr := call2 fnKonst (k0 symA) (.quote (call0 fnLoop))

/-- `twice @pick`: code activated twice. -/
def twicePick : Expr := call1 fnTwice (.quote (call0 fnPick))

/-- `same @pick`: held code shared, never run. -/
def sameHeldPick : Expr := call1 fnSame (.quote (call0 fnPick))

/-- Under call-time choice the unused diverging argument is never run. -/
theorem konstLoop_need : sourceValues .need programExt 60 konstLoop = some [vA] := by
  decide +kernel

/-- Under run-time choice too. -/
theorem konstLoop_name : sourceValues .name programExt 60 konstLoop = some [vA] := by
  decide +kernel

theorem loop_candidates :
    candidates (observed (programExt.toCore .value)) (fnLoop + 1) 0 =
      [⟨fnLoop + 1, 0, .call (fnLoop + 1) []⟩] := by
  decide

/-- **Eager evaluation runs the unused argument, so it has no observation at all.** -/
theorem konstLoop_toCore_value :
    konstLoop.toCore .value id =
      .seq (.ret (.sym symA))
        (.seq (.call (fnLoop + 1) []) (.call (fnKonst + 1) [.var 1, .var 0])) := by
  decide

/-- **Eager evaluation runs the unused argument, so it has no observation at all.** -/
theorem konstLoop_value_diverges (L : List Result) :
    ¬ SourceObserves .value programExt konstLoop L := by
  intro h
  unfold SourceObserves Observes observe at h
  rw [konstLoop_toCore_value] at h
  cases h with
  | seq whole _ =>
    cases whole with
    | seq first rest =>
      cases first
      cases rest with
      | seqKOk tail _ =>
        cases tail with
        | seq loop _ => exact (selfCall_underivable loop_candidates loop).1 _ _ rfl
      | seqKStop stop _ => simp [Outcome.isOk] at stop

/-- Held code is not run, even eagerly: the diverging argument is harmless. -/
theorem konstHeldLoop_value : sourceValues .value programExt 60 konstHeldLoop = some [vA] := by
  decide +kernel

/-- Each activation runs the code afresh: two independent choices, under every
profile, against the two shared ones of `same pick`. -/
theorem twicePick_need :
    sourceValues .need programExt 80 twicePick =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

theorem twicePick_value :
    sourceValues .value programExt 80 twicePick =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

/-- Held code that is never activated is one answer that makes no choice. -/
theorem sameHeldPick_need :
    (sourceValues .need programExt 60 sameHeldPick).map List.length = some 1 := by
  decide +kernel

end Witnesses

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
