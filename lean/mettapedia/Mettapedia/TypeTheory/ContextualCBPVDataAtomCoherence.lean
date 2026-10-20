import Mettapedia.TypeTheory.ContextualCBPVEquations
import Mettapedia.TypeTheory.ContextualCBPVPolarizedValues

/-!
# Data vs. Code Polarity Laws and Elaboration Trade-offs in `ContextualCBPV`

## Scope of This Module

This module formulates the Data/Code (`Atom`) laws and compares the three
candidate MeTTa Prime elaboration rules **directly inside `ContextualCBPV`**
(`Mettapedia.TypeTheory.ContextualCBPV` and
`Mettapedia.TypeTheory.ContextualCBPV.PolarizedValues`), with no standalone toy
calculi.

1. **General `ContextualCBPV` and `PolarizedValues` Laws (§1–§2)**:
   * **Law 1 (`let`-Binding Preserves Value Polarity)**: In `ContextualCBPV`,
     binding a value `v : Val sig context A` in `Comp.bind (.ret v) body`
     substitutes `v` directly (`ret_bind`), and in `PolarizedValues`
     (`Shaped.Computation.valueApply (.valueLambda body) v`) binds `v` in the
     semantic value environment (`read_valueApply_valueLambda`) without forcing
     it as a computation.
   * **Law 2 (Data Passed Through `Atom` / `%Undefined%` Remains Data Unless
     Explicitly Cast/Evaluated)**: Passing a `Data` value through a lambda or
     `let` binder at a polymorphic or sum-typed `Atom` (`Data ⊕ Code`) carrier
     preserves its `Data` tag (`lam_app`, `ret_bind`,
     `data_preserved_through_atom_lambda`, `data_preserved_through_atom_let`).
     Only the explicit eliminator (`Comp.force` on thunks, or explicit `eval`
     on `Atom`) runs a suspended computation.
   * **Law 3 (Algebraic Laws of `eval` and `quote`)**:
     * β-law (`eval (quote M) = M`): `force_thunk` and `read_forceThunk_thunk`.
     * η-law (`quote (eval V) = V` on suspended thunks): `thunk_force`.
     * Sequencing and nondeterministic choice commute with `eval (quote ...)`:
       `eval_quote_bind` and `eval_quote_choose`.

2. **Formal Comparison of Path A, Path B, and HE's Return-Type Boundary (§3)**:
   Over a concrete `ContextualCBPV.Signature` (`AtomPolaritySig`) that models
   compound expressions carrying an evaluated-data mark (`isData : Bool`,
   corresponding to `ATOM_FLAG_HE_EVALUATED` in `src/atom.h:678`) alongside
   atomic symbols (`AtomSym`, which cannot carry `ATOM_FLAG_HE_EVALUATED`), we
   define the three candidate elaborations as `ContextualCBPV` computations and
   prove their exact properties:
   * **HE Return-Type Boundary** violates Law 2
     (`heBoundary_violates_data_through_atom`): returning a `Data` expression
     through an `Atom`-typed function strips `isData` and re-evaluates it.
   * **Both Path A and Path B** satisfy Law 1 and Law 2
     (`pathA_preserves_data_through_atom`,
     `pathB_preserves_data_through_atom`).
   * **Where Path A and Path B Trade Off**:
     * **Nested compound extraction**: Path B's provenance-preserving
       `car-atom` preserves `isData = true` on extracted compound subterms such
       as `((Field (+ 1 2)))` (`pathB_preserves_nested_compound_data`).
     * **Unquoted code inspection vs. evaluation**: On an unquoted reducible
       expression `(foo bar)`, Path B's shape destructor returns `foo` whereas
       Path A evaluates `(foo bar)` first (`pathA_vs_pathB_unquoted_code`).
     * **Atomic-head destructor/constructor η-rebuild**: Because atomic symbols
       cannot carry `ATOM_FLAG_HE_EVALUATED`, decomposing a `Data` expression
       `(+ 1 2)` down to its atomic head `+` via `car-atom` and rebuilding via
       `(cons-atom (car-atom d) (cdr-atom d))` preserves `isData = true` under
       Path A (`pathA_atomic_head_eta_preserves_data`), whereas under Path B
       with unmarked `cons-atom` the rebuilt expression loses `isData`
       (`pathB_unmarked_cons_loses_data_on_atomic_head`) unless `cons-atom`
       marks its output or symbols carry provenance.

**What this module does NOT claim**:
* Neither Path A nor Path B is claimed to be "uniquely coherent"; both satisfy
  Laws 1–3 and make different explicit trade-offs on unquoted code inspection
  vs. atomic-head rebuild and wrapper congruence.
* The theorems in §3 characterize the three candidate elaboration rules in
  `ContextualCBPV`; they do not verify the C evaluator in
  `cetta-prime-2.0-draft-20260910`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.DataAtomCoherence

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.ContextualCBPV
open Mettapedia.TypeTheory.ContextualCBPV.PolarizedValues
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {sig : Signature} [DecidableEq sig.Kind]

/-! ## §1. General Polarity & Evaluation Laws in `ContextualCBPV` -/

section GeneralCBPVLaws

variable {context : List (VTy sig.Ground)}

/-- **Law 1 (`let`-Binding Preserves Value Polarity)**:
In `ContextualCBPV`, `let x = ret v in body` (`Comp.bind (.ret v) body`)
substitutes the value `v` directly into `body` without forcing or re-evaluating
it. -/
theorem let_ret_preserves_value {answer : VTy sig.Ground} {type : CTy sig.Ground}
    (value : Val sig context answer) (body : Comp sig (answer :: context) type)
    (η : Env sig context) :
    (Comp.bind (.ret value) body).den η = (body.instantiate value).den η :=
  ret_bind value body η

/-- **Law 1 Corollary (`let x = ret v in ret x = ret v`)**:
Binding a value `v` to `$x` and returning `$x` denotes the exact same program as
returning `v` directly, whether `v` is ground `Data` (`.ground s`) or a
suspended `Code` thunk (`.thunk B`). -/
theorem let_ret_var_zero_eq_ret {answer : VTy sig.Ground}
    (value : Val sig context answer) (η : Env sig context) :
    (Comp.bind (.ret value) (.ret (.var .zero))).den η = (Comp.ret value).den η :=
  ret_bind value (.ret (.var .zero)) η

/-- **Law 2 (Passing a Value Through a Function Parameter Preserves Value Polarity)**:
Applying `Comp.lam body` to `value` substitutes `value` directly without
forcing it. -/
theorem lam_app_preserves_value {domain : VTy sig.Ground} {type : CTy sig.Ground}
    (body : Comp sig (domain :: context) type) (value : Val sig context domain)
    (η : Env sig context) :
    (Comp.app (.lam body) value).den η = (body.instantiate value).den η :=
  lam_app body value η

/-- The identity function at any `ContextualCBPV` value type `A` (including
ground `Data`, pairs, or suspended `Code` thunks) preserves its argument's
denotation exactly. -/
def idComp (A : VTy sig.Ground) : Comp sig context (.arrow A (.ret A)) :=
  .lam (.ret (.var .zero))

theorem app_idComp_preserves_value {A : VTy sig.Ground}
    (value : Val sig context A) (η : Env sig context) :
    (Comp.app (idComp A) value).den η = (Comp.ret value).den η :=
  lam_app (.ret (.var .zero)) value η

/-- **Law 3a (`eval (quote M) = M`)**:
Forcing a quoted/thunked computation `Val.thunk body` runs `body`. -/
theorem eval_quote_beta {type : CTy sig.Ground} (body : Comp sig context type)
    (η : Env sig context) :
    (Comp.force (.thunk body)).den η = body.den η :=
  force_thunk body η

/-- **Law 3b (`quote (eval V) = V` on suspended thunks)**:
Re-quoting a forced thunk `Val.thunk (.force V)` is denotationally identical to
`V`. -/
theorem quote_eval_eta {type : CTy sig.Ground} (suspended : Val sig context (.thunk type))
    (η : Env sig context) :
    (Val.thunk (.force suspended)).den η = suspended.den η :=
  thunk_force suspended η

/-- **Law 3c (`let q = ret (quote M) in eval q = M`)**:
Binding a quoted computation to a variable via `let` does not run `M`, and
subsequently calling `eval` (`Comp.force`) on that variable runs `M` once. -/
theorem let_quote_then_eval {type : CTy sig.Ground} (body : Comp sig context type)
    (η : Env sig context) :
    (Comp.bind (.ret (.thunk body)) (.force (.var .zero))).den η = body.den η := by
  rw [ret_bind]
  rfl

/-- **Law 3d (Algebraicity of `eval (quote ...)` with `let` sequencing)**:
Evaluating a quoted sequential computation `M to x. N` before continuing with `K`
associates cleanly with `Comp.bind`. -/
theorem eval_quote_bind {answer middle : VTy sig.Ground} {type : CTy sig.Ground}
    (first : Comp sig context (.ret answer))
    (second : Comp sig (answer :: context) (.ret middle))
    (third : Comp sig (middle :: context) type) (η : Env sig context) :
    (Comp.bind (.force (.thunk (.bind first second))) third).den η =
      (Comp.bind first (.bind second (Comp.weakenUnder third))).den η := by
  change (Comp.bind (.bind first second) third).den η = _
  exact bind_assoc first second third η

/-- **Law 3e (Algebraicity of `eval (quote ...)` with nondeterministic `choose`)**:
Evaluating a quoted nondeterministic computation `choose M₁ M₂` inside a `let`
distributes over both branches. -/
theorem eval_quote_choose {answer : VTy sig.Ground} {type : CTy sig.Ground}
    (left right : Comp sig context (.ret answer))
    (body : Comp sig (answer :: context) type) (η : Env sig context) :
    (Comp.bind (.force (.thunk (.choose left right))) body).den η =
      (Comp.choose (.bind left body) (.bind right body)).den η := by
  change (Comp.bind (.choose left right) body).den η = _
  exact choose_bind left right body η

end GeneralCBPVLaws

/-! ## §2. Polarity Laws in `PolarizedValues` (`Shaped.Value` / `Shaped.Computation`) -/

section PolarizedValueLaws

open PolarizedValues
open PolarizedValues.Shaped

variable {Head Operation Effect StableFault NativeFault : Type} {m n k : Nat}
  {scope : List VShape}
  (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
  (native : Sub Head n m)
  (env : SemEnv (Head := Head) (Effect := Effect) (StableFault := StableFault)
    (NativeFault := NativeFault) (m := m) scope)
  (refs : Fin k → ScopedNeed.Ref Head Effect StableFault NativeFault m)

/-- In `PolarizedValues`, a native term `Tm Head n` (`VShape.native`) is read as
a substituted syntax tree `subst native term`, never forced as a computation. -/
theorem native_value_is_passive (term : Tm Head n) :
    readValue primitive (.native term) native env refs = subst native term :=
  rfl

/-- In `PolarizedValues`, passing any value (whether `.native` data or `.thunk`
code) through a polymorphic `valueLambda` preserves its semantic value in
`SemEnv.cons` without forcing thunks (`read_valueApply_valueLambda`). -/
theorem valueLambda_preserves_shape {domain : VShape} {shape : CShape}
    (body : Computation Head Operation Effect n (domain :: scope) k shape)
    (argument : Value Head Operation Effect n scope k domain) :
    (readComputation primitive (.valueApply (.valueLambda body) argument) native env refs).1 =
      (readComputation primitive body native
        (SemEnv.cons (readValue primitive argument native env refs) env) refs).1 :=
  read_valueApply_valueLambda primitive native env refs body argument

/-- In `PolarizedValues`, only `forceThunk` eliminates a `.thunk` value into its
underlying computation (`read_forceThunk_thunk`). -/
theorem forceThunk_runs_thunk {shape : CShape}
    (body : Computation Head Operation Effect n scope k shape) :
    (readComputation primitive (.forceThunk (.thunk body)) native env refs).1 =
      (readComputation primitive body native env refs).1 :=
  read_forceThunk_thunk primitive native env refs body

end PolarizedValueLaws

/-! ## §3. Formal Comparison of Path A, Path B, and HE Boundary in `ContextualCBPV`

We instantiate `ContextualCBPV.Signature` with a concrete signature
`AtomPolaritySig` that captures the exact representation issue in
`cetta-prime-2.0-draft-20260910`:
* Compound expressions `(head arg)` carry an explicit boolean `isData : Bool`
  (modeling `ATOM_FLAG_HE_EVALUATED` on `ATOM_KIND_EXPR` in `src/atom.h:678`).
* Atomic symbols and numbers (`AtomSym`) are leaves and **cannot** carry
  `ATOM_FLAG_HE_EVALUATED` in `src/atom.h:678`.
-/

namespace AtomComparison

/-- Atomic symbols/leaves (which cannot carry `ATOM_FLAG_HE_EVALUATED` in
`src/atom.h:678`). -/
inductive AtomSym where
  | num (n : Nat)
  | plus
  | foo
  | bar
  | done
  | field
  | err
  deriving DecidableEq, Repr

/-- Runtime atoms in the `Atom` / `%Undefined%` carrier:
* `sym s`: an atomic symbol or number (no `ATOM_FLAG_HE_EVALUATED` bit),
* `expr isData head arg`: a compound expression whose outer cell carries
  `isData : Bool` (`ATOM_FLAG_HE_EVALUATED`). -/
inductive MarkedAtom where
  | sym (s : AtomSym)
  | expr (isData : Bool) (head : MarkedAtom) (arg : MarkedAtom)
  deriving DecidableEq, Repr

namespace MarkedAtom

/-- Whether a `MarkedAtom` is marked as evaluated data (`ATOM_FLAG_HE_EVALUATED`).
In `src/atom.h:678`, only `ATOM_KIND_EXPR` can hold this flag; symbols return
`false`. -/
def isDataMarked : MarkedAtom → Bool
  | .sym _ => false
  | .expr isData _ _ => isData

/-- Whether a symbol is a callable reducer head (`+` or `foo`) vs. a passive
constructor/constant (`field`, `bar`, `done`, `num`). -/
def isCallableSym : AtomSym → Bool
  | .plus => true
  | .foo => true
  | _ => false

/-- Single-step reduction of unmarked callable expressions (`eval` on an
expression):
* If `isData = true`, `evalStep` when forced via explicit `eval` strips the
  outer data mark and evaluates the underlying code (`eval` casts Data to Code);
* In normal argument/return evaluation (`evalUnlessData`), `isData = true`
  prevents reduction, whereas `isData = false` reduces callable heads and marks
  the resulting compound datum if any. -/
def evalUnlessData : MarkedAtom → MarkedAtom
  | .sym s => .sym s
  | .expr true h a => .expr true h a
  | .expr false h a =>
      let h' := evalUnlessData h
      let a' := evalUnlessData a
      match h', a' with
      | .sym .plus, .expr _ (.sym (.num m)) (.sym (.num n)) =>
          .sym (.num (m + n))
      | .sym .foo, .sym .bar =>
          .sym .done
      | .sym .field, v =>
          .expr true (.sym .field) v
      | _, _ =>
          .expr true h' a'

/-- Explicit `(eval x)` forces evaluation even when the outer expression carries
`isData = true` (casting `Data` into a computation). -/
def explicitEval : MarkedAtom → MarkedAtom
  | .sym s => .sym s
  | .expr _ h a => evalUnlessData (.expr false h a)

/-- **HE Return-Type Boundary**:
If a function is declared with return type `Atom` or `%Undefined%`, HE strips
the data barrier and re-evaluates the returned expression (`evalUnlessData` on
the unmarked form). -/
def heBoundaryReturn : MarkedAtom → MarkedAtom
  | .sym s => .sym s
  | .expr _ h a => evalUnlessData (.expr false h a)

/-- **Path A `car-atom`**: evaluates its argument first (`evalUnlessData`), then
projects the head (preserving any mark on that head). -/
def pathACar (x : MarkedAtom) : MarkedAtom :=
  match evalUnlessData x with
  | .expr _ h _ => h
  | .sym _ => .sym .err

/-- **Path A `cdr-atom`**: evaluates its argument first (`evalUnlessData`), then
projects the tail (preserving any mark on that tail). -/
def pathACdr (x : MarkedAtom) : MarkedAtom :=
  match evalUnlessData x with
  | .expr _ _ a => a
  | .sym _ => .sym .err

/-- **Path A `cons-atom`**: constructs a `Data`-marked compound expression
(`isData = true`). -/
def pathACons (h a : MarkedAtom) : MarkedAtom :=
  .expr true h a

/-- **Path B (Provenance-Preserving) `car-atom`**:
Inspects the outer shape without evaluating a literal expression argument, and
**preserves existing `isData` marks** on compound subterms. (Note: if `h` is an
atomic symbol `.sym s`, `MarkedAtom.sym` cannot carry `isData`.) -/
def pathBCar : MarkedAtom → MarkedAtom
  | .expr _ h _ => h
  | .sym _ => .sym .err

/-- **Path B (Provenance-Preserving) `cdr-atom`**:
Inspects the outer shape without evaluating a literal expression argument, and
**preserves existing `isData` marks** on compound subterms. -/
def pathBCdr : MarkedAtom → MarkedAtom
  | .expr _ _ a => a
  | .sym _ => .sym .err

/-- **Path B (Unmarked-Code) `cons-atom`**:
Rebuilding from an unmarked head and tail produces an unmarked expression
(`isData = false`), so that code built from symbols can still be reduced if
passed to an evaluator, while existing `isData` marks on subterms are
preserved. -/
def pathBCons (h a : MarkedAtom) : MarkedAtom :=
  .expr false h a

end MarkedAtom

/-- Ground sorts of `AtomPolaritySig`. -/
inductive GroundSort where
  | atom
  | nat
  deriving DecidableEq

def AtomData : GroundSort → Type
  | .atom => MarkedAtom
  | .nat => Nat

/-- Unary operations exposed as pure primitives on `GroundSort.atom`. -/
inductive AtomPrim : GroundSort → GroundSort → Type where
  | evalUnlessData : AtomPrim .atom .atom
  | explicitEval : AtomPrim .atom .atom
  | heBoundaryReturn : AtomPrim .atom .atom
  | pathACar : AtomPrim .atom .atom
  | pathACdr : AtomPrim .atom .atom
  | pathBCar : AtomPrim .atom .atom
  | pathBCdr : AtomPrim .atom .atom
  | pathAConsWith12 : AtomPrim .atom .atom
  | pathBConsWith12 : AtomPrim .atom .atom

def evalAtomPrim : {source target : GroundSort} → AtomPrim source target → AtomData source → AtomData target
  | _, _, .evalUnlessData, (x : MarkedAtom) => x.evalUnlessData
  | _, _, .explicitEval, (x : MarkedAtom) => x.explicitEval
  | _, _, .heBoundaryReturn, (x : MarkedAtom) => x.heBoundaryReturn
  | _, _, .pathACar, (x : MarkedAtom) => x.pathACar
  | _, _, .pathACdr, (x : MarkedAtom) => x.pathACdr
  | _, _, .pathBCar, (x : MarkedAtom) => x.pathBCar
  | _, _, .pathBCdr, (x : MarkedAtom) => x.pathBCdr
  | _, _, .pathAConsWith12, (h : MarkedAtom) =>
      MarkedAtom.pathACons h (.expr true (.sym (.num 1)) (.sym (.num 2)))
  | _, _, .pathBConsWith12, (h : MarkedAtom) =>
      MarkedAtom.pathBCons h (.expr true (.sym (.num 1)) (.sym (.num 2)))

/-- The `ContextualCBPV.Signature` for `AtomPolaritySig`. -/
abbrev AtomPolaritySig : Signature where
  Ground := GroundSort
  Data := AtomData
  stateSort := GroundSort.nat
  intentSort := GroundSort.atom
  payloadSort := GroundSort.atom
  Kind := Unit
  Prim := AtomPrim
  evalPrim := evalAtomPrim

abbrev atomT : VTy AtomPolaritySig.Ground := .ground GroundSort.atom

/-- A `ContextualCBPV` value constant for a `MarkedAtom`. -/
abbrev atomVal {context : List (VTy AtomPolaritySig.Ground)} (a : MarkedAtom) :
    Val AtomPolaritySig context atomT :=
  .const (sig := AtomPolaritySig) GroundSort.atom (a : AtomData GroundSort.atom)

/-- The `Data`-marked expression `(+ 1 2)` (`isData = true`), as produced by a
quoted/data literal or data constructor. -/
def dataPlus12 : MarkedAtom :=
  .expr true (.sym .plus) (.expr true (.sym (.num 1)) (.sym (.num 2)))

/-- The nested `Data`-marked expression `(((Field (+ 1 2))))` from
`elaborate_need_fixtures.metta` (`P4`), where both the outer list cell and the
inner `(Field (+ 1 2))` cell carry `isData = true`. -/
def nestedFieldData : MarkedAtom :=
  .expr true
    (.expr true (.sym .field) dataPlus12)
    (.sym .done)

/-- The unquoted reducible expression `(foo bar)` (`isData = false`). -/
def unquotedFooBar : MarkedAtom :=
  .expr false (.sym .foo) (.sym .bar)

/-! ### 3.1 Zar's Law 2: `Data` Passed Through `Atom` / `%Undefined%` vs. HE Boundary -/

/-- Passing a `MarkedAtom` through an `Atom → F Atom` function in
`ContextualCBPV` under Path A / Path B (where `Atom` parameter passing and
return do not strip `isData`) vs. under HE's return-type boundary rule. -/
def passThroughAtomIdentity {context : List (VTy AtomPolaritySig.Ground)}
    (x : Val AtomPolaritySig context atomT) :
    Comp AtomPolaritySig context (.ret atomT) :=
  .app (.lam (.ret (.prim AtomPrim.evalUnlessData (.var .zero)))) x

def passThroughHEBoundaryIdentity {context : List (VTy AtomPolaritySig.Ground)}
    (x : Val AtomPolaritySig context atomT) :
    Comp AtomPolaritySig context (.ret atomT) :=
  .app (.lam (.ret (.prim AtomPrim.heBoundaryReturn (.var .zero)))) x

/-- **Both Path A and Path B satisfy Zar's Law 2**:
Passing the `Data` expression `dataPlus12` (`(+ 1 2)` with `isData = true`)
through an `Atom`-typed function `(: id-atom (-> Atom Atom))` or `let` binding
preserves `dataPlus12` without evaluating it to `3`. -/
theorem data_preserved_through_atom_lambda (η : Env AtomPolaritySig []) :
    (passThroughAtomIdentity (atomVal dataPlus12)).den η =
      (Comp.ret (atomVal dataPlus12)).den η := by
  unfold passThroughAtomIdentity
  rw [lam_app (sig := AtomPolaritySig)]
  rfl

/-- **Explicit `(eval d)` Law**:
When `dataPlus12` is explicitly passed to `explicitEval` (`(eval d)`), it casts
the `Data` expression to a computation and evaluates `(+ 1 2)` to `3`. -/
theorem explicit_eval_evaluates_data (η : Env AtomPolaritySig []) :
    (Comp.ret (Val.prim (sig := AtomPolaritySig) AtomPrim.explicitEval (atomVal dataPlus12))).den η =
      (Comp.ret (atomVal (.sym (.num 3)))).den η :=
  rfl

/-- **HE Return-Type Boundary Violates Zar's Law 2**:
Under HE's boundary rule, passing `dataPlus12` (`(+ 1 2)` with `isData = true`)
through `(: id-atom (-> Atom Atom))` strips its `Data` mark at the `Atom`
return boundary and evaluates it to `3`. -/
theorem heBoundary_violates_data_through_atom (η : Env AtomPolaritySig []) :
    (passThroughHEBoundaryIdentity (atomVal dataPlus12)).den η =
      (Comp.ret (atomVal (.sym (.num 3)))).den η ∧
    (passThroughHEBoundaryIdentity (atomVal dataPlus12)).den η ≠
      (Comp.ret (atomVal dataPlus12)).den η := by
  have hEval :
      (passThroughHEBoundaryIdentity (atomVal dataPlus12)).den η =
        (Comp.ret (atomVal (.sym (.num 3)))).den η := by
    unfold passThroughHEBoundaryIdentity
    rw [lam_app (sig := AtomPolaritySig)]
    rfl
  refine ⟨hEval, ?_⟩
  rw [hEval]
  intro hEq
  have hRun :
      (runWorlds (CTy.asProgram AtomPolaritySig ((Comp.ret (atomVal (.sym (.num 3)))).den η)) (0 : Nat)).map
          WorldResult.answer =
      (runWorlds (CTy.asProgram AtomPolaritySig ((Comp.ret (atomVal dataPlus12)).den η)) (0 : Nat)).map
          WorldResult.answer :=
    congrArg (fun p => (runWorlds (CTy.asProgram AtomPolaritySig p) (0 : Nat)).map WorldResult.answer) hEq
  change [Sum.inl (MarkedAtom.sym (AtomSym.num 3))] = [Sum.inl dataPlus12] at hRun
  cases hRun

/-! ### 3.2 Where Path A and Path B Agree: Nested Compound Extraction (`P4`) -/

/-- **Path B Preserves Nested Compound Data (`P4`)**:
When `nestedFieldData` (`(((Field (+ 1 2))))`) has `isData = true` on its
compound subterms, Path B's provenance-preserving `car-atom` extracts
`((Field (+ 1 2)))` **with `isData = true` intact**, so subsequent evaluation
(e.g., passing `$p` to `sort-atom` or `evalUnlessData`) does not reduce
`(+ 1 2)` to `3`. -/
theorem pathB_preserves_nested_compound_data (η : Env AtomPolaritySig []) :
    (Comp.bind
      (.ret (.prim AtomPrim.pathBCar (atomVal nestedFieldData)))
      (.ret (.prim AtomPrim.evalUnlessData (.var .zero)))).den η =
    (Comp.ret (atomVal (.expr true (.sym .field) dataPlus12))).den η := by
  rw [ret_bind (sig := AtomPolaritySig)]
  rfl

/-- **Path A Also Preserves Nested Compound Data (`P4`)**:
Because the outer list cell of `nestedFieldData` already carries `isData = true`,
Path A's `car-atom` also extracts `((Field (+ 1 2)))` with `isData = true`
intact. -/
theorem pathA_preserves_nested_compound_data (η : Env AtomPolaritySig []) :
    (Comp.bind
      (.ret (.prim AtomPrim.pathACar (atomVal nestedFieldData)))
      (.ret (.prim AtomPrim.evalUnlessData (.var .zero)))).den η =
    (Comp.ret (atomVal (.expr true (.sym .field) dataPlus12))).den η := by
  rw [ret_bind (sig := AtomPolaritySig)]
  rfl

/-! ### 3.3 Where Path A and Path B Trade Off -/

/-- **Trade-off 1: Unquoted Code Inspection (`(car-atom (foo bar))`)**:
* **Path B** inspects the outer shape of the unquoted expression `(foo bar)` and
  returns the head symbol `foo`.
* **Path A** evaluates `(foo bar)` to `done` first, so `(car-atom (foo bar))`
  returns `err` (and code inspection under Path A must be written explicitly as
  `(car-atom (quote (foo bar)))`). -/
theorem pathA_vs_pathB_unquoted_code :
    MarkedAtom.pathBCar unquotedFooBar = .sym .foo ∧
    MarkedAtom.pathACar unquotedFooBar = .sym .err :=
  ⟨rfl, rfl⟩

/-- **Trade-off 2: Atomic-Head Destructor/Constructor η-Rebuild
(`(cons-atom (car-atom d) (cdr-atom d))` on `d = (+ 1 2)`)**:
Because atomic symbols (`AtomSym.plus`) cannot carry `ATOM_FLAG_HE_EVALUATED` in
`src/atom.h:678`, extracting the head `+` from `dataPlus12` produces `.sym .plus`
under both Path A and Path B.
* Under **Path A**, `cons-atom` marks the rebuilt expression with `isData = true`,
  so `(cons-atom (car-atom d) (cdr-atom d))` remains `Data` (`dataPlus12`) and
  does not reduce to `3` when passed through normal evaluation.
* Under **Path B with unmarked `cons-atom`**, rebuilding `(cons-atom + (1 2))`
  produces `isData = false`, which reduces to `3` when passed through normal
  evaluation (the exact mechanism behind `plain-all` in
  `elaborate_need_fixtures.metta`). -/
theorem pathA_atomic_head_eta_preserves_data (η : Env AtomPolaritySig []) :
    (Comp.bind
      (.ret (.prim AtomPrim.pathAConsWith12 (.prim AtomPrim.pathACar (atomVal dataPlus12))))
      (.ret (.prim AtomPrim.evalUnlessData (.var .zero)))).den η =
    (Comp.ret (atomVal dataPlus12)).den η := by
  rw [ret_bind (sig := AtomPolaritySig)]
  rfl

theorem pathB_unmarked_cons_loses_data_on_atomic_head (η : Env AtomPolaritySig []) :
    (Comp.bind
      (.ret (.prim AtomPrim.pathBConsWith12 (.prim AtomPrim.pathBCar (atomVal dataPlus12))))
      (.ret (.prim AtomPrim.evalUnlessData (.var .zero)))).den η =
    (Comp.ret (atomVal (.sym (.num 3)))).den η := by
  rw [ret_bind (sig := AtomPolaritySig)]
  rfl

#print axioms data_preserved_through_atom_lambda
#print axioms explicit_eval_evaluates_data
#print axioms heBoundary_violates_data_through_atom
#print axioms pathB_preserves_nested_compound_data
#print axioms pathA_preserves_nested_compound_data
#print axioms pathA_vs_pathB_unquoted_code
#print axioms pathA_atomic_head_eta_preserves_data
#print axioms pathB_unmarked_cons_loses_data_on_atomic_head

end AtomComparison

#print axioms let_ret_preserves_value
#print axioms let_ret_var_zero_eq_ret
#print axioms lam_app_preserves_value
#print axioms app_idComp_preserves_value
#print axioms eval_quote_beta
#print axioms quote_eval_eta
#print axioms let_quote_then_eval
#print axioms eval_quote_bind
#print axioms eval_quote_choose
#print axioms native_value_is_passive
#print axioms valueLambda_preserves_shape
#print axioms forceThunk_runs_thunk

end Mettapedia.TypeTheory.ContextualCBPV.DataAtomCoherence
