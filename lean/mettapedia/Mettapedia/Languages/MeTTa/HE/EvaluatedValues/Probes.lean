import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.CoherenceCheck
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.CodeFree

/-!
# The three return rules on concrete programs

One probe program, evaluated under the three rules by kernel computation.
Answer counts (`reevaluate` / `rustEqualToInput` / `evaluatedValues`):

| input                                         | old | Rust | repaired |
|-----------------------------------------------|-----|------|----------|
| `(fr a)`                                      | 2   | 2    | 2        |
| `(wrap (fr a))`                               | 2   | 2    | 2        |
| `(g (fr a))`, `g` an alias of `wrap`          | 4   | 2    | 2        |
| `(g1 (fr a))`, `g1` an alias of `g`           | 8   | 2    | 2        |
| `(twice (fr a))`                              | 8   | 2    | 2        |
| `(pairit (fr a))`                             | 8   | 4    | 4        |
| `(let $c (collapse (fr a)) (superpose $c))`   | 4   | 2    | 2        |
| `(unique (g1 (fr a)))`                        | 2   | 1    | 1        |
| `(twice (coin))`                              | 2   | 2    | 2        |
| `(twicem (coin))`                             | 4   | 4    | 4        |
| `(unquote (quote (fr a)))`                    | 2   | 2    | 2        |
| `(let $m (ga (fr a)) (pair $m))`              | 2   | 2    | 2        |
| `(let $e (car-atom ((fr a) b)) (wrap $e))`    | 2   | 2    | 2        |
| `(usem (ga (fr a)))`                          | 2   | 2    | 2        |
| `(fr (h))`                                    | 2   | 2    | 2        |
| `(wrap (fr (h)))`                             | 2   | 2    | 2        |
| `(g (fr (h)))`                                | 4   | 4    | 2        |
| `(g1 (fr (h)))`                               | 8   | 4    | 2        |
| `(let $c (collapse (fr (h))) (superpose $c))` | 4   | 4    | 2        |

`fr` has two equations replying `NotReducible`, so `(fr a)` is returned twice
and is stuck. The old rule evaluates that returned value again at every
return, multiplying the answers by 2 per alias layer, per occurrence of a
parameter, and per pass through `superpose`.

The Rust rule marks an answer equal to the evaluated term, so `(fr a)` is a
value. `(h)` reduces to `a`, so `(fr (h))` returns the stuck call `(fr a)`,
which is not the evaluated term: Rust leaves it unmarked, and an alias
evaluates it again (`rust_violates_alias`,
`rust_violates_superpose_collapse`). The repaired rule also marks a call that
is stuck after its arguments were evaluated, and gives 2 everywhere.

Syntax is not a value under any rule. `ga` has an `Atom` parameter and an
`Atom` result, so `(ga (fr a))` returns the code `(wrap (fr a))` unmarked, and
`car-atom` returns the child `(fr a)` of `((fr a) b)` as code: both are
evaluated where they are used (`macro_ga_obs`, `macro_car_obs`,
`ga_result_is_code`).

Positive controls: `coin` (two equations replying the numbers 0 and 1)
returns values that are stable, and all rules agree on `twice` (call-time
choice, 2 answers) and on `twicem`, whose parameter is `Atom` (run-time
choice, 4 answers). `quote` has an `Atom` parameter and result; the stuck call
`(quote (fr a))` is a value, while its child `(fr a)` is still code: `unquote`
evaluates it. Marks are per node, not hereditary.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

namespace Probe

/-- Symbol. -/
def S (n : String) : Atom := .symbol n
/-- Expression. -/
def E (xs : List Atom) : Atom := .expression xs
/-- Variable. -/
def V (n : String) : Atom := .var n
/-- The number 0. -/
def zero : Atom := .grounded (.int 0)
/-- The number 1. -/
def one : Atom := .grounded (.int 1)
/-- The stuck call `(fr a)`. -/
def fra : Atom := E [S "fr", S "a"]

/-- The probe program. -/
def program : Program where
  equations := [
    (E [S "fr", V "x"], Atom.notReducible),
    (E [S "fr", V "x"], Atom.notReducible),
    (E [S "g", V "x"], E [S "wrap", V "x"]),
    (E [S "g1", V "x"], E [S "g", V "x"]),
    (E [S "coin"], zero),
    (E [S "coin"], one),
    (E [S "twice", V "x"], E [S "pair", V "x", V "x"]),
    (E [S "twicem", V "x"], E [S "pair", V "x", V "x"]),
    (E [S "pairit", V "x"], E [S "pair", V "x", fra]),
    (E [S "unquote", E [S "quote", V "a"]], V "a"),
    (E [S "h"], S "a"),
    (E [S "ga", V "x"], E [S "wrap", V "x"]),
    (E [S "usem", V "m"], E [S "pair", V "m"])]
  decls := [⟨"twicem", [.atom], .evaluate⟩, ⟨"quote", [.atom], .atom⟩,
    ⟨"ga", [.atom], .atom⟩]

/-- `(let $c (collapse (fr a)) (superpose $c))` -/
def letCollapse : Atom :=
  E [S "let", V "c", E [S "collapse", fra], E [S "superpose", V "c"]]

/-- `(fr (h))`: a stuck call whose argument reduces. -/
def frh : Atom := E [S "fr", E [S "h"]]

/-- `(let $m (ga (fr a)) (pair $m))` -/
def macroGa : Atom := E [S "let", V "m", E [S "ga", fra], E [S "pair", V "m"]]

/-- `(let $e (car-atom ((fr a) b)) (wrap $e))` -/
def macroCar : Atom :=
  E [S "let", V "e", E [S "car-atom", E [fra, S "b"]], E [S "wrap", V "e"]]

end Probe

open Probe

theorem program_codeFree : program.CodeFree := by
  unfold Program.CodeFree Program.CodeFreeT
  decide

/-! ## Observations under the three rules -/

/-- The three observations of a probe. -/
noncomputable def obs3 (a : Atom) : Option (List Atom) × Option (List Atom) × Option (List Atom) :=
  (observe .reevaluate program a, observe .rustEqualToInput program a,
    observe .evaluatedValues program a)

theorem obs3_of {a : Atom} {n : ℕ} {R₁ R₂ R₃ : List Atom}
    (h₁ : (evalFuel .reevaluate program n (code a)).map (List.map MAtom.erase) = some R₁)
    (h₂ : (evalFuel .rustEqualToInput program n (code a)).map (List.map MAtom.erase) = some R₂)
    (h₃ : (evalFuel .evaluatedValues program n (code a)).map (List.map MAtom.erase) = some R₃) :
    obs3 a = (some R₁, some R₂, some R₃) := by
  simp [obs3, observe_of_evalFuel h₁, observe_of_evalFuel h₂, observe_of_evalFuel h₃]

theorem fr_obs : obs3 fra = (some [fra, fra], some [fra, fra], some [fra, fra]) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wrap_obs : obs3 (E [S "wrap", fra]) =
    (some (List.replicate 2 (E [S "wrap", fra])), some (List.replicate 2 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem alias_obs : obs3 (E [S "g", fra]) =
    (some (List.replicate 4 (E [S "wrap", fra])), some (List.replicate 2 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem alias2_obs : obs3 (E [S "g1", fra]) =
    (some (List.replicate 8 (E [S "wrap", fra])), some (List.replicate 2 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem twice_fr_obs : obs3 (E [S "twice", fra]) =
    (some (List.replicate 8 (E [S "pair", fra, fra])), some (List.replicate 2 (E [S "pair", fra, fra])),
      some (List.replicate 2 (E [S "pair", fra, fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pairit_obs : obs3 (E [S "pairit", fra]) =
    (some (List.replicate 8 (E [S "pair", fra, fra])), some (List.replicate 4 (E [S "pair", fra, fra])),
      some (List.replicate 4 (E [S "pair", fra, fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pair_fr_obs : obs3 (E [S "pair", fra, fra]) =
    (some (List.replicate 4 (E [S "pair", fra, fra])), some (List.replicate 4 (E [S "pair", fra, fra])),
      some (List.replicate 4 (E [S "pair", fra, fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem superpose_collapse_obs : obs3 letCollapse =
    (some (List.replicate 4 fra), some (List.replicate 2 fra), some (List.replicate 2 fra)) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem unique_obs : obs3 (E [S "unique", E [S "g1", fra]]) =
    (some (List.replicate 2 (E [S "wrap", fra])), some [E [S "wrap", fra]],
      some [E [S "wrap", fra]]) :=
  obs3_of (n := 14) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem twice_coin_obs : obs3 (E [S "twice", E [S "coin"]]) =
    (some [E [S "pair", zero, zero], E [S "pair", one, one]],
      some [E [S "pair", zero, zero], E [S "pair", one, one]],
      some [E [S "pair", zero, zero], E [S "pair", one, one]]) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem twicem_coin_obs : obs3 (E [S "twicem", E [S "coin"]]) =
    (some [E [S "pair", zero, zero], E [S "pair", zero, one], E [S "pair", one, zero],
        E [S "pair", one, one]],
      some [E [S "pair", zero, zero], E [S "pair", zero, one], E [S "pair", one, zero],
        E [S "pair", one, one]],
      some [E [S "pair", zero, zero], E [S "pair", zero, one], E [S "pair", one, zero],
        E [S "pair", one, one]]) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem unquote_obs : obs3 (E [S "unquote", E [S "quote", fra]]) =
    (some [fra, fra], some [fra, fra], some [fra, fra]) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem macro_ga_obs : obs3 macroGa =
    (some (List.replicate 2 (E [S "pair", E [S "wrap", fra]])),
      some (List.replicate 2 (E [S "pair", E [S "wrap", fra]])),
      some (List.replicate 2 (E [S "pair", E [S "wrap", fra]]))) :=
  obs3_of (n := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem macro_car_obs : obs3 macroCar =
    (some (List.replicate 2 (E [S "wrap", fra])), some (List.replicate 2 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem usem_ga_obs : obs3 (E [S "usem", E [S "ga", fra]]) =
    (some (List.replicate 2 (E [S "pair", E [S "wrap", fra]])),
      some (List.replicate 2 (E [S "pair", E [S "wrap", fra]])),
      some (List.replicate 2 (E [S "pair", E [S "wrap", fra]]))) :=
  obs3_of (n := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fr_h_obs : obs3 frh = (some [fra, fra], some [fra, fra], some [fra, fra]) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wrap_fr_h_obs : obs3 (E [S "wrap", frh]) =
    (some (List.replicate 2 (E [S "wrap", fra])), some (List.replicate 2 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem alias_fr_h_obs : obs3 (E [S "g", frh]) =
    (some (List.replicate 4 (E [S "wrap", fra])), some (List.replicate 4 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem alias2_fr_h_obs : obs3 (E [S "g1", frh]) =
    (some (List.replicate 8 (E [S "wrap", fra])), some (List.replicate 4 (E [S "wrap", fra])),
      some (List.replicate 2 (E [S "wrap", fra]))) :=
  obs3_of (n := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `(let $c (collapse (fr (h))) (superpose $c))` -/
def letCollapseFrh : Atom :=
  E [S "let", V "c", E [S "collapse", frh], E [S "superpose", V "c"]]

theorem superpose_collapse_fr_h_obs : obs3 letCollapseFrh =
    (some (List.replicate 4 fra), some (List.replicate 4 fra), some (List.replicate 2 fra)) :=
  obs3_of (n := 10) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The Rust rule is incoherent on reduced stuck calls -/

/-- **Rust violates the alias law.** `g` is defined by `(g $x) = (wrap $x)`, yet
`(g (fr (h)))` has 4 answers and `(wrap (fr (h)))` has 2. -/
theorem rust_violates_alias :
    observe .rustEqualToInput program (E [S "g", frh]) ≠
      observe .rustEqualToInput program (E [S "wrap", frh]) := by
  have h₁ := congrArg (fun x => x.2.1) alias_fr_h_obs
  have h₂ := congrArg (fun x => x.2.1) wrap_fr_h_obs
  simp only [obs3] at h₁ h₂
  rw [h₁, h₂]
  decide

/-- **Rust violates collapse-then-superpose.** `(fr (h))` has 2 answers; after
`collapse` and `superpose` it has 4. -/
theorem rust_violates_superpose_collapse :
    observe .rustEqualToInput program letCollapseFrh ≠ observe .rustEqualToInput program frh := by
  have h₁ := congrArg (fun x => x.2.1) superpose_collapse_fr_h_obs
  have h₂ := congrArg (fun x => x.2.1) fr_h_obs
  simp only [obs3] at h₁ h₂
  rw [h₁, h₂]
  decide

/-- The repaired rule keeps both laws on the same input. -/
theorem evaluatedValues_alias_superpose_fr_h :
    observe .evaluatedValues program (E [S "g", frh]) =
        observe .evaluatedValues program (E [S "wrap", frh]) ∧
      observe .evaluatedValues program letCollapseFrh = observe .evaluatedValues program frh := by
  have h₁ := congrArg (fun x => x.2.2) alias_fr_h_obs
  have h₂ := congrArg (fun x => x.2.2) wrap_fr_h_obs
  have h₃ := congrArg (fun x => x.2.2) superpose_collapse_fr_h_obs
  have h₄ := congrArg (fun x => x.2.2) fr_h_obs
  simp only [obs3] at h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact ⟨rfl, rfl⟩

/-- Under Rust's rule `(fr (h))` has no value results; under the repaired rule
it has. -/
theorem fr_h_values :
    ¬ ValueResults .rustEqualToInput program (code frh) ∧
      ValueResults .evaluatedValues program (code frh) := by
  have h : (evalFuel .rustEqualToInput program 10 (code frh)).map (List.map MAtom.isValue) =
      some [false, false] := by decide +kernel
  obtain ⟨R, hR, hRv⟩ := Option.map_eq_some_iff.mp h
  refine ⟨fun hv => ?_, ValueResults.of_codeFree program_codeFree (by unfold Program.CodeFreeT; decide)⟩
  match R, hRv with
  | [r₁, r₂], hRv =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hRv
    have := hv [r₁, r₂] (eval_of_evalFuel hR) r₁ List.mem_cons_self
    rw [hRv.1] at this
    cases this

/-! ## Syntax returned through `Atom` stays code -/

/-- **An `Atom` result is code.** `(ga (fr a))` returns `(wrap (fr a))`
unmarked under the repaired rule; evaluated again it has two answers. -/
theorem ga_result_is_code :
    observe .evaluatedValues program (E [S "ga", fra]) = some [E [S "wrap", fra]] ∧
      ¬ ValueResults .evaluatedValues program (code (E [S "ga", fra])) := by
  have h : (evalFuel .evaluatedValues program 10 (code (E [S "ga", fra]))).map
      (List.map MAtom.isValue) = some [false] := by decide +kernel
  obtain ⟨R, hR, hRv⟩ := Option.map_eq_some_iff.mp h
  refine ⟨observe_of_evalFuel (n := 10) (by decide +kernel), fun hv => ?_⟩
  match R, hRv with
  | [r], hRv =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hRv
    have := hv [r] (eval_of_evalFuel hR) r List.mem_cons_self
    rw [hRv] at this
    cases this

/-- **The old rule is not idempotent.** Evaluating the two results of
`(fr a)` again yields four. -/
theorem reevaluate_not_idempotent :
    (kbind (eval .reevaluate program (code fra)) (eval .reevaluate program)).map
        (List.map MAtom.erase) = some [fra, fra, fra, fra] ∧
      (eval .reevaluate program (code fra)).map (List.map MAtom.erase) = some [fra, fra] := by
  have h₀ : (evalFuel .reevaluate program 10 (code fra)).map (List.map MAtom.erase) =
      some [fra, fra] := by decide +kernel
  obtain ⟨R, hR, hRe⟩ := Option.map_eq_some_iff.mp h₀
  have hR' := eval_of_evalFuel hR
  refine ⟨?_, by rw [hR']; simpa using hRe⟩
  match R, hRe with
  | [r₁, r₂], hRe =>
    have hRe' : [r₁, r₂].map MAtom.erase = [fra, fra] := hRe
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hRe
    have h₁ := eval_reevaluate_erase program (t := r₁) (u := code fra) (by simp [hRe.1])
    have h₂ := eval_reevaluate_erase program (t := r₂) (u := code fra) (by simp [hRe.2])
    rw [hR', Option.map_some, hRe'] at h₁ h₂
    obtain ⟨R₁, hR₁, hR₁e⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨R₂, hR₂, hR₂e⟩ := Option.map_eq_some_iff.mp h₂
    rw [hR']
    simp only [kbind, Option.bind_some, optFlatMap_cons, hR₁, hR₂, optFlatMap_nil,
      Option.map_some, List.append_nil, List.map_append, hR₁e, hR₂e]
    rfl

theorem reevaluate_not_idempotent' :
    kbind (eval .reevaluate program (code fra)) (eval .reevaluate program) ≠
      eval .reevaluate program (code fra) := by
  intro h
  have := reevaluate_not_idempotent
  rw [h, this.2] at this
  simp at this

/-- `collapse` turns results into a tuple that the old rule runs again as code:
the single result `(superpose (x y))` of the first input, evaluated again,
gives `x` and `y`. The construction uses only symbols without equations, which
is why coherence is stated for an evaluation (`Program.CoherentAt`) rather
than for a whole program. -/
theorem collapse_result_unstable :
    observe .reevaluate program
        (E [S "collapse", E [S "superpose", E [S "superpose", E [S "x", S "y"]]]]) =
      some [E [S "superpose", E [S "x", S "y"]]] ∧
    observe .reevaluate program (E [S "superpose", E [S "x", S "y"]]) = some [S "x", S "y"] :=
  ⟨observe_of_evalFuel (n := 10) (by decide +kernel),
    observe_of_evalFuel (n := 10) (by decide +kernel)⟩

/-! ## The laws applied -/

theorem program_symbolHeaded : program.SymbolHeaded := by
  unfold Program.SymbolHeaded
  decide

/-- `(coin)` has value results under the repaired rule. -/
theorem coin_valueResults : ValueResults .evaluatedValues program (code (E [S "coin"])) :=
  ValueResults.of_codeFree program_codeFree (by unfold Program.CodeFreeT; decide)

/-- `eval_twice` instantiated: `(twice (coin))` returns `(pair v v)` for each
result `v` of `(coin)`. -/
theorem twice_coin_by_law :
    eval .evaluatedValues program (.expr false [.symbol "twice", code (E [S "coin"])]) =
      (eval .evaluatedValues program (code (E [S "coin"]))).map
        (List.map fun v => .expr true [.symbol "pair", v, v]) :=
  eval_twice rfl (x := "x") program_symbolHeaded rfl rfl rfl rfl (by decide) (by decide) _
    coin_valueResults

/-- `eval_alias_codeFree` instantiated on the reduced stuck call. -/
theorem alias_fr_h_exact :
    eval .evaluatedValues program (.expr false [.symbol "g", code frh]) =
      eval .evaluatedValues program (.expr false [.symbol "wrap", code frh]) :=
  eval_alias_codeFree (xs := ["x"]) program_codeFree program_symbolHeaded (by decide) rfl rfl rfl
    rfl (by decide) [code frh] rfl (by
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      unfold Program.CodeFreeT
      decide)

/-- `(pairit e)` and its unfolding `(pair e (fr a))` have the same results, as
multisets, under the repaired rule, for every code-free argument. -/
theorem pairit_unfold (e : MAtom) (he : program.CodeFreeT e) {R : List MAtom}
    (h : eval .evaluatedValues program (.expr false [.symbol "pair", e, code fra]) = some R) :
    ∃ R', eval .evaluatedValues program (.expr false [.symbol "pairit", e]) = some R' ∧
      (R : Multiset MAtom) = R' := by
  have hstrict : ∀ fr ∈ [Frame.mk (.symbol "pair") [] [code fra]], fr.Strict program := by
    intro fr hfr
    simp only [List.mem_singleton] at hfr
    subst hfr
    unfold Frame.Strict
    decide
  have havoid : ∀ fr ∈ [Frame.mk (.symbol "pair") [] [code fra]], fr.Avoids "x" := by
    intro fr hfr
    simp only [List.mem_singleton] at hfr
    subst hfr
    unfold Frame.Avoids
    decide
  have hsub : (code fra).subst [("x", e)] = code fra := MAtom.subst_of_not_touched _ _ rfl
  refine unfold_preserves_eval_codeFree program_codeFree program_symbolHeaded
    [⟨.symbol "pair", [], [code fra]⟩] hstrict (by simp) havoid (rhs := E [S "pair", V "x", fra])
    (x := "x") rfl rfl rfl (by decide) e he ?_
  have hc : (code (E [S "pair", V "x", fra])).subst [("x", e)] =
      .expr false [.symbol "pair", e, code fra] := by
    rw [show code (E [S "pair", V "x", fra]) =
      .expr false [.symbol "pair", .var "x", code fra] from rfl]
    simp [Subst.lookup_cons, hsub]
  rw [hc]
  exact h

/-! ## Coherence -/

/-- The old evaluation of `(twice (coin))` passes only stable atoms. -/
theorem coherent_twice_coin : program.CoherentAt (code (E [S "twice", E [S "coin"]])) :=
  coherentAt_of_check (n := 10) (by decide +kernel)

/-- Hence every rule agrees with the old one on it, by conservativity alone. -/
theorem twice_coin_agree (rule : ReturnRule) :
    observe rule program (E [S "twice", E [S "coin"]]) =
      observe .reevaluate program (E [S "twice", E [S "coin"]]) :=
  conservativity rule program _ coherent_twice_coin

theorem coherent_twicem_coin : program.CoherentAt (code (E [S "twicem", E [S "coin"]])) :=
  coherentAt_of_check (n := 10) (by decide +kernel)

/-- The old evaluation of `(g (fr a))` passes the unstable `(fr a)`. -/
theorem not_coherent_alias : ¬ program.CoherentAt (code (E [S "g", fra])) := by
  refine not_coherent_of_disagree (rule := .evaluatedValues) ?_
  have h := alias_obs
  simp only [obs3, Prod.mk.injEq] at h
  rw [h.1, h.2.2]
  decide

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
