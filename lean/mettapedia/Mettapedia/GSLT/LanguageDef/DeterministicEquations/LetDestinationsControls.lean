import Mettapedia.GSLT.LanguageDef.DeterministicEquations.LetDestinations

/-!
# Let-destination controls

The negative controls are the clashes SWI-PeTTa prunes.  In each, a let's pattern
`(Pair 5 $x)` meets an output with another atom where the pattern has `5`, while a
call that never ends runs beneath it:

* a literal field: `(let (Pair 5 $x) (Pair 3 (spin 0)) $x)`;
* a field holding an argument: `(g 3)` with `(= (g $a) (let (Pair 5 $x) (Pair $a (spin 0)) $x))`;
* a later field beside the call: `(let (Pair $x 5) (Pair (spin 0) 3) $x)`;
* an inner let's body: `(let (Pair 5 $x) (let $y (spin 0) (Pair 3 $y)) $x)`;
* a callee's output: `(let (Pair 5 $x) (h 0) $x)` with `(= (h $n) (Pair 3 (spin $n)))`;
* an `if` branch: `(let (Pair 5 $x) (if True (Pair 3 (spin 0)) (Pair 5 1)) $x)`.

The value-first reading runs out of fuel on each, the destination-first reading
fails, each query is well scoped, and none of the lets is admitted.

The positive controls are lets the evidence admits and the coarse rule (no call
in the value, or a fresh variable as the pattern) refuses: a loop whose let takes
apart the pair its recursive call returns, and a lookup whose let takes `Just`
apart, whose equations are judged one by one.  Both readings compute the same
answers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.LetDestinations.Controls

open Mettapedia.GSLT.LanguageDef.DeterministicEquations.LetDestinations

/-- The expression `(c a₁ … aₙ)` as cons cells. -/
def con (c : String) (args : List Tm) : Tm := .cons (.atom c) (args.foldr .cons .nil)

/-- The value `(c a₁ … aₙ)` as cons cells. -/
def conV (c : String) (args : List Val) : Val := .cons (.atom c) (args.foldr .cons .nil)

/-- No host primitives. -/
def noHost : Host := fun _ _ => none

/-! ## Runs that do not end -/

section Divergence

variable (P : Program) (H : Host)

/-- The value-first reading of `t` runs out of every fuel. -/
def Diverges (env : Env) (t : Tm) : Prop := ∀ n, evalV P H n env t = .exhausted

/-- The value-first reading of `t` gives `v` once it has fuel. -/
def Settles (env : Env) (t : Tm) (v : Val) : Prop :=
  ∀ n, evalV P H n env t = .exhausted ∨ evalV P H n env t = .value v

theorem settles_atom (env : Env) (a : String) : Settles P H env (.atom a) (.atom a)
  | 0 => Or.inl rfl
  | _ + 1 => Or.inr rfl

theorem settles_var {env : Env} {x : String} {v : Val} (h : lookup env x = some v) :
    Settles P H env (.var x) v
  | 0 => Or.inl rfl
  | _ + 1 => Or.inr (by simp [evalV, stepV, h])

theorem diverges_cons_left {env : Env} {a b : Tm} (ha : Diverges P H env a) :
    Diverges P H env (.cons a b)
  | 0 => rfl
  | n + 1 => by simp [evalV, stepV, ha n]

theorem diverges_cons_right {env : Env} {a b : Tm} {x : Val} (ha : Settles P H env a x)
    (hb : Diverges P H env b) : Diverges P H env (.cons a b)
  | 0 => rfl
  | n + 1 => by
    rcases ha n with ha | ha <;> simp [evalV, stepV, ha, hb n]

theorem diverges_letp {env : Env} {p v b : Tm} (hv : Diverges P H env v) :
    Diverges P H env (.letp p v b)
  | 0 => rfl
  | n + 1 => by simp [evalV, stepV, hv n]

theorem diverges_call {env : Env} {f : String} {a : Tm} {v : Val} {e : Equation} {σ : Env}
    (ha : Settles P H env a v) (hsel : select P f v = some (e, σ))
    (hb : Diverges P H σ e.body) : Diverges P H env (.call f a)
  | 0 => rfl
  | n + 1 => by
    rcases ha n with ha | ha <;> simp [evalV, stepV, ha, hsel, hb n]

theorem diverges_ite_true {env : Env} {c a b : Tm} (hc : Settles P H env c (.atom "True"))
    (ha : Diverges P H env a) : Diverges P H env (.ite c a b)
  | 0 => rfl
  | n + 1 => by
    rcases hc n with hc | hc <;> simp [evalV, stepV, hc, ha n]

end Divergence

/-- `(= (spin $x) (spin $x))`. -/
def spinEq : Equation := ⟨"spin", .var "x", .call "spin" (.var "x")⟩

theorem select_spin (rest : Program) (v : Val) :
    select (spinEq :: rest) "spin" v = some (spinEq, [("x", v)]) := by
  simp [select, spinEq, matchPat, lookup]

theorem spin_diverges (rest : Program) (H : Host) (v : Val) :
    Diverges (spinEq :: rest) H [("x", v)] (.call "spin" (.var "x")) := by
  intro n
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    have h₁ : evalV (spinEq :: rest) H (n + 1) [("x", v)] (.call "spin" (.var "x")) =
        (evalV (spinEq :: rest) H n [("x", v)] (.var "x")).bind fun v' =>
          match select (spinEq :: rest) "spin" v' with
          | some (e, σ) => evalV (spinEq :: rest) H n σ e.body
          | none => .failure := rfl
    rw [h₁]
    cases n with
    | zero => rfl
    | succ m =>
      have hx : evalV (spinEq :: rest) H (m + 1) [("x", v)] (.var "x") = .value v := by
        simp [evalV, stepV, lookup]
      rw [hx, Outcome.bind_value, select_spin]
      exact ih v

theorem spin_zero_diverges (rest : Program) (H : Host) (env : Env) :
    Diverges (spinEq :: rest) H env (.call "spin" (.atom "0")) :=
  diverges_call _ H (settles_atom _ H env "0") (select_spin rest _)
    (spin_diverges rest H (.atom "0"))

/-! ## Destination-first runs that meet a clash -/

section Clash

variable (P : Program) (H : Host)

/-- A let whose value's skeleton cannot meet the let's pattern fails at once. -/
theorem evalD_letp_clash {n : Nat} {env : Env} {p v b : Tm} {M : Set Val}
    (hm : SkelMeets env (.letp p v b) M)
    (hc : ¬SkelMeets env v {w | ∃ σ, matchPat env p w = some σ ∧ SkelMeets σ b M}) :
    evalD P H (n + 2) env (.letp p v b) M = .failure := by
  rw [evalD_succ_pos P H hm]
  simp only [stepD]
  rw [evalD_succ_neg P H hc, Outcome.bind_failure]

theorem evalD_atom {n : Nat} {env : Env} {a : String} {M : Set Val} (ha : Val.atom a ∈ M) :
    evalD P H (n + 1) env (.atom a) M = .value (.atom a) := by
  have hm : SkelMeets env (.atom a) M := ⟨.atom a, ha, rfl⟩
  rw [evalD_succ_pos P H hm]
  rfl

end Clash

/-- The pattern `(Pair 5 $x)`. -/
def pairFive : Tm := con "Pair" [.atom "5", .var "x"]

/-- The values `(Pair 5 $x)` matches, with the let's body `$x` meeting no
destination. -/
def pairFiveDest : Set Val :=
  {w | ∃ σ, matchPat [] pairFive w = some σ ∧ SkelMeets σ (.var "x") Set.univ}

theorem pairFive_skel : SkelMeets [] (.letp pairFive (.atom "0") (.var "x")) Set.univ :=
  ⟨.atom "0", Set.mem_univ _, conV "Pair" [.atom "5", .atom "0"], [("x", .atom "0")], by decide,
    by simp [Skel, lookup]⟩

theorem skelMeets_letp_pairFive (v : Tm) :
    SkelMeets [] (.letp pairFive v (.var "x")) Set.univ := pairFive_skel

theorem pairFiveDest_mem : conV "Pair" [.atom "5", .atom "0"] ∈ pairFiveDest :=
  ⟨[("x", .atom "0")], by decide, .atom "0", Set.mem_univ _, by simp [Skel, lookup]⟩

/-- A value `(Pair 3 _)` is not among those `(Pair 5 $x)` matches. -/
theorem pairFive_rejects_three {σ : Env} {y : Val} {σ' : Env}
    (h : matchPat σ pairFive (.cons (.atom "Pair") (.cons (.atom "3") (.cons y .nil))) =
      some σ') : False := by
  simp [pairFive, con, matchPat] at h

/-! ### A literal field -/

/-- `(let (Pair 5 $x) (Pair 3 (spin 0)) $x)`. -/
def literalField : Tm :=
  .letp pairFive (con "Pair" [.atom "3", .call "spin" (.atom "0")]) (.var "x")

theorem literalField_scoped : WellScoped [] literalField := by
  simp [literalField, pairFive, con, WellScoped, IsPat, patVars]

theorem literalField_value_first : Diverges [spinEq] noHost [] literalField :=
  diverges_letp _ _ <| diverges_cons_right _ _ (settles_atom _ _ _ _) <|
    diverges_cons_right _ _ (settles_atom _ _ _ _) <| diverges_cons_left _ _ <|
      spin_zero_diverges [] _ _

theorem literalField_destination_first :
    evalD [spinEq] noHost 2 [] literalField Set.univ = .failure := by
  refine evalD_letp_clash _ _ (skelMeets_letp_pairFive _) ?_
  rintro ⟨u, ⟨σ, hm, -⟩, hs⟩
  simp only [con, List.foldr, Skel] at hs
  obtain ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, -, rfl⟩ := hs
  exact pairFive_rejects_three hm

theorem literalField_not_admitted : ¬LetsAdmitted [spinEq] [] literalField := by
  rintro ⟨hcf | ⟨-, W, -, hadm⟩, -⟩
  · simp [con, CallFree] at hcf
  · simp only [pairFive, con, List.foldr] at hadm
    rcases hadm with hc | hcf
    · rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨hc, _⟩
      rcases hc with _ | ⟨hm⟩
      simp [CertMatch] at hm
    · simp [CallFree] at hcf

/-! ### A field holding an argument -/

/-- `(= (g $a) (let (Pair 5 $x) (Pair $a (spin 0)) $x))`. -/
def slotEq : Equation :=
  ⟨"g", .var "a", .letp pairFive (con "Pair" [.var "a", .call "spin" (.atom "0")]) (.var "x")⟩

def slotProgram : Program := [spinEq, slotEq]

/-- `(g 3)`. -/
def argumentSlot : Tm := .call "g" (.atom "3")

theorem select_slot : select slotProgram "g" (.atom "3") = some (slotEq, [("a", .atom "3")]) := by
  decide

theorem argumentSlot_scoped : WellScoped [] argumentSlot ∧
    WellScoped (patVars slotEq.param) slotEq.body := by
  simp [argumentSlot, slotEq, pairFive, con, WellScoped, IsPat, patVars]

theorem argumentSlot_value_first : Diverges slotProgram noHost [] argumentSlot :=
  diverges_call _ _ (settles_atom _ _ _ _) select_slot <|
    diverges_letp _ _ <| diverges_cons_right _ _ (settles_atom _ _ _ _) <|
      diverges_cons_right _ _ (settles_var _ _ (v := .atom "3") (by decide)) <|
        diverges_cons_left _ _ <|
        spin_zero_diverges [slotEq] _ _

theorem argumentSlot_destination_first :
    evalD slotProgram noHost 3 [] argumentSlot Set.univ = .failure := by
  have hm : SkelMeets [] argumentSlot Set.univ := ⟨.nil, Set.mem_univ _, trivial⟩
  rw [evalD_succ_pos _ _ hm]
  simp only [argumentSlot, stepD]
  rw [evalD_atom _ _ (Set.mem_univ _), Outcome.bind_value, select_slot]
  dsimp only
  refine evalD_letp_clash _ _ ⟨.atom "0", Set.mem_univ _, conV "Pair" [.atom "5", .atom "0"],
    [("x", .atom "0"), ("a", .atom "3")], by decide, by simp [Skel, lookup]⟩ ?_
  rintro ⟨u, ⟨σ, hm, -⟩, hs⟩
  simp only [con, List.foldr, Skel, lookup] at hs
  obtain ⟨_, _, rfl, rfl, _, _, rfl, hy, _, _, rfl, -, rfl⟩ := hs
  simp only [reduceIte, Option.some.injEq] at hy
  subst hy
  exact pairFive_rejects_three hm

theorem argumentSlot_not_admitted : ¬ProgramAdmitted slotProgram := by
  intro h
  obtain ⟨-, -, hcf | ⟨-, W, -, hadm⟩, -⟩ := h slotEq (by simp [slotProgram])
  · simp [con, CallFree] at hcf
  · simp only [slotEq, pairFive, con, List.foldr] at hadm
    rcases hadm with hc | hcf
    · rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨hc, _⟩
      cases hc
    · simp [CallFree] at hcf

/-! ### A later field beside the call -/

/-- `(let (Pair $x 5) (Pair (spin 0) 3) $x)`. -/
def laterField : Tm :=
  .letp (con "Pair" [.var "x", .atom "5"]) (con "Pair" [.call "spin" (.atom "0"), .atom "3"])
    (.var "x")

theorem laterField_scoped : WellScoped [] laterField := by
  simp [laterField, con, WellScoped, IsPat, patVars]

theorem laterField_value_first : Diverges [spinEq] noHost [] laterField :=
  diverges_letp _ _ <| diverges_cons_right _ _ (settles_atom _ _ _ _) <|
    diverges_cons_left _ _ <| spin_zero_diverges [] _ _

theorem laterField_destination_first :
    evalD [spinEq] noHost 2 [] laterField Set.univ = .failure := by
  refine evalD_letp_clash _ _ ⟨.atom "0", Set.mem_univ _, conV "Pair" [.atom "0", .atom "5"],
    [("x", .atom "0")], by decide, by simp [Skel, lookup]⟩ ?_
  rintro ⟨u, ⟨σ, hm, -⟩, hs⟩
  simp only [con, List.foldr, Skel] at hs
  obtain ⟨_, _, rfl, rfl, _, _, rfl, -, _, _, rfl, rfl, rfl⟩ := hs
  simp [con, List.foldr, matchPat, lookup] at hm

theorem laterField_not_admitted : ¬LetsAdmitted [spinEq] [] laterField := by
  rintro ⟨hcf | ⟨-, W, -, hadm⟩, -⟩
  · simp [con, CallFree] at hcf
  · simp only [con, List.foldr] at hadm
    rcases hadm with hc | hcf
    · rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨hc, _⟩
      rcases hc with _ | ⟨hm⟩
      simp [CertMatch] at hm
    · simp [CallFree] at hcf

/-! ### An inner let's body -/

/-- `(let (Pair 5 $x) (let $y (spin 0) (Pair 3 $y)) $x)`. -/
def letBody : Tm :=
  .letp pairFive (.letp (.var "y") (.call "spin" (.atom "0")) (con "Pair" [.atom "3", .var "y"]))
    (.var "x")

theorem letBody_scoped : WellScoped [] letBody := by
  simp [letBody, pairFive, con, WellScoped, IsPat, patVars]

theorem letBody_value_first : Diverges [spinEq] noHost [] letBody :=
  diverges_letp _ _ <| diverges_letp _ _ <| spin_zero_diverges [] _ _

theorem letBody_destination_first :
    evalD [spinEq] noHost 2 [] letBody Set.univ = .failure := by
  refine evalD_letp_clash _ _ (skelMeets_letp_pairFive _) ?_
  rintro ⟨u, ⟨σ, hm, -⟩, w, σ', hw, hs⟩
  have hσ' : σ' = [("y", w)] := by
    rcases matchPat_var_eq.1 hw with ⟨h, -⟩ | ⟨-, h⟩
    · simp [lookup] at h
    · exact h
  subst hσ'
  simp only [con, List.foldr, Skel, lookup] at hs
  obtain ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, hy, rfl⟩ := hs
  simp only [reduceIte, Option.some.injEq] at hy
  subst hy
  exact pairFive_rejects_three hm

/-- The inner let has a fresh variable as its pattern and is admitted; the outer
let is not. -/
theorem letBody_not_admitted : ¬LetsAdmitted [spinEq] [] letBody := by
  rintro ⟨hcf | ⟨-, W, -, hadm⟩, -⟩
  · simp [con, CallFree] at hcf
  · simp only [pairFive, con, List.foldr] at hadm
    rcases hadm with hc | hcf
    · rcases hc with _ | _ | _ | _ | _ | _ | ⟨hc⟩
      rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨hc, _⟩
      rcases hc with _ | ⟨hm⟩
      simp [CertMatch] at hm
    · simp [CallFree] at hcf

theorem letBody_inner_admitted :
    LetAdmitted [spinEq] (patVars pairFive) (.var "y") (.call "spin" (.atom "0")) :=
  Or.inr ⟨by simp [Linear, patVars], [], fun _ _ _ h => absurd h List.not_mem_nil,
    .certain (.recv (by decide))⟩

/-! ### A callee's output -/

/-- `(= (h $n) (Pair 3 (spin $n)))`. -/
def outputEq : Equation := ⟨"h", .var "n", con "Pair" [.atom "3", .call "spin" (.var "n")]⟩

def outputProgram : Program := [spinEq, outputEq]

/-- `(let (Pair 5 $x) (h 0) $x)`. -/
def calleeOutput : Tm := .letp pairFive (.call "h" (.atom "0")) (.var "x")

theorem select_output :
    select outputProgram "h" (.atom "0") = some (outputEq, [("n", .atom "0")]) := by
  decide

theorem calleeOutput_scoped : WellScoped [] calleeOutput ∧
    WellScoped (patVars outputEq.param) outputEq.body := by
  simp [calleeOutput, outputEq, pairFive, con, WellScoped, IsPat, patVars]

theorem calleeOutput_value_first : Diverges outputProgram noHost [] calleeOutput :=
  diverges_letp _ _ <| diverges_call _ _ (settles_atom _ _ _ _) select_output <|
    diverges_cons_right _ _ (settles_atom _ _ _ _) <|
      diverges_cons_right _ _ (settles_atom _ _ _ _) <| diverges_cons_left _ _ <|
        diverges_call _ _ (settles_var _ _ (v := .atom "0") (by decide)) (select_spin _ _)
          (spin_diverges _ _ _)

theorem calleeOutput_destination_first :
    evalD outputProgram noHost 3 [] calleeOutput Set.univ = .failure := by
  unfold calleeOutput
  rw [evalD_succ_pos _ _ (skelMeets_letp_pairFive _)]
  simp only [stepD]
  rw [evalD_succ_pos _ _ (env := []) (t := .call "h" (.atom "0"))
    (M := {w | ∃ σ, matchPat [] pairFive w = some σ ∧ SkelMeets σ (.var "x") Set.univ})
    ⟨_, pairFiveDest_mem, trivial⟩]
  simp only [stepD]
  rw [evalD_atom _ _ (Set.mem_univ _), Outcome.bind_value, select_output]
  dsimp only
  rw [evalD_succ_neg, Outcome.bind_failure]
  rintro ⟨u, ⟨σ, hm, -⟩, hs⟩
  simp only [outputEq, con, List.foldr, Skel] at hs
  obtain ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, -, rfl⟩ := hs
  exact pairFive_rejects_three hm

theorem calleeOutput_not_admitted : ¬LetsAdmitted outputProgram [] calleeOutput := by
  have hbody : ∀ (W : Certificate) (R : List String), ¬Admits W R outputEq.body pairFive := by
    intro W R hadm
    simp only [outputEq, pairFive, con, List.foldr] at hadm
    rcases hadm with hc | hcf
    · rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨hc, _⟩
      rcases hc with _ | ⟨hm⟩
      simp [CertMatch] at hm
    · simp [CallFree] at hcf
  rintro ⟨hcf | ⟨-, W, hW, hadm⟩, -⟩
  · exact (hcf : False).elim
  · have hmem : outputEq ∈ outputProgram := by simp [outputProgram]
    rcases hadm with hc | hcf | _ | hf
    · rcases hc with _ | _ | _ | _ | hf
      exact hbody W _ (.certain ((hW _ _ _ hf outputEq hmem rfl).1 rfl))
    · simp [CallFree] at hcf
    · exact hbody W _ ((hW _ _ _ hf outputEq hmem rfl).2 rfl)

/-! ### An `if` branch -/

/-- `(let (Pair 5 $x) (if True (Pair 3 (spin 0)) (Pair 5 1)) $x)`. -/
def ifBranch : Tm :=
  .letp pairFive
    (.ite (.atom "True") (con "Pair" [.atom "3", .call "spin" (.atom "0")])
      (con "Pair" [.atom "5", .atom "1"]))
    (.var "x")

theorem ifBranch_scoped : WellScoped [] ifBranch := by
  simp [ifBranch, pairFive, con, WellScoped, IsPat, patVars]

theorem ifBranch_value_first : Diverges [spinEq] noHost [] ifBranch :=
  diverges_letp _ _ <| diverges_ite_true _ _ (settles_atom _ _ _ _) <|
    diverges_cons_right _ _ (settles_atom _ _ _ _) <|
      diverges_cons_right _ _ (settles_atom _ _ _ _) <| diverges_cons_left _ _ <|
        spin_zero_diverges [] _ _

theorem ifBranch_destination_first :
    evalD [spinEq] noHost 3 [] ifBranch Set.univ = .failure := by
  unfold ifBranch
  rw [evalD_succ_pos _ _ (skelMeets_letp_pairFive _)]
  simp only [stepD]
  rw [evalD_succ_pos _ _ (env := [])
    (t := .ite (.atom "True") (con "Pair" [.atom "3", .call "spin" (.atom "0")])
      (con "Pair" [.atom "5", .atom "1"]))
    (M := {w | ∃ σ, matchPat [] pairFive w = some σ ∧ SkelMeets σ (.var "x") Set.univ})
    ⟨_, pairFiveDest_mem, trivial⟩]
  simp only [stepD]
  rw [evalD_atom _ _ (Set.mem_univ _), Outcome.bind_value]
  simp only [reduceIte]
  rw [evalD_succ_neg, Outcome.bind_failure]
  rintro ⟨u, ⟨σ, hm, -⟩, hs⟩
  simp only [con, List.foldr, Skel] at hs
  obtain ⟨_, _, rfl, rfl, _, _, rfl, rfl, _, _, rfl, -, rfl⟩ := hs
  exact pairFive_rejects_three hm

theorem ifBranch_not_admitted : ¬LetsAdmitted [spinEq] [] ifBranch := by
  have hbranch : ∀ (W : Certificate) (R : List String),
      ¬Admits W R (con "Pair" [.atom "3", .call "spin" (.atom "0")]) pairFive := by
    intro W R hadm
    simp only [pairFive, con, List.foldr] at hadm
    rcases hadm with hc | hcf
    · rcases hc with _ | _ | _ | ⟨_, hc⟩
      rcases hc with _ | _ | _ | ⟨hc, _⟩
      rcases hc with _ | ⟨hm⟩
      simp [CertMatch] at hm
    · simp [CallFree] at hcf
  rintro ⟨hcf | ⟨-, W, -, hadm⟩, -⟩
  · simp [con, CallFree] at hcf
  · rcases hadm with hc | hcf | ⟨ha, -⟩
    · rcases hc with _ | _ | _ | _ | _ | ⟨hc, -⟩
      exact hbranch W _ (.certain hc)
    · simp [CallFree, con] at hcf
    · exact hbranch W _ ha

/-! ## Admitted lets -/

/-! ### A loop over a pair -/

def succT (t : Tm) : Tm := con "S" [t]
def zeroT : Tm := .atom "Z"
def succV (v : Val) : Val := conV "S" [v]
def zeroV : Val := .atom "Z"

/-- The pattern `(Pair $a $b)`. -/
def pairAB : Tm := con "Pair" [.var "a", .var "b"]

/-- `(= (fib Z) (Pair Z (S Z)))`. -/
def fibZero : Equation := ⟨"fib", zeroT, con "Pair" [zeroT, succT zeroT]⟩

/-- `(= (fib (S $n)) (let (Pair $a $b) (fib $n) (Pair $b (add (Args $a $b)))))`. -/
def fibSucc : Equation :=
  ⟨"fib", succT (.var "n"),
    .letp pairAB (.call "fib" (.var "n"))
      (con "Pair" [.var "b", .call "add" (con "Args" [.var "a", .var "b"])])⟩

/-- `(= (add (Args Z $m)) $m)`. -/
def addZero : Equation := ⟨"add", con "Args" [zeroT, .var "m"], .var "m"⟩

/-- `(= (add (Args (S $k) $m)) (S (add (Args $k $m))))`. -/
def addSucc : Equation :=
  ⟨"add", con "Args" [succT (.var "k"), .var "m"],
    succT (.call "add" (con "Args" [.var "k", .var "m"]))⟩

def fibProgram : Program := [fibZero, fibSucc, addZero, addSucc]

/-- The coarse rule refuses the loop's let: its value makes a call and its
pattern is not a variable. -/
theorem fib_let_needs_evidence : ¬CallFree (.call "fib" (.var "n")) ∧ ∀ x, pairAB ≠ .var x :=
  ⟨id, fun _ h => by cases h⟩

theorem fib_receiving : receiving ["n"] pairAB = ["a", "b"] := by decide

/-- The certificate of the loop's let: `fib` entered with `(Pair $a $b)` certainly
meets it. -/
def fibCertificate : Certificate := [("fib", pairAB, true)]

theorem fib_certain_pair (t₁ t₂ : Tm) :
    Certain fibCertificate ["a", "b"] (con "Pair" [t₁, t₂]) pairAB :=
  .cons (.atom rfl) (.cons (.recv (by decide)) (.cons (.recv (by decide)) (.nil trivial)))

theorem fib_consistent : Consistent fibProgram fibCertificate ["a", "b"] := by
  intro f d c hW e he hhead
  simp only [fibCertificate, List.mem_singleton, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
  simp only [fibProgram, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact fib_certain_pair _ _
  · exact .letp (fib_certain_pair _ _)
  · exact absurd hhead (by decide)
  · exact absurd hhead (by decide)

theorem fib_admitted : ProgramAdmitted fibProgram := by
  intro e he
  simp only [fibProgram, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp [fibZero, zeroT, succT, con, IsPat, WellScoped, LetsAdmitted]
  · refine ⟨by simp [fibSucc, succT, con, IsPat], by
      simp [fibSucc, pairAB, succT, con, WellScoped, IsPat, patVars], ?_⟩
    refine ⟨Or.inr ⟨(by decide : (patVars pairAB).Nodup), fibCertificate, ?_, ?_⟩,
      by simp [LetsAdmitted], by
      simp [LetsAdmitted, con]⟩
    · show Consistent fibProgram fibCertificate (receiving (patVars (succT (.var "n"))) pairAB)
      simpa [succT, con, patVars, fib_receiving] using fib_consistent
    · show Admits fibCertificate (receiving (patVars (succT (.var "n"))) pairAB)
        (.call "fib" (.var "n")) pairAB
      simpa [succT, con, patVars, fib_receiving] using
        (Admits.certain (Certain.call (List.mem_singleton_self _)) :
          Admits fibCertificate ["a", "b"] (.call "fib" (.var "n")) pairAB)
  · simp [addZero, zeroT, con, IsPat, WellScoped, LetsAdmitted, patVars]
  · simp [addSucc, succT, con, IsPat, WellScoped, LetsAdmitted, patVars]

/-- `(fib (S (S (S Z))))`. -/
def fibThree : Tm := .call "fib" (succT (succT (succT zeroT)))

/-- `(Pair 2 3)` in successor numerals. -/
def pairTwoThree : Val :=
  conV "Pair" [succV (succV zeroV), succV (succV (succV zeroV))]

theorem fibThree_value_first : evalV fibProgram noHost 15 [] fibThree = .value pairTwoThree := by
  decide

theorem fibThree_destination_first :
    ∃ n, evalD fibProgram noHost n [] fibThree Set.univ = .value pairTwoThree :=
  (destination_square fibProgram noHost fib_admitted
    (by simp [fibThree, succT, zeroT, con, WellScoped])
    (by simp [fibThree, succT, zeroT, con, LetsAdmitted]) (by simp)).1
    ⟨15, fibThree_value_first⟩

/-! ### A lookup judged per equation -/

/-- The pattern `(Just $v)`. -/
def justV : Tm := con "Just" [.var "v"]

/-- `(= (find (Args $k Nil)) Nothing)`. -/
def findNil : Equation := ⟨"find", con "Args" [.var "k", .atom "Nil"], .atom "Nothing"⟩

/-- `(= (find (Args $k (Cons (Entry $j $w) $rest)))
       (if (eq (Args $k $j)) (Just $w) (find (Args $k $rest))))`. -/
def findCons : Equation :=
  ⟨"find", con "Args" [.var "k", con "Cons" [con "Entry" [.var "j", .var "w"], .var "rest"]],
    .ite (.prim "eq" (con "Args" [.var "k", .var "j"])) (con "Just" [.var "w"])
      (.call "find" (con "Args" [.var "k", .var "rest"]))⟩

def findProgram : Program := [findNil, findCons]

/-- The host's `eq` on `(Args a b)`. -/
def eqHost : Host := fun f v =>
  if f = "eq" then
    match v with
    | .cons (.atom "Args") (.cons a (.cons b .nil)) =>
      some (.atom (if a = b then "True" else "False"))
    | _ => none
  else none

/-- `find` entered with `(Just $v)` admits it: one equation answers `Nothing`, which
makes no call, and the other answers `(Just $w)` or calls `find` again. -/
def findCertificate : Certificate := [("find", justV, false)]

/-- `Nothing` does not certainly meet `(Just $v)`: the evidence is per equation. -/
theorem nothing_not_certain (W : Certificate) (R : List String) :
    ¬Certain W R (.atom "Nothing") justV := by
  intro h
  rcases h with _ | ⟨hm⟩
  exact hm

theorem find_consistent : Consistent findProgram findCertificate ["v"] := by
  intro f d c hW e he hhead
  simp only [findCertificate, List.mem_singleton, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  simp only [findProgram, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact .callFree trivial
  · exact .ite (.certain (.cons (.atom rfl) (.cons (.recv (by decide)) (.nil trivial))))
      (.call (List.mem_singleton_self _))

theorem find_admitted : ProgramAdmitted findProgram := by
  intro e he
  simp only [findProgram, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp [findNil, con, IsPat, WellScoped, LetsAdmitted]
  · simp [findCons, con, IsPat, WellScoped, LetsAdmitted, patVars]

/-- A table `(Cons (Entry a 1) (Cons (Entry b 2) Nil))`. -/
def table : Tm :=
  con "Cons" [con "Entry" [.atom "a", .atom "1"],
    con "Cons" [con "Entry" [.atom "b", .atom "2"], .atom "Nil"]]

/-- `(let (Just $v) (find (Args key table)) $v)`. -/
def lookupQuery (key : String) : Tm :=
  .letp justV (.call "find" (con "Args" [.atom key, table])) (.var "v")

theorem lookupQuery_admitted (key : String) : LetsAdmitted findProgram [] (lookupQuery key) := by
  refine ⟨Or.inr ⟨(by decide : (patVars justV).Nodup), findCertificate, ?_, .call ?_⟩, by
    simp [LetsAdmitted, table, con], trivial⟩
  · simpa [receiving, justV, con, patVars] using find_consistent
  · simp [justV, con, findCertificate]

theorem lookupQuery_scoped (key : String) : WellScoped [] (lookupQuery key) := by
  simp [lookupQuery, justV, table, con, WellScoped, IsPat, patVars]

theorem lookup_found_value_first :
    evalV findProgram eqHost 30 [] (lookupQuery "b") = .value (.atom "2") := by
  decide

theorem lookup_missing_value_first :
    evalV findProgram eqHost 30 [] (lookupQuery "c") = .failure := by
  decide

theorem lookup_found_destination_first :
    ∃ n, evalD findProgram eqHost n [] (lookupQuery "b") Set.univ = .value (.atom "2") :=
  (destination_square findProgram eqHost find_admitted (lookupQuery_scoped "b")
    (lookupQuery_admitted "b") (by simp)).1 ⟨30, lookup_found_value_first⟩

theorem lookup_missing_destination_first :
    ∃ n, evalD findProgram eqHost n [] (lookupQuery "c") Set.univ = .failure :=
  (destination_square findProgram eqHost find_admitted (lookupQuery_scoped "c")
    (lookupQuery_admitted "c") (by simp)).1 ⟨30, lookup_missing_value_first⟩

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.LetDestinations.Controls
