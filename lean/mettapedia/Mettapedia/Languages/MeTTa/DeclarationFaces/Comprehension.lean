import Mettapedia.Languages.MeTTa.DeclarationFaces.Controls

/-!
# Types are sets for the programmable fragment: sorts, comprehensions and subset domains

In an admitted scope every sort denotes a set of data (`Signature.Denotes`). A **comprehension**
`{| x : τ | p x |}` names a declared predicate `p : τ → Bool` of the same scope; it denotes the data
of `τ` on which `p` computes to the truth constant (`Admitted.DenotesComp`), and a closed term has the
comprehension sort when it has sort `τ` and `p` computes to truth on it (`Admitted.HasSortComp`).

* **Typing and membership agree** (`Admitted.hasSortComp_iff_mem`): a closed term of sort `τ` has the
  comprehension sort exactly when its value is in the comprehension's set.
* **Membership is decided by evaluation** (`Admitted.hasSortComp_iff_evalTm`): the predicate is a
  program of the admitted fragment, so running it decides the comprehension.
* **Typing certifies membership; it is not membership** (`typing_finer_than_membership`): a sorted
  term's value lies in its sort's set, but a term can compute to a value of a sort without having
  that sort: `(add Z Nil)` computes to `Nil` and has no sort.
* **A subset domain admits a partial function** (`pred_covered_on_nonzero`,
  `pred_unique_on_nonzero`): the equation `(= (pred (S $n)) $n)` alone is refused for missing the
  case `Z`; on the comprehension `{| n : Nat | nonzero n |}` it covers every value, and every
  interpretation satisfying it agrees there.

Three readings of the predicate, and what each costs: a predicate that is a program of the admitted
fragment (here: typing decidable by evaluation); a program outside it (membership only
semi-decidable, typing undecidable in general); a proposition (typing needs a proof, the
`type:prove` route). Only the first is formalized here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm Relation

universe u

variable {S : Type u} [DecidableEq S] {sig : Signature S} {P : Program S}

/-- **A comprehension sort** `{| x : base | pred x |}`, with the constructor that means truth. -/
structure CompSort (S : Type u) where
  base : Sort'
  pred : S
  yes : S

namespace Admitted

/-- **The set a comprehension denotes.** -/
def DenotesComp (adm : Admitted sig P) (c : CompSort S) : Set (Tm S) :=
  {v | v ∈ sig.Denotes c.base ∧ adm.normalForm (.app c.pred [v]) = .app c.yes []}

/-- **The comprehension typing** of a closed term. -/
def HasSortComp (adm : Admitted sig P) (t : Tm S) (c : CompSort S) : Prop :=
  HasSort sig Ctx.empty t c.base ∧ adm.normalForm (.app c.pred [t]) = .app c.yes []

/-- A call's normal form does not change when its argument is replaced by the argument's normal
form. -/
theorem normalForm_call_arg (adm : Admitted sig P) (f : S) (t : Tm S) :
    adm.normalForm (.app f [adm.normalForm t]) = adm.normalForm (.app f [t]) := by
  symm
  apply adm.normalForm_of_steps
  exact steps_args f [t] [adm.normalForm t] rfl fun i hi _ => by
    have : i = 0 := by simpa using hi
    subst this
    simpa using (adm.normalForm_spec t).1

/-- **Typing and membership agree** for a closed term of the base sort. -/
theorem hasSortComp_iff_mem (adm : Admitted sig P) (c : CompSort S) {t : Tm S}
    (typed : HasSort sig Ctx.empty t c.base) :
    adm.HasSortComp t c ↔ adm.normalForm t ∈ adm.DenotesComp c := by
  constructor
  · rintro ⟨_, holds⟩
    exact ⟨adm.normalForm_value typed, by rw [normalForm_call_arg]; exact holds⟩
  · rintro ⟨_, holds⟩
    exact ⟨typed, by rw [← normalForm_call_arg]; exact holds⟩

/-- **Membership is decided by evaluation**: the comprehension typing holds exactly when the
evaluator runs the predicate to the single result truth. -/
theorem hasSortComp_iff_evalTm (adm : Admitted sig P) (c : CompSort S) {t : Tm S}
    (typed : HasSort sig Ctx.empty t c.base) :
    adm.HasSortComp t c ↔ ∃ n, evalTm P n (.app c.pred [t]) = some [.app c.yes []] := by
  obtain ⟨⟨n, hn⟩, result⟩ := adm.evalTm_result (.app c.pred [t])
  constructor
  · rintro ⟨_, holds⟩
    exact ⟨n, by rw [hn, holds]⟩
  · rintro ⟨m, hm⟩
    have := result m _ hm
    simp only [List.cons.injEq, and_true] at this
    exact ⟨typed, this.symm⟩

end Admitted

/-! ## Controls -/

namespace Controls

/-- `(: Bool Type)`, `(: True Bool)`, `(: False Bool)`. -/
def boolData : DataDecl String := ⟨"Bool", [], [("True", []), ("False", [])]⟩

/-- `(: nonzero (-> Nat Bool))`. -/
def nonzeroSig : Signature String := ⟨[natData, boolData], [⟨"nonzero", [nat], .app "Bool" []⟩]⟩

/-- `(= (nonzero Z) False)`, `(= (nonzero (S $n)) True)`. -/
def nonzeroProgram : Program String :=
  [⟨.app "nonzero" [num 0], .app "False" []⟩, ⟨.app "nonzero" [.app "S" [.var "n"]], .app "True" []⟩]

theorem nonzero_admitted : admit nonzeroSig nonzeroProgram = none := by decide

theorem nonzero_adm : Admitted nonzeroSig nonzeroProgram := admit_sound nonzero_admitted

/-- The comprehension `{| n : Nat | nonzero n |}`. -/
def positive : CompSort String := ⟨nat, "nonzero", "True"⟩

/-- `(nonzero Z)` computes to `False`. -/
theorem nonzero_zero : nonzero_adm.normalForm (.app "nonzero" [num 0]) = .app "False" [] := by
  have h := (nonzero_adm.evalTm_result (.app "nonzero" [num 0])).2 5 _
    (by decide : evalTm nonzeroProgram 5 (.app "nonzero" [num 0]) = some [.app "False" []])
  simpa using h.symm

/-- **Membership decided by evaluation**: `2` is in `{| n : Nat | nonzero n |}`. -/
example : nonzero_adm.HasSortComp (num 2) positive :=
  (nonzero_adm.hasSortComp_iff_evalTm positive
    (.ctor (d := natData) (fields := [nat]) (fun _ => nat) (by simp [nonzeroSig]) (by simp [natData])
      (by simp) fun i hi hj => by
        have : i = 0 := by simpa using hi
        subst this
        exact .ctor (d := natData) (fields := [nat]) (fun _ => nat) (by simp [nonzeroSig])
          (by simp [natData]) (by simp) fun i hi hj => by
            have : i = 0 := by simpa using hi
            subst this
            exact .ctor (d := natData) (fields := []) (fun _ => nat) (by simp [nonzeroSig])
              (by simp [natData]) (by simp) fun i hi _ => absurd hi (by simp))).mpr
    ⟨5, by decide⟩

/-- **`Z` is not in the comprehension.** -/
theorem zero_not_positive : num 0 ∉ nonzero_adm.DenotesComp positive := by
  rintro ⟨_, holds⟩
  rw [show (positive : CompSort String).pred = "nonzero" from rfl, nonzero_zero] at holds
  simp [positive] at holds

/-- A value of sort `Nat` is `Z` or `S` of a value. -/
theorem nat_value_cases {v : Tm String} (value : nonzeroSig.IsValueOf v nat) :
    v = num 0 ∨ ∃ w, v = .app "S" [w] := by
  obtain ⟨data, typed⟩ := value
  cases data with
  | @app c args _ _ =>
      rcases HasSort.app_inv typed with ⟨d, hd, fields, hc, θ, hsort, len, _⟩ |
          ⟨fd, hfd, hname, _, _, _⟩
      · simp only [nonzeroSig, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · simp only [natData, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · left
            simp at len
            subst len
            rfl
          · right
            obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp (by simpa using len)
            exact ⟨w, rfl⟩
        · simp [DataDecl.sort, boolData] at hsort
      · simp only [nonzeroSig, List.mem_cons, List.not_mem_nil, or_false] at hfd
        subst hfd
        rename_i isCtor _
        simp at isCtor

/-- `(: pred (-> Nat Nat))` with `(= (pred (S $n)) $n)` alone: refused over all of `Nat`. -/
theorem pred_refused_on_nat :
    admit (⟨[natData, boolData], [⟨"pred", [nat], nat⟩]⟩ : Signature String) predPartial =
      some (.missingCase "pred") := by decide

/-- **On the subset domain the partial `pred` covers every value.** -/
theorem pred_covered_on_nonzero {v : Tm String} (member : v ∈ nonzero_adm.DenotesComp positive) :
    ∃ σ : String → Tm String, predPartial[0].lhs.subst σ = .app "pred" [v] := by
  obtain ⟨value, holds⟩ := member
  rcases nat_value_cases value with rfl | ⟨w, rfl⟩
  · exact absurd ⟨value, holds⟩ zero_not_positive
  · exact ⟨fun _ => w, by simp [predPartial]⟩

/-- **On the subset domain the partial `pred` is determined**: every interpretation satisfying its
equation gives `w` at `(S w)`. -/
theorem pred_unique_on_nonzero (g : String → List (Tm String) → Tm String)
    (equation : ∀ ρ : String → Tm String,
      interp predPartial g ρ predPartial[0].lhs = interp predPartial g ρ predPartial[0].rhs)
    {v : Tm String} (member : v ∈ nonzero_adm.DenotesComp positive) :
    ∃ w, v = .app "S" [w] ∧ g "pred" [v] = w := by
  obtain ⟨value, holds⟩ := member
  rcases nat_value_cases value with rfl | ⟨w, rfl⟩
  · exact absurd ⟨value, holds⟩ zero_not_positive
  · refine ⟨w, rfl, ?_⟩
    have defined : predPartial.Defines "pred" := ⟨predPartial[0], by simp [predPartial], rfl⟩
    have undefinedS : ¬ predPartial.Defines "S" := by
      rintro ⟨e, he, h⟩
      simp only [predPartial, List.mem_singleton] at he
      subst he
      simp [head?] at h
    have := equation fun _ => w
    change interp predPartial g (fun _ => w) (.app "pred" [.app "S" [.var "n"]]) =
      interp predPartial g (fun _ => w) (.var "n") at this
    rw [interp_app, if_pos defined, List.map_cons, List.map_nil, interp_app, if_neg undefinedS]
      at this
    simpa using this

/-- `(add Z Nil)`: ill-sorted, yet it computes to `Nil`. -/
def addZeroNil : Tm String := .app "add" [num 0, .app "Nil" []]

/-- **Typing is finer than membership**: `(add Z Nil)` computes to `Nil`, a value of the sort
`(List Nat)`, and has no sort. -/
theorem typing_finer_than_membership :
    evalTm addProgram 5 addZeroNil = some [.app "Nil" []] ∧
      ∀ τ, ¬ HasSort (⟨[natData, listData], [⟨"add", [nat, nat], nat⟩]⟩ : Signature String)
        Ctx.empty addZeroNil τ := by
  refine ⟨by decide, fun τ typed => ?_⟩
  rcases HasSort.app_inv typed with ⟨d, hd, fields, hc, _, _, _⟩ | ⟨fd, hfd, hname, θ, _, len, args⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [natData, listData] at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfd
    subst hfd
    have second := args 1 (by simp) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at second
    rcases HasSort.app_inv second with ⟨d, hd, fields, hc, θ', hsort, _, _⟩ |
        ⟨fd, hfd, hname', _, _, _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · simp [natData] at hc
      · simp [DataDecl.sort, listData] at hsort
    · simp at hfd; subst hfd; simp at hname'

end Controls

end Mettapedia.Languages.MeTTa.DeclarationFaces
