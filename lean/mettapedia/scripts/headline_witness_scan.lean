import Lean

/-!
# Hypothesis-witness scan

A theorem whose hypotheses can never hold together is true and useless. This script
looks for evidence that the hypotheses of a theorem hold together.

**Witnessed.** A theorem `t` is witnessed when some declaration applies `t` with every
hypothesis argument closed: no bound or free variable, no metavariable, no `sorryAx`.
The hypothesis positions are

* binders whose type is a proposition (explicit, implicit or instance-implicit), and
* binders whose type is a structure with at least one proof field (a certificate
  bundle such as `ExtensionalDefinableCut T`).

A closed argument at each of these positions is a proof that the hypotheses hold
together at the given data, so a witnessed theorem is not vacuous. Data arguments may
be anything. Aliases such as `abbrev e := @t` are not applications and do not count.

Witnesses propagate through proofs: when `t a₁ … aₙ` is a closed application and the
proof of `t` is `fun x₁ … xₙ => b`, every closed application inside `b[a/x]` witnesses the
theorem it applies (reported as `t.via`).

**Statuses.**
* `no-hypotheses`: no hypothesis position; nothing to witness.
* `refutation`: the conclusion is `False`, so the hypotheses are meant to be refuted.
* `witnessed`: as above; the witnessing declaration is reported.
* `structs-inhabited`: no closed application was found, but every hypothesis position is
  a structure that some imported declaration builds, with closed proof fields or
  generically in types and instances (for example a theorem about every Henkin model);
  the theorem is not vacuous unless its structures cannot be inhabited at the same data.
* `unwitnessed`: no closed application was found among the imported declarations.

**Flags** (unwitnessed theorems only).
* `ex-falso`: the proof eliminates `False` (or an empty type) right after introducing the
  hypotheses, so the hypotheses cannot hold together and the theorem is vacuous, whatever
  its conclusion.
* `contains+restricts`: some binder `T` is required to contain a set (`∀ x ∈ A, x ∈ T` or
  `A ⊆ T`) and to satisfy a pointwise restriction (`∀ x ∈ T, …`, other than an inclusion
  into another binder). This is the shape of a
  parameter-freeness requirement on a theory that must also contain a schema with
  parameters; check that every member of `A` meets the restriction.
* `uninhabited:S`: a hypothesis position has type a structure `S` of the package (a
  certificate bundle, or a proposition declared as a structure), no
  imported declaration applies the constructor of `S` with closed proof fields, and no
  package declaration constructs `S`: none has type `∀ b₁ … bₖ, S a₁ … aₙ` with every
  binder ranging over types (a universe, a family of types or of propositions) or an
  instance of a class of data. Check whether `S` can be inhabited at all (a provider or
  package of assumptions with no instance).
* `unreferenced`: no other imported declaration mentions the theorem.

**Limits.** `unwitnessed` is not a verdict: most such theorems are general lemmas whose
hypotheses plainly hold together, with no closed application in the imported modules.
Witnesses are searched only among the imported modules. A construction that takes a
structure or a proof as argument (a canonical model built from a scheduler provider) does
not count as inhabiting its structure, so `uninhabited:S` asks for review; only `ex-falso`
shows vacuity by itself.

## Usage

```
lake env lean --run scripts/headline_witness_scan.lean audit \
  --imports-file <modules.txt> --module-prefix <Prefix> [--module-prefix <Prefix>]... \
  [--names-file <names.txt>] --out <report.tsv>

lake env lean --run scripts/headline_witness_scan.lean verify \
  --imports-file <modules.txt> --pairs-file <pairs.tsv> --out <report.tsv>
```

`modules.txt` lists the modules to import, one per line. In `audit` mode the theorems
examined are those of the imported modules whose names start with a `--module-prefix`
(or exactly the names of `--names-file`); every imported declaration of the `Mettapedia`
package is searched for uses. In `verify` mode each line of `pairs.tsv` is
`<theorem>\t<witness>`, and the check succeeds when the value of `<witness>` contains a
closed application of `<theorem>`, directly or through the instantiated proofs of the
theorems it applies (to depth four). The exit code is `1` when a pair fails or a name is
missing.
-/

open Lean Meta

namespace HeadlineWitnessScan

inductive HypKind where
  | prop
  | struct
  deriving BEq, Inhabited

structure Hyp where
  index : Nat
  kind : HypKind
  deriving Inhabited

structure Info where
  name : Name
  module : Name
  hyps : Array Hyp
  falseConclusion : Bool
  containsRestricts : Bool
  /-- The structures at hypothesis positions: the certificate bundles at `struct`
  positions, and the propositions declared as structures at `prop` positions. -/
  structs : Array Name := #[]
  /-- The number of binders of the statement, before its conclusion. -/
  arity : Nat := 0
  deriving Inhabited

/-- Whether `e` can serve as concrete evidence. -/
def closedArg (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && !e.hasSorry

/-- The structure of `ty` when `ty` is a structure type with at least one proof field. -/
def structWithProofField? (ty : Expr) : MetaM (Option Name) := do
  let ty ← whnfR ty
  let .const s us := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env s do return none
  let ctor := getStructureCtor env s
  let args := ty.getAppArgs
  if args.size < ctor.numParams then return none
  let ctorTy ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams us)
    (args.extract 0 ctor.numParams)
  let proofField ← forallTelescopeReducing ctorTy fun fields _ =>
    fields.anyM fun f => do isProp (← inferType f)
  return if proofField then some s else none

/-- `@Membership.mem α γ inst coll elem` as `(coll, elem)`. -/
def memParts? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Membership.mem 5 then some (e.getArg! 3, e.getArg! 4) else none

/-- The binder `T` such that `ty` says `∀ x ∈ A, x ∈ T` (with `A ≠ T`) or `A ⊆ T`. -/
def containsTarget? (ty : Expr) : MetaM (Option FVarId) := do
  if ty.isAppOfArity ``HasSubset.Subset 4 then
    let t := ty.getArg! 3
    return if t.isFVar then some t.fvarId! else none
  forallTelescope ty fun ys body => do
    if ys.size < 2 then return none
    let some (coll, elem) := memParts? body | return none
    unless coll.isFVar && elem == ys[0]! do return none
    let some (src, elem') := memParts? (← inferType ys[1]!) | return none
    unless elem' == ys[0]! && src != coll do return none
    return some coll.fvarId!

/-- The binder `T` such that `ty` says `∀ x ∈ T, P x` for a `P` other than membership in a
binder (an inclusion `T ⊆ U` into a free `U` restricts nothing). -/
def restrictsTarget? (ty : Expr) : MetaM (Option FVarId) := do
  forallTelescope ty fun ys body => do
    if ys.size < 2 then return none
    let some (coll, elem) := memParts? (← inferType ys[1]!) | return none
    unless coll.isFVar && elem == ys[0]! do return none
    if ys.size == 2 then
      if let some (target, elem') := memParts? body then
        if target.isFVar && elem' == ys[0]! then return none
    return some coll.fvarId!

def analyze (name module : Name) (type : Expr) : MetaM Info := do
  forallTelescope type fun xs body => do
    let mut hyps : Array Hyp := #[]
    let mut contained : Array FVarId := #[]
    let mut restricted : Array FVarId := #[]
    let mut structs : Array Name := #[]
    for h : i in [:xs.size] do
      let x := xs[i]
      let ty ← inferType x
      if ← isProp ty then
        hyps := hyps.push { index := i, kind := .prop }
        if let some t ← containsTarget? ty then contained := contained.push t
        if let some t ← restrictsTarget? ty then restricted := restricted.push t
        -- A proposition declared as a structure (a package of assumptions in `Prop`) is
        -- checked for inhabitation too.
        if let .const s _ := (← whnfR ty).getAppFn then
          if isStructure (← getEnv) s && !structs.contains s then structs := structs.push s
      else if let some s ← structWithProofField? ty then
        hyps := hyps.push { index := i, kind := .struct }
        unless structs.contains s do structs := structs.push s
    let falseConclusion := (← whnfR body).isConstOf ``False
    return { name, module, hyps, falseConclusion,
             containsRestricts := contained.any restricted.contains, structs, arity := xs.size }

def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<witness-scan>", fileMap := default,
                              maxHeartbeats := 0 }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-! ## Searching declaration values for closed applications -/

unsafe structure ScanState where
  visited : PtrSet Expr := mkPtrSet
  witness : Std.HashMap Name Name := {}
  /-- The closed application found for each witnessed target. -/
  application : Std.HashMap Name Expr := {}
  /-- Witnessed targets whose proofs have not yet been instantiated. -/
  pending : Array Name := #[]

unsafe def visit (targets : Std.HashMap Name Info) (user : Name) (e : Expr) :
    StateM ScanState Unit := do
  if (← get).visited.contains e then return
  modify fun s => { s with visited := s.visited.insert e }
  match e with
  | .app f a =>
      if let .const n _ := e.getAppFn then
        if let some info := targets[n]? then
          unless (← get).witness.contains n do
            let args := e.getAppArgs
            let needed := info.hyps.foldl (fun m h => max m (h.index + 1)) 0
            if args.size ≥ needed && info.hyps.all (fun h => closedArg args[h.index]!) then
              modify fun s => { s with witness := s.witness.insert n user,
                                       application := s.application.insert n e,
                                       pending := s.pending.push n }
      visit targets user f
      visit targets user a
  | .lam _ t b _ | .forallE _ t b _ =>
      visit targets user t
      visit targets user b
  | .letE _ t v b _ =>
      visit targets user t
      visit targets user v
      visit targets user b
  | .mdata _ b | .proj _ _ b => visit targets user b
  | _ => return

/-- Whether a proof derives `False` from its own hypotheses at the top: after its leading
abstractions, it is an elimination of `False` or of an empty type. Such a theorem has
hypotheses that cannot hold together. -/
def exFalsoProof (arity : Nat) (v : Expr) : Bool :=
  let rec dropLams : Nat → Expr → Expr
    | 0, e => e
    | n + 1, .lam _ _ b _ => dropLams n b
    | n + 1, .mdata _ b => dropLams (n + 1) b
    | _, e => e
  let body := dropLams arity v
  let rec strip : Nat → Expr → Expr
    | 0, e => e
    | n + 1, e => match e with
      | .mdata _ b => strip n b
      | .letE _ _ _ b _ => strip n b
      | e => e
  let body := strip 16 body
  match body.getAppFn with
  | .const n _ => n ∈ [``False.elim, ``False.rec, ``False.casesOn, ``absurd, ``Empty.elim,
      ``Empty.rec, ``Empty.casesOn, ``PEmpty.elim, ``PEmpty.rec, ``PEmpty.casesOn, ``Not.elim]
  | _ => false

/-- Whether `ty` is an application of a class whose instances are proofs. -/
def propClass (env : Environment) (ty : Expr) : Bool :=
  match ty.getAppFn with
  | .const c _ => match env.find? c with
    | some ci => ci.type.getForallBody.isProp
    | none => true
  | _ => true

/-- The structure `S` of `structs` when `ty` is `∀ b₁ … bₖ, S a₁ … aₙ` and every binder
ranges over types (a universe, a family of types or of propositions) or is an instance of a
class of data: a construction of `S` at closed arguments (`k = 0`), or one that can be
instantiated at any types with instances. -/
def constructs? (env : Environment) (structs : NameSet) : Expr → Option Name
  | .forallE _ t b bi =>
      if t.getForallBody.isSort || (bi.isInstImplicit && !propClass env t) then
        constructs? env structs b
      else none
  | .mdata _ b => constructs? env structs b
  | e => match e.getAppFn with
    | .const s _ => if structs.contains s then some s else none
    | _ => none

def isPackageDecl (env : Environment) (pkg : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => pkg.isPrefixOf (env.header.moduleNames[idx.toNat]!)
  | none => false

/-- Propagate witnesses through proofs: if `t a₁ … aₙ` is a closed application and the
proof of `t` is `fun x₁ … xₙ => b`, then `b[a/x]` is a closed proof, and every closed
application inside it witnesses the theorem it applies. The witness recorded for a
theorem found this way is `t` itself, marked `via`. -/
unsafe def propagate (env : Environment) (targets : Std.HashMap Name Info)
    (st : ScanState) : ScanState := Id.run do
  let mut st := st
  let mut fuel := 1000000
  while !st.pending.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let n := st.pending.back!
    st := { st with pending := st.pending.pop }
    let some app := st.application[n]? | continue
    let some ci := env.find? n | continue
    let some v := ci.value? (allowOpaque := true) | continue
    let body := v.beta app.getAppArgs
    st := ((visit targets (n.str "via") body).run st).2
  return st

/-- Search every declaration of the package for closed applications of the targets,
propagate the witnesses found through proofs, and count the declarations that mention
each target. -/
unsafe def scanUses (env : Environment) (pkg : Name) (targets : Std.HashMap Name Info) :
    Std.HashMap Name Name × Std.HashMap Name Nat := Id.run do
  let mut st : ScanState := {}
  let mut refs : Std.HashMap Name Nat := {}
  for (user, ci) in env.constants do
    unless isPackageDecl env pkg user do continue
    let some v := ci.value? (allowOpaque := true) | continue
    let hits := v.getUsedConstants.filter fun c => targets.contains c && c != user
    if hits.isEmpty then continue
    for c in hits do
      refs := refs.insert c (refs.getD c 0 + 1)
    st := ((visit targets user v).run st).2
  st := propagate env targets st
  return (st.witness, refs)

/-! ## Command line -/

structure Options where
  mode : String := ""
  importsFile : String := ""
  prefixes : Array Name := #[]
  namesFile : String := ""
  pairsFile : String := ""
  out : String := ""
  pkg : Name := `Mettapedia

partial def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--imports-file" :: v :: rest, o => parseArgs rest { o with importsFile := v }
  | "--module-prefix" :: v :: rest, o =>
      parseArgs rest { o with prefixes := o.prefixes.push v.toName }
  | "--names-file" :: v :: rest, o => parseArgs rest { o with namesFile := v }
  | "--pairs-file" :: v :: rest, o => parseArgs rest { o with pairsFile := v }
  | "--out" :: v :: rest, o => parseArgs rest { o with out := v }
  | "--package" :: v :: rest, o => parseArgs rest { o with pkg := v.toName }
  | m :: rest, o =>
      if o.mode.isEmpty && !m.startsWith "--" then parseArgs rest { o with mode := m }
      else .error s!"unexpected argument {m}"

def readLines (path : String) : IO (Array String) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").toArray.filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none else some l

unsafe def loadEnv (importsFile : String) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods ← readLines importsFile
  importModules (mods.map fun m => { module := m.toName }) {} (trustLevel := 1024)
    (leakEnv := true) (loadExts := true)

/-- Declarations generated by the elaborator rather than stated by an author. -/
def generated (n : Name) : Bool :=
  match n with
  | .str _ s => s ∈ ["congr_simp", "injEq", "inj", "sizeOf_spec", "noConfusion", "ext_iff"]
  | _ => false

def kindsString (i : Info) : String :=
  ",".intercalate (i.hyps.toList.map fun h =>
    s!"{h.index}:" ++ (match h.kind with | .prop => "prop" | .struct => "struct"))

unsafe def audit (o : Options) : IO UInt32 := do
  let env ← loadEnv o.importsFile
  let names : Option (Array Name) ←
    if o.namesFile.isEmpty then pure none
    else some <$> ((← readLines o.namesFile).map String.toName |> pure)
  let mut selected : Array (Name × Name × Expr) := #[]
  let mut missing : Array Name := #[]
  match names with
  | some ns =>
      for n in ns do
        match env.find? n with
        | some ci =>
            let m := match env.getModuleIdxFor? n with
              | some idx => env.header.moduleNames[idx.toNat]!
              | none => .anonymous
            selected := selected.push (n, m, ci.type)
        | none => missing := missing.push n
  | none =>
      for (n, ci) in env.constants do
        unless ci matches .thmInfo _ do continue
        if n.isInternalDetail || generated n then continue
        let some idx := env.getModuleIdxFor? n | continue
        let m := env.header.moduleNames[idx.toNat]!
        if o.prefixes.any (·.isPrefixOf m) then
          selected := selected.push (n, m, ci.type)
  let infos ← runMeta env <| selected.mapM fun (n, m, ty) => analyze n m ty
  -- The constructors of the certificate structures at struct positions are searched
  -- too: a closed constructor application shows that the structure is inhabited.
  -- Only the package's own structures: a library structure (a topology, a string) is
  -- built in the library, whose declarations are not searched.
  let structNames := infos.foldl (fun acc i =>
    i.structs.foldl (fun acc s =>
      if acc.contains s || !isPackageDecl env o.pkg s then acc else acc.push s) acc) #[]
  let ctorInfos ← runMeta env <| structNames.filterMapM fun s => do
    let ctor := getStructureCtor env s
    let info ← analyze ctor.name .anonymous ctor.type
    return if info.hyps.isEmpty then none else some (s, info)
  let targets : Std.HashMap Name Info := infos.foldl (fun t i =>
    if i.hyps.isEmpty || i.falseConclusion then t else t.insert i.name i) {}
  let targets := ctorInfos.foldl (fun t (_, i) => t.insert i.name i) targets
  let (witness, refs) := scanUses env o.pkg targets
  -- A structure is also inhabited when a package declaration constructs it: a closed model
  -- or certificate, or a construction generic in types and instances.
  let structSet : NameSet := structNames.foldl (·.insert ·) {}
  let constructed : NameSet := Id.run do
    let mut acc : NameSet := {}
    for (n, ci) in env.constants do
      unless isPackageDecl env o.pkg n do continue
      let some s := constructs? env structSet ci.type | continue
      if let some v := ci.value? (allowOpaque := true) then
        unless v.hasSorry do acc := acc.insert s
    return acc
  let uninhabited : NameSet := ctorInfos.foldl (fun acc (s, i) =>
    if witness.contains i.name || constructed.contains s then acc else acc.insert s) {}
  let mut lines : Array String :=
    #["status\ttheorem\tmodule\thypotheses\trefs\twitness\tflags"]
  let mut counts : Std.HashMap String Nat := {}
  for i in infos do
    let structsOnly := i.hyps.all (·.kind == .struct) &&
      i.structs.all (fun s => !uninhabited.contains s)
    let status :=
      if i.hyps.isEmpty then "no-hypotheses"
      else if i.falseConclusion then "refutation"
      else if witness.contains i.name then "witnessed"
      else if structsOnly then "structs-inhabited" else "unwitnessed"
    counts := counts.insert status (counts.getD status 0 + 1)
    let r := refs.getD i.name 0
    let exFalso := match env.find? i.name with
      | some ci => (ci.value? (allowOpaque := true)).map (exFalsoProof i.arity) |>.getD false
      | none => false
    let flags := if status == "unwitnessed" then
        ",".intercalate ((if exFalso then ["ex-falso"] else []) ++
          (if i.containsRestricts then ["contains+restricts"] else []) ++
          (i.structs.toList.filter uninhabited.contains |>.map (s!"uninhabited:{·}")) ++
          (if r == 0 then ["unreferenced"] else []))
      else ""
    lines := lines.push s!"{status}\t{i.name}\t{i.module}\t{kindsString i}\t{r}\t\
      {(witness.get? i.name).map toString |>.getD ""}\t{flags}"
  for n in missing do
    lines := lines.push s!"missing\t{n}\t\t\t\t\t"
  IO.FS.writeFile o.out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"examined {infos.size} theorems; missing {missing.size}"
  for (k, v) in counts.toList do
    IO.println s!"  {k}: {v}"
  return if missing.isEmpty then 0 else 1

/-- The theorems that `roots` mention, and that their proofs mention, to `depth` levels. -/
def mentionedTheorems (env : Environment) (roots : Array Name) (depth : Nat) : Array Name :=
  Id.run do
    let mut seen : NameSet := {}
    let mut frontier := roots
    let mut result : Array Name := #[]
    for _ in [:depth] do
      let mut next : Array Name := #[]
      for n in frontier do
        let some ci := env.find? n | continue
        let some v := ci.value? (allowOpaque := true) | continue
        for c in v.getUsedConstants do
          if seen.contains c then continue
          seen := seen.insert c
          if let some (.thmInfo _) := env.find? c then
            result := result.push c
            next := next.push c
      frontier := next
    return result

unsafe def verify (o : Options) : IO UInt32 := do
  let env ← loadEnv o.importsFile
  let pairs := (← readLines o.pairsFile).filterMap fun l =>
    match l.splitOn "\t" with
    | [t, w] => some (t.toName, w.toName)
    | _ => none
  let mut lines : Array String := #["result\ttheorem\twitness"]
  let mut failures := 0
  for (t, w) in pairs do
    let result ← match env.find? t, env.find? w with
      | none, _ => pure "missing-theorem"
      | _, none => pure "missing-witness"
      | some tc, some wc => do
          let info ← runMeta env (analyze t .anonymous tc.type)
          if info.hyps.isEmpty then pure "no-hypotheses"
          else if info.falseConclusion then pure "refutation"
          else
            match wc.value? (allowOpaque := true) with
            | none => pure "witness-has-no-value"
            | some v =>
                let names := (mentionedTheorems env #[w] 4).push t
                let infos ← runMeta env <| names.filterMapM fun n => do
                  match env.find? n with
                  | some ci => return some (← analyze n .anonymous ci.type)
                  | none => return none
                let targets : Std.HashMap Name Info := infos.foldl (fun m i =>
                  if i.hyps.isEmpty || i.falseConclusion then m else m.insert i.name i) {}
                let st := propagate env targets ((visit targets w v).run {}).2
                pure (if st.witness.contains t then "ok" else "no-closed-application")
    unless result == "ok" || result == "no-hypotheses" || result == "refutation" do
      failures := failures + 1
    lines := lines.push s!"{result}\t{t}\t{w}"
  IO.FS.writeFile o.out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"checked {pairs.size} pairs; failures {failures}"
  return if failures == 0 then 0 else 1

end HeadlineWitnessScan

open HeadlineWitnessScan in
unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
      IO.eprintln e
      return 2
  | .ok o =>
      if o.importsFile.isEmpty || o.out.isEmpty then
        IO.eprintln "required: --imports-file and --out"
        return 2
      match o.mode with
      | "audit" => audit o
      | "verify" =>
          if o.pairsFile.isEmpty then
            IO.eprintln "verify requires --pairs-file"
            return 2
          verify o
      | m =>
          IO.eprintln s!"unknown mode {m}; expected audit or verify"
          return 2
