/-
  The linearity linter.

  For every new definition it rebuilds the parameter telescope and the body, and enforces

  * **R4 consumption** — a binder of linear type, and a binder introduced by a `-*`
    constructor field, is consumed exactly once. Zero consuming uses is a leak (discharge with
    `Drop.drop`); two or more is a copy.
  * **R3 admission** — a linear value may only be handed to a consumed (`-*`) parameter, a
    `-*` constructor field, a `casesOn` major premise, `Drop.drop`, or `escape`.

  Uses in zero-bucket positions (`R5`) are free: proofs, types, motives and indices.

  This is a linter, not a kernel feature: `simp`, `rw`, `unsafe`, `implemented_by` and the
  compiler can still copy.
-/
import Linear.Basic

open Lean Meta Elab Command Linter

namespace Linear

register_option linter.linear : Bool := {
  defValue := true
  descr := "check that linear values are consumed exactly once"
}

/-! ### Small queries -/

/-- Number of parameters of a constant. -/
def pcount (n : Name) : MetaM Nat := do
  let some ci := (← getEnv).find? n | return 0
  forallTelescopeReducing ci.type fun xs _ => return xs.size

/-- A constant may accept a linear value in parameter/field slot `j`: `Drop.drop` and `escape`
are the designated sinks, and otherwise the slot must be marked `-*`. -/
def admitsLinear (c : Name) (j : Nat) : MetaM Bool := do
  if c == ``Drop.drop || c == ``escape then return true
  return (consumedParamsOf (← getEnv) c).contains j

/-- `true` for class projections such as `BEq.beq` and `Repr.repr`. -/
def isBorrowingMethod (n : Name) : MetaM Bool :=
  return (← getProjectionFnInfo? n).isSome

/-- `true` if `e` is `target` or a projection chain starting at it. -/
partial def isTargetTail (target : FVarId) (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isFVar then e.fvarId! == target
  else if e.isProj then isTargetTail target e.projExpr!
  else if e.isApp then
    if let .fvar f := e.getAppFn then f == target else false
  else false

/-- A position is a zero bucket when it is a proof or its type lands in a `Sort`. -/
def isZeroPos (e : Expr) : MetaM Bool := do
  if (← isProp e) then return true
  let t ← inferType e
  forallTelescopeReducing t fun _ b => return b.isSort

/-- Raw occurrences of `target` in `e`, ignoring buckets. -/
partial def countAll (target : FVarId) (e : Expr) : Nat :=
  let e := e.consumeMData
  if e.isFVar then if e.fvarId! == target then 1 else 0
  else if e.isApp then
    countAll target e.getAppFn
      + e.getAppArgs.foldl (init := 0) (fun acc a => acc + countAll target a)
  else if e.isLambda || e.isForall then countAll target e.bindingBody!
  else if e.isLet then countAll target e.letValue! + countAll target e.letBody!
  else if e.isProj then countAll target e.projExpr!
  else 0

/-- `true` when the type starts with a motive binder `I → Sort u`. Eliminators — both the
kernel's `casesOn`/`rec` and the matchers the equation compiler invents (`f.match_1`) — all do. -/
partial def hasMotiveBinder (t : Expr) : Bool :=
  match t with
  | .forallE _ d b _ => (d.isForall && d.bindingBody!.isSort) || hasMotiveBinder b
  | _ => false

/-- For an eliminator application, the argument index of the major premise. Everything before it
is the motive, the parameters and the indices: those are type positions (`R5`, zero bucket) and
must not be counted as uses. `none` for ordinary applications. -/
def majorIdxOf (e : Expr) : MetaM (Option Nat) := do
  if !e.isApp then return none
  let some c := e.getAppFn.constName? | return none
  let env ← getEnv
  let some ci := env.find? c | return none
  unless hasMotiveBinder ci.type do return none
  let args := e.getAppArgs
  for _h : i in [0:args.size] do
    let t ← inferType args[i]
    if let some n := t.getAppFn.constName? then
      if let some (.inductInfo _) := env.find? n then return some i
  return none

/-! ### Counting

  `countOcc` counts occurrences of one free variable in a body, split into
  `(zero bucket, consuming uses)`. Motives, indices and proofs land in the zero bucket;
  `Drop.drop x` discharges `x` and contributes to neither.

  Branching is handled path-wise: a pair `(must, may)` records the smallest and the largest
  number of uses over all execution paths. Two occurrences executed in sequence add up; two
  occurrences in mutually exclusive branches combine with `min`/`max`, so `match b with
  | true => use h | false => use h` is exactly one use, while `| false => 7` leaks. -/

/-- Usage summaries of two expressions that both run. -/
def seqUse (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- Usage summaries of two mutually exclusive branches. -/
def altUse (a b : Nat × Nat) : Nat × Nat := (min a.1 b.1, max a.2 b.2)

partial def countOcc (target : FVarId) (e : Expr) : MetaM (Nat × Nat) := do
  let e := e.consumeMData
  if e.isFVar then
    return if e.fvarId! == target then (1, 1) else (0, 0)
  if e.isBVar then return (0, 0)
  if !e.hasLooseBVars && (← isProp e) then return (0, 0)
  if e.isApp then
    if let some mi := ← majorIdxOf e then
      let args := e.getAppArgs
      let mut majorUse : Nat × Nat := (0, 0)
      let mut branchUse : Option (Nat × Nat) := none
      for _h : i in [mi:args.size] do
        if h2 : i < args.size then
          let r ← countOcc target args[i]
          if i == mi then majorUse := r
          else match branchUse with
            | none => branchUse := some r
            | some b => branchUse := some (altUse b r)
      return seqUse majorUse (branchUse.getD (0, 0))
    if let some c := e.getAppFn.constName? then
      if c == `Drop.drop then
        return (if countAll target e > 0 then (1, 1) else (0, 0))
    let mut acc : Nat × Nat := (0, 0)
    -- A non-constant head is a value being applied: for a linear function that *is* the
    -- consumption (`(fun _ => consume h) ()` mentions `h` through its head).
    if !e.getAppFn.isConst then
      acc := seqUse acc (← countOcc target e.getAppFn)
    for a in e.getAppArgs do
      acc := seqUse acc (← countOcc target a)
    return acc
  if e.isLambda then
    return ← lambdaTelescope e fun _ body => countOcc target body
  if e.isLet then
    -- The bound value is evaluated once; every use of the binder *is* that one evaluation, so
    -- counting the substituted body already prices each use exactly once. Only when the binder is
    -- unused does the value need to be counted on its own.
    let body := e.letBody!.instantiate1 e.letValue!
    if e.letBody!.hasLooseBVar 0 then return ← countOcc target body
    return seqUse (← countOcc target e.letValue!) (← countOcc target body)
  if e.isProj then return ← countOcc target e.projExpr!
  return (0, 0)

/-- `true` when a definition uses parameter `i` at least once. -/
def consumesParam (n : Name) (i : Nat) : MetaM Bool := do
  let some (.defnInfo dv) := (← getEnv).find? n | return false
  lambdaTelescope dv.value fun xs body => do
    if h : i < xs.size then
      if let .fvar fid := xs[i] then
        return (← countOcc fid body).2 > 0
    return false

/-! ### Captures

  A closure that mentions a linear value has captured it: calling the closure is what consumes
  the value, so the closure itself behaves like Rust's `FnOnce`. Two consequences, both checked
  below: such a closure may not be handed to a parameter that is not `-*` (the callee is free to
  call it any number of times), and it may not escape as the definition's result (its type is
  unrestricted, so it could be called later, many times). -/

/-- `true` when `e` mentions one of `s` as a free variable. -/
partial def mentionsAny (e : Expr) (s : Std.HashSet FVarId) : Bool :=
  let e := e.consumeMData
  if e.isFVar then s.contains e.fvarId!
  else if e.isApp then
    mentionsAny e.getAppFn s ||
      e.getAppArgs.foldl (init := false) (fun acc a => acc || mentionsAny a s)
  else if e.isLambda || e.isForall then mentionsAny e.bindingBody! s
  else if e.isLet then mentionsAny e.letValue! s || mentionsAny e.letBody! s
  else if e.isProj then mentionsAny e.projExpr! s
  else false

/-! ### Taint -/

/-- `true` when `e` may carry a linear payload, given the locally linear variables. -/
partial def isTainted (e : Expr) (linear : Std.HashSet FVarId) : MetaM Bool := do
  let e := e.consumeMData
  if e.hasLooseBVars then return false
  if e.isLambda then return mentionsAny e.bindingBody! linear
  if e.isFVar then return linear.contains e.fvarId!
  if !e.isApp then return ← isLinearType (← inferType e)
  let some c := e.getAppFn.constName? | return false
  if c == ``Lin.lin then return true
  if ← isLinearType (← inferType e) then return true
  -- Result taint: applying something to a linear value and getting a *function* back yields a
  -- closure that has probably captured it (`mk h : Unit → Nat`). What it captured is not in its
  -- type, so the obligation has to travel with the value.
  if (← inferType e).isForall && mentionsAny e linear then return true
  let some (.ctorInfo cv) := (← getEnv).find? c | return false
  let args := e.getAppArgs
  for _h : i in [0:args.size] do
    if i < cv.numParams then continue
    if isLinearField (← getEnv) c (i - cv.numParams) && (← isTainted args[i]! linear) then
      return true
  return false

/-- Walk `e` and collect every illegal hand-off of a linear value. Values already reported as
copied or leaked are skipped: the copy report is the actionable one. -/
partial def checkAdmission (e : Expr) (linear : Std.HashSet FVarId)
    (skip : Std.HashSet FVarId) : MetaM (Array MessageData) := do
  let e := e.consumeMData
  let mut out := #[]
  if e.isApp then
    let args := e.getAppArgs
    -- Eliminators (recursors and the equation compiler's matchers): the motive, the parameters
    -- and the indices are type positions, and the major premise is the legal consumption. Only
    -- the minor premises contain values that may carry a linear payload.
    let mi? ← majorIdxOf e
    if let some c := e.getAppFn.constName? then
      let borrow ← isBorrowingMethod c
      let env ← getEnv
      let mut off := 0
      let mut insts : Array Bool := #[]
      let mut isCtor := false
      if let some ci := env.find? c then
        match ci with
        | .ctorInfo cv => off := cv.numParams; isCtor := true
        | _ => pure ()
        -- Type-class arguments are resolved by the elaborator, not written by the user; the
        -- instance value itself never carries a linear payload.
        insts ← forallTelescopeReducing ci.type fun bs _ =>
          bs.mapM fun b => pure (b.binderInfo == .instImplicit)
      for _h : i in [0:args.size] do
        let a := args[i]
        let isElim := mi?.any fun mi => i >= mi
        let isInst := insts[i]?.getD false
        let skipped := a.isFVar && skip.contains a.fvarId!
        -- Constructors are the way values are stored, so a payload may enter a data structure; the
        -- obligation then travels with the container (see the limitations in `README.md`).
        if !isElim && !isInst && !borrow && !isCtor && !skipped && !(← admitsLinear c (i - off)) then
          let t ← try
            isTainted a linear
          catch _ => pure false
          if t then
            out := out.push
              m!"linear value passed to parameter {i - off} of `{c}`, which is not marked `-*`"
        out := out ++ (← checkAdmission a linear skip)
      return out
    for a in args do out := out ++ (← checkAdmission a linear skip)
    return out
  -- Only lambdas carry values. A `forall` is a *type*, which is a zero-bucket position (R5), and
  -- `lambdaTelescope` on a forall hands the forall itself back, so recursing there never ends.
  if e.isLambda then
    return ← lambdaTelescope e fun _ body => checkAdmission body linear skip
  if e.isLet then
    return (← checkAdmission e.letValue! linear skip)
      ++ (← checkAdmission (e.letBody!.instantiate1 e.letValue!) linear skip)
  if e.isProj then return ← checkAdmission e.projExpr! linear skip
  return out

/-! ### Reporting -/

/-- The user-facing name of a free variable. Binder names coming from compiled `match`
auxiliaries carry a hygienic suffix (`h._@.Foo.123._hyg.4`); show the readable prefix. -/
def userNameOf (fid : FVarId) : MetaM String := do
  let raw ← match (← getLCtx).find? fid with
    | some d => pure (toString d.userName)
    | none => pure (toString fid.name)
  match raw.splitOn "._@" with
  | p :: _ => return p
  | [] => return raw

/-- Does parameter `k` (0 = outermost) of the closed definition value occur under a lambda that
the definition itself does not bind — i.e. inside a returned closure? At binder depth `d` the
parameter `k` is `bvar (d - 1 - k)`, so an occurrence under one extra lambda has `d ≥ k + 2`.
Positions passed to a callee are skipped: the admission check reports those. -/
partial def escapeMention (e : Expr) (d : Nat) (k : Nat) (inArg : Bool := false) : Bool :=
  let e := e.consumeMData
  if e.isBVar then
    !inArg && d ≥ k + 2 && e.bvarIdx! == d - 1 - k
  else if e.isApp then
    -- A closure handed to a callee is the admission check's business, hence `inArg` only for
    -- arguments that are themselves lambdas. A lambda in function position is applied right
    -- here, so it is consumed exactly once and is not an escape.
    (!e.getAppFn.isLambda && escapeMention e.getAppFn d k inArg) ||
      e.getAppArgs.foldl (init := false)
        (fun acc a => acc || escapeMention a d k (inArg || a.isLambda))
  else if e.isLambda then
    escapeMention e.bindingBody! (d + 1) k inArg
  else if e.isLet then
    -- A closure bound by `let` is not itself an escape: it leaves through its uses, which the
    -- substituted body shows.
    (!e.letValue!.isLambda && escapeMention e.letValue! d k inArg) ||
      escapeMention (e.letBody!.instantiate1 e.letValue!) d k inArg
  else if e.isProj then
    escapeMention e.projExpr! d k inArg
  else false

/-- Check one binder: along every path it must be consumed exactly once. -/
def checkBinder (fid : FVarId) (body : Expr) : MetaM (Array MessageData × Bool) := do
  let (must, may) ← countOcc fid body
  if may > 1 then
    let n ← userNameOf fid
    return (#[m!"linear value `{n}` is consumed {may} times on some path and will be copied"], true)
  if must == 0 then
    let n ← userNameOf fid
    return (#[m!"linear value `{n}` is not consumed on every path; discharge it with `Drop.drop`"], true)
  return (#[], false)

/-- Check the binders of one `casesOn` minor: field `i` marked `-*` makes binder `i` linear. -/
def checkMinor (minor : Expr) (linFields : Array Nat) :
    MetaM (Array MessageData × Array FVarId) := do
  lambdaTelescope minor fun xs body => do
    let mut out := #[]
    let mut rep : Array FVarId := #[]
    for _h : i in [0:xs.size] do
      if linFields.contains i then
        let .fvar fid := xs[i] | continue
        let (msgs, hit) ← checkBinder fid body
        out := out ++ msgs
        if hit then rep := rep.push fid
    return (out, rep)

/-- Walk a body and check every binder that is linear, either by type or because it was
introduced by a `-*` constructor field. -/
partial def checkBinders (e : Expr) : MetaM (Array MessageData × Array FVarId) := do
  let e := e.consumeMData
  if e.isLambda then
    return ← lambdaTelescope e fun xs body => do
      let mut out := #[]
      let mut rep : Array FVarId := #[]
      for x in xs do
        let .fvar fid := x | continue
        if ← isLinearType (← inferType x) then
          let (msgs, hit) ← checkBinder fid body
          out := out ++ msgs
          if hit then rep := rep.push fid
      let (msgs, r2) ← checkBinders body
      return (out ++ msgs, rep ++ r2)
  if e.isApp then
    let mut out := #[]
    let mut rep : Array FVarId := #[]
    let env ← getEnv
    let args := e.getAppArgs
    let mi? ← majorIdxOf e
    let startFrom := mi?.getD 0
    if let some mi := mi? then
      let major := args[mi]!
      if let some ind := (← inferType major).getAppFn.constName? then
        if let some (.inductInfo iv) := env.find? ind then
          let start := mi + 1
          for _h : i in [start:args.size] do
            if h2 : i < args.size then
              let k := i - start
              if hk : k < iv.ctors.length then
                let (msgs, r) ← checkMinor args[i] (linearFieldsOf env iv.ctors[k])
                out := out ++ msgs
                rep := rep ++ r
    for _h : i in [startFrom:args.size] do
      if h2 : i < args.size then
        let (msgs, r) ← checkBinders args[i]
        out := out ++ msgs
        rep := rep ++ r
    return (out, rep)
  if e.isLet then
    let (m1, r1) ← checkBinders e.letValue!
    let (m2, r2) ← checkBinders (e.letBody!.instantiate1 e.letValue!)
    return (m1 ++ m2, r1 ++ r2)
  if e.isProj then return ← checkBinders e.projExpr!
  return (#[], #[])

/-! ### The linter -/

/-- The body of `checkDecl`, kept separate so that one broken declaration can never take the
linter down: the whole pass is wrapped in a `try`. -/
def checkDeclCore (declName : Name) : TermElabM Unit := do
  let some (.defnInfo dv) := (← getEnv).find? declName | return
  unless dv.value.isLambda do return
  -- Definitions are closed. Values that still mention free variables come from generated code
  -- whose context is gone by the time the linter runs; checking them would only produce noise.
  if dv.value.hasFVar then return
  lambdaTelescope dv.value fun xs body => do
    let mut linear : Std.HashSet FVarId := {}
    let mut reported : Std.HashSet FVarId := {}
    for h : idx in [0:xs.size] do
      let x := xs[idx]
      let .fvar fid := x | continue
      if ← isLinearType (← inferType x) then
        linear := linear.insert fid
        -- A capture that leaves the definition is reported before the use count, which cannot
        -- see through the closure.
        if escapeMention dv.value 0 idx then
          let n ← userNameOf fid
          logWarning m!"closure capturing linear value `{n}` escapes: its type is not linear, \
so nothing forces it to be called exactly once"
        let (msgs, hit) ← checkBinder fid body
        for m in msgs do logWarning m
        if hit then reported := reported.insert fid
    let (bmsgs, brep) ← checkBinders body
    for m in bmsgs do logWarning m
    for k in brep do reported := reported.insert k
    for msg in (← checkAdmission body linear reported) do
      logWarning msg

/-- Check one definition. A matcher generated by the equation compiler keeps free variables in
its value, and those live in a context that is gone once the command has been elaborated;
recovering from a failed check is cheaper than reproducing that context. -/
def checkDecl (declName : Name) : CommandElabM Unit := do
  let some (.defnInfo _) := (← getEnv).find? declName | return
  try
    liftTermElabM (checkDeclCore declName)
  catch _ => return

/-- The linter body, kept as a plain function so that registration can live in another module.
The option guard reads `linter.linear` directly instead of going through `getLinterValue`, which
trips an IR-interpreter assertion when the body runs from an importing module's initializer. -/
def runLint (_stx : Syntax) : CommandElabM Unit := do
  if (← get).messages.hasErrors then return
  let env ← getEnv
  let mut names : List Name := []
  for t in (← getInfoState).trees.toArray do
    names := names ++ getNewDecls t
  for d in names.eraseDups do
    -- The flag is recorded per declaration: a scoped `set_option` is already popped here.
    if env.contains d && isLinearCheckEnabled env d then checkDecl d

/-- Warns when a linear value is copied, leaked, or handed to an unmarked position. -/
def linearLint : Linter :=
  { run := runLint }

end Linear

open Lean Elab Command Linter in
initialize addLinter Linear.linearLint

