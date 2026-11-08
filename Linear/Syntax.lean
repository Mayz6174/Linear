/-
  Syntax layer for linearity markers.

  Lean's kernel has no linearity (`Expr.forallE` carries no multiplicity), so `-*` is a pure
  syntax marker that elaborates to the plain arrow. The markers therefore exist only in the
  declaration syntax tree; this command elaborator wraps `declaration`, records the governed
  positions in persistent environment extensions, and then hands the untouched syntax to the
  ordinary elaborator. Nothing downstream re-parses source.

  A position is "governed" by a marker when
  * its binder type is itself a `-*` arrow (`(f : α -* β)` — `f` is a linear function),
  * it is introduced by a `-*` arrow in the result type (`def incr : Nat -* Nat`), or
  * it is a constructor field introduced by a `-*` arrow (`lin : α -* Lin α`).
-/
import Lean

open Lean Elab Command

namespace Linear

/-! ### Syntax -/

syntax:35 term " -* " term:35 : term

macro_rules
  | `($a -* $b) => `($a → $b)

/-- Syntax kind of the linear arrow, for scanning signatures. -/
def linearArrowKind : Name := ``«term_-*_»

/-- `true` iff the given term syntax is a linear arrow. -/
def isLinearArrowStx (stx : Syntax) : Bool :=
  stx.getKind == linearArrowKind

/-! ### Tags -/

/-- Escape hatch: `f` may copy and drop its arguments. -/
initialize nonLinearFn : TagAttribute ←
  registerTagAttribute `nonLinearFn
    "Marks a function that may freely copy and drop its arguments"
    (asyncMode := .local)

/-- Force a type linear even though no field is marked. -/
initialize linearInductive : TagAttribute ←
  registerTagAttribute `linearInductive
    "Marks an inductive type whose values are linear regardless of its fields"
    (asyncMode := .local)

/-! ### Marker storage -/

def pushIdx (m : Std.HashMap Name (Array Nat)) (k : Name) (i : Nat) : Std.HashMap Name (Array Nat) :=
  let is := m.getD k #[]
  if is.contains i then m else m.insert k (is.push i)

def pushAllIdx (ess : Array (Array (Name × Nat))) : ImportM (Std.HashMap Name (Array Nat)) := do
  let mut m : Std.HashMap Name (Array Nat) := {}
  for es in ess do
    for (n, i) in es do m := pushIdx m n i
  return m

def exportIdx (m : Std.HashMap Name (Array Nat)) : Array (Name × Nat) :=
  m.fold (init := #[]) fun acc n is => is.foldl (init := acc) fun acc i => acc.push (n, i)

/-- Linear constructor fields. -/
initialize linearFieldExt :
    PersistentEnvExtension (Name × Nat) (Name × Nat) (Std.HashMap Name (Array Nat)) ←
  registerPersistentEnvExtension {
    name := `linearField
    mkInitial := pure {}
    addImportedFn := pushAllIdx
    addEntryFn := fun m (n, i) => pushIdx m n i
    exportEntriesFn := exportIdx
    asyncMode := .local
  }

/-- Consumed declaration parameters. -/
initialize linearParamExt :
    PersistentEnvExtension (Name × Nat) (Name × Nat) (Std.HashMap Name (Array Nat)) ←
  registerPersistentEnvExtension {
    name := `linearParam
    mkInitial := pure {}
    addImportedFn := pushAllIdx
    addEntryFn := fun m (n, i) => pushIdx m n i
    exportEntriesFn := exportIdx
    asyncMode := .local
  }

def markLinearField (ctor : Name) (i : Nat) : CommandElabM Unit :=
  modifyEnv fun env => linearFieldExt.addEntry env (ctor, i)

def markLinearParam (decl : Name) (i : Nat) : CommandElabM Unit :=
  modifyEnv fun env => linearParamExt.addEntry env (decl, i)

/-- Declarations elaborated while `linter.linear` was enabled. A scoped
`set_option linter.linear false in ...` is popped before linters run, so the flag has to be
sampled while the command itself is elaborated. -/
def addAllEnabled (ess : Array (Array Name)) : ImportM (Std.HashSet Name) := do
  let mut s : Std.HashSet Name := {}
  for es in ess do
    for n in es do s := s.insert n
  return s

initialize enabledExt : PersistentEnvExtension Name Name (Std.HashSet Name) ←
  registerPersistentEnvExtension {
    name := `linearEnabled
    mkInitial := pure {}
    addImportedFn := addAllEnabled
    addEntryFn := fun s n => s.insert n
    exportEntriesFn := fun s => s.toArray
    asyncMode := .local
  }

/-- `true` iff `decl` was elaborated with the linear linter enabled. -/
def isLinearCheckEnabled (env : Environment) (decl : Name) : Bool :=
  (enabledExt.getState env).contains decl

def markCheckEnabled (decl : Name) : CommandElabM Unit :=
  modifyEnv fun env => enabledExt.addEntry env decl

/-! ### Scanning

`optDeclSig` is `many binder` followed by `optional typeSpec`, so the binders sit inside the
leading `many` node and the type inside the trailing `optional` node. -/

/-- The type annotation of a binder node. The `:` and its type live inside a nested `null`
node (`(f : α -* β)` is `( null[f] null[:, α -* β] )`), so scan for the `:` atom; direct
children win so a nested binder in a type does not shadow the real annotation. -/
partial def binderTypeStx? (b : Syntax) : Option Syntax :=
  let args := b.getArgs
  match args.findIdx? (fun a => a.isAtom && a.getAtomVal == ":") with
  | some i => args[i + 1]?
  | none => args.findSome? fun a => binderTypeStx? a

/-- Positions governed by a `-*` chain from telescope index `base` on. The chain is
right-nested, so `A -* B -* C` governs `base` and `base + 1`. -/
partial def scanChain (base : Nat) (stx : Syntax) (acc : Array Nat) : Array Nat :=
  if isLinearArrowStx stx then
    match stx.getArgs[2]? with
    | some rest => scanChain (base + 1) rest (acc.push base)
    | none => acc.push base
  else acc

/-- Split a signature into (binders, result type). -/
def splitSig (sig : Syntax) : Array Syntax × Option Syntax :=
  let isBinder (b : Syntax) :=
    b.isOfKind ``Lean.Parser.Term.explicitBinder
      || b.isOfKind ``Lean.Parser.Term.implicitBinder
      || b.isOfKind ``Lean.Parser.Term.strictImplicitBinder
      || b.isOfKind ``Lean.Parser.Term.instBinder
  let binders := match sig.getArgs[0]? with
    | some b => b.getArgs.filter isBinder
    | none => #[]
  let result := sig.getArgs.findSome? fun a =>
    a.getArgs.findSome? fun c =>
      if c.isOfKind ``Lean.Parser.Term.typeSpec then c.getArgs[1]? else none
  (binders, result)

/-- Positions governed by markers in a signature. -/
def markedIdxs (sig : Syntax) : Array Nat := Id.run do
  let (binders, result?) := splitSig sig
  let mut acc : Array Nat := #[]
  for h : i in [0:binders.size] do
    if let some t := binderTypeStx? binders[i] then
      if isLinearArrowStx t then acc := acc.push i
  if let some r := result? then acc := scanChain binders.size r acc
  return acc

def isInductiveLike (declKind : Name) : Bool :=
  declKind == ``Lean.Parser.Command.inductive || declKind == ``Lean.Parser.Command.structure

def declNameOf (declId : Syntax) : CommandElabM Name := do
  let (id, _) := expandDeclIdCore declId
  if (`_root_).isPrefixOf id then return id
  return (← getCurrNamespace) ++ id

/-- Collect the `ctor` nodes of an inductive declaration. They are nested inside the
`many ctor` node rather than sitting directly under the declaration. -/
partial def collectCtors (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
  let acc := if stx.isOfKind ``Lean.Parser.Command.ctor then acc.push stx else acc
  stx.getArgs.foldl (init := acc) (fun acc c => collectCtors c acc)

/-- `true` iff the binder list of a signature is empty and the signature has no binders at
all, i.e. a constructor with only an arrow chain. -/
def markCtor (inductName : Name) (ctor : Syntax) : CommandElabM Unit := do
  let some ctorId := ctor.getArgs[3]? | return
  let some sig := ctor.getArgs[4]? | return
  let ctorName := inductName ++ ctorId.getId
  for i in markedIdxs sig do
    markLinearField ctorName i
    markLinearParam ctorName i

def markDecl (decl : Syntax) : CommandElabM Unit := do
  let some declId := decl.getArgs[1]? | return
  let declName ← declNameOf declId
  if isInductiveLike decl.getKind then
    for ctor in collectCtors decl #[] do markCtor declName ctor
  else
    let some sig := decl.getArgs[2]? | return
    for i in markedIdxs sig do markLinearParam declName i

/-- Wrapper elaborator: record markers, then elaborate normally. -/
@[command_elab declaration]
def elabDeclarationWithMarkers : CommandElab := fun stx => do
  let decl := stx[1]
  markDecl decl
  if (← getOptions).getBool `linter.linear true then
    if let some declId := decl.getArgs[1]? then
      markCheckEnabled (← declNameOf declId)
  Lean.Elab.Command.elabDeclaration stx

end Linear
