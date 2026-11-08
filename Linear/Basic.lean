/-
  Linear: an affine/linear resource checker for Lean 4, entirely outside the kernel.

  The kernel has no linearity (`Expr.forallE` carries no multiplicity), so every linearity
  fact here is an elaborator- and linter-level invariant, recorded in persistent environment
  extensions by `Linear.Syntax` and enforced by `Linear.Check`.

  Vocabulary
  ----------
  * `a -* b` — linear arrow. As a parameter type: the argument is consumed. As a
    constructor-field type: the field is linear.
  * `Lin α` — linear wrapper. Its payload field is `-*`, so `Lin α` is linear for every `α`,
    and matching on a `Lin` yields a binder that is still constrained.
  * `Ur α` — plain wrapper, never linear; `Ur.ur` accepts only unrestricted payloads.
  * `Drop α` — user-supplied "consume zero times" capability.
-/
import Linear.Syntax

open Lean Meta

namespace Linear

/-! ### Core types -/

/-- `α` may be consumed zero times. Instances are the user's responsibility. -/
class Drop (α : Type) where
  drop : α → Unit

/-- Linear wrapper: the payload is `-*`, so `Lin α` is linear for every `α` and matching on a
`Lin` yields a still-constrained binder. -/
inductive Lin (α : Type) where
  | lin : α -* Lin α

/-- Unrestricted wrapper: never linear. `Ur.ur` accepts only unrestricted payloads, so a
`Lin α` cannot be wrapped without `escape`. -/
inductive Ur (α : Type) where
  | ur : α → Ur α

/-- The one-way door from linear to unrestricted. -/
@[irreducible] def escape (a : α) : Ur α := .ur a

/-! ### Queries -/

/-- Linear fields of a constructor (indices into its explicit fields). -/
def linearFieldsOf (env : Environment) (ctor : Name) : Array Nat :=
  (linearFieldExt.getState env).getD ctor #[]

/-- Consumed parameters of a declaration. -/
def consumedParamsOf (env : Environment) (decl : Name) : Array Nat :=
  (linearParamExt.getState env).getD decl #[]

/-- Field types of a constructor, dropping its parameters, indices and binders. The types are
returned while the telescope is still open, so callers must use them before returning from
`k`; escaping the free variables makes later queries fail with `unknown free variable`. -/
def ctorFieldsIn (ctor : Name) (k : Array Expr → MetaM α) : MetaM α := do
  let some (.ctorInfo cv) := (← getEnv).find? ctor | return ← k #[]
  forallTelescopeReducing cv.type fun xs _ => do
    let mut acc := #[]
    for h : i in [cv.numParams:xs.size] do
      acc := acc.push (← inferType xs[i])
    k acc

/-- `true` iff values of `type` are linear: tagged types are, and otherwise a type is linear
when it has a marked field or a field of a linear type (structural closure). `seen` breaks
mutual recursion. Types that are not inductive constants (functions, `Prop`, sort-polymorphic
applications) are unrestricted. -/
partial def isLinearType (type : Expr) (seen : Std.HashSet Name := {}) : MetaM Bool := do
  let type ← whnfR type
  let some n := type.getAppFn.constName? | return false
  if seen.contains n then return false
  let env ← getEnv
  if linearInductive.hasTag env n then return true
  let some (.inductInfo iv) := env.find? n | return false
  let seen := seen.insert n
  for c in iv.ctors do
    if !(linearFieldsOf env c).isEmpty then return true
    -- Kept inside the telescope: these types mention the constructor's parameters.
    if ← ctorFieldsIn c fun fs => do
      for fty in fs do
        if ← isLinearType fty.getForallBody seen then return true
      return false
    then return true
  return false

/-- `true` iff parameter `i` of `n` is marked consumed. -/
def isConsumedParam (env : Environment) (n : Name) (i : Nat) : Bool :=
  (consumedParamsOf env n).contains i

/-- `true` iff `n` may freely copy and drop its arguments. -/
def isNonLinearFn (env : Environment) (n : Name) : Bool :=
  nonLinearFn.hasTag env n

/-- `true` iff constructor field `i` is linear. -/
def isLinearField (env : Environment) (ctor : Name) (i : Nat) : Bool :=
  (linearFieldsOf env ctor).contains i

end Linear
