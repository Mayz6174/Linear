# Linear

An affine/linear resource checker for Lean 4, implemented entirely outside the kernel as a
command elaborator plus a linter.

Lean's kernel has no linearity: `Expr.forallE` carries no multiplicity. The `a -* b` arrow is
therefore a pure syntax marker that elaborates to the ordinary function arrow. Every linearity
fact in this library is an elaborator- and linter-level invariant, recorded in persistent
environment extensions by `Linear.Syntax` and enforced by `Linear.Check`.

This is a prototype, not a sound type system. See [Limitations](#limitations).

## Usage

```lean
import Linear

open Linear

/-- Consume a `Lin` exactly once. -/
def unwrap : Lin Nat -* Nat := fun h =>
  match h with
  | .lin n => n
```

`linearproto` exposes a single module, `Linear`, which re-exports everything.

### Markers

A position is *governed* by a marker when

* its binder type is itself a `-*` arrow (`(f : α -* β)` — `f` is a linear function),
* it is introduced by a `-*` arrow in the result type (`def incr : Nat -* Nat`), or
* it is a constructor field introduced by a `-*` arrow (`lin : α -* Lin α`).

A governed parameter is *consumed*: a linear value may be passed to it. A governed constructor
field is *linear*: matching on the constructor yields a binder that is checked.

### Core types

| Name | Meaning |
| --- | --- |
| `a -* b` | Linear arrow. Elaborates to `a → b`; only the markers in the syntax tree are recorded. |
| `Lin α` | Linear wrapper. Its payload field is `-*`, so `Lin α` is linear for every `α`. |
| `Ur α` | Unrestricted wrapper, never linear. `Ur.ur` accepts only unrestricted payloads. |
| `Drop α` | User-supplied "consume zero times" capability. |
| `escape` | The one-way door from linear to unrestricted. |

### Attributes and options

* `@[linearInductive]` — force a type to be treated as linear even though no field is marked.
* `@[nonLinearFn]` — reserved for a future escape hatch; it is recorded but the linter does not
  consult it yet.

The checker is on by default (`linter.linear = true`) and can be disabled per declaration:

```lean
set_option linter.linear false in
def unchecked : Lin Nat -* Nat := fun _h => 7
```

## What is enforced

For every definition with linear parameters, the linter rebuilds the parameter telescope and
the body and checks:

* **R4 consumption** — a binder of linear type, and a binder introduced by a `-*` constructor
  field, is consumed exactly once. Zero consuming uses is a leak (discharge it with
  `Drop.drop`); two or more is a copy.
* **R3 admission** — a linear value may only be handed to a consumed (`-*`) parameter, a `-*`
  constructor field, a `casesOn` major premise, `Drop.drop`, or `escape`.
* **R5 zero bucket** — uses in proof, type, motive, and index positions are free.

Usage is counted path-wise: occurrences executed in sequence add up, while occurrences in
mutually exclusive branches combine with `min`/`max`. A closure that mentions a linear value is
treated like Rust's `FnOnce`: it may not be handed to a non-`-*` parameter and may not escape as
the definition's result.

## Limitations

* **Linter, not kernel.** `simp`, `rw`, `unsafe`, `implemented_by`, and the compiler can still
  copy or drop linear values. There is no runtime or kernel enforcement.
* **Containers are not tracked.** Storing a closure in a data structure
  (`let fs := [mk h]`) hides later calls; only the definition that created the closure can
  report its escape. `Tests/KnownHoles.lean` pins down the current (unsound) behaviour.
* **`let` is counted by substitution.** This is what catches
  `let g := fun _ => consume h; g () + g ()`, but it is an approximation: a value that is bound
  and used once is indistinguishable from a value that is never evaluated.
* **Generated code is skipped.** Definitions whose value still mentions free variables (such as
  equation-compiler matchers) are not checked, and definitions whose value is not a lambda are
  skipped.
* **Borrowing projections are trusted.** Class projections such as `BEq.beq` are assumed to
  borrow rather than consume their argument for admission purposes.
* **`@[nonLinearFn]` is not wired up yet.**

## Project layout

```
Linear.lean        umbrella module (`import Linear`)
Linear/Basic.lean  core types, attributes, linearity queries
Linear/Syntax.lean `-*` syntax, declaration wrapper, environment extensions
Linear/Check.lean  use counting, admission, closure checks, the linter
Tests/             `#guard_msgs` regression tests (not part of the library)
```

## Building and testing

```sh
lake build
```
