/-
  The `linter.linear` option is sampled while each declaration is elaborated, so a scoped
  `set_option linter.linear false in ...` actually disables the check for that declaration.
-/
import Linear

open Linear

namespace Tests.Options

-- The checker is off for the nested declaration, so the leak goes unreported.
#guard_msgs in
set_option linter.linear false in
def unchecked : Lin Nat -* Nat := fun _h => 7

-- The positive control: with the option on, a well-behaved definition stays silent.
#guard_msgs in
set_option linter.linear true in
def checked : Lin Nat -* Nat := fun h =>
  match h with
  | .lin n => n

end Tests.Options
