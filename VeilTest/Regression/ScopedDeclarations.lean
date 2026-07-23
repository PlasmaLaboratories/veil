import Veil

/-!
# Regression: Veil declarations survive nested command scopes

Veil keeps the active module marker scoped so `end ModuleName` closes the
module. The module record itself must not be scoped: otherwise declarations
inside common command wrappers such as `set_option ... in` disappear when the
wrapper closes, silently weakening the assembled specification.
-/

set_option linter.unusedVariables false

veil module ScopedDeclarations

type node
relation seen : node → Bool
individual flag : Bool

set_option linter.unusedVariables false in
veil_set_field_representation relation Veil.CanonicalField

#gen_state

#check (rfl : @ScopedDeclarations.FieldConcreteType = fun node f =>
  ScopedDeclarations.State.Label.casesOn f
    (node → Bool)
    Bool)

after_init {
  seen N := false
  flag := false
}

set_option linter.unusedVariables false in
action scopedAction {
  flag := false
}

set_option linter.unusedVariables false in
invariant [scopedInvariant] flag = false

#gen_spec

-- The scoped action must be assembled into the generated label type.
#check ScopedDeclarations.Label.scopedAction

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  scopedInvariant ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  scopedAction
    doesNotThrow ... ✅
    scopedInvariant ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end ScopedDeclarations
