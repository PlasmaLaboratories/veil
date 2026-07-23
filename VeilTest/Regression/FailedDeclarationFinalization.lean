import Veil

/-!
# Regression: failed declarations block specification finalization

Lean can recover from a command elaboration error, and `#guard_msgs` deliberately
does so in batch tests. A failed Veil declaration must remain visible to
`#gen_spec`; otherwise finalization silently assembles and verifies a weaker
specification with the failed declaration omitted.
-/

set_option linter.unusedVariables false

veil module FailedDeclarationFinalization

individual flag : Bool

#gen_state

after_init { flag := false }

action keep { flag := false }

invariant [valid] flag = false

/-- error: Unbound uncapitalized variable: nonexistent_pred -/
#guard_msgs in
invariant [broken] nonexistent_pred flag

/-- error: Cannot finalize Veil module FailedDeclarationFinalization: 1 Veil declaration failed to elaborate. -/
#guard_msgs in
#gen_spec

end FailedDeclarationFinalization
