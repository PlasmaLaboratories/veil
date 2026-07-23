import Veil

veil module ModuleStateComponentDiagnostic

/--
error: declareStateComponent called with `module` kind or `inherit` mutability; use `declareChildModule` instead
-/
#guard_msgs in
module sub : Nat

end ModuleStateComponentDiagnostic
