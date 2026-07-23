import Veil

set_option linter.unusedVariables false

veil module TraceCommandBoundary

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action stutter {
  pure ()
}

invariant true

#gen_spec

#guard_msgs(drop warning, drop info) in
sat trace [initial] { }

set_option linter.unusedVariables false in
def commandAfterTrace : Nat := 0

#guard commandAfterTrace = 0

end TraceCommandBoundary
