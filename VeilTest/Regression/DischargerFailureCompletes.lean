import Veil

/-!
# Regression: an asynchronous discharger failure always completes

The SMT tactic below reports `unsat` and a following tactic then fails. Result
processing must turn that combination into an error and resolve the worker's
promise; otherwise the verification condition remains `running` forever.
-/

open Lean Elab Command Veil Veil.Verifier

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DischargerFailureCompletes

private def addFailingVC (nm : Name) : CommandElabM Unit := do
  withVCManager fun ref => do
    let mgr ← ref.get
    let statement : VCStatement := {
      name := nm
      params := #[]
      statement := ← `(term| True)
    }
    let data : VCData VCMetadata := ⟨statement, default⟩
    let (mgr, vcId) := mgr.addVC data {} #[]
    let tactic ← `(term| by (smt (config := { trust := true }); fail "post-smt failure"))
    let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm tactic nm)
    ref.set mgr

private def waitForFinalStatus (nm : Name) (timeoutMs : Nat) : CommandElabM (Option String) := do
  for _ in [0:timeoutMs / 10] do
    let status? ← vcManager.atomically fun ref => do
      let mgr ← ref.get
      let vcId? := mgr.nodes.toList.findSome? fun (uid, vc) =>
        if vc.name == nm then some uid else none
      let some vcId := vcId? | return none
      let status := mgr.statusEmoji vcId
      return if status == "❓❓❓" then none else some status
    if status?.isSome then return status?
    IO.sleep 10
  return none

elab "#check_discharger_failure_completes" : command => do
  let vcName := `postSmtFailure
  addFailingVC vcName
  startAll
  let some status ← waitForFinalStatus vcName 5000
    | throwError "discharger result promise was not resolved within five seconds"
  unless status == "💥" do
    throwError "expected the failed discharger to finish with an error status, got {status}"
  logInfo "post-SMT discharger failure completed with error status"

end DischargerFailureCompletes

veil module DischargerFailureCompletesFixture

type node
relation flag : node → Bool

#gen_state

after_init { flag N := false }

action keep { pure () }

invariant flag N ∨ ¬ flag N

#gen_spec

/-- info: post-SMT discharger failure completed with error status -/
#guard_msgs(info) in
#check_discharger_failure_completes

end DischargerFailureCompletesFixture
