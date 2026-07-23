import Veil.Core.Tools.ModelChecker.Concrete.Checker

open Veil Veil.ModelChecker Veil.ModelChecker.Concrete

private def chainSystem :
    EnumerableTransitionSystem Unit (List Unit) Nat (List Nat) Int Nat
      (List (Nat × ExecutionOutcome Int Nat)) () := {
  initStates := [0]
  tr := fun _ n => if n < 6 then [(n, .success (n + 1))] else []
}

private def searchParameters (maxDepth : Nat) : SearchParameters Unit Nat := {
  invariants := [{ name := `belowFour, property := fun _ st => st < 4 }]
  earlyTerminationConditions := [
    .foundViolatingState,
    .assertionFailed,
    .deadlockOccurred,
    .reachedDepthBound maxDepth
  ]
}

private def checkDepthBound
    (parallelCfg : Option ParallelConfig)
    (maxDepth : Nat)
    (expectViolation : Bool) : IO Unit := do
  let token ← IO.CancelToken.new
  let result ← findReachable (asm := ActionStatsMap Nat)
    chainSystem (searchParameters maxDepth) parallelCfg 999999 token
  match expectViolation, result with
  | false, .noViolationFound _ (.earlyTermination (.reachedDepthBound bound)) =>
    unless bound == maxDepth do
      throw <| IO.userError s!"reported depth bound {bound}, expected {maxDepth}"
  | true, .foundViolation _ (.safetyFailure [`belowFour]) (some trace) =>
    unless trace.steps.size == 4 do
      throw <| IO.userError s!"violation trace has {trace.steps.size} steps, expected 4"
  | _, _ =>
    throw <| IO.userError s!"unexpected model-checking result: {repr result}"

#eval checkDepthBound none 3 false
#eval checkDepthBound none 4 true

private def parallelConfig : ParallelConfig := {
  numSubTasks := 2
  thresholdToParallel := 1
  numSubSteps := 1
}

#eval checkDepthBound (some parallelConfig) 3 false
#eval checkDepthBound (some parallelConfig) 4 true
