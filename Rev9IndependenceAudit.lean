import Rev9FiniteBase
import Rev9PeriodReduction
import Lean.Util.FoldConsts

/-! Verification command only: traverse theorem types and proof values,
including opaque/theorem bodies, to reject circular dependencies. It declares
no mathematical theorem or axiom and does not modify the environment. -/
open Lean Elab Command

def auditIndependentProof (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let prohibited : List Name :=
    [``HypothesisMAssembly.hypothesis_M,
     ``HypothesisMAssembly.coefficient_exit_bound,
     ``HypMRev9.corollary2_residue,
     ``HypMRev9.corollary2_integer,
     ``HypMRev9.survivor_square_bound]
  let mut todo := [root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let current := todo.head!
    todo := todo.tail!
    if seen.contains current then continue
    seen := seen.insert current
    if prohibited.contains current then
      throwError "Circular dependency in {root}: {current}"
    let some info := env.find? current
      | throwError "Missing declaration while auditing {root}: {current}"
    todo := info.getUsedConstantsAsSet.toList ++ todo
  logInfo m!"INDEPENDENCE PASS: {root}; original Theorem 1 and Corollary 2 absent from the transitive proof/type closure."

run_cmd auditIndependentProof ``HypMRev9Base.second_proof_finite_base
run_cmd auditIndependentProof ``HypMRev9.period_implies_exit
