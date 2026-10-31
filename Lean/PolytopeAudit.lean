import PolytopeSPR
import Lean.Util.CollectAxioms
import Lean.PrivateName

#print axioms SPR.Polytope.Direct.classification

run_cmd do
  let env ← Lean.getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (name, info) in env.constants.toList do
    if (`SPR).isPrefixOf (Lean.privateToUserName name) && info.isTheorem then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
