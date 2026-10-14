import PSTheorem1
import AdaptiveBernoulli
import UniformProductChernoff
import RankMGF
import UniformSubsetRank
import UniformPermutationProfile
import PSProcess
import SequentialRevelation
import AdaptiveCategorical
import StoppedChoices
import LoadBound
import PhaseIntegral
import PhaseAdapter
import AsymptoticClosure
import ConcreteTheoremOne
import PSChoiceMachine
import ConcreteTheoremOneFinal
import StandardLogStar
import RandomPriority
import PaperTheoremOne
import WeightedArrival
import FiniteExposure
import ReplicaPS
import ReplicaRevelation
import FinitePhaseConstants
import FinitePhaseGrowth
import FinitePhaseSum
import FiniteAtomicExposure
import ReplicaRank
import ReplicaTrace
import FiniteArrivalCertificate
import FiniteFiveCertificate
import ReplicaAsymptoticConstants
import ReplicaRP
import FiniteSurvivor
import PaperReplicaInterface
import PSRankIncrement
import PSRankHistory
import PSFiniteClock
import PSFiniteCapacity
import PSWeightedExposure
import PSExposureBound
import PSRankAllocation
import PSExpectedRank
import ReplicaRankIncrement
import ReplicaChoiceMachine
import ReplicaHistory
import ReplicaLaw
import ReplicaCapacity
import ReplicaWeightedExposure
import ReplicaExposureBound
import ReplicaRankAllocation
import ReplicaExpectedRank
import CouponLowerBound
import UniformLowerRank
import ReplicaLowerRank
import LowerBoundBands
import ReplicaRawStep
import ReplicaRawProcess
import ReplicaRawClock
import RawSubsetCounts
import ReplicaSurvivorEntries
import ReplicaUntouched
import UniformRawPrefixes
import ReplicaRawBands
import ReplicaConsumptionLower
import RawSurvivorBound
import CouponUntouched
import ReplicaBandLower
import ReplicaRawRankBridge
import RawPrefixGood
import ReplicaRawCostRank
import LowerBoundEntropy
import FiniteLowerBound
import LowerBoundErrors
import LowerBoundCutoffs
import LowerBoundBandErrors
import LowerBoundSchedule
import LowerBoundMarket
import FixedQuotaParameters
import FixedQuotaLowerBound
import FiniteQuotaEnvelope
import TheoremContracts
import ReplicaQuotaBound
import HighQuotaAsymptotics
import BoundedQuotaAsymptotics
import Lean.Util.CollectAxioms

/-!
Audit every safe declaration originating in a project proof module, including
private helpers, definitions and generated logical constants. Module imports are checked against
all library roots by scripts/verify_sources.py. A shared dependency traversal
also checks declarations omitted from the selected public-interface audit.
Unsafe compiler implementation artifacts cannot occur in kernel proofs and are
excluded only as audit roots. Transitive dependencies are never filtered.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.imports.map (·.module) |>.filter
    (fun mod => mod != `Init && mod != `Lean.Util.CollectAxioms)
  if modules.isEmpty then
    throwError "No project modules selected for the full declaration audit"
  let mut moduleIndices : Array ModuleIdx := #[]
  for mod in modules do
    let some idx := env.getModuleIdx? mod
      | throwError "Required project module was not imported: {mod}"
    moduleIndices := moduleIndices.push idx
  let targets := env.constants.fold (init := #[]) fun names name info =>
    if info.isUnsafe then names else
      match env.getModuleIdxFor? name with
      | some idx => if moduleIndices.contains idx then names.push name else names
      | none => names
  if targets.isEmpty then
    throwError "No project declarations found in the imported modules"
  let (_, result) := ((do
    for name in targets do
      CollectAxioms.collect name).run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for dependency in result.axioms do
    unless allowed.contains dependency do
      throwError "Unexpected dependency in project declarations: {dependency}"
  for mod in modules do
    let idx := env.getModuleIdx? mod
    let count : Nat := targets.foldl (fun n name =>
      if env.getModuleIdxFor? name == idx then n + 1 else n) 0
    logInfo m!"MODULE {mod}: {count} declarations"
  logInfo m!"PASS: {targets.size} safe project declarations from {modules.size} modules; dependencies {result.axioms}"
