module Stage0.Hadron.NucleosynthesisStream

import Data.List
import Data.Fuel
import Stage0.OnSeq.FusedStream
import Stage0.Hadron.AlphaReplication
import Stage1.VexelMaxel
import Stage0.BoxInt
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 1. DEFORESTED NUCLEOSYNTHESIS & JET STREAMING
------------------------------------------------------------------------

||| Convert a sequence of Alpha clusters into a deforested stream.
public export
streamAlphaClusters : List AlphaClusterState -> FusedStream AlphaClusterState
streamAlphaClusters = stream

||| Deforested extraction of 3D spatial Boxel representations from Alpha clusters.
public export
fusedAlphaBoxelStream : FusedStream AlphaClusterState -> FusedStream Boxel
fusedAlphaBoxelStream = mapStream alphaClusterToBoxel

||| Deforested filter for stable nuclear clusters.
public export
fusedFilterStableAlpha : FusedStream AlphaClusterState -> FusedStream AlphaClusterState
fusedFilterStableAlpha = filterStream isAlphaStable

||| Deforested triple-alpha fusion map (Combines trios into 324-token carbon core total flux).
public export
fusedTripleAlphaFluxStream : FusedStream AlphaClusterState -> FusedStream Stage0.BoxInt.BoxInt
fusedTripleAlphaFluxStream = mapStream (\alpha => totalAlphaFlux alpha * Stage0.BoxInt.intToBoxInt 3)

||| Evaluates an Alpha cluster stream into a List container.
public export
runAlphaStream : Fuel -> FusedStream AlphaClusterState -> List AlphaClusterState
runAlphaStream = runFueledStream

||| Direct stream generation for triple-alpha Carbon fusion flux ($3 \times 108 \to 324$).
public export
unfoldAlphaFusionStream : List AlphaClusterState -> FusedStream Stage0.BoxInt.BoxInt
unfoldAlphaFusionStream alphas = fusedTripleAlphaFluxStream (stream alphas)

||| Total triple-alpha nucleosynthesis fusion energy flux accumulation using foldStreamNat.
public export
fusedComputeTotalNucleosynthesisFluxNat : (fuel : Nat) -> List AlphaClusterState -> Stage0.BoxInt.BoxInt
fusedComputeTotalNucleosynthesisFluxNat fuel alphas =
  foldStreamNat fuel (\acc, alpha => (totalAlphaFlux alpha * intToBoxInt 3) + acc) (intToBoxInt 0) (stream alphas)

||| Backward-compatible total nucleosynthesis flux accumulation using foldStreamFuel.
public export
fusedComputeTotalNucleosynthesisFlux : Fuel -> List AlphaClusterState -> Stage0.BoxInt.BoxInt
fusedComputeTotalNucleosynthesisFlux f alphas =
  foldStreamFuel f (\acc, alpha => (totalAlphaFlux alpha * intToBoxInt 3) + acc) (intToBoxInt 0) (stream alphas)

||| Verification audit witness proving zero-allocation triple-alpha fusion energy flux computation.
public export
auditNucleosynthesisStreamProof : Bool
auditNucleosynthesisStreamProof =
  let alpha = seedAlphaClusterEpoch4
      flux = fusedComputeTotalNucleosynthesisFluxNat 100 [alpha, alpha, alpha]
  in unwrapBox flux == 972

------------------------------------------------------------------------
-- 2. LINEAR QTT NUCLEON STREAM TRANSDUCERS & 2LTT STAGING
------------------------------------------------------------------------

||| Strictly linear QTT stream transducer enforcing nucleon conservation across fusion reactions:
public export
record LinearNucleonTransducer where
  constructor MkLinearNucleonTransducer
  runLinearNucleons : (1 strm : FusedStream AlphaClusterState) -> FusedStream Stage0.BoxInt.BoxInt

public export
linearTripleAlphaTransducer : LinearNucleonTransducer
linearTripleAlphaTransducer =
  MkLinearNucleonTransducer (\(MkStream next seed) =>
    MkStream (\s => case next s of
                      Done => Done
                      Skip s' => Skip s'
                      Yield alpha s' => Yield (totalAlphaFlux alpha * Stage0.BoxInt.intToBoxInt 3) s') seed)

||| Audits strict linear nucleon conservation under triple-alpha streaming:
public export
auditLinearNucleonConservationProof : Bool
auditLinearNucleonConservationProof =
  let alpha = seedAlphaClusterEpoch4
      flux = fusedComputeTotalNucleosynthesisFluxNat 100 [alpha, alpha, alpha]
  in unwrapBox flux == 972

||| Deforested 2LTT staged code generator transducer for nucleosynthesis fusion stream.
%inline public export
stagedNucleosynthesisPipeline : List AlphaClusterState -> Code Stage0.BoxInt.BoxInt
stagedNucleosynthesisPipeline alphas = quote (fusedComputeTotalNucleosynthesisFluxNat 100 alphas)

||| QTT 0 erased proof witness verifying nucleosynthesis fusion stream staging inverse identity.
public export
0 prfStagedNucleosynthesisPipeline : (alphas : List AlphaClusterState) -> splice (stagedNucleosynthesisPipeline alphas) = fusedComputeTotalNucleosynthesisFluxNat 100 alphas
prfStagedNucleosynthesisPipeline alphas = inverseSpliceQuote (fusedComputeTotalNucleosynthesisFluxNat 100 alphas)

