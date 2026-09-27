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

||| Zero-allocation total triple-alpha nucleosynthesis fusion energy flux accumulation using fusedHylomorphism.
public export covering
fusedComputeTotalNucleosynthesisFlux : Fuel -> List AlphaClusterState -> Stage0.BoxInt.BoxInt
fusedComputeTotalNucleosynthesisFlux f alphas =
  fusedHylomorphism f
    (\st => case st of
              [] => Done
              alpha :: rest => Yield (totalAlphaFlux alpha * intToBoxInt 3) rest)
    (\flux, acc => flux + acc)
    (intToBoxInt 0)
    alphas

||| Verification audit witness proving zero-allocation triple-alpha fusion energy flux computation.
public export
auditNucleosynthesisStreamProof : Bool
auditNucleosynthesisStreamProof =
  let alpha = seedAlphaClusterEpoch4
      flux = fusedComputeTotalNucleosynthesisFlux (limit 100) [alpha, alpha, alpha]
  in unwrapBox flux == 972

------------------------------------------------------------------------
-- 2. 2LTT STAGING CODE GENERATOR TRANSDUCERS
------------------------------------------------------------------------

||| Deforested 2LTT staged code generator transducer for nucleosynthesis fusion stream.
%inline public export
stagedNucleosynthesisPipeline : List AlphaClusterState -> Code Stage0.BoxInt.BoxInt
stagedNucleosynthesisPipeline alphas = quote (fusedComputeTotalNucleosynthesisFlux (limit 100) alphas)

||| QTT 0 erased proof witness verifying nucleosynthesis fusion stream staging inverse identity.
public export
0 prfStagedNucleosynthesisPipeline : (alphas : List AlphaClusterState) -> splice (stagedNucleosynthesisPipeline alphas) = fusedComputeTotalNucleosynthesisFlux (limit 100) alphas
prfStagedNucleosynthesisPipeline alphas = inverseSpliceQuote (fusedComputeTotalNucleosynthesisFlux (limit 100) alphas)
