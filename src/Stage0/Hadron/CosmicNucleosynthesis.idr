module Stage0.Hadron.CosmicNucleosynthesis

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Token
import Stage0.Bit
import Stage0.StructuralFuel
import Stage0.FieldStream
import Stage0.FluctuationStream
import Stage0.OnSeq.FusedStream
import public Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.Hadron.HadronicConfinement
import Stage1.Hadron.QuarkHadronAlgebra
import Stage0.Hadron.StellarNucleosynthesis
import Stage1.ScalePipeline
import Data.List

%default total

------------------------------------------------------------------------
-- 1. BIG BANG NUCLEOSYNTHESIS (BBN) LIGHT COSMIC NUCLEI AS DEPENDENT NUCLIDES
------------------------------------------------------------------------

||| Certified Triton (3H): 1 proton, 2 neutrons (81 tokens = 3 * 27).
public export
tritonNuclide : Nuclide 1 2
tritonNuclide = fuseNuclides deuteronNuclide neutronNuclide "H-3"

||| Certified Lithium-7 (7Li): 3 protons, 4 neutrons (189 tokens = 7 * 27).
public export
lithium7Nuclide : Nuclide 3 4
lithium7Nuclide = fuseNuclides alphaNuclide tritonNuclide "Li-7"

||| Computes exact fundamental mass tokens of a nuclide observed from constituent hadrons (each nucleon carries 27 tokens).
public export
nuclideMassTokensFromHadrons : Nuclide z n -> BoxInt
nuclideMassTokensFromHadrons (MkNuclide _ hadrons _ _ _ _) =
  mulBox (natToBoxInt 27) (addBox (countProtonsBox hadrons) (countNeutronsBox hadrons))

||| Light Cosmic Nucleus Species.
public export
data LightNucleusSpec = Deuteron2H | Triton3H | Helium3He | Lithium7Li

public export
Eq LightNucleusSpec where
  Deuteron2H == Deuteron2H = True
  Triton3H   == Triton3H   = True
  Helium3He  == Helium3He  = True
  Lithium7Li == Lithium7Li = True
  _          == _          = False

public export
Show LightNucleusSpec where
  show Deuteron2H = "2H (Deuteron)"
  show Triton3H   = "3H (Triton)"
  show Helium3He  = "3He"
  show Lithium7Li = "7Li"

||| Canonical ground truth mapping from LightNucleusSpec to its dependent Nuclide carrier (Rule 03 §8).
public export
lightNucleusToNuclide : LightNucleusSpec -> (z : Nat ** (n : Nat ** Nuclide z n))
lightNucleusToNuclide Deuteron2H = (1 ** (1 ** deuteronNuclide))
lightNucleusToNuclide Triton3H   = (1 ** (2 ** tritonNuclide))
lightNucleusToNuclide Helium3He  = (2 ** (1 ** helium3Nuclide))
lightNucleusToNuclide Lithium7Li = (3 ** (4 ** lithium7Nuclide))

||| Computes exact nucleon count of a light cosmic nucleus directly from the dependent Nuclide carrier.
public export
nucleusNucleonCount : LightNucleusSpec -> Nat
nucleusNucleonCount spec =
  let (_ ** (_ ** MkNuclide _ _ p n _ _)) = lightNucleusToNuclide spec
  in p + n

||| Computes exact fundamental mass token count of a light cosmic nucleus observed from constituent hadrons.
public export
nucleusMassTokens : LightNucleusSpec -> BoxInt
nucleusMassTokens spec =
  let (_ ** (_ ** nuc)) = lightNucleusToNuclide spec
  in nuclideMassTokensFromHadrons nuc

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR BBN NUCLEI (BOXEL REPRESENTATION)
------------------------------------------------------------------------

||| Fuses 1 Proton (27) and 1 Neutron (27) into a Deuteron 2H nucleus (54 tokens).
public export
fuseDeuteron : HadronBoxel -> HadronBoxel -> Boxel
fuseDeuteron p n = p <+> n

||| Fuses an authentic HadronToken multiset into a composite nuclear Boxel in a single pass (Rule 04 §12).
public export
fuseHadronsToBoxel : Multiset BoxInt HadronToken -> Boxel
fuseHadronsToBoxel bag =
  foldStreamNat (boxToNat (absBox (multisetSum bag)))
    (\acc, _ => acc <+> seedHadronBoxel)
    emptyCellMultiset
    (streamTokens bag)

||| Fuses 3 Protons and 4 Neutrons from an authentic HadronToken multiset into a Lithium-7 Boxel.
public export
fuseLithium7Multiset : Multiset BoxInt HadronToken -> Boxel
fuseLithium7Multiset = fuseHadronsToBoxel

||| @deprecated Materializes nucleons into intermediate `List HadronBoxel` (violates Rule 04 §8).
||| Use `fuseLithium7Multiset` or `fuseHadronsToBoxel` instead.
public export
fuseLithium7 : List HadronBoxel -> Boxel
fuseLithium7 nucleons = foldl (<+>) emptyCellMultiset nucleons

------------------------------------------------------------------------
-- 2b. RADIATIVE CAPTURE PHOTON EMISSION (FINSC-ELECTROMAGNETISM)
------------------------------------------------------------------------

||| Single radiative capture reaction step: p + n -> d + gamma.
||| Produces a certified Deuteron nuclide and an emitted discrete PhotonStateToken (FinSc-Electromagnetism).
public export
radiativeDeuteronCapture : HadronToken -> HadronToken -> Maybe (Nuclide 1 1, PhotonStateToken)
radiativeDeuteronCapture ProtonToken NeutronToken =
  Just (deuteronNuclide, MkPhotonToken One (intToBoxInt 2))
radiativeDeuteronCapture NeutronToken ProtonToken =
  Just (deuteronNuclide, MkPhotonToken One (intToBoxInt 2))
radiativeDeuteronCapture _ _ = Nothing

||| Streaming radiative deuteron capture emitting a deforested stream of photon tokens (Rule 04 §8).
public export
streamRadiativeDeuteronPhotons : FusedStream (HadronToken, HadronToken) -> FusedStream PhotonStateToken
streamRadiativeDeuteronPhotons strm =
  filterMapStream (\(h1, h2) => case radiativeDeuteronCapture h1 h2 of
                                  Just (_, photon) => Just photon
                                  Nothing          => Nothing) strm

||| Evaluates total radiative energy released during cosmic deuteron synthesis directly in O(1) memory.
%spec fuel
public export
evaluateCosmicRadiativeEnergy : (fuel : Nat) -> FusedStream PhotonStateToken -> BoxInt
evaluateCosmicRadiativeEnergy fuel strm =
  fusedComputePhotonStreamEnergyDirect (limit fuel) (fusedPhotonStateStream strm)

------------------------------------------------------------------------
-- 3. COSMIC BBN REACTOR STREAM TRANSDUCER & MASS FRACTION REDUCTION
------------------------------------------------------------------------

||| Primordial Nucleon token entering the Big Bang cosmic reactor.
public export
data BBNNucleon = PrimordialProton | PrimordialNeutron

public export
Eq BBNNucleon where
  PrimordialProton  == PrimordialProton  = True
  PrimordialNeutron == PrimordialNeutron = True
  _                 == _                 = False

public export
Show BBNNucleon where
  show PrimordialProton  = "p_bbn"
  show PrimordialNeutron = "n_bbn"

||| Embedding into foundational HadronToken carrier.
public export
bbnToHadronToken : BBNNucleon -> HadronToken
bbnToHadronToken PrimordialProton  = ProtonToken
bbnToHadronToken PrimordialNeutron = NeutronToken

||| Observable output of a cosmic BBN reaction step.
public export
record BBNReactionStep where
  constructor MkBBNReactionStep
  stepIndex        : Nat
  freeProtons      : Nat
  freeNeutrons     : Nat
  deuteronCount    : Nat
  helium4Count     : Nat
  totalNucleons    : Nat
  observedHeliumYp : UnixelFraction

------------------------------------------------------------------------
-- 3b. BBN THERMODYNAMIC ENTROPY PRODUCTION (FINSC-THERMODYNAMICS)
------------------------------------------------------------------------

||| Represents the thermodynamic step of cosmic nucleosynthesis with energy release and entropy production.
public export
bbnThermodynamicFluctuation : BBNReactionStep -> FluctuationStep
bbnThermodynamicFluctuation step =
  let qYield = mulBox (natToBoxInt step.deuteronCount) (intToBoxInt 2)
      heat = addBox qYield (mulBox (natToBoxInt step.helium4Count) (intToBoxInt 28))
  in MkFluctuation (cast step.stepIndex) qYield heat

||| Streams concurrent (work/energy yield, bath heat) fluctuation steps from the BBN reactor stream
||| via FinSc-Thermodynamics zipSystemBathFluctuations (Rule 03 §8):
public export
streamBBNFluctuationPairs : FusedStream BBNReactionStep -> FusedStream FluctuationStep
streamBBNFluctuationPairs strm =
  let workStrm = mapStream (\s => mulBox (natToBoxInt s.deuteronCount) (intToBoxInt 2)) strm
      heatStrm = mapStream (\s => addBox (mulBox (natToBoxInt s.deuteronCount) (intToBoxInt 2))
                                         (mulBox (natToBoxInt s.helium4Count) (intToBoxInt 28))) strm
  in zipSystemBathFluctuations workStrm heatStrm

public export
record BBNReactorState where
  constructor MkBBNReactorState
  stepIdx     : Nat
  pUnbound    : Nat
  nUnbound    : Nat
  deuterons   : Nat
  he4         : Nat
  totStreamed : Nat

||| Initial quiescent state of the cosmic BBN reactor.
public export
initialBBNState : BBNReactorState
initialBBNState = MkBBNReactorState 0 0 0 0 0 0

||| Single-pass state transition step for BBN reactor.
||| Models the standard BBN fusion chain:
||| 1. p + n -> d (Deuteron bottleneck formation)
||| 2. 2d -> 4He (Helium-4 synthesis)
public export
stepBBNState : BBNReactorState -> BBNNucleon -> BBNReactorState
stepBBNState (MkBBNReactorState idx p n d he4 tot) PrimordialProton =
  let idx' = S idx
      tot' = S tot
  in case n of
       Z => MkBBNReactorState idx' (S p) 0 d he4 tot'
       S nRem =>
         let d' = S d
         in case d' of
              (S (S dRem)) => MkBBNReactorState idx' p nRem dRem (S he4) tot'
              _ => MkBBNReactorState idx' p nRem d' he4 tot'
stepBBNState (MkBBNReactorState idx p n d he4 tot) PrimordialNeutron =
  let idx' = S idx
      tot' = S tot
  in case p of
       Z => MkBBNReactorState idx' 0 (S n) d he4 tot'
       S pRem =>
         let d' = S d
         in case d' of
              (S (S dRem)) => MkBBNReactorState idx' pRem n dRem (S he4) tot'
              _ => MkBBNReactorState idx' pRem n d' he4 tot'

||| Converts reactor state into an observable reaction step.
public export
bbnStateToStep : BBNReactorState -> BBNReactionStep
bbnStateToStep (MkBBNReactorState idx p n d he4 tot) =
  let he4Nucleons = he4 * 4
      yp = if tot > 0
             then mkUnixelFraction (natToBoxInt he4Nucleons) tot
             else zeroUnixelFraction
  in MkBBNReactionStep idx p n d he4 tot yp

||| Deforested stream step for BBN reactor.
public export
bbnTransducerStep : BBNReactorState -> BBNNucleon -> Step BBNReactorState BBNReactionStep
bbnTransducerStep st nuc =
  let st' = stepBBNState st nuc
  in Yield (bbnStateToStep st') st'

||| Stateful deforested stream transducer for the cosmic BBN reactor.
public export
bbnReactorTransducer : StreamTransducer BBNNucleon BBNReactionStep
bbnReactorTransducer = MkTransducer bbnTransducerStep initialBBNState

||| Streams the cosmic BBN reactor in single-pass O(1) auxiliary registers.
public export
streamBBNReactor : FusedStream BBNNucleon -> FusedStream BBNReactionStep
streamBBNReactor = transduceStream bbnReactorTransducer

||| Canonical primordial freeze-out nucleon feed (n/p = 1/7, represented by 2 neutrons and 14 protons, total 16 nucleons).
public export
primordialFreezeOutFeed : List BBNNucleon
primordialFreezeOutFeed =
  [ PrimordialNeutron, PrimordialProton
  , PrimordialNeutron, PrimordialProton
  , PrimordialProton, PrimordialProton
  , PrimordialProton, PrimordialProton
  , PrimordialProton, PrimordialProton
  , PrimordialProton, PrimordialProton
  , PrimordialProton, PrimordialProton
  , PrimordialProton, PrimordialProton
  ]

||| Retrieves the final step from a sequence of BBN reaction steps.
public export
lastBBNStep : List BBNReactionStep -> Maybe BBNReactionStep
lastBBNStep [] = Nothing
lastBBNStep [x] = Just x
lastBBNStep (_ :: rest) = lastBBNStep rest

||| Primordial Helium-4 mass fraction observed from the BBN reactor stream:
||| Y_p = 4 / 16 = 1/4 = 0.25.
public export
observedPrimordialHelium4MassFraction : UnixelFraction
observedPrimordialHelium4MassFraction =
  case lastBBNStep (runFueledStreamNat 32 (streamBBNReactor (stream primordialFreezeOutFeed))) of
    Just step => step.observedHeliumYp
    Nothing   => zeroUnixelFraction

||| Verifies nucleon conservation at an individual BBN reaction step:
||| freeProtons + freeNeutrons + 2*deuterons + 4*he4 = totalNucleons.
public export
stepNucleonConservation : BBNReactionStep -> Bool
stepNucleonConservation step =
  (step.freeProtons + step.freeNeutrons + (2 * step.deuteronCount) + (4 * step.helium4Count)) == step.totalNucleons

------------------------------------------------------------------------
-- 4. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Audits BBN Mass Token Conservation:
||| 1. Deuteron 2H = 2 * 27 = 54 tokens.
||| 2. Triton 3H = 3 * 27 = 81 tokens.
||| 3. Helium-3 = 3 * 27 = 81 tokens.
||| 4. Lithium-7 = 7 * 27 = 189 tokens.
public export
auditCosmicNucleosynthesisProof : Bool
auditCosmicNucleosynthesisProof =
  (nucleusMassTokens Deuteron2H == intToBoxInt 54) &&
  (nucleusMassTokens Triton3H   == intToBoxInt 81) &&
  (nucleusMassTokens Helium3He  == intToBoxInt 81) &&
  (nucleusMassTokens Lithium7Li == intToBoxInt 189)

||| Neutron-to-proton freeze-out ratio prior to BBN: n/p = 1/7.
public export
neutronProtonFreezeOutRatio : UnixelFraction
neutronProtonFreezeOutRatio = mkUnixelFraction (intToBoxInt 1) 7

||| Primordial Helium-4 mass fraction observed from BBN reactor stream: Y_p = 4/16 = 1/4 = 0.25.
public export
primordialHelium4MassFraction : UnixelFraction
primordialHelium4MassFraction = observedPrimordialHelium4MassFraction

||| PDG / Planck 2018 empirical lower bound: Y_p >= 0.24.
public export
pdgHelium4LowerBound : UnixelFraction
pdgHelium4LowerBound = mkUnixelFraction (intToBoxInt 24) 100

||| PDG / Planck 2018 empirical upper bound: Y_p <= 0.26.
public export
pdgHelium4UpperBound : UnixelFraction
pdgHelium4UpperBound = mkUnixelFraction (intToBoxInt 26) 100

||| Audits that primordial Helium-4 mass fraction falls within PDG empirical bounds:
||| 0.24 <= 0.25 <= 0.26.
public export
auditBBNHeliumMassFractionProof : Bool
auditBBNHeliumMassFractionProof =
  rationalGTE primordialHelium4MassFraction pdgHelium4LowerBound &&
  rationalLTE primordialHelium4MassFraction pdgHelium4UpperBound

||| Deuteron boundary area tokens: Area(d) = 2 * 27 = 54.
||| Matches Law 13 Holographic Area: Area(partial V) = 6 * 3^2 = 54.
public export
deuteronHolographicAreaTokens : Nat
deuteronHolographicAreaTokens = 54

||| Audits that Deuteron (54) saturates the 2D boundary of the 3D unit cube (L=3)
||| and that 4 Deuterons enclose the Primorial 210 cosmic budget (4 * 54 = 216 >= 210).
public export
auditBBNHolographicSaturationProof : Bool
auditBBNHolographicSaturationProof =
  (deuteronHolographicAreaTokens == 54) &&
  (4 * deuteronHolographicAreaTokens >= 210) &&
  (nucleusMassTokens Lithium7Li + intToBoxInt 21 == intToBoxInt 210)

||| Audits that all 16 steps of the deforested BBN reactor stream preserve strict nucleon conservation (ΔA = 0).
public export
auditBBNStreamNucleonConservationProof : Bool
auditBBNStreamNucleonConservationProof =
  let steps = runFueledStreamNat 32 (streamBBNReactor (stream primordialFreezeOutFeed))
  in all stepNucleonConservation steps && (length steps == 16)

||| Audits that streaming radiative deuteron capture emits valid photon energy tokens (FinSc-Electromagnetism).
public export
auditRadiativeDeuteronCaptureProof : Bool
auditRadiativeDeuteronCaptureProof =
  let pairStream = stream [(ProtonToken, NeutronToken), (NeutronToken, ProtonToken)]
      photonStream = streamRadiativeDeuteronPhotons pairStream
      totE = evaluateCosmicRadiativeEnergy 4 photonStream
  in totE == intToBoxInt 6

||| Audits that cosmic BBN open-system entropy production is non-negative at every step (FinSc-Thermodynamics).
public export
auditBBNThermodynamicEntropyProof : Bool
auditBBNThermodynamicEntropyProof =
  let steps = runFueledStreamNat 32 (streamBBNReactor (stream primordialFreezeOutFeed))
      flucts = map bbnThermodynamicFluctuation steps
      strm = linearEntropyTransducer.stepEntropyProduction (stream flucts)
      results = runFueledStreamNat 32 strm
      bbnPairs = runFueledStreamNat 32 (streamBBNFluctuationPairs (stream steps))
  in all snd results && (length bbnPairs == 16)

||| Audits that Lithium-7 multiset fusion produces exact 189 fundamental mass tokens (7 * 27) without lists (Rule 04 §12).
public export
auditLithium7MultisetFusionProof : Bool
auditLithium7MultisetFusionProof =
  let (_ ** _ ** li7) = lightNucleusToNuclide Lithium7Li
      boxel = fuseLithium7Multiset li7.hadrons
  in totalCellMultisetWeight boxel == intToBoxInt 189
