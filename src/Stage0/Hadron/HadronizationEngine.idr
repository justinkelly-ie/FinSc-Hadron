module Stage0.Hadron.HadronizationEngine

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.Token
import Stage0.OnSeq.FusedStream
import Stage1.Hadron.StandardModel
import Stage1.ScalePipeline
import Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. QUARK-GLUON PLASMA (QGP) JET FRAGMENTATION & QCD HADRONIZATION
------------------------------------------------------------------------

||| Cosmological Phase of Strong Matter:
||| - QuarkGluonPlasma: Deconfined high-temperature color-octet phase.
||| - HadronGasTransition: Flux-tube string breaking & hadron formation.
||| - ConfinementHadronGas: Low-temperature color-singlet hadron phase.
public export
data QGPPhase = QuarkGluonPlasma | HadronGasTransition | ConfinementHadronGas

public export
Eq QGPPhase where
  QuarkGluonPlasma     == QuarkGluonPlasma     = True
  HadronGasTransition  == HadronGasTransition  = True
  ConfinementHadronGas == ConfinementHadronGas = True
  _                    == _                    = False

||| A Hadronized Jet State resulting from QGP flux-tube fragmentation.
|||
||| @deprecated Non-conforming carrier holding intermediate `List StandardModelParticle`
||| (violates Rule 04 §8 and Rule 04 §12). Prefer `MultisetHadronizedJetState` or deforested
||| streams of tokens (`streamFragmentQGPJetTokens`).
public export
record HadronizedJetState where
  constructor MkHadronizedJetState
  hadrons  : List StandardModelParticle
  qgpPhase : QGPPhase

------------------------------------------------------------------------
-- 1B. PURE MULTISET QGP JET FRAGMENTATION & GALOIS FIBER PULLBACK (f^*)
------------------------------------------------------------------------

||| Pure Multiset Fiber Decay Map for QGP Jet Fragmentation:
||| Gluons decay into u u_bar pairs (g -> u + u_bar), while color-singlet hadrons remain invariant.
|||
||| @deprecated Allocates intermediate List instances in fiber expansion (violates Rule 04 §12).
||| Prefer `qgpDecayFiberStream` or `streamFragmentQGPJetTokens`.
public export
qgpDecayFiberMap : StandardModelParticle -> List StandardModelParticle
qgpDecayFiberMap (SMPBoson GluonR) = [SMPFermion QuarkU, SMPFermion AntiQuarkU]
qgpDecayFiberMap p                 = [p]

||| Deforested stream-to-stream Galois fiber pullback QGP jet fragmentation.
||| Uses a zero-allocation step generator without intermediate heap list allocation (Rule 04 §8).
public export
qgpDecayFiberStream : StandardModelParticle -> FusedStream StandardModelParticle
qgpDecayFiberStream (SMPBoson GluonR) =
  MkStream (\case
    0 => Yield (SMPFermion QuarkU) 1
    1 => Yield (SMPFermion AntiQuarkU) 2
    _ => Done
  ) (the Nat 0)
qgpDecayFiberStream p =
  MkStream (\case
    0 => Yield p 1
    _ => Done
  ) (the Nat 0)

||| Single-pass deforested QGP jet fragmentation operator streaming partons in O(1) memory.
public export
streamFragmentQGPJet : FusedStream StandardModelParticle -> FusedStream StandardModelParticle
streamFragmentQGPJet = flatMapStream qgpDecayFiberStream

||| Atomic token-level QGP jet decay fiber stream:
||| Splitting gluon tokens into u and u_bar quark tokens in O(1) auxiliary registers (Rule 04 §12).
public export
qgpDecayTokenStream : Token StandardModelParticle -> FusedStream (Token StandardModelParticle)
qgpDecayTokenStream (MkToken (SMPBoson GluonR)) =
  MkStream (\case
    0 => Yield (MkToken (SMPFermion QuarkU)) 1
    1 => Yield (MkToken (SMPFermion AntiQuarkU)) 2
    _ => Done
  ) (the Nat 0)
qgpDecayTokenStream tok =
  MkStream (\case
    0 => Yield tok 1
    _ => Done
  ) (the Nat 0)

||| Single-pass deforested token stream QGP jet fragmentation operator (Rule 04 §12).
public export
streamFragmentQGPJetTokens : FusedStream (Token StandardModelParticle) -> FusedStream (Token StandardModelParticle)
streamFragmentQGPJetTokens = flatMapStream qgpDecayTokenStream

||| Key-weight decay fiber stream for QGP jet fragmentation.
public export
qgpDecayWeightStream : (StandardModelParticle, BoxInt) -> FusedStream (StandardModelParticle, BoxInt)
qgpDecayWeightStream (SMPBoson GluonR, w) =
  MkStream (\case
    0 => Yield (SMPFermion QuarkU, w) 1
    1 => Yield (SMPFermion AntiQuarkU, w) 2
    _ => Done
  ) (the Nat 0)
qgpDecayWeightStream (other, w) =
  MkStream (\case
    0 => Yield (other, w) 1
    _ => Done
  ) (the Nat 0)

||| Key-weight stream QGP jet fragmentation operator (Rule 04 §12).
||| Each gluon of weight w splits into u (weight w) and u_bar (weight w) in O(1) registers.
public export
streamFragmentQGPJetWeights : FusedStream (StandardModelParticle, BoxInt) -> FusedStream (StandardModelParticle, BoxInt)
streamFragmentQGPJetWeights = flatMapStream qgpDecayWeightStream

||| Multiset-powered Hadronized Jet State.
public export
record MultisetHadronizedJetState where
  constructor MkMultisetHadronizedJetState
  hadronBag : Multiset BoxInt StandardModelParticle
  qgpPhase  : QGPPhase

||| Pure Galois Fiber Pullback (f^*) QGP jet fragmentation operator over Multiset BoxInt StandardModelParticle.
|||
||| @deprecated Relies on fiberPullback with intermediate List conversions. Prefer `fragmentQGPJetStreamDirect`.
public export
fragmentQGPJetMultiset : Multiset BoxInt StandardModelParticle -> MultisetHadronizedJetState
fragmentQGPJetMultiset jetBag =
  let hadronBag = fiberPullback qgpDecayFiberMap jetBag
  in MkMultisetHadronizedJetState hadronBag ConfinementHadronGas

||| Deforested streaming QGP jet fragmentation directly consuming and producing multisets (Rule 04 §12).
||| Eliminates all intermediate List allocations by streaming tokens in O(1) auxiliary registers.
public export
fragmentQGPJetStreamDirect : Multiset BoxInt StandardModelParticle -> MultisetHadronizedJetState
fragmentQGPJetStreamDirect jetBag =
  let hadronBag = streamTokensToMultiset (streamFragmentQGPJetTokens (streamTokens jetBag))
  in MkMultisetHadronizedJetState hadronBag ConfinementHadronGas

||| Strict QTT Linear State Evolution for QGP Hadronization pairing state with hadron yields (Rule 04 §1).
public export
stepHadronizationLinearPair : (1 state : MultisetHadronizedJetState) ->
                              LinearStatePair MultisetHadronizedJetState (Multiset BoxInt StandardModelParticle)
stepHadronizationLinearPair (MkMultisetHadronizedJetState bag _) =
  let nextState = fragmentQGPJetStreamDirect bag
  in MkLStatePair nextState (hadronBag nextState)

||| Strict QTT Linear State Evolution for QGP Hadronization (Rule 04).
||| Consumes the deconfined QGP state linearly to guarantee zero state cloning or silent decay loss.
public export
stepHadronizationLinear : (1 state : MultisetHadronizedJetState) -> MultisetHadronizedJetState
stepHadronizationLinear st =
  let MkLStatePair st' _ = stepHadronizationLinearPair st
  in st'

------------------------------------------------------------------------
-- 2. HADRONIZATION AUTOMATON (g -> q q_bar, q q_bar -> Pion, q q q -> Nucleon)
------------------------------------------------------------------------

||| Fragments a Quark-Gluon Plasma jet into color-singlet hadrons.
||| 1. Gluons decay into quark-antiquark pairs (g -> u u_bar or d d_bar).
||| 2. Quark-antiquark pairs condense into Mesons (Pions).
||| 3. Triplet quarks condense into Baryons (Protons/Neutrons).
|||
||| @deprecated Non-conforming legacy List processor (allocates heap cons cells, violates Rule 04 §8).
||| Prefer `streamFragmentQGPJetTokens` or `fragmentQGPJetStreamDirect`.
public export
fragmentQGPJet : List StandardModelParticle -> HadronizedJetState
fragmentQGPJet inputJet =
  let hadronList = mapHadron inputJet
  in MkHadronizedJetState hadronList ConfinementHadronGas
  where
    mapHadron : List StandardModelParticle -> List StandardModelParticle
    mapHadron [] = []
    mapHadron (SMPBoson GluonR :: rest) =
      SMPFermion QuarkU :: SMPFermion AntiQuarkU :: mapHadron rest
    mapHadron (p :: rest) = p :: mapHadron rest

||| Verifies color-singlet confinement invariant (nominal phase check):
|||
||| @deprecated Nominal check inspecting only the QGPPhase enum. Prefer `isColorNeutralBuffer`
||| which rigorously verifies zero residual color charges in the condensation buffer (Rule 03 §8).
public export
isColorConlinedState : HadronizedJetState -> Bool
isColorConlinedState (MkHadronizedJetState hadrons phase) =
  phase == ConfinementHadronGas

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL INVARIANT AUDIT
------------------------------------------------------------------------

||| Audits Hadronization & QGP Jet Fragmentation Automaton:
||| 1. Verifies gluon jet splitting g -> u u_bar.
||| 2. Verifies transition to ConfinementHadronGas phase.
||| 3. Pure multiset Galois fiber pullback jet fragmentation verified.
||| 4. Deforested stream-to-multiset direct fragmentation verified (Rule 04 §12).
public export
auditHadronizationEngineProof : Bool
auditHadronizationEngineProof =
  let jet = [SMPBoson GluonR]
      hadronState = fragmentQGPJet jet
      
      initJet : Multiset BoxInt StandardModelParticle
      initJet = AddM (SMPBoson GluonR) (intToBoxInt 1) ZeroM
      mState  = fragmentQGPJetMultiset initJet
      mDirect = fragmentQGPJetStreamDirect initJet
      expectedBag : Multiset BoxInt StandardModelParticle
      expectedBag = AddM (SMPFermion QuarkU) (intToBoxInt 1) (AddM (SMPFermion AntiQuarkU) (intToBoxInt 1) ZeroM)
      
      tList = (isColorConlinedState hadronState == True) &&
              (hadrons hadronState == [SMPFermion QuarkU, SMPFermion AntiQuarkU])
      tMultiset = (qgpPhase mState == ConfinementHadronGas) &&
                  (hadronBag mState == expectedBag)
      tDirect   = (qgpPhase mDirect == ConfinementHadronGas) &&
                  (hadronBag mDirect == expectedBag)
      strmJet = streamFragmentQGPJet (stream [SMPBoson GluonR])
      strmCount = foldStreamNat 2 (\acc, _ => S acc) 0 strmJet
  in tList && tMultiset && tDirect && strmCount == 2

------------------------------------------------------------------------
-- 4. RLE MULTIPLICITY STREAMING JET FRAGMENTATION (BoxNat)
------------------------------------------------------------------------

||| RLE-compressed particle token carrying exact BoxNat multiplicity.
public export
record RLEParticleToken where
  constructor MkRLEParticle
  particle     : StandardModelParticle
  multiplicity : BoxNat

public export
Eq RLEParticleToken where
  (MkRLEParticle p1 m1) == (MkRLEParticle p2 m2) =
    p1 == p2 && boxNatToNat m1 == boxNatToNat m2

||| Streams a hadron bag as a zero-allocation deforested RLE stream of (particle, BoxNat).
|||
||| @deprecated Manual loop over AddM constructors. Prefer `multisetToRLEStream` or native `multisetToStream` (Rule 04 §12).
public export
streamHadronBagRLE : Multiset BoxInt StandardModelParticle -> FusedStream RLEParticleToken
streamHadronBagRLE bag =
  unfoldStream step bag
  where
    step : Multiset BoxInt StandardModelParticle -> Step (Multiset BoxInt StandardModelParticle) RLEParticleToken
    step ZeroM = Done
    step (AddM p w rest) =
      let m = natToBoxNat (boxToNat (absBox w))
      in Yield (MkRLEParticle p m) rest

||| Deforested stream mapping from native multiset stream directly into RLEParticleTokens (Rule 04 §12).
public export
multisetToRLEStream : Multiset BoxInt StandardModelParticle -> FusedStream RLEParticleToken
multisetToRLEStream bag =
  mapStream (\(p, w) => MkRLEParticle p (natToBoxNat (boxToNat (absBox w)))) (multisetToStream bag)

||| Folds an RLE particle stream back into an algebraic Multiset with explicit fuel bound (Rule 04 §12).
%spec fuel
public export
streamRLEToMultiset : (fuel : Nat) -> FusedStream RLEParticleToken -> Multiset BoxInt StandardModelParticle
streamRLEToMultiset fuel strm =
  foldStreamNat fuel
    (\bag, (MkRLEParticle p m) => insertItemBox p (natToBoxInt (boxNatToNat m)) bag)
    ZeroM
    strm

||| RLE decay fiber stream for QGP jet fragmentation.
public export
qgpDecayRLEStream : RLEParticleToken -> FusedStream RLEParticleToken
qgpDecayRLEStream (MkRLEParticle (SMPBoson GluonR) m) =
  MkStream (\case
    0 => Yield (MkRLEParticle (SMPFermion QuarkU) m) 1
    1 => Yield (MkRLEParticle (SMPFermion AntiQuarkU) m) 2
    _ => Done
  ) (the Nat 0)
qgpDecayRLEStream (MkRLEParticle other m) =
  MkStream (\case
    0 => Yield (MkRLEParticle other m) 1
    _ => Done
  ) (the Nat 0)

||| Deforested QGP fragmentation transducer over RLE particle streams:
||| Splitting gluons into u and u_bar pairs while preserving BoxNat multiplicities in O(1) registers.
public export
streamFragmentQGPRLE : FusedStream RLEParticleToken -> FusedStream RLEParticleToken
streamFragmentQGPRLE = flatMapStream qgpDecayRLEStream

||| Evaluates discrete internal energy contribution of an RLE particle token.
public export
rleParticleEnergy : RLEParticleToken -> BoxInt
rleParticleEnergy (MkRLEParticle p m) =
  let w = natToBoxInt (boxNatToNat m)
  in mulBox w (intToBoxInt 1)

||| Deforested transducer mapping an RLE particle stream to discrete energy-weight pairs (E, w).
public export
streamRLEParticleToEnergyPairs : FusedStream RLEParticleToken -> FusedStream (BoxInt, BoxInt)
streamRLEParticleToEnergyPairs strm =
  mapStream (\tok => (rleParticleEnergy tok, natToBoxInt (boxNatToNat (multiplicity tok)))) strm

------------------------------------------------------------------------
-- 5. DEFORESTED COLOR-SINGLET CONDENSATION STREAM TRANSDUCER
------------------------------------------------------------------------

||| Triplet Quark Color Charge (SU(3) fundamental representation 3).
public export
data TripletColor = ColorRed | ColorGreen | ColorBlue

public export
Eq TripletColor where
  ColorRed   == ColorRed   = True
  ColorGreen == ColorGreen = True
  ColorBlue  == ColorBlue  = True
  _          == _          = False

public export
Show TripletColor where
  show ColorRed   = "R"
  show ColorGreen = "G"
  show ColorBlue  = "B"

||| Antitriplet Antiquark Color Charge (SU(3) conjugate representation 3*).
public export
data AntiTripletColor = AntiRed | AntiGreen | AntiBlue

public export
Eq AntiTripletColor where
  AntiRed   == AntiRed   = True
  AntiGreen == AntiGreen = True
  AntiBlue  == AntiBlue  = True
  _         == _         = False

public export
Show AntiTripletColor where
  show AntiRed   = "R_bar"
  show AntiGreen = "G_bar"
  show AntiBlue  = "B_bar"

||| A colored parton entering the hadronization condensation stream.
public export
data ColoredParton =
    QuarkParton SMFermion TripletColor
  | AntiQuarkParton SMFermion AntiTripletColor
  | GluonParton SMBoson

public export
Eq ColoredParton where
  (QuarkParton f1 c1)     == (QuarkParton f2 c2)     = f1 == f2 && c1 == c2
  (AntiQuarkParton f1 c1) == (AntiQuarkParton f2 c2) = f1 == f2 && c1 == c2
  (GluonParton g1)        == (GluonParton g2)        = g1 == g2
  _                       == _                       = False

||| State buffer for single-pass color-singlet condensation.
public export
record ColorCondensationState where
  constructor MkCondensationState
  uR : Nat; uG : Nat; uB : Nat
  dR : Nat; dG : Nat; dB : Nat
  uBarR : Nat; uBarG : Nat; uBarB : Nat
  dBarR : Nat; dBarG : Nat; dBarB : Nat

public export
Eq ColorCondensationState where
  (MkCondensationState ur1 ug1 ub1 dr1 dg1 db1 ubr1 ubg1 ubb1 dbr1 dbg1 dbb1) ==
  (MkCondensationState ur2 ug2 ub2 dr2 dg2 db2 ubr2 ubg2 ubb2 dbr2 dbg2 dbb2) =
    ur1 == ur2 && ug1 == ug2 && ub1 == ub2 &&
    dr1 == dr2 && dg1 == dg2 && db1 == db2 &&
    ubr1 == ubr2 && ubg1 == ubg2 && ubb1 == ubb2 &&
    dbr1 == dbr2 && dbg1 == dbg2 && dbb1 == dbb2

public export
initialCondensationState : ColorCondensationState
initialCondensationState = MkCondensationState 0 0 0 0 0 0 0 0 0 0 0 0

||| Constructivist verification that the condensation buffer is strictly color neutral (Rule 03 §8).
||| Proves that zero isolated fractional or triplet color charges remain unconfined.
public export
isColorNeutralBuffer : ColorCondensationState -> Bool
isColorNeutralBuffer (MkCondensationState 0 0 0 0 0 0 0 0 0 0 0 0) = True
isColorNeutralBuffer _ = False

||| Ingests an incoming colored parton into the condensation buffer.
public export
ingestParton : ColorCondensationState -> ColoredParton -> ColorCondensationState
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (QuarkParton QuarkU ColorRed)   = MkCondensationState (S ur) ug ub dr dg db ubr ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (QuarkParton QuarkU ColorGreen) = MkCondensationState ur (S ug) ub dr dg db ubr ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (QuarkParton QuarkU ColorBlue)  = MkCondensationState ur ug (S ub) dr dg db ubr ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (QuarkParton QuarkD ColorRed)   = MkCondensationState ur ug ub (S dr) dg db ubr ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (QuarkParton QuarkD ColorGreen) = MkCondensationState ur ug ub dr (S dg) db ubr ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (QuarkParton QuarkD ColorBlue)  = MkCondensationState ur ug ub dr dg (S db) ubr ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (AntiQuarkParton AntiQuarkU AntiRed)   = MkCondensationState ur ug ub dr dg db (S ubr) ubg ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (AntiQuarkParton AntiQuarkU AntiGreen) = MkCondensationState ur ug ub dr dg db ubr (S ubg) ubb dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (AntiQuarkParton AntiQuarkU AntiBlue)  = MkCondensationState ur ug ub dr dg db ubr ubg (S ubb) dbr dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (AntiQuarkParton AntiQuarkD AntiRed)   = MkCondensationState ur ug ub dr dg db ubr ubg ubb (S dbr) dbg dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (AntiQuarkParton AntiQuarkD AntiGreen) = MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr (S dbg) dbb
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (AntiQuarkParton AntiQuarkD AntiBlue)  = MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg (S dbb)
ingestParton (MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb) (GluonParton _) =
  -- Gluon splits into u_R + u_bar_R pair in QGP
  MkCondensationState (S ur) ug ub dr dg db (S ubr) ubg ubb dbr dbg dbb
ingestParton st _ = st

------------------------------------------------------------------------
-- 5B. LAYER L-1 OBSERVABLE REDUCTIONS & CONSTRUCTIVE CLASSIFICATION (Rule 03 §8)
------------------------------------------------------------------------

||| Observes the exact electrical charge (in 1/3 e units) of a colored parton from Layer L-1 (Rule 03 §8).
public export
partonChargeThirds : ColoredParton -> BoxInt
partonChargeThirds (QuarkParton f _)     = electricChargeThirds (SMPFermion f)
partonChargeThirds (AntiQuarkParton f _) = electricChargeThirds (SMPFermion f)
partonChargeThirds (GluonParton g)        = electricChargeThirds (SMPBoson g)

||| Observes the exact baryon number (in 1/3 units) of a colored parton from Layer L-1 (Rule 03 §8).
public export
partonBaryonThirds : ColoredParton -> BoxInt
partonBaryonThirds (QuarkParton f _)     = (particleQuantumNumbers (SMPFermion f)).baryonThirds
partonBaryonThirds (AntiQuarkParton f _) = (particleQuantumNumbers (SMPFermion f)).baryonThirds
partonBaryonThirds (GluonParton g)        = (particleQuantumNumbers (SMPBoson g)).baryonThirds

||| Observes the exact weak isospin (doubled, 2 * I_3) of a colored parton from Layer L-1 (Rule 03 §8).
public export
partonIsospinDoubled : ColoredParton -> BoxInt
partonIsospinDoubled (QuarkParton f _)     = (particleQuantumNumbers (SMPFermion f)).weakIsospinDoubled
partonIsospinDoubled (AntiQuarkParton f _) = (particleQuantumNumbers (SMPFermion f)).weakIsospinDoubled
partonIsospinDoubled (GluonParton g)        = (particleQuantumNumbers (SMPBoson g)).weakIsospinDoubled

||| Observes the exact mass tokens of a constituent parton from Layer L-1 (Rule 03 §8).
||| Quarks carry 9 mass tokens in the 3x3x3 hadronic lattice.
public export
partonMassTokens : ColoredParton -> BoxInt
partonMassTokens (QuarkParton _ _)     = intToBoxInt 9
partonMassTokens (AntiQuarkParton _ _) = intToBoxInt 9
partonMassTokens (GluonParton _)        = intToBoxInt 0

||| Observes total electrical charge of a candidate parton multiset via monomorphic reduction (Rule 03 §8).
public export
observePartonBagChargeThirds : Multiset BoxInt ColoredParton -> BoxInt
observePartonBagChargeThirds = foldMultiset (\p, w, acc => addBox (mulBox w (partonChargeThirds p)) acc) (intToBoxInt 0)

||| Observes total baryon number of a candidate parton multiset via monomorphic reduction (Rule 03 §8).
public export
observePartonBagBaryonThirds : Multiset BoxInt ColoredParton -> BoxInt
observePartonBagBaryonThirds = foldMultiset (\p, w, acc => addBox (mulBox w (partonBaryonThirds p)) acc) (intToBoxInt 0)

||| Observes total mass tokens of a candidate parton multiset via monomorphic reduction (Rule 03 §8).
public export
observePartonBagMassTokens : Multiset BoxInt ColoredParton -> BoxInt
observePartonBagMassTokens = foldMultiset (\p, w, acc => addBox (mulBox w (partonMassTokens p)) acc) (intToBoxInt 0)

||| Constructively classifies a color-singlet cluster into a HadronToken by observing its conserved charges (Rule 03 §8).
||| All macroscopic hadron identities emerge strictly from the algebra of observables of Layer L-1.
public export
classifyHadronByObservables : (bThirds : BoxInt) -> (qThirds : BoxInt) -> Maybe HadronToken
classifyHadronByObservables (MkBoxInt 3) (MkBoxInt 3)    = Just ProtonToken       -- B = +1, Q = +1 (uud)
classifyHadronByObservables (MkBoxInt 3) (MkBoxInt 0)    = Just NeutronToken      -- B = +1, Q = 0  (udd)
classifyHadronByObservables (MkBoxInt 0) (MkBoxInt 3)    = Just PionPlusToken     -- B = 0,  Q = +1 (u d_bar)
classifyHadronByObservables (MkBoxInt 0) (MkBoxInt (-3)) = Just PionMinusToken    -- B = 0,  Q = -1 (d u_bar)
classifyHadronByObservables (MkBoxInt 0) (MkBoxInt 0)    = Just NeutralPionToken  -- B = 0,  Q = 0  (u u_bar / d d_bar)
classifyHadronByObservables _           _               = Nothing

||| Measures a candidate cluster and classifies its emergent HadronToken from L-1 observables (Rule 03 §8).
public export
condenseClusterByObservables : Multiset BoxInt ColoredParton -> Maybe HadronToken
condenseClusterByObservables cluster =
  let b = observePartonBagBaryonThirds cluster
      q = observePartonBagChargeThirds cluster
  in classifyHadronByObservables b q

clusterProtonRGD : Multiset BoxInt ColoredParton
clusterProtonRGD = AddM (QuarkParton QuarkU ColorRed) (intToBoxInt 1)
                  (AddM (QuarkParton QuarkU ColorGreen) (intToBoxInt 1)
                  (AddM (QuarkParton QuarkD ColorBlue) (intToBoxInt 1) ZeroM))

clusterProtonRDB : Multiset BoxInt ColoredParton
clusterProtonRDB = AddM (QuarkParton QuarkU ColorRed) (intToBoxInt 1)
                  (AddM (QuarkParton QuarkU ColorBlue) (intToBoxInt 1)
                  (AddM (QuarkParton QuarkD ColorGreen) (intToBoxInt 1) ZeroM))

clusterProtonGDB : Multiset BoxInt ColoredParton
clusterProtonGDB = AddM (QuarkParton QuarkU ColorGreen) (intToBoxInt 1)
                  (AddM (QuarkParton QuarkU ColorBlue) (intToBoxInt 1)
                  (AddM (QuarkParton QuarkD ColorRed) (intToBoxInt 1) ZeroM))

clusterNeutronRDD : Multiset BoxInt ColoredParton
clusterNeutronRDD = AddM (QuarkParton QuarkU ColorRed) (intToBoxInt 1)
                   (AddM (QuarkParton QuarkD ColorGreen) (intToBoxInt 1)
                   (AddM (QuarkParton QuarkD ColorBlue) (intToBoxInt 1) ZeroM))

clusterNeutronGDD : Multiset BoxInt ColoredParton
clusterNeutronGDD = AddM (QuarkParton QuarkU ColorGreen) (intToBoxInt 1)
                   (AddM (QuarkParton QuarkD ColorRed) (intToBoxInt 1)
                   (AddM (QuarkParton QuarkD ColorBlue) (intToBoxInt 1) ZeroM))

clusterNeutronBDD : Multiset BoxInt ColoredParton
clusterNeutronBDD = AddM (QuarkParton QuarkU ColorBlue) (intToBoxInt 1)
                   (AddM (QuarkParton QuarkD ColorRed) (intToBoxInt 1)
                   (AddM (QuarkParton QuarkD ColorGreen) (intToBoxInt 1) ZeroM))

clusterPionPlus : TripletColor -> Multiset BoxInt ColoredParton
clusterPionPlus ColorRed   = AddM (QuarkParton QuarkU ColorRed) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkD AntiRed) (intToBoxInt 1) ZeroM)
clusterPionPlus ColorGreen = AddM (QuarkParton QuarkU ColorGreen) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkD AntiGreen) (intToBoxInt 1) ZeroM)
clusterPionPlus ColorBlue  = AddM (QuarkParton QuarkU ColorBlue) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkD AntiBlue) (intToBoxInt 1) ZeroM)

clusterPionMinus : TripletColor -> Multiset BoxInt ColoredParton
clusterPionMinus ColorRed   = AddM (QuarkParton QuarkD ColorRed) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkU AntiRed) (intToBoxInt 1) ZeroM)
clusterPionMinus ColorGreen = AddM (QuarkParton QuarkD ColorGreen) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkU AntiGreen) (intToBoxInt 1) ZeroM)
clusterPionMinus ColorBlue  = AddM (QuarkParton QuarkD ColorBlue) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkU AntiBlue) (intToBoxInt 1) ZeroM)

clusterPionZero : TripletColor -> Multiset BoxInt ColoredParton
clusterPionZero ColorRed   = AddM (QuarkParton QuarkU ColorRed) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkU AntiRed) (intToBoxInt 1) ZeroM)
clusterPionZero ColorGreen = AddM (QuarkParton QuarkU ColorGreen) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkU AntiGreen) (intToBoxInt 1) ZeroM)
clusterPionZero ColorBlue  = AddM (QuarkParton QuarkU ColorBlue) (intToBoxInt 1) (AddM (AntiQuarkParton AntiQuarkU AntiBlue) (intToBoxInt 1) ZeroM)

||| Attempts to condense a color-singlet meson or baryon from current buffer state:
||| Derives the resulting HadronToken directly from Layer L-1 reduced observables (Rule 03 §8).
||| Returns (Just formedHadron, updatedBuffer) if a singlet forms, or (Nothing, buffer) if incomplete.
public export
tryCondenseSinglet : ColorCondensationState -> (Maybe HadronToken, ColorCondensationState)
tryCondenseSinglet (MkCondensationState (S ur) ug ub dr dg db ubr ubg ubb (S dbr) dbg dbb) =
  (condenseClusterByObservables (clusterPionPlus ColorRed), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) ub dr dg db ubr ubg ubb dbr (S dbg) dbb) =
  (condenseClusterByObservables (clusterPionPlus ColorGreen), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug (S ub) dr dg db ubr ubg ubb dbr dbg (S dbb)) =
  (condenseClusterByObservables (clusterPionPlus ColorBlue), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug ub (S dr) dg db (S ubr) ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables (clusterPionMinus ColorRed), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug ub dr (S dg) db ubr (S ubg) ubb dbr dbg dbb) =
  (condenseClusterByObservables (clusterPionMinus ColorGreen), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug ub dr dg (S db) ubr ubg (S ubb) dbr dbg dbb) =
  (condenseClusterByObservables (clusterPionMinus ColorBlue), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState (S ur) ug ub dr dg db (S ubr) ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables (clusterPionZero ColorRed), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) ub dr dg db ubr (S ubg) ubb dbr dbg dbb) =
  (condenseClusterByObservables (clusterPionZero ColorGreen), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug (S ub) dr dg db ubr ubg (S ubb) dbr dbg dbb) =
  (condenseClusterByObservables (clusterPionZero ColorBlue), MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
-- Proton: uud (R, G, B)
tryCondenseSinglet (MkCondensationState (S ur) (S ug) ub dr dg (S db) ubr ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables clusterProtonRGD, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState (S ur) ug (S ub) dr (S dg) db ubr ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables clusterProtonRDB, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) (S ub) (S dr) dg db ubr ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables clusterProtonGDB, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
-- Neutron: udd (R, G, B)
tryCondenseSinglet (MkCondensationState (S ur) ug ub dr (S dg) (S db) ubr ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables clusterNeutronRDD, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) ub (S dr) dg (S db) ubr ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables clusterNeutronGDD, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug (S ub) (S dr) (S dg) db ubr ubg ubb dbr dbg dbb) =
  (condenseClusterByObservables clusterNeutronBDD, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet st = (Nothing, st)

||| State transition step for the single-pass color-singlet condensation transducer.
public export
condensationStep : ColorCondensationState -> ColoredParton -> Step ColorCondensationState HadronToken
condensationStep st parton =
  let st' = ingestParton st parton
  in case tryCondenseSinglet st' of
       (Just hadron, nextSt) => Yield hadron nextSt
       (Nothing, nextSt)     => Skip nextSt

||| Deforested stream transducer condensing colored partons into color-singlet hadrons.
public export
hadronizationCondensationTransducer : StreamTransducer ColoredParton HadronToken
hadronizationCondensationTransducer = MkTransducer condensationStep initialCondensationState

||| Streams color-singlet condensation over a deforested stream of colored partons.
public export
streamHadronizationTransducer : FusedStream ColoredParton -> FusedStream HadronToken
streamHadronizationTransducer = transduceStream hadronizationCondensationTransducer

||| Evaluates hadronization condensation over Nat fuel producing a List.
|||
||| @deprecated Materializes stream into intermediate `List HadronToken` (violates Rule 04 §8).
||| Prefer `streamHadronizationToMultiset` or `hadronizePartonBag` (Rule 04 §12).
public export
runHadronizationTransducerNat : (fuel : Nat) -> FusedStream ColoredParton -> List HadronToken
runHadronizationTransducerNat fuel strm = runFueledStreamNat fuel (streamHadronizationTransducer strm)

||| Deforested multiset sink: Folds a stream of colored partons directly into a color-singlet
||| HadronToken multiset in O(1) auxiliary registers without intermediate List allocations (Rule 04 §12).
%spec fuel
public export
streamHadronizationToMultiset : (fuel : Nat) -> FusedStream ColoredParton -> Multiset BoxInt HadronToken
streamHadronizationToMultiset fuel strm =
  foldStreamNat fuel
    (\bag, h => insertItemBox h (intToBoxInt 1) bag)
    ZeroM
    (streamHadronizationTransducer strm)

||| End-to-end multiset hadronization: streams an algebraic multiset of colored partons
||| through the single-pass color-singlet condensation transducer directly into a HadronToken multiset.
%spec fuel
public export
hadronizePartonBag : (fuel : Nat) -> Multiset BoxInt ColoredParton -> Multiset BoxInt HadronToken
hadronizePartonBag fuel bag =
  streamHadronizationToMultiset fuel (mapStream element (streamTokens bag))

||| Deforested transducer folding partons into hadrons while tracking residual color buffer state (Rule 03 §8).
%spec fuel
public export
runCondensationWithResidual : (fuel : Nat) -> FusedStream ColoredParton -> (Multiset BoxInt HadronToken, ColorCondensationState)
runCondensationWithResidual fuel (MkStream {s} step seed) = loop fuel seed initialCondensationState ZeroM
  where
    loop : Nat -> s -> ColorCondensationState -> Multiset BoxInt HadronToken -> (Multiset BoxInt HadronToken, ColorCondensationState)
    loop 0 _ buf acc = (acc, buf)
    loop (S k) st buf acc = case step st of
      Done => (acc, buf)
      Skip st' => loop k st' buf acc
      Yield parton st' =>
        let buf' = ingestParton buf parton
        in case tryCondenseSinglet buf' of
             (Just hadron, nextBuf) => loop k st' nextBuf (insertItemBox hadron (intToBoxInt 1) acc)
             (Nothing, nextBuf)     => loop k st' nextBuf acc

||| Audits that a color-triplet proton feed (u_R + u_G + d_B) condenses into a ProtonToken.
public export
auditProtonCondensationProof : Bool
auditProtonCondensationProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , QuarkParton QuarkU ColorGreen
             , QuarkParton QuarkD ColorBlue
             ]
      result = runHadronizationTransducerNat 10 (stream feed)
  in result == [ProtonToken]

||| Audits that a color-triplet neutron feed (u_R + d_G + d_B) condenses into a NeutronToken.
public export
auditNeutronCondensationProof : Bool
auditNeutronCondensationProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , QuarkParton QuarkD ColorGreen
             , QuarkParton QuarkD ColorBlue
             ]
      result = runHadronizationTransducerNat 10 (stream feed)
  in result == [NeutronToken]

||| Audits that a meson pair feed (u_R + d_bar_R) condenses into a PionPlusToken.
public export
auditPionCondensationProof : Bool
auditPionCondensationProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , AntiQuarkParton AntiQuarkD AntiRed
             ]
      result = runHadronizationTransducerNat 10 (stream feed)
  in result == [PionPlusToken]

||| Audits that a color-triplet proton feed condenses into a ProtonToken multiset with neutral residual buffer.
public export
auditProtonCondensationMultisetProof : Bool
auditProtonCondensationMultisetProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , QuarkParton QuarkU ColorGreen
             , QuarkParton QuarkD ColorBlue
             ]
      (resultBag, residualBuf) = runCondensationWithResidual 10 (stream feed)
      expectedBag : Multiset BoxInt HadronToken
      expectedBag = insertItemBox ProtonToken (intToBoxInt 1) ZeroM
  in resultBag == expectedBag && isColorNeutralBuffer residualBuf == True

||| Audits that a color-triplet neutron feed condenses into a NeutronToken multiset with neutral residual buffer.
public export
auditNeutronCondensationMultisetProof : Bool
auditNeutronCondensationMultisetProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , QuarkParton QuarkD ColorGreen
             , QuarkParton QuarkD ColorBlue
             ]
      (resultBag, residualBuf) = runCondensationWithResidual 10 (stream feed)
      expectedBag : Multiset BoxInt HadronToken
      expectedBag = insertItemBox NeutronToken (intToBoxInt 1) ZeroM
  in resultBag == expectedBag && isColorNeutralBuffer residualBuf == True

||| Audits that a meson pair feed condenses into a PionPlusToken multiset with neutral residual buffer.
public export
auditPionCondensationMultisetProof : Bool
auditPionCondensationMultisetProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , AntiQuarkParton AntiQuarkD AntiRed
             ]
      (resultBag, residualBuf) = runCondensationWithResidual 10 (stream feed)
      expectedBag : Multiset BoxInt HadronToken
      expectedBag = insertItemBox PionPlusToken (intToBoxInt 1) ZeroM
  in resultBag == expectedBag && isColorNeutralBuffer residualBuf == True

||| Audits that a gluon parton in QGP decays and condenses into a NeutralPionToken multiset with neutral residual buffer.
public export
auditGluonCondensationMultisetProof : Bool
auditGluonCondensationMultisetProof =
  let feed = [ GluonParton GluonR ]
      (resultBag, residualBuf) = runCondensationWithResidual 10 (stream feed)
      expectedBag : Multiset BoxInt HadronToken
      expectedBag = insertItemBox NeutralPionToken (intToBoxInt 1) ZeroM
  in resultBag == expectedBag && isColorNeutralBuffer residualBuf == True

||| Comprehensive audit of the streaming color-singlet condensation engine across list and multiset carriers.
public export
auditColorSingletCondensationProof : Bool
auditColorSingletCondensationProof =
  auditProtonCondensationProof &&
  auditNeutronCondensationProof &&
  auditPionCondensationProof &&
  auditProtonCondensationMultisetProof &&
  auditNeutronCondensationMultisetProof &&
  auditPionCondensationMultisetProof &&
  auditGluonCondensationMultisetProof
