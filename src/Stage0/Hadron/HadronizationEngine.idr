module Stage0.Hadron.HadronizationEngine

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage1.MultisetTree
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
  hadronBag : Carrier StandardModelParticle
  qgpPhase  : QGPPhase

||| QGP jet fragmentation operator over indexed `Carrier StandardModelParticle`.
public export
fragmentQGPJetMultiset : Carrier StandardModelParticle -> MultisetHadronizedJetState
fragmentQGPJetMultiset jetBag =
  let hadronBag : Carrier StandardModelParticle
      hadronBag = foldBoxTreeL
                    (\acc, (p, w) =>
                      if boxIsNonZero w
                        then foldl (\a, p' => a <+> singletonCarrier p' w) acc (qgpDecayFiberMap p)
                        else acc)
                    (the (Carrier StandardModelParticle) BoxLeaf)
                    jetBag
  in MkMultisetHadronizedJetState hadronBag ConfinementHadronGas

||| Deforested streaming QGP jet fragmentation directly consuming and producing Carriers (Rule 04 §12).
||| Eliminates all intermediate List allocations by streaming key-weights in O(1) auxiliary registers.
public export
fragmentQGPJetStreamDirect : Carrier StandardModelParticle -> MultisetHadronizedJetState
fragmentQGPJetStreamDirect jetBag =
  let hadronBag : Carrier StandardModelParticle
      hadronBag = foldStream
                    (\acc, (p, w) => acc <+> singletonCarrier p w)
                    (the (Carrier StandardModelParticle) BoxLeaf)
                    (streamFragmentQGPJetWeights (streamBoxMultisetTree jetBag))
  in MkMultisetHadronizedJetState hadronBag ConfinementHadronGas

||| Strict QTT Linear State Evolution for QGP Hadronization pairing state with hadron yields (Rule 04 §1).
public export
stepHadronizationLinearPair : (1 state : MultisetHadronizedJetState) ->
                              LinearStatePair MultisetHadronizedJetState (Carrier StandardModelParticle)
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
      
      initJet : Carrier StandardModelParticle
      initJet = singletonCarrier (SMPBoson GluonR) (intToBoxInt 1)
      mState  = fragmentQGPJetMultiset initJet
      mDirect = fragmentQGPJetStreamDirect initJet
      expectedBag : Carrier StandardModelParticle
      expectedBag = singletonCarrier (SMPFermion QuarkU) (intToBoxInt 1) <+> singletonCarrier (SMPFermion AntiQuarkU) (intToBoxInt 1)
      
      tList = (isColorConlinedState hadronState == True) &&
              (hadrons hadronState == [SMPFermion QuarkU, SMPFermion AntiQuarkU])
      tMultiset = (qgpPhase mState == ConfinementHadronGas) &&
                  (hadronBag mState == expectedBag)
      tDirect   = (qgpPhase mDirect == ConfinementHadronGas) &&
                  (hadronBag mDirect == expectedBag)
      strmJet = streamFragmentQGPJet (stream [SMPBoson GluonR])
      strmCount = foldStream (\acc, _ => S acc) 0 strmJet
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

||| Deforested stream mapping from indexed Carrier stream directly into RLEParticleTokens (Rule 04 §12).
public export
multisetToRLEStream : Carrier StandardModelParticle -> FusedStream RLEParticleToken
multisetToRLEStream bag =
  mapStream (\(p, w) => MkRLEParticle p (natToBoxNat (boxToNat (absBox w)))) (streamBoxMultisetTree bag)

||| Streams a hadron bag as a zero-allocation deforested RLE stream of (particle, BoxNat).
public export
streamHadronBagRLE : Carrier StandardModelParticle -> FusedStream RLEParticleToken
streamHadronBagRLE = multisetToRLEStream

||| Folds an RLE particle stream back into an indexed Carrier with explicit fuel bound (Rule 04 §12).
public export
streamRLEToMultiset : (fuel : Nat) -> FusedStream RLEParticleToken -> Carrier StandardModelParticle
streamRLEToMultiset fuel strm =
  foldStreamNat fuel
    (\bag, (MkRLEParticle p m) => bag <+> singletonCarrier p (natToBoxInt (boxNatToNat m)))
    BoxLeaf
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
Ord TripletColor where
  compare x y = compare (tag x) (tag y)
    where
      tag : TripletColor -> Nat
      tag ColorRed   = 0
      tag ColorGreen = 1
      tag ColorBlue  = 2

public export
DiscreteCoord TripletColor where

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
Ord AntiTripletColor where
  compare x y = compare (tag x) (tag y)
    where
      tag : AntiTripletColor -> Nat
      tag AntiRed   = 0
      tag AntiGreen = 1
      tag AntiBlue  = 2

public export
DiscreteCoord AntiTripletColor where

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

public export
Ord ColoredParton where
  compare (QuarkParton f1 c1)     (QuarkParton f2 c2)     = compare f1 f2 <+> compare c1 c2
  compare (QuarkParton _ _)       _                       = LT
  compare _                       (QuarkParton _ _)       = GT
  compare (AntiQuarkParton f1 c1) (AntiQuarkParton f2 c2) = compare f1 f2 <+> compare c1 c2
  compare (AntiQuarkParton _ _)   (GluonParton _)         = LT
  compare (GluonParton _)         (AntiQuarkParton _ _)   = GT
  compare (GluonParton g1)        (GluonParton g2)        = compare g1 g2

public export
DiscreteCoord ColoredParton where

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
observePartonBagChargeThirds : Carrier ColoredParton -> BoxInt
observePartonBagChargeThirds = foldBoxTreeL (\acc, (p, w) => addBox (mulBox w (partonChargeThirds p)) acc) (intToBoxInt 0)

||| Observes total baryon number of a candidate parton multiset via monomorphic reduction (Rule 03 §8).
public export
observePartonBagBaryonThirds : Carrier ColoredParton -> BoxInt
observePartonBagBaryonThirds = foldBoxTreeL (\acc, (p, w) => addBox (mulBox w (partonBaryonThirds p)) acc) (intToBoxInt 0)

||| Observes total mass tokens of a candidate parton multiset via monomorphic reduction (Rule 03 §8).
public export
observePartonBagMassTokens : Carrier ColoredParton -> BoxInt
observePartonBagMassTokens = foldBoxTreeL (\acc, (p, w) => addBox (mulBox w (partonMassTokens p)) acc) (intToBoxInt 0)

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
condenseClusterByObservables : Carrier ColoredParton -> Maybe HadronToken
condenseClusterByObservables cluster =
  let b = observePartonBagBaryonThirds cluster
      q = observePartonBagChargeThirds cluster
  in classifyHadronByObservables b q

clusterProtonRGD : Carrier ColoredParton
clusterProtonRGD = singletonCarrier (QuarkParton QuarkU ColorRed) (intToBoxInt 1)
               <+> singletonCarrier (QuarkParton QuarkU ColorGreen) (intToBoxInt 1)
               <+> singletonCarrier (QuarkParton QuarkD ColorBlue) (intToBoxInt 1)

clusterProtonRDB : Carrier ColoredParton
clusterProtonRDB = singletonCarrier (QuarkParton QuarkU ColorRed) (intToBoxInt 1)
               <+> singletonCarrier (QuarkParton QuarkU ColorBlue) (intToBoxInt 1)
               <+> singletonCarrier (QuarkParton QuarkD ColorGreen) (intToBoxInt 1)

clusterProtonGDB : Carrier ColoredParton
clusterProtonGDB = singletonCarrier (QuarkParton QuarkU ColorGreen) (intToBoxInt 1)
               <+> singletonCarrier (QuarkParton QuarkU ColorBlue) (intToBoxInt 1)
               <+> singletonCarrier (QuarkParton QuarkD ColorRed) (intToBoxInt 1)

clusterNeutronRDD : Carrier ColoredParton
clusterNeutronRDD = singletonCarrier (QuarkParton QuarkU ColorRed) (intToBoxInt 1)
                <+> singletonCarrier (QuarkParton QuarkD ColorGreen) (intToBoxInt 1)
                <+> singletonCarrier (QuarkParton QuarkD ColorBlue) (intToBoxInt 1)

clusterNeutronGDD : Carrier ColoredParton
clusterNeutronGDD = singletonCarrier (QuarkParton QuarkU ColorGreen) (intToBoxInt 1)
                <+> singletonCarrier (QuarkParton QuarkD ColorRed) (intToBoxInt 1)
                <+> singletonCarrier (QuarkParton QuarkD ColorBlue) (intToBoxInt 1)

clusterNeutronBDD : Carrier ColoredParton
clusterNeutronBDD = singletonCarrier (QuarkParton QuarkU ColorBlue) (intToBoxInt 1)
                <+> singletonCarrier (QuarkParton QuarkD ColorRed) (intToBoxInt 1)
                <+> singletonCarrier (QuarkParton QuarkD ColorGreen) (intToBoxInt 1)

clusterPionPlus : TripletColor -> Carrier ColoredParton
clusterPionPlus ColorRed   = singletonCarrier (QuarkParton QuarkU ColorRed) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkD AntiRed) (intToBoxInt 1)
clusterPionPlus ColorGreen = singletonCarrier (QuarkParton QuarkU ColorGreen) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkD AntiGreen) (intToBoxInt 1)
clusterPionPlus ColorBlue  = singletonCarrier (QuarkParton QuarkU ColorBlue) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkD AntiBlue) (intToBoxInt 1)

clusterPionMinus : TripletColor -> Carrier ColoredParton
clusterPionMinus ColorRed   = singletonCarrier (QuarkParton QuarkD ColorRed) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkU AntiRed) (intToBoxInt 1)
clusterPionMinus ColorGreen = singletonCarrier (QuarkParton QuarkD ColorGreen) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkU AntiGreen) (intToBoxInt 1)
clusterPionMinus ColorBlue  = singletonCarrier (QuarkParton QuarkD ColorBlue) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkU AntiBlue) (intToBoxInt 1)

clusterPionZero : TripletColor -> Carrier ColoredParton
clusterPionZero ColorRed   = singletonCarrier (QuarkParton QuarkU ColorRed) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkU AntiRed) (intToBoxInt 1)
clusterPionZero ColorGreen = singletonCarrier (QuarkParton QuarkU ColorGreen) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkU AntiGreen) (intToBoxInt 1)
clusterPionZero ColorBlue  = singletonCarrier (QuarkParton QuarkU ColorBlue) (intToBoxInt 1) <+> singletonCarrier (AntiQuarkParton AntiQuarkU AntiBlue) (intToBoxInt 1)

||| Structural positivity test on a colour-buffer count (Z => False, S _ => True).
public export
hasColorCount : Nat -> Bool
hasColorCount Z     = False
hasColorCount (S _) = True

||| Structural decrement of a colour-buffer count (only applied to counts proven positive by `hasColorCount`).
public export
decColorCount : Nat -> Nat
decColorCount Z     = Z
decColorCount (S k) = k

||| Attempts to condense a color-singlet meson or baryon from current buffer state:
||| Derives the resulting HadronToken directly from Layer L-1 reduced observables (Rule 03 §8).
||| Returns (Just formedHadron, updatedBuffer) if a singlet forms, or (Nothing, buffer) if incomplete.
|||
||| Implemented as a linear first-match guard chain over field projections rather than
||| 15 overlapping 12-ary constructor patterns: the latter forces the case-tree compiler
||| into a combinatorial split over all 12 Nat fields (multi-GB elaboration stall).
||| Priority order is preserved exactly: pi+ (R,G,B), pi- (R,G,B), pi0 (R,G,B),
||| proton (RGD, RDB, GDB), neutron (RDD, GDD, BDD).
public export
tryCondenseSinglet : ColorCondensationState -> (Maybe HadronToken, ColorCondensationState)
tryCondenseSinglet st =
  -- Pion+: u + d_bar
  if hasColorCount st.uR && hasColorCount st.dBarR then
    (condenseClusterByObservables (clusterPionPlus ColorRed), { uR $= decColorCount, dBarR $= decColorCount } st)
  else if hasColorCount st.uG && hasColorCount st.dBarG then
    (condenseClusterByObservables (clusterPionPlus ColorGreen), { uG $= decColorCount, dBarG $= decColorCount } st)
  else if hasColorCount st.uB && hasColorCount st.dBarB then
    (condenseClusterByObservables (clusterPionPlus ColorBlue), { uB $= decColorCount, dBarB $= decColorCount } st)
  -- Pion-: d + u_bar
  else if hasColorCount st.dR && hasColorCount st.uBarR then
    (condenseClusterByObservables (clusterPionMinus ColorRed), { dR $= decColorCount, uBarR $= decColorCount } st)
  else if hasColorCount st.dG && hasColorCount st.uBarG then
    (condenseClusterByObservables (clusterPionMinus ColorGreen), { dG $= decColorCount, uBarG $= decColorCount } st)
  else if hasColorCount st.dB && hasColorCount st.uBarB then
    (condenseClusterByObservables (clusterPionMinus ColorBlue), { dB $= decColorCount, uBarB $= decColorCount } st)
  -- Pion0: u + u_bar
  else if hasColorCount st.uR && hasColorCount st.uBarR then
    (condenseClusterByObservables (clusterPionZero ColorRed), { uR $= decColorCount, uBarR $= decColorCount } st)
  else if hasColorCount st.uG && hasColorCount st.uBarG then
    (condenseClusterByObservables (clusterPionZero ColorGreen), { uG $= decColorCount, uBarG $= decColorCount } st)
  else if hasColorCount st.uB && hasColorCount st.uBarB then
    (condenseClusterByObservables (clusterPionZero ColorBlue), { uB $= decColorCount, uBarB $= decColorCount } st)
  -- Proton: uud (R, G, B)
  else if hasColorCount st.uR && hasColorCount st.uG && hasColorCount st.dB then
    (condenseClusterByObservables clusterProtonRGD, { uR $= decColorCount, uG $= decColorCount, dB $= decColorCount } st)
  else if hasColorCount st.uR && hasColorCount st.uB && hasColorCount st.dG then
    (condenseClusterByObservables clusterProtonRDB, { uR $= decColorCount, uB $= decColorCount, dG $= decColorCount } st)
  else if hasColorCount st.uG && hasColorCount st.uB && hasColorCount st.dR then
    (condenseClusterByObservables clusterProtonGDB, { uG $= decColorCount, uB $= decColorCount, dR $= decColorCount } st)
  -- Neutron: udd (R, G, B)
  else if hasColorCount st.uR && hasColorCount st.dG && hasColorCount st.dB then
    (condenseClusterByObservables clusterNeutronRDD, { uR $= decColorCount, dG $= decColorCount, dB $= decColorCount } st)
  else if hasColorCount st.uG && hasColorCount st.dR && hasColorCount st.dB then
    (condenseClusterByObservables clusterNeutronGDD, { uG $= decColorCount, dR $= decColorCount, dB $= decColorCount } st)
  else if hasColorCount st.uB && hasColorCount st.dR && hasColorCount st.dG then
    (condenseClusterByObservables clusterNeutronBDD, { uB $= decColorCount, dR $= decColorCount, dG $= decColorCount } st)
  else (Nothing, st)

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
||| HadronToken Carrier in O(1) auxiliary registers without intermediate List allocations (Rule 04 §12).
public export
streamHadronizationToMultiset : (fuel : Nat) -> FusedStream ColoredParton -> Carrier HadronToken
streamHadronizationToMultiset fuel strm =
  foldStreamNat fuel
    (\bag, h => bag <+> singletonCarrier h (intToBoxInt 1))
    BoxLeaf
    (streamHadronizationTransducer strm)

||| End-to-end multiset hadronization: streams an indexed Carrier of colored partons
||| through the single-pass color-singlet condensation transducer directly into a HadronToken Carrier.
public export
hadronizePartonBag : (fuel : Nat) -> Carrier ColoredParton -> Carrier HadronToken
hadronizePartonBag fuel bag =
  streamHadronizationToMultiset fuel
    (flatMapStream
      (\(p, w) =>
        let n = if w > intToBoxInt 0 then boxToNat w else 0
        in unfoldStream (\k => case k of Z => Done; S k' => Yield p k') n)
      (streamBoxMultisetTree bag))

||| Deforested transducer folding partons into hadrons while tracking residual color buffer state (Rule 03 §8).
public export
runCondensationWithResidual : (fuel : Nat) -> FusedStream ColoredParton -> (Carrier HadronToken, ColorCondensationState)
runCondensationWithResidual fuel (MkStream {s} step seed) = loop fuel seed initialCondensationState BoxLeaf
  where
    loop : Nat -> s -> ColorCondensationState -> Carrier HadronToken -> (Carrier HadronToken, ColorCondensationState)
    loop 0 _ buf acc = (acc, buf)
    loop (S k) st buf acc = case step st of
      Done => (acc, buf)
      Skip st' => loop k st' buf acc
      Yield parton st' =>
        let buf' = ingestParton buf parton
        in case tryCondenseSinglet buf' of
             (Just hadron, nextBuf) => loop k st' nextBuf (acc <+> singletonCarrier hadron (intToBoxInt 1))
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
      expectedBag : Carrier HadronToken
      expectedBag = singletonCarrier ProtonToken (intToBoxInt 1)
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
      expectedBag : Carrier HadronToken
      expectedBag = singletonCarrier NeutronToken (intToBoxInt 1)
  in resultBag == expectedBag && isColorNeutralBuffer residualBuf == True

||| Audits that a meson pair feed condenses into a PionPlusToken multiset with neutral residual buffer.
public export
auditPionCondensationMultisetProof : Bool
auditPionCondensationMultisetProof =
  let feed = [ QuarkParton QuarkU ColorRed
             , AntiQuarkParton AntiQuarkD AntiRed
             ]
      (resultBag, residualBuf) = runCondensationWithResidual 10 (stream feed)
      expectedBag : Carrier HadronToken
      expectedBag = singletonCarrier PionPlusToken (intToBoxInt 1)
  in resultBag == expectedBag && isColorNeutralBuffer residualBuf == True

||| Audits that a gluon parton in QGP decays and condenses into a NeutralPionToken multiset with neutral residual buffer.
public export
auditGluonCondensationMultisetProof : Bool
auditGluonCondensationMultisetProof =
  let feed = [ GluonParton GluonR ]
      (resultBag, residualBuf) = runCondensationWithResidual 10 (stream feed)
      expectedBag : Carrier HadronToken
      expectedBag = singletonCarrier NeutralPionToken (intToBoxInt 1)
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
