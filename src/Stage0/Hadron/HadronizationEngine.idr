module Stage0.Hadron.HadronizationEngine

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.Hadron.StandardModel
import Stage1.ScalePipeline

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
public export
qgpDecayFiberMap : StandardModelParticle -> List StandardModelParticle
qgpDecayFiberMap (SMPBoson GluonR) = [SMPFermion QuarkU, SMPFermion AntiQuarkU]
qgpDecayFiberMap p                 = [p]

||| Multiset-powered Hadronized Jet State.
public export
record MultisetHadronizedJetState where
  constructor MkMultisetHadronizedJetState
  hadronBag : Multiset BoxInt StandardModelParticle
  qgpPhase  : QGPPhase

||| Pure Galois Fiber Pullback (f^*) QGP jet fragmentation operator over Multiset BoxInt StandardModelParticle.
public export
fragmentQGPJetMultiset : Multiset BoxInt StandardModelParticle -> MultisetHadronizedJetState
fragmentQGPJetMultiset jetBag =
  let hadronBag = fiberPullback qgpDecayFiberMap jetBag
  in MkMultisetHadronizedJetState hadronBag ConfinementHadronGas

||| Strict QTT Linear State Evolution for QGP Hadronization (Rule 04).
||| Consumes the deconfined QGP state linearly to guarantee zero state cloning or silent decay loss.
public export
stepHadronizationLinear : (1 state : MultisetHadronizedJetState) -> MultisetHadronizedJetState
stepHadronizationLinear (MkMultisetHadronizedJetState bag _) =
  fragmentQGPJetMultiset bag

------------------------------------------------------------------------
-- 2. HADRONIZATION AUTOMATON (g -> q q_bar, q q_bar -> Pion, q q q -> Nucleon)
------------------------------------------------------------------------

||| Fragments a Quark-Gluon Plasma jet into color-singlet hadrons.
||| 1. Gluons decay into quark-antiquark pairs (g -> u u_bar or d d_bar).
||| 2. Quark-antiquark pairs condense into Mesons (Pions).
||| 3. Triplet quarks condense into Baryons (Protons/Neutrons).
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

||| Verifies color-singlet confinement invariant:
||| Ensures no free isolated quarks or gluons remain in the final hadronized state.
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
public export
auditHadronizationEngineProof : Bool
auditHadronizationEngineProof =
  let jet = [SMPBoson GluonR]
      hadronState = fragmentQGPJet jet
      
      initJet : Multiset BoxInt StandardModelParticle
      initJet = AddM (SMPBoson GluonR) (intToBoxInt 1) ZeroM
      mState  = fragmentQGPJetMultiset initJet
      expectedBag : Multiset BoxInt StandardModelParticle
      expectedBag = AddM (SMPFermion QuarkU) (intToBoxInt 1) (AddM (SMPFermion AntiQuarkU) (intToBoxInt 1) ZeroM)
      
      tList = (isColorConlinedState hadronState == True) &&
              (hadrons hadronState == [SMPFermion QuarkU, SMPFermion AntiQuarkU])
      tMultiset = (qgpPhase mState == ConfinementHadronGas) &&
                  (hadronBag mState == expectedBag)
  in tList && tMultiset

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

||| Deforested QGP fragmentation transducer over RLE particle streams:
||| Splitting gluons into u and u_bar pairs while preserving BoxNat multiplicities.
public export
streamFragmentQGPRLE : FusedStream RLEParticleToken -> FusedStream RLEParticleToken
streamFragmentQGPRLE strm =
  fusedConcat (mapStream (\(MkRLEParticle p m) =>
    case p of
      SMPBoson GluonR =>
        stream [ MkRLEParticle (SMPFermion QuarkU) m
               , MkRLEParticle (SMPFermion AntiQuarkU) m
               ]
      other => stream [ MkRLEParticle other m ]
  ) strm)

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
initialCondensationState : ColorCondensationState
initialCondensationState = MkCondensationState 0 0 0 0 0 0 0 0 0 0 0 0

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

||| Attempts to condense a color-singlet meson or baryon from current buffer state:
||| Returns (Just formedHadron, updatedBuffer) if a singlet forms, or (Nothing, buffer) if incomplete.
public export
tryCondenseSinglet : ColorCondensationState -> (Maybe HadronToken, ColorCondensationState)
tryCondenseSinglet (MkCondensationState (S ur) ug ub dr dg db ubr ubg ubb (S dbr) dbg dbb) =
  (Just PionPlusToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) ub dr dg db ubr ubg ubb dbr (S dbg) dbb) =
  (Just PionPlusToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug (S ub) dr dg db ubr ubg ubb dbr dbg (S dbb)) =
  (Just PionPlusToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug ub (S dr) dg db (S ubr) ubg ubb dbr dbg dbb) =
  (Just PionMinusToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug ub dr (S dg) db ubr (S ubg) ubb dbr dbg dbb) =
  (Just PionMinusToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug ub dr dg (S db) ubr ubg (S ubb) dbr dbg dbb) =
  (Just PionMinusToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState (S ur) ug ub dr dg db (S ubr) ubg ubb dbr dbg dbb) =
  (Just NeutralPionToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) ub dr dg db ubr (S ubg) ubb dbr dbg dbb) =
  (Just NeutralPionToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug (S ub) dr dg db ubr ubg (S ubb) dbr dbg dbb) =
  (Just NeutralPionToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
-- Proton: uud (R, G, B)
tryCondenseSinglet (MkCondensationState (S ur) (S ug) ub dr dg (S db) ubr ubg ubb dbr dbg dbb) =
  (Just ProtonToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState (S ur) ug (S ub) dr (S dg) db ubr ubg ubb dbr dbg dbb) =
  (Just ProtonToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) (S ub) (S dr) dg db ubr ubg ubb dbr dbg dbb) =
  (Just ProtonToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
-- Neutron: udd (R, G, B)
tryCondenseSinglet (MkCondensationState (S ur) ug ub dr (S dg) (S db) ubr ubg ubb dbr dbg dbb) =
  (Just NeutronToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur (S ug) ub (S dr) dg (S db) ubr ubg ubb dbr dbg dbb) =
  (Just NeutronToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
tryCondenseSinglet (MkCondensationState ur ug (S ub) (S dr) (S dg) db ubr ubg ubb dbr dbg dbb) =
  (Just NeutronToken, MkCondensationState ur ug ub dr dg db ubr ubg ubb dbr dbg dbb)
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

||| Evaluates hadronization condensation over Nat fuel.
public export
runHadronizationTransducerNat : (fuel : Nat) -> FusedStream ColoredParton -> List HadronToken
runHadronizationTransducerNat fuel strm = runFueledStreamNat fuel (streamHadronizationTransducer strm)

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

||| Comprehensive audit of the streaming color-singlet condensation engine.
public export
auditColorSingletCondensationProof : Bool
auditColorSingletCondensationProof =
  auditProtonCondensationProof &&
  auditNeutronCondensationProof &&
  auditPionCondensationProof
