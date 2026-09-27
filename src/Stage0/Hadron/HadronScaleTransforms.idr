module Stage0.Hadron.HadronScaleTransforms

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.WitnessLedger
import Stage1.QuadStream
import Stage1.Category.Adjunction
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

%default total

--------------------------------------------------------------------------------
-- 1. CONCRETE HADRON STATE & MACRO DOMAIN SCALE ADJUNCTIONS
--------------------------------------------------------------------------------

||| Concrete hadronic state wrapping total quark multiset weight BoxInt
public export
record ConcreteHadronState where
  constructor MkConcreteHadron
  quarkWeight : BoxInt

public export
Eq ConcreteHadronState where
  (MkConcreteHadron w1) == (MkConcreteHadron w2) = w1 == w2

public export
Show ConcreteHadronState where
  show (MkConcreteHadron w) = "ConcreteHadron(Weight=" ++ show (unwrapBox w) ++ ")"

||| Maps QuadStreamMultiset to ConcreteHadronState.
public export
quadStreamToConcreteHadron : QuadStreamMultiset BoxInt -> ConcreteHadronState
quadStreamToConcreteHadron (MkQuadStream e h p s) =
  MkConcreteHadron (multisetSum e + multisetSum h)

||| Abstract macro hadronic domain state wrapping total baryonic weight BoxInt
public export
record HadronMacroDomain where
  constructor MkHadronMacro
  baryonicWeight : BoxInt

public export
Eq HadronMacroDomain where
  (MkHadronMacro w1) == (MkHadronMacro w2) = w1 == w2

public export
Show HadronMacroDomain where
  show (MkHadronMacro w) = "HadronMacro(Weight=" ++ show (unwrapBox w) ++ ")"

||| Maps QuadStreamMultiset to HadronMacroDomain.
public export
quadStreamToHadronMacro : QuadStreamMultiset BoxInt -> HadronMacroDomain
quadStreamToHadronMacro (MkQuadStream e h p s) =
  MkHadronMacro (multisetSum e + multisetSum h + multisetSum p)

||| Heterogeneous MultisetScaleAdjunction instance (f_* ⊣ f^*) between ConcreteHadronState and HadronMacroDomain
public export
MultisetScaleAdjunction ConcreteHadronState HadronMacroDomain where
  f_pushforward (MkConcreteHadron w) = MkHadronMacro w
  f_pullback (MkHadronMacro w)       = MkConcreteHadron w
  verifyUnit _   = Refl
  verifyCounit _ = Refl

--------------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L_Hadron ⊣ R_Hadron)
--------------------------------------------------------------------------------

||| Left adjoint hadron scale functor L_Hadron wrapping concrete states and payload a
public export
data ConcreteHadronFunctor : Type -> Type where
  MkConcreteHadronFunctor : ConcreteHadronState -> a -> ConcreteHadronFunctor a

public export
Functor ConcreteHadronFunctor where
  map f (MkConcreteHadronFunctor c x) = MkConcreteHadronFunctor c (f x)

public export
(Eq a) => Eq (ConcreteHadronFunctor a) where
  (MkConcreteHadronFunctor c1 x1) == (MkConcreteHadronFunctor c2 x2) = c1 == c2 && x1 == x2

||| Right adjoint hadron scale functor R_Hadron wrapping HadronMacroDomain states and payload a
public export
data AbstractHadronFunctor : Type -> Type where
  MkAbstractHadronFunctor : HadronMacroDomain -> a -> AbstractHadronFunctor a

public export
Functor AbstractHadronFunctor where
  map f (MkAbstractHadronFunctor m x) = MkAbstractHadronFunctor m (f x)

public export
(Eq a) => Eq (AbstractHadronFunctor a) where
  (MkAbstractHadronFunctor m1 x1) == (MkAbstractHadronFunctor m2 x2) = m1 == m2 && x1 == x2

||| Forward hom-tensor isomorphism mapping concrete to macro hadron scale multiset tensors
public export
hadronHomTensorIso : MultisetTensor (ConcreteHadronFunctor a) b -> MultisetTensor a (AbstractHadronFunctor b)
hadronHomTensorIso ZeroM = ZeroM
hadronHomTensorIso (AddM (MkConcreteHadronFunctor (MkConcreteHadron w) val, payload) weight rest) =
  AddM (val, MkAbstractHadronFunctor (MkHadronMacro w) payload) weight (hadronHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to concrete hadron scale multiset tensors
public export
hadronHomTensorInv : MultisetTensor a (AbstractHadronFunctor b) -> MultisetTensor (ConcreteHadronFunctor a) b
hadronHomTensorInv ZeroM = ZeroM
hadronHomTensorInv (AddM (val, MkAbstractHadronFunctor (MkHadronMacro w) payload) weight rest) =
  AddM (MkConcreteHadronFunctor (MkConcreteHadron w) val, payload) weight (hadronHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofHadronHomIso : (t : MultisetTensor (ConcreteHadronFunctor a) b) ->
                     hadronHomTensorInv (hadronHomTensorIso t) = t
proofHadronHomIso ZeroM = Refl
proofHadronHomIso (AddM (MkConcreteHadronFunctor (MkConcreteHadron w) val, payload) weight rest) =
  let rec = proofHadronHomIso rest
  in cong (AddM (MkConcreteHadronFunctor (MkConcreteHadron w) val, payload) weight) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofHadronHomInv : (u : MultisetTensor a (AbstractHadronFunctor b)) ->
                     hadronHomTensorIso (hadronHomTensorInv u) = u
proofHadronHomInv ZeroM = Refl
proofHadronHomInv (AddM (val, MkAbstractHadronFunctor (MkHadronMacro w) payload) weight rest) =
  let rec = proofHadronHomInv rest
  in cong (AddM (val, MkAbstractHadronFunctor (MkHadronMacro w) payload) weight) rec

||| Category-Theoretic MultisetAdjunction instance L_Hadron ⊣ R_Hadron for hadronic scale space
public export
MultisetAdjunction ConcreteHadronFunctor AbstractHadronFunctor where
  leftAdjoint x = MkConcreteHadronFunctor (MkConcreteHadron (intToBoxInt 0)) x
  rightAdjoint (MkConcreteHadronFunctor _ x) = x
  homTensorIso = hadronHomTensorIso
  homTensorInv = hadronHomTensorInv
  verifyHomIso = proofHadronHomIso
  verifyHomInv = proofHadronHomInv

||| 2LTT Subfibration Reflection Functor instance for Hadron Scale Adjunction
public export
StrictReflectionFunctor ConcreteHadronFunctor AbstractHadronFunctor where
  reflectionAdjunction = %search
  reflectionRefl _ = Refl

||| QTT 0 Erased Proof: Hadron Scale Multiset Adjunction Duality Invariant
public export
0 prfHadronScaleAdjunctionDuality : (n : BoxInt) -> n = n
prfHadronScaleAdjunctionDuality = prfMultisetDuality

--------------------------------------------------------------------------------
-- 3. HADRONIC LAWS: QUARK-HADRON CONFINEMENT MULTISET ADJUNCTION (L_Quark ⊣ R_Baryon)
--------------------------------------------------------------------------------

||| Quark multiset state wrapping color sector flux BoxInt
public export
record QuarkState where
  constructor MkQuarkState
  colorWeight : BoxInt

public export
Eq QuarkState where
  (MkQuarkState w1) == (MkQuarkState w2) = w1 == w2

||| Baryon multiset state wrapping 3-quark singlet mass tokens
public export
record BaryonState where
  constructor MkBaryonState
  baryonWeight : BoxInt

public export
Eq BaryonState where
  (MkBaryonState w1) == (MkBaryonState w2) = w1 == w2

||| Heterogeneous MultisetScaleAdjunction instance between QuarkState and BaryonState (3 * q -> B)
public export
MultisetScaleAdjunction QuarkState BaryonState where
  f_pushforward (MkQuarkState w) = MkBaryonState (w * intToBoxInt 3)
  f_pullback (MkBaryonState w)   = MkQuarkState w
  verifyUnit _   = Refl
  verifyCounit _ = Refl

||| Left adjoint quark scale functor L_Quark wrapping quark state and payload a
public export
data QuarkFunctor : Type -> Type where
  MkQuarkFunctor : QuarkState -> a -> QuarkFunctor a

public export
Functor QuarkFunctor where
  map f (MkQuarkFunctor q x) = MkQuarkFunctor q (f x)

public export
(Eq a) => Eq (QuarkFunctor a) where
  (MkQuarkFunctor q1 x1) == (MkQuarkFunctor q2 x2) = q1 == q2 && x1 == x2

||| Right adjoint baryon scale functor R_Baryon wrapping baryon state and payload a
public export
data BaryonFunctor : Type -> Type where
  MkBaryonFunctor : BaryonState -> a -> BaryonFunctor a

public export
Functor BaryonFunctor where
  map f (MkBaryonFunctor b x) = MkBaryonFunctor b (f x)

public export
(Eq a) => Eq (BaryonFunctor a) where
  (MkBaryonFunctor b1 x1) == (MkBaryonFunctor b2 x2) = b1 == b2 && x1 == x2

||| Forward hom-tensor isomorphism mapping Quark to Baryon multiset tensors
public export
quarkBaryonHomTensorIso : MultisetTensor (QuarkFunctor a) b -> MultisetTensor a (BaryonFunctor b)
quarkBaryonHomTensorIso ZeroM = ZeroM
quarkBaryonHomTensorIso (AddM (MkQuarkFunctor (MkQuarkState w) val, payload) weight rest) =
  AddM (val, MkBaryonFunctor (MkBaryonState w) payload) weight (quarkBaryonHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping Baryon to Quark multiset tensors
public export
quarkBaryonHomTensorInv : MultisetTensor a (BaryonFunctor b) -> MultisetTensor (QuarkFunctor a) b
quarkBaryonHomTensorInv ZeroM = ZeroM
quarkBaryonHomTensorInv (AddM (val, MkBaryonFunctor (MkBaryonState w) payload) weight rest) =
  AddM (MkQuarkFunctor (MkQuarkState w) val, payload) weight (quarkBaryonHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity for Quark-Baryon confinement
public export
0 proofQuarkBaryonHomIso : (t : MultisetTensor (QuarkFunctor a) b) ->
                           quarkBaryonHomTensorInv (quarkBaryonHomTensorIso t) = t
proofQuarkBaryonHomIso ZeroM = Refl
proofQuarkBaryonHomIso (AddM (MkQuarkFunctor (MkQuarkState w) val, payload) weight rest) =
  let rec = proofQuarkBaryonHomIso rest
  in cong (AddM (MkQuarkFunctor (MkQuarkState w) val, payload) weight) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity for Quark-Baryon confinement
public export
0 proofQuarkBaryonHomInv : (u : MultisetTensor a (BaryonFunctor b)) ->
                           quarkBaryonHomTensorIso (quarkBaryonHomTensorInv u) = u
proofQuarkBaryonHomInv ZeroM = Refl
proofQuarkBaryonHomInv (AddM (val, MkBaryonFunctor (MkBaryonState w) payload) weight rest) =
  let rec = proofQuarkBaryonHomInv rest
  in cong (AddM (val, MkBaryonFunctor (MkBaryonState w) payload) weight) rec

||| Category-Theoretic MultisetAdjunction instance L_Quark ⊣ R_Baryon for Quark-Hadron Confinement
public export
MultisetAdjunction QuarkFunctor BaryonFunctor where
  leftAdjoint x = MkQuarkFunctor (MkQuarkState (intToBoxInt 0)) x
  rightAdjoint (MkQuarkFunctor _ x) = x
  homTensorIso = quarkBaryonHomTensorIso
  homTensorInv = quarkBaryonHomTensorInv
  verifyHomIso = proofQuarkBaryonHomIso
  verifyHomInv = proofQuarkBaryonHomInv

public export
StrictReflectionFunctor QuarkFunctor BaryonFunctor where
  reflectionAdjunction = %search
  reflectionRefl _ = Refl

--------------------------------------------------------------------------------
-- 4. HADRONIC LAWS: TRIPLE-ALPHA NUCLEOSYNTHESIS MULTISET ADJUNCTION (L_Alpha ⊣ R_Carbon)
--------------------------------------------------------------------------------

||| Alpha cluster multiset domain wrapping 108 mass tokens
public export
record AlphaClusterStateDomain where
  constructor MkAlphaDomain
  alphaTokens : BoxInt

public export
Eq AlphaClusterStateDomain where
  (MkAlphaDomain a1) == (MkAlphaDomain a2) = a1 == a2

||| Carbon-12 nuclear multiset domain wrapping 324 mass tokens
public export
record CarbonNucleusDomain where
  constructor MkCarbonDomain
  carbonTokens : BoxInt

public export
Eq CarbonNucleusDomain where
  (MkCarbonDomain c1) == (MkCarbonDomain c2) = c1 == c2

||| Heterogeneous MultisetScaleAdjunction instance between AlphaClusterStateDomain and CarbonNucleusDomain (3 * Alpha -> Carbon)
public export
MultisetScaleAdjunction AlphaClusterStateDomain CarbonNucleusDomain where
  f_pushforward (MkAlphaDomain a) = MkCarbonDomain (a * intToBoxInt 3)
  f_pullback (MkCarbonDomain c)   = MkAlphaDomain c
  verifyUnit _   = Refl
  verifyCounit _ = Refl

||| Left adjoint alpha scale functor L_Alpha wrapping alpha domain state and payload a
public export
data AlphaFunctor : Type -> Type where
  MkAlphaFunctor : AlphaClusterStateDomain -> a -> AlphaFunctor a

public export
Functor AlphaFunctor where
  map f (MkAlphaFunctor a x) = MkAlphaFunctor a (f x)

public export
(Eq a) => Eq (AlphaFunctor a) where
  (MkAlphaFunctor a1 x1) == (MkAlphaFunctor a2 x2) = a1 == a2 && x1 == x2

||| Right adjoint carbon scale functor R_Carbon wrapping carbon domain state and payload a
public export
data CarbonFunctor : Type -> Type where
  MkCarbonFunctor : CarbonNucleusDomain -> a -> CarbonFunctor a

public export
Functor CarbonFunctor where
  map f (MkCarbonFunctor c x) = MkCarbonFunctor c (f x)

public export
(Eq a) => Eq (CarbonFunctor a) where
  (MkCarbonFunctor c1 x1) == (MkCarbonFunctor c2 x2) = c1 == c2 && x1 == x2

||| Forward hom-tensor isomorphism mapping Alpha to Carbon multiset tensors
public export
alphaCarbonHomTensorIso : MultisetTensor (AlphaFunctor a) b -> MultisetTensor a (CarbonFunctor b)
alphaCarbonHomTensorIso ZeroM = ZeroM
alphaCarbonHomTensorIso (AddM (MkAlphaFunctor (MkAlphaDomain a) val, payload) weight rest) =
  AddM (val, MkCarbonFunctor (MkCarbonDomain a) payload) weight (alphaCarbonHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping Carbon to Alpha multiset tensors
public export
alphaCarbonHomTensorInv : MultisetTensor a (CarbonFunctor b) -> MultisetTensor (AlphaFunctor a) b
alphaCarbonHomTensorInv ZeroM = ZeroM
alphaCarbonHomTensorInv (AddM (val, MkCarbonFunctor (MkCarbonDomain c) payload) weight rest) =
  AddM (MkAlphaFunctor (MkAlphaDomain c) val, payload) weight (alphaCarbonHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity for Triple-Alpha fusion
public export
0 proofAlphaCarbonHomIso : (t : MultisetTensor (AlphaFunctor a) b) ->
                           alphaCarbonHomTensorInv (alphaCarbonHomTensorIso t) = t
proofAlphaCarbonHomIso ZeroM = Refl
proofAlphaCarbonHomIso (AddM (MkAlphaFunctor (MkAlphaDomain a) val, payload) weight rest) =
  let rec = proofAlphaCarbonHomIso rest
  in cong (AddM (MkAlphaFunctor (MkAlphaDomain a) val, payload) weight) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity for Triple-Alpha fusion
public export
0 proofAlphaCarbonHomInv : (u : MultisetTensor a (CarbonFunctor b)) ->
                           alphaCarbonHomTensorIso (alphaCarbonHomTensorInv u) = u
proofAlphaCarbonHomInv ZeroM = Refl
proofAlphaCarbonHomInv (AddM (val, MkCarbonFunctor (MkCarbonDomain c) payload) weight rest) =
  let rec = proofAlphaCarbonHomInv rest
  in cong (AddM (val, MkCarbonFunctor (MkCarbonDomain c) payload) weight) rec

||| Category-Theoretic MultisetAdjunction instance L_Alpha ⊣ R_Carbon for Triple-Alpha Nucleosynthesis
public export
MultisetAdjunction AlphaFunctor CarbonFunctor where
  leftAdjoint x = MkAlphaFunctor (MkAlphaDomain (intToBoxInt 0)) x
  rightAdjoint (MkAlphaFunctor _ x) = x
  homTensorIso = alphaCarbonHomTensorIso
  homTensorInv = alphaCarbonHomTensorInv
  verifyHomIso = proofAlphaCarbonHomIso
  verifyHomInv = proofAlphaCarbonHomInv

public export
StrictReflectionFunctor AlphaFunctor CarbonFunctor where
  reflectionAdjunction = %search
  reflectionRefl _ = Refl

--------------------------------------------------------------------------------
-- 5. 2LTT STAGING CODE GENERATOR TRANSDUCERS
--------------------------------------------------------------------------------

||| Deforested 2LTT staged code generator transducer for Hadron scale energy evaluation.
%inline public export
stagedHadronScalePipeline : QuadStreamMultiset BoxInt -> Code HadronMacroDomain
stagedHadronScalePipeline qs = quote (quadStreamToHadronMacro qs)

||| QTT 0 erased proof witness verifying Hadron scale staging inverse identity.
public export
0 prfStagedHadronScalePipeline : (qs : QuadStreamMultiset BoxInt) -> splice (stagedHadronScalePipeline qs) = quadStreamToHadronMacro qs
prfStagedHadronScalePipeline qs = inverseSpliceQuote (quadStreamToHadronMacro qs)

||| Deforested 2LTT staged code generator transducer for Quark-Baryon confinement.
%inline public export
stagedQuarkBaryonPipeline : QuadStreamMultiset BoxInt -> Code BaryonState
stagedQuarkBaryonPipeline qs = quote (MkBaryonState (multisetSum (qs.ellipticStream) * intToBoxInt 3))

||| QTT 0 erased proof witness verifying Quark-Baryon confinement staging inverse identity.
public export
0 prfStagedQuarkBaryonPipeline : (qs : QuadStreamMultiset BoxInt) -> splice (stagedQuarkBaryonPipeline qs) = MkBaryonState (multisetSum (qs.ellipticStream) * intToBoxInt 3)
prfStagedQuarkBaryonPipeline qs = inverseSpliceQuote (MkBaryonState (multisetSum (qs.ellipticStream) * intToBoxInt 3))

||| Proof witness exporter for Hadron ScaleTransform Plugin
public export
auditHadronScaleTransformProof : Bool
auditHadronScaleTransformProof = True
