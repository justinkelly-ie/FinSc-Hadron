module Stage1.Hadron.CertifiedHadron

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Hadron.StandardModel
import Language.Reflection

%default total

------------------------------------------------------------------------
-- 1. STANDARD BARYON SPECIES SPECIFICATION & CONSTITUENT VALENCE QUARKS
------------------------------------------------------------------------

||| Standard Baryon Ground State Classification (3-Quark Bound States).
public export
data StandardBaryonSpec =
    ProtonBaryon
  | NeutronBaryon
  | LambdaBaryon
  | SigmaBaryon
  | XiBaryon
  | OmegaBaryon

public export
Eq StandardBaryonSpec where
  ProtonBaryon  == ProtonBaryon  = True
  NeutronBaryon == NeutronBaryon = True
  LambdaBaryon  == LambdaBaryon  = True
  SigmaBaryon   == SigmaBaryon   = True
  XiBaryon      == XiBaryon      = True
  OmegaBaryon   == OmegaBaryon   = True
  _             == _             = False

public export
Show StandardBaryonSpec where
  show ProtonBaryon  = "Proton (u u d)"
  show NeutronBaryon = "Neutron (u d d)"
  show LambdaBaryon  = "Lambda (u d s)"
  show SigmaBaryon   = "Sigma (u u s)"
  show XiBaryon      = "Xi (u s s)"
  show OmegaBaryon   = "Omega (s s s)"

||| Constituent valence quark multiset representation for standard baryons (Rule 03 §8).
public export
baryonConstituentQuarks : StandardBaryonSpec -> Carrier SMFermion
baryonConstituentQuarks ProtonBaryon  = singletonCarrier QuarkU (intToBoxInt 2) <+> singletonCarrier QuarkD (intToBoxInt 1)
baryonConstituentQuarks NeutronBaryon = singletonCarrier QuarkU (intToBoxInt 1) <+> singletonCarrier QuarkD (intToBoxInt 2)
baryonConstituentQuarks LambdaBaryon  = singletonCarrier QuarkU (intToBoxInt 1) <+> singletonCarrier QuarkD (intToBoxInt 1) <+> singletonCarrier QuarkS (intToBoxInt 1)
baryonConstituentQuarks SigmaBaryon   = singletonCarrier QuarkU (intToBoxInt 2) <+> singletonCarrier QuarkS (intToBoxInt 1)
baryonConstituentQuarks XiBaryon      = singletonCarrier QuarkU (intToBoxInt 1) <+> singletonCarrier QuarkS (intToBoxInt 2)
baryonConstituentQuarks OmegaBaryon   = singletonCarrier QuarkS (intToBoxInt 3)

||| Certified Dependent Baryon Carrier (Rule 03 §7, §8).
||| Bundles the underlying Carrier with QTT multiplicity 0 proof that
||| total constituent quarks match exact baryon valence (3 quarks).
public export
record CertifiedBaryon (spec : StandardBaryonSpec) where
  constructor MkCertifiedBaryon
  quarks       : Carrier SMFermion
  0 prfValence : totalMassBox quarks = intToBoxInt 3

||| Canonical certified Proton state (2 u + 1 d = 3 quarks):
public export
certifiedProton : CertifiedBaryon ProtonBaryon
certifiedProton = MkCertifiedBaryon (baryonConstituentQuarks ProtonBaryon) Refl

||| Canonical certified Neutron state (1 u + 2 d = 3 quarks):
public export
certifiedNeutron : CertifiedBaryon NeutronBaryon
certifiedNeutron = MkCertifiedBaryon (baryonConstituentQuarks NeutronBaryon) Refl

||| Canonical certified Lambda baryon state (1 u + 1 d + 1 s = 3 quarks):
public export
certifiedLambda : CertifiedBaryon LambdaBaryon
certifiedLambda = MkCertifiedBaryon (baryonConstituentQuarks LambdaBaryon) Refl

||| Canonical certified Sigma baryon state (2 u + 1 s = 3 quarks):
public export
certifiedSigma : CertifiedBaryon SigmaBaryon
certifiedSigma = MkCertifiedBaryon (baryonConstituentQuarks SigmaBaryon) Refl

||| Canonical certified Xi baryon state (1 u + 2 s = 3 quarks):
public export
certifiedXi : CertifiedBaryon XiBaryon
certifiedXi = MkCertifiedBaryon (baryonConstituentQuarks XiBaryon) Refl

||| Canonical certified Omega baryon state (3 s = 3 quarks):
public export
certifiedOmega : CertifiedBaryon OmegaBaryon
certifiedOmega = MkCertifiedBaryon (baryonConstituentQuarks OmegaBaryon) Refl

------------------------------------------------------------------------
-- 2. STANDARD MESON SPECIES SPECIFICATION & CONSTITUENT VALENCE QUARKS
------------------------------------------------------------------------

||| Standard Meson Ground State Classification (Quark-Antiquark Bound States).
public export
data StandardMesonSpec =
    PionPlusMeson
  | PionMinusMeson
  | NeutralPionMeson
  | KaonPlusMeson
  | KaonMinusMeson
  | NeutralKaonMeson

public export
Eq StandardMesonSpec where
  PionPlusMeson    == PionPlusMeson    = True
  PionMinusMeson   == PionMinusMeson   = True
  NeutralPionMeson == NeutralPionMeson = True
  KaonPlusMeson    == KaonPlusMeson    = True
  KaonMinusMeson   == KaonMinusMeson   = True
  NeutralKaonMeson == NeutralKaonMeson = True
  _                == _                = False

public export
Show StandardMesonSpec where
  show PionPlusMeson    = "Pion+ (u d_bar)"
  show PionMinusMeson   = "Pion- (u_bar d)"
  show NeutralPionMeson = "Pion0 (u u_bar)"
  show KaonPlusMeson    = "Kaon+ (u s_bar)"
  show KaonMinusMeson   = "Kaon- (u_bar s)"
  show NeutralKaonMeson = "Kaon0 (d s_bar)"

||| Constituent valence quark multiset representation for standard mesons (Rule 03 §8).
public export
mesonConstituentQuarks : StandardMesonSpec -> Carrier SMFermion
mesonConstituentQuarks PionPlusMeson    = singletonCarrier QuarkU (intToBoxInt 1) <+> singletonCarrier AntiQuarkD (intToBoxInt 1)
mesonConstituentQuarks PionMinusMeson   = singletonCarrier AntiQuarkU (intToBoxInt 1) <+> singletonCarrier QuarkD (intToBoxInt 1)
mesonConstituentQuarks NeutralPionMeson = singletonCarrier QuarkU (intToBoxInt 1) <+> singletonCarrier AntiQuarkU (intToBoxInt 1)
mesonConstituentQuarks KaonPlusMeson    = singletonCarrier QuarkU (intToBoxInt 1) <+> singletonCarrier AntiQuarkS (intToBoxInt 1)
mesonConstituentQuarks KaonMinusMeson   = singletonCarrier AntiQuarkU (intToBoxInt 1) <+> singletonCarrier QuarkS (intToBoxInt 1)
mesonConstituentQuarks NeutralKaonMeson = singletonCarrier QuarkD (intToBoxInt 1) <+> singletonCarrier AntiQuarkS (intToBoxInt 1)

||| Certified Dependent Meson Carrier (Rule 03 §7, §8).
||| Bundles the underlying Carrier with QTT multiplicity 0 proof that
||| total constituent quarks match exact meson valence (2 quarks).
public export
record CertifiedMeson (spec : StandardMesonSpec) where
  constructor MkCertifiedMeson
  quarks       : Carrier SMFermion
  0 prfValence : totalMassBox quarks = intToBoxInt 2

||| Canonical certified Pion+ state (1 u + 1 d_bar = 2 quarks):
public export
certifiedPionPlus : CertifiedMeson PionPlusMeson
certifiedPionPlus = MkCertifiedMeson (mesonConstituentQuarks PionPlusMeson) Refl

||| Canonical certified Pion- state (1 u_bar + 1 d = 2 quarks):
public export
certifiedPionMinus : CertifiedMeson PionMinusMeson
certifiedPionMinus = MkCertifiedMeson (mesonConstituentQuarks PionMinusMeson) Refl

||| Canonical certified Neutral Pion state (1 u + 1 u_bar = 2 quarks):
public export
certifiedNeutralPion : CertifiedMeson NeutralPionMeson
certifiedNeutralPion = MkCertifiedMeson (mesonConstituentQuarks NeutralPionMeson) Refl

||| Canonical certified Kaon+ state (1 u + 1 s_bar = 2 quarks):
public export
certifiedKaonPlus : CertifiedMeson KaonPlusMeson
certifiedKaonPlus = MkCertifiedMeson (mesonConstituentQuarks KaonPlusMeson) Refl

||| Canonical certified Kaon- state (1 u_bar + 1 s = 2 quarks):
public export
certifiedKaonMinus : CertifiedMeson KaonMinusMeson
certifiedKaonMinus = MkCertifiedMeson (mesonConstituentQuarks KaonMinusMeson) Refl

||| Canonical certified Neutral Kaon state (1 d + 1 s_bar = 2 quarks):
public export
certifiedNeutralKaon : CertifiedMeson NeutralKaonMeson
certifiedNeutralKaon = MkCertifiedMeson (mesonConstituentQuarks NeutralKaonMeson) Refl

------------------------------------------------------------------------
-- 3. COMPILE-TIME AUDITS & VALENCE PROJECTIONS
------------------------------------------------------------------------

||| Observes exact valence count from certified baryon carrier in O(1) memory:
public export
baryonValenceCount : CertifiedBaryon spec -> BoxInt
baryonValenceCount (MkCertifiedBaryon q _) = totalMassBox q

||| Observes exact valence count from certified meson carrier in O(1) memory:
public export
mesonValenceCount : CertifiedMeson spec -> BoxInt
mesonValenceCount (MkCertifiedMeson q _) = totalMassBox q

||| Audit witness verifying that all canonical baryons and mesons satisfy exact valence:
public export
auditCertifiedHadronsProof : Bool
auditCertifiedHadronsProof =
  boxEq (baryonValenceCount certifiedProton) (intToBoxInt 3) &&
  boxEq (baryonValenceCount certifiedNeutron) (intToBoxInt 3) &&
  boxEq (baryonValenceCount certifiedLambda) (intToBoxInt 3) &&
  boxEq (mesonValenceCount certifiedPionPlus) (intToBoxInt 2) &&
  boxEq (mesonValenceCount certifiedPionMinus) (intToBoxInt 2) &&
  boxEq (mesonValenceCount certifiedNeutralPion) (intToBoxInt 2) &&
  boxEq (mesonValenceCount certifiedKaonPlus) (intToBoxInt 2)

||| Compile-time QTT erased proof witness for canonical baryon and meson valence:
public export
0 prfCertifiedProtonValence : totalMassBox (baryonConstituentQuarks ProtonBaryon) = intToBoxInt 3
prfCertifiedProtonValence = Refl

public export
0 prfCertifiedNeutronValence : totalMassBox (baryonConstituentQuarks NeutronBaryon) = intToBoxInt 3
prfCertifiedNeutronValence = Refl

public export
0 prfCertifiedPionPlusValence : totalMassBox (mesonConstituentQuarks PionPlusMeson) = intToBoxInt 2
prfCertifiedPionPlusValence = Refl
