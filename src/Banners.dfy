include "Characters.dfy"

module Banners {
  import opened Characters

  datatype BannerType = Standard | LimitedCharacter | LimitedWeapon

  const BannerTypes : seq<BannerType> := [Standard, LimitedCharacter, LimitedWeapon]

  // All rates stored as per-10000 (using nat arithmetic)
  const RATE_5STAR_CHAR    : nat := 60    // 0.60%
  const RATE_5STAR_WEAPON  : nat := 70    // 0.70%
  const RATE_4STAR_CHAR    : nat := 510   // 5.10%
  const RATE_4STAR_WEAPON  : nat := 600   // 6.00%
  const HARD_PITY_CHAR     : nat := 90
  const HARD_PITY_WEAPON   : nat := 80
  const SOFT_PITY_CHAR     : nat := 74
  const SOFT_PITY_WEAPON   : nat := 62
  const GUARANTEE_CHAR     : nat := 2     // 50/50 -> guaranteed featured on 2nd 5star
  const GUARANTEE_WEAPON   : nat := 2     // epitomized path: guaranteed on 2nd attempt

  datatype BannerConfig = BannerConfig(
    bannerType      : BannerType,
    featuredElement : Element,
    featuredWeapon  : WeaponType,
    rate5StarPer10k : nat,
    rate4StarPer10k : nat,
    hardPity        : nat,
    softPity        : nat,
    guaranteeAt     : nat
  ) {
    predicate Valid() {
      rate5StarPer10k > 0 &&
      rate4StarPer10k > rate5StarPer10k &&
      rate5StarPer10k + rate4StarPer10k < 10000 &&
      softPity < hardPity &&
      hardPity > 0 &&
      guaranteeAt > 0
    }
  }

  function MakeBanner(bt: BannerType, fe: Element, fw: WeaponType): BannerConfig
    ensures MakeBanner(bt, fe, fw).Valid()
  {
    match bt
      case Standard =>
        BannerConfig(bt, fe, fw, RATE_5STAR_CHAR, RATE_4STAR_CHAR, HARD_PITY_CHAR, SOFT_PITY_CHAR, GUARANTEE_CHAR)
      case LimitedCharacter =>
        BannerConfig(bt, fe, fw, RATE_5STAR_CHAR, RATE_4STAR_CHAR, HARD_PITY_CHAR, SOFT_PITY_CHAR, GUARANTEE_CHAR)
      case LimitedWeapon =>
        BannerConfig(bt, fe, fw, RATE_5STAR_WEAPON, RATE_4STAR_WEAPON, HARD_PITY_WEAPON, SOFT_PITY_WEAPON, GUARANTEE_WEAPON)
  }

  // Generate all: 3 types x 7 elements x 5 weapons = 105
  method GenerateAllForType(bt: BannerType) returns (result: seq<BannerConfig>)
    ensures |result| == |Elements| * |WeaponTypes|
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var ei := 0;
    while ei < |Elements|
      invariant 0 <= ei <= |Elements|
      invariant |result| == ei * |WeaponTypes|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var wi := 0;
      while wi < |WeaponTypes|
        invariant 0 <= wi <= |WeaponTypes|
        invariant |result| == ei * |WeaponTypes| + wi
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        result := result + [MakeBanner(bt, Elements[ei], WeaponTypes[wi])];
        wi := wi + 1;
      }
      ei := ei + 1;
    }
  }

  method AllBanners() returns (result: seq<BannerConfig>)
    ensures |result| == |BannerTypes| * |Elements| * |WeaponTypes|
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var bi := 0;
    while bi < |BannerTypes|
      invariant 0 <= bi <= |BannerTypes|
      invariant |result| == bi * |Elements| * |WeaponTypes|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var batch := GenerateAllForType(BannerTypes[bi]);
      result := result + batch;
      bi := bi + 1;
    }
  }

  function BannerTypeStr(bt: BannerType): string {
    match bt
      case Standard => "Standard"
      case LimitedCharacter => "LimitedChar"
      case LimitedWeapon => "LimitedWeapon"
  }
  function BElemStr(e: Element): string {
    match e
      case Pyro => "Pyro" case Hydro => "Hydro" case Anemo => "Anemo"
      case Electro => "Electro" case Geo => "Geo" case Cryo => "Cryo" case Dendro => "Dendro"
  }
  function BWeaponStr(w: WeaponType): string {
    match w
      case Sword => "Sword" case Claymore => "Claymore" case Polearm => "Polearm"
      case Bow => "Bow" case Catalyst => "Catalyst"
  }

  method {:print} PrintBanner(b: BannerConfig) {
    print BannerTypeStr(b.bannerType);
    print " | Featured:"; print BElemStr(b.featuredElement); print "-"; print BWeaponStr(b.featuredWeapon);
    print " | 5star:"; print b.rate5StarPer10k; print "/10k";
    print " | 4star:"; print b.rate4StarPer10k; print "/10k";
    print " | HardPity:"; print b.hardPity;
    print " | SoftPity:"; print b.softPity;
    print " | GuaranteeAt:"; print b.guaranteeAt;
    print "\n";
  }
  method {:print} PrintBanners(banners: seq<BannerConfig>) {
    var i := 0;
    while i < |banners| invariant 0 <= i <= |banners| {
      PrintBanner(banners[i]);
      i := i + 1;
    }
  }

  method {:print} MainBanners() {
    print "=== GACHA BANNER CONFIGS ===\n";
    print "Total: "; print |BannerTypes| * |Elements| * |WeaponTypes|; print "\n\n";
    var bi := 0;
    while bi < |BannerTypes| invariant 0 <= bi <= |BannerTypes| {
      print "-- "; print BannerTypeStr(BannerTypes[bi]); print " --\n";
      var batch := GenerateAllForType(BannerTypes[bi]);
      PrintBanners(batch);
      print "\n";
      bi := bi + 1;
    }
  }
}
