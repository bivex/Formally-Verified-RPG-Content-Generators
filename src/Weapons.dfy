include "Characters.dfy"

module Weapons {
  import opened Characters

  datatype Substat = ATK_Pct | CritRate | CritDMG | ElemMastery | EnergyRecharge | HP_Pct | DEF_Pct

  const Substats : seq<Substat> := [ATK_Pct, CritRate, CritDMG, ElemMastery, EnergyRecharge, HP_Pct, DEF_Pct]
  const MIN_REF  : nat := 1
  const MAX_REF  : nat := 5

  datatype Weapon = Weapon(
    name        : string,
    weaponType  : WeaponType,
    rarity      : StarRarity,
    substat     : Substat,
    refinement  : nat,
    baseATK     : nat,
    substatValue: nat
  ) {
    predicate Valid() {
      MIN_REF <= refinement <= MAX_REF && baseATK > 0 && substatValue > 0
    }
  }

  function WeaponBaseATK_R3(w: WeaponType): nat {
    match w
      case Sword => 40 case Claymore => 38 case Polearm => 39
      case Bow => 37 case Catalyst => 33
  }
  function WeaponBaseATK_R4(w: WeaponType): nat {
    match w
      case Sword => 44 case Claymore => 42 case Polearm => 43
      case Bow => 41 case Catalyst => 42
  }
  function WeaponBaseATK_R5(w: WeaponType): nat {
    match w
      case Sword => 48 case Claymore => 46 case Polearm => 48
      case Bow => 46 case Catalyst => 49
  }
  function WeaponBaseATK(w: WeaponType, r: StarRarity): nat {
    match r
      case R3 => WeaponBaseATK_R3(w)
      case R4 => WeaponBaseATK_R4(w)
      case R5 => WeaponBaseATK_R5(w)
  }

  function SubstatBase_R3(s: Substat): nat
    ensures SubstatBase_R3(s) > 0
  {
    match s
      case ATK_Pct => 6 case CritRate => 4 case CritDMG => 8
      case ElemMastery => 20 case EnergyRecharge => 7 case HP_Pct => 6 case DEF_Pct => 7
  }
  function SubstatBase_R4(s: Substat): nat
    ensures SubstatBase_R4(s) > 0
  {
    match s
      case ATK_Pct => 9 case CritRate => 6 case CritDMG => 12
      case ElemMastery => 36 case EnergyRecharge => 10 case HP_Pct => 9 case DEF_Pct => 11
  }
  function SubstatBase_R5(s: Substat): nat
    ensures SubstatBase_R5(s) > 0
  {
    match s
      case ATK_Pct => 11 case CritRate => 7 case CritDMG => 14
      case ElemMastery => 44 case EnergyRecharge => 12 case HP_Pct => 11 case DEF_Pct => 13
  }
  function SubstatBase(s: Substat, r: StarRarity): nat
    ensures SubstatBase(s, r) > 0
  {
    match r
      case R3 => SubstatBase_R3(s)
      case R4 => SubstatBase_R4(s)
      case R5 => SubstatBase_R5(s)
  }

  // Substat scales linearly with refinement: R1=base, R5=5*base
  function SubstatValue(s: Substat, ref: nat, r: StarRarity): nat
    requires MIN_REF <= ref <= MAX_REF
    ensures SubstatValue(s, ref, r) > 0
  {
    SubstatBase(s, r) * ref
  }

  function SubstatAbbrev(s: Substat): string {
    match s
      case ATK_Pct => "Sharp" case CritRate => "Keen" case CritDMG => "Lethal"
      case ElemMastery => "Ancient" case EnergyRecharge => "Flowing"
      case HP_Pct => "Sturdy" case DEF_Pct => "Guarded"
  }
  function WeaponSuffix(w: WeaponType): string {
    match w
      case Sword => "Edge" case Claymore => "Impact" case Polearm => "Thrust"
      case Bow => "Shot" case Catalyst => "Tome"
  }
  function WRarityPrefix(r: StarRarity): string {
    match r case R3 => "" case R4 => "Prototype " case R5 => "Primordial "
  }
  function RefTag(ref: nat): string
    requires MIN_REF <= ref <= MAX_REF
  {
    match ref case 1 => "" case 2 => " R2" case 3 => " R3" case 4 => " R4" case 5 => " R5" case _ => ""
  }
  function GenerateName(w: WeaponType, r: StarRarity, s: Substat, ref: nat): string
    requires MIN_REF <= ref <= MAX_REF
  {
    WRarityPrefix(r) + SubstatAbbrev(s) + " " + WeaponSuffix(w) + RefTag(ref)
  }

  function CreateWeapon(w: WeaponType, r: StarRarity, s: Substat, ref: nat): Weapon
    requires MIN_REF <= ref <= MAX_REF
    ensures CreateWeapon(w, r, s, ref).Valid()
  {
    Weapon(GenerateName(w, r, s, ref), w, r, s, ref, WeaponBaseATK(w, r), SubstatValue(s, ref, r))
  }

  // Per weapon type: 3 rarities x 7 substats x 5 refinements = 105
  method GenerateAllForType(w: WeaponType) returns (result: seq<Weapon>)
    ensures |result| == |Rarities| * |Substats| * (MAX_REF - MIN_REF + 1)
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var ri := 0;
    while ri < |Rarities|
      invariant 0 <= ri <= |Rarities|
      invariant |result| == ri * |Substats| * (MAX_REF - MIN_REF + 1)
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var si := 0;
      while si < |Substats|
        invariant 0 <= si <= |Substats|
        invariant |result| == ri * |Substats| * (MAX_REF - MIN_REF + 1) + si * (MAX_REF - MIN_REF + 1)
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        var ref := MIN_REF;
        while ref <= MAX_REF
          invariant MIN_REF <= ref <= MAX_REF + 1
          invariant |result| == ri * |Substats| * (MAX_REF - MIN_REF + 1) + si * (MAX_REF - MIN_REF + 1) + (ref - MIN_REF)
          invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
        {
          result := result + [CreateWeapon(w, Rarities[ri], Substats[si], ref)];
          ref := ref + 1;
        }
        si := si + 1;
      }
      ri := ri + 1;
    }
  }

  // Total: 5 types x 105 = 525
  method AllWeapons() returns (result: seq<Weapon>)
    ensures |result| == |WeaponTypes| * |Rarities| * |Substats| * (MAX_REF - MIN_REF + 1)
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var wi := 0;
    while wi < |WeaponTypes|
      invariant 0 <= wi <= |WeaponTypes|
      invariant |result| == wi * |Rarities| * |Substats| * (MAX_REF - MIN_REF + 1)
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var batch := GenerateAllForType(WeaponTypes[wi]);
      result := result + batch;
      wi := wi + 1;
    }
  }

  function SubstatStr(s: Substat): string {
    match s
      case ATK_Pct => "ATK%" case CritRate => "CritRate" case CritDMG => "CritDMG"
      case ElemMastery => "EM" case EnergyRecharge => "ER" case HP_Pct => "HP%" case DEF_Pct => "DEF%"
  }
  function WRarityStr(r: StarRarity): string {
    match r case R3 => "3star" case R4 => "4star" case R5 => "5star"
  }

  method {:print} PrintWeapon(wp: Weapon) {
    print wp.name;
    print " | ATK:"; print wp.baseATK;
    print " | "; print SubstatStr(wp.substat); print ":"; print wp.substatValue;
    print " | Ref:R"; print wp.refinement;
    print " ["; print WRarityStr(wp.rarity); print "]";
    print "\n";
  }
  method {:print} PrintWeapons(weapons: seq<Weapon>) {
    var i := 0;
    while i < |weapons| invariant 0 <= i <= |weapons| {
      PrintWeapon(weapons[i]);
      i := i + 1;
    }
  }

  method {:print} MainWeapons() {
    print "=== GACHA WEAPON DATABASE ===\n";
    print "Total: "; print |WeaponTypes| * |Rarities| * |Substats| * (MAX_REF - MIN_REF + 1); print "\n\n";
    var wi := 0;
    while wi < |WeaponTypes| invariant 0 <= wi <= |WeaponTypes| {
      var batch := GenerateAllForType(WeaponTypes[wi]);
      PrintWeapons(batch);
      print "\n";
      wi := wi + 1;
    }
  }
}
