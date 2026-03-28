module Characters {

  datatype Element    = Pyro | Hydro | Anemo | Electro | Geo | Cryo | Dendro
  datatype WeaponType = Sword | Claymore | Polearm | Bow | Catalyst
  datatype StarRarity = R3 | R4 | R5

  const Elements    : seq<Element>    := [Pyro, Hydro, Anemo, Electro, Geo, Cryo, Dendro]
  const WeaponTypes : seq<WeaponType> := [Sword, Claymore, Polearm, Bow, Catalyst]
  const Rarities    : seq<StarRarity> := [R3, R4, R5]

  datatype Character = Character(
    name      : string,
    element   : Element,
    weaponType: WeaponType,
    rarity    : StarRarity,
    baseHP    : nat,
    baseATK   : nat,
    baseDEF   : nat
  ) {
    predicate Valid() { baseHP > 0 && baseATK > 0 && baseDEF > 0 }
  }

  function RarityHPBase(r: StarRarity): nat {
    match r case R3 => 5000 case R4 => 8000 case R5 => 11000
  }
  function RarityATKBase(r: StarRarity): nat {
    match r case R3 => 15 case R4 => 22 case R5 => 30
  }
  function RarityDEFBase(r: StarRarity): nat {
    match r case R3 => 50 case R4 => 75 case R5 => 100
  }
  function ElemHPBonus(e: Element): nat {
    match e
      case Pyro => 500 case Hydro => 1000 case Anemo => 300
      case Electro => 600 case Geo => 800 case Cryo => 700 case Dendro => 900
  }
  function ElemDEFBonus(e: Element): nat {
    match e
      case Pyro => 5 case Hydro => 3 case Anemo => 8
      case Electro => 6 case Geo => 10 case Cryo => 7 case Dendro => 4
  }
  function WeaponATKBonus(w: WeaponType): nat {
    match w
      case Sword => 10 case Claymore => 15 case Polearm => 12
      case Bow => 8 case Catalyst => 7
  }
  function WeaponHPBonus(w: WeaponType): nat {
    match w
      case Sword => 500 case Claymore => 300 case Polearm => 400
      case Bow => 600 case Catalyst => 800
  }

  function ElemTitle(e: Element): string {
    match e
      case Pyro => "Flame" case Hydro => "Tide" case Anemo => "Storm"
      case Electro => "Thunder" case Geo => "Stone" case Cryo => "Frost" case Dendro => "Bloom"
  }
  function WeaponTitle(w: WeaponType): string {
    match w
      case Sword => "Blade" case Claymore => "Greatsword" case Polearm => "Spear"
      case Bow => "Archer" case Catalyst => "Sage"
  }
  function RarityPrefix(r: StarRarity): string {
    match r case R3 => "" case R4 => "Arcane " case R5 => "Celestial "
  }
  function GenerateName(e: Element, w: WeaponType, r: StarRarity): string {
    RarityPrefix(r) + ElemTitle(e) + " " + WeaponTitle(w)
  }

  function CreateCharacter(e: Element, w: WeaponType, r: StarRarity): Character
    ensures CreateCharacter(e, w, r).Valid()
  {
    Character(
      GenerateName(e, w, r), e, w, r,
      RarityHPBase(r) + ElemHPBonus(e) + WeaponHPBonus(w),
      RarityATKBase(r) + WeaponATKBonus(w),
      RarityDEFBase(r) + ElemDEFBonus(e)
    )
  }

  method GenerateAllForRarity(r: StarRarity) returns (result: seq<Character>)
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
        result := result + [CreateCharacter(Elements[ei], WeaponTypes[wi], r)];
        wi := wi + 1;
      }
      ei := ei + 1;
    }
  }

  method AllCharacters() returns (result: seq<Character>)
    ensures |result| == |Rarities| * |Elements| * |WeaponTypes|
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var ri := 0;
    while ri < |Rarities|
      invariant 0 <= ri <= |Rarities|
      invariant |result| == ri * |Elements| * |WeaponTypes|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var batch := GenerateAllForRarity(Rarities[ri]);
      result := result + batch;
      ri := ri + 1;
    }
  }

  function RarityStr(r: StarRarity): string {
    match r case R3 => "3star" case R4 => "4star" case R5 => "5star"
  }
  function ElemStr(e: Element): string {
    match e
      case Pyro => "Pyro" case Hydro => "Hydro" case Anemo => "Anemo"
      case Electro => "Electro" case Geo => "Geo" case Cryo => "Cryo" case Dendro => "Dendro"
  }
  function WeaponStr(w: WeaponType): string {
    match w
      case Sword => "Sword" case Claymore => "Claymore" case Polearm => "Polearm"
      case Bow => "Bow" case Catalyst => "Catalyst"
  }

  method {:print} PrintCharacter(c: Character) {
    print c.name;
    print " ["; print RarityStr(c.rarity); print "]";
    print " | "; print ElemStr(c.element);
    print " | "; print WeaponStr(c.weaponType);
    print " | HP:"; print c.baseHP;
    print " ATK:"; print c.baseATK;
    print " DEF:"; print c.baseDEF;
    print "\n";
  }

  method {:print} PrintCharacters(chars: seq<Character>) {
    var i := 0;
    while i < |chars| invariant 0 <= i <= |chars| {
      PrintCharacter(chars[i]);
      i := i + 1;
    }
  }

  method ExampleAsserts() {
    var c1 := CreateCharacter(Pyro, Sword, R5);
    assert c1.baseHP  == 11000 + 500 + 500;
    assert c1.baseATK == 30 + 10;
    assert c1.baseDEF == 100 + 5;
    var c2 := CreateCharacter(Hydro, Catalyst, R4);
    assert c2.baseHP  == 8000 + 1000 + 800;
    assert c2.baseATK == 22 + 7;
    var c3 := CreateCharacter(Cryo, Bow, R3);
    assert c3.baseHP  == 5000 + 700 + 600;
    assert c3.baseDEF == 50 + 7;
  }

  method {:print} MainCharacters() {
    print "=== GACHA CHARACTER DATABASE ===\n";
    print "Total: "; print |Rarities| * |Elements| * |WeaponTypes|; print "\n\n";
    var ri := 0;
    while ri < |Rarities| invariant 0 <= ri <= |Rarities| {
      print "--- "; print RarityStr(Rarities[ri]); print " ---\n";
      var batch := GenerateAllForRarity(Rarities[ri]);
      PrintCharacters(batch);
      print "\n";
      ri := ri + 1;
    }
  }
}
