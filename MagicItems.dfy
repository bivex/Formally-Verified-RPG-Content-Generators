module MagicItems {

  // ═══════════════════════════════════════════════════════════════════
  //  Core Types — proper datatypes for exhaustiveness & type safety
  // ═══════════════════════════════════════════════════════════════════

  datatype Element = Fire | Water | Earth | Air | Lightning | Ice | Light | Dark
  datatype ItemType = Sword | Staff | Ring | Amulet | Potion | Wand | Dagger | Shield | Bow | Helmet
  datatype Rarity  = Common | Uncommon | Rare | Epic | Legendary | Mythical

  const Elements : seq<Element>  := [Fire, Water, Earth, Air, Lightning, Ice, Light, Dark]
  const Types    : seq<ItemType> := [Sword, Staff, Ring, Amulet, Potion, Wand, Dagger, Shield, Bow, Helmet]
  const Rarities : seq<Rarity>   := [Common, Uncommon, Rare, Epic, Legendary, Mythical]

  // ═══════════════════════════════════════════════════════════════════
  //  Magic Item
  // ═══════════════════════════════════════════════════════════════════

  datatype MagicItem = MagicItem(
    name: string,
    element: Element,
    itemType: ItemType,
    rarity: Rarity,
    power: nat
  )

  // ═══════════════════════════════════════════════════════════════════
  //  Naming — Elemental Components
  // ═══════════════════════════════════════════════════════════════════

  function Material(e: Element): string {
    match e
      case Fire() => "Ember"
      case Water() => "Tide"
      case Earth() => "Stone"
      case Air() => "Wind"
      case Lightning() => "Storm"
      case Ice() => "Frost"
      case Light() => "Dawn"
      case Dark() => "Shadow"
  }

  function Adjective(e: Element): string {
    match e
      case Fire() => "Blazing"
      case Water() => "Surging"
      case Earth() => "Iron"
      case Air() => "Howling"
      case Lightning() => "Crackling"
      case Ice() => "Bitter"
      case Light() => "Holy"
      case Dark() => "Cursed"
  }

  function WeaponName(t: ItemType): string {
    match t
      case Sword() => "Blade"
      case Staff() => "Rod"
      case Ring() => "Band"
      case Amulet() => "Talisman"
      case Potion() => "Elixir"
      case Wand() => "Scepter"
      case Dagger() => "Fang"
      case Shield() => "Aegis"
      case Bow() => "Longbow"
      case Helmet() => "Crown"
  }

  function RarityTitle(r: Rarity): string {
    match r
      case Common() => ""
      case Uncommon() => ""
      case Rare() => "Grand "
      case Epic() => "Sovereign "
      case Legendary() => "Eternal "
      case Mythical() => "Celestial "
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Naming — Power Suffixes by Rarity Tier
  // ═══════════════════════════════════════════════════════════════════

  function EpicSuffix(e: Element): string {
    match e
      case Fire() => " of the Inferno"
      case Water() => " of the Abyss"
      case Earth() => " of the Mountain"
      case Air() => " of the Tempest"
      case Lightning() => " of the Thunder"
      case Ice() => " of the Frozen Waste"
      case Light() => " of Radiance"
      case Dark() => " of the Void"
  }

  function LegendarySuffix(e: Element): string {
    match e
      case Fire() => " of the Burning Throne"
      case Water() => " of the Drowned King"
      case Earth() => " of the Colossus"
      case Air() => " of the Endless Sky"
      case Lightning() => " of the Stormlord"
      case Ice() => " of the Eternal Winter"
      case Light() => " of the Divine Order"
      case Dark() => " of the Fallen Empire"
  }

  function MythicalSuffix(e: Element): string {
    match e
      case Fire() => ", Scourge of the Sun"
      case Water() => ", Wrath of the Depths"
      case Earth() => ", Heart of the World"
      case Air() => ", Breath of Creation"
      case Lightning() => ", Fury of the Heavens"
      case Ice() => ", Crown of Permafrost"
      case Light() => ", Dawning Star"
      case Dark() => ", Eclipse of Souls"
  }

  function PowerSuffix(e: Element, r: Rarity): string {
    match r
      case Mythical() => MythicalSuffix(e)
      case Legendary() => LegendarySuffix(e)
      case Epic() => EpicSuffix(e)
      case Rare() => " of Fortune"
      case Uncommon() => " of the Craft"
      case Common() => ""
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Naming — Template Patterns by Rarity
  // ═══════════════════════════════════════════════════════════════════
  //
  //  Common:    "{Material} {Weapon}"
  //  Uncommon:  "{Adjective} {Material} {Weapon} of the Craft"
  //  Rare:      "Grand {Adjective} {Material} {Weapon} of Fortune"
  //  Epic:      "Sovereign {Weapon} of the {ElementalRealm}"
  //  Legendary: "Eternal {Material} {Weapon} of the {Lore}"
  //  Mythical:  "Celestial {Weapon}, {Epithet}"
  // ═══════════════════════════════════════════════════════════════════

  function GenerateName(e: Element, t: ItemType, r: Rarity): string {
    match r
      case Common() =>
        Material(e) + " " + WeaponName(t)
      case Uncommon() =>
        Adjective(e) + " " + Material(e) + " " + WeaponName(t) + PowerSuffix(e, r)
      case Rare() =>
        RarityTitle(r) + Adjective(e) + " " + Material(e) + " " + WeaponName(t) + PowerSuffix(e, r)
      case Epic() =>
        RarityTitle(r) + WeaponName(t) + PowerSuffix(e, r)
      case Legendary() =>
        RarityTitle(r) + Material(e) + " " + WeaponName(t) + PowerSuffix(e, r)
      case Mythical() =>
        RarityTitle(r) + WeaponName(t) + MythicalSuffix(e)
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Power Calculation — Fibonacci-Inspired Scaling
  // ═══════════════════════════════════════════════════════════════════

  function RarityMultiplier(r: Rarity): nat {
    match r
      case Common() => 1
      case Uncommon() => 2
      case Rare() => 3
      case Epic() => 5
      case Legendary() => 8
      case Mythical() => 13
  }

  function ElementBonus(e: Element): nat {
    match e
      case Fire() => 5
      case Water() => 3
      case Earth() => 4
      case Air() => 2
      case Lightning() => 6
      case Ice() => 4
      case Light() => 7
      case Dark() => 7
  }

  function TypeBonus(t: ItemType): nat {
    match t
      case Sword() => 8
      case Staff() => 6
      case Ring() => 4
      case Amulet() => 5
      case Potion() => 2
      case Wand() => 7
      case Dagger() => 3
      case Shield() => 6
      case Bow() => 5
      case Helmet() => 4
  }

  function CalculatePower(e: Element, t: ItemType, r: Rarity): nat {
    RarityMultiplier(r) * 10 + ElementBonus(e) + TypeBonus(t)
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Item Creation
  // ═══════════════════════════════════════════════════════════════════

  function CreateItem(e: Element, t: ItemType, r: Rarity): MagicItem {
    MagicItem(GenerateName(e, t, r), e, t, r, CalculatePower(e, t, r))
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Bulk Generation
  // ═══════════════════════════════════════════════════════════════════

  method GenerateAllForElement(e: Element) returns (result: seq<MagicItem>)
    ensures |result| == |Types| * |Rarities|
    ensures forall i :: 0 <= i < |result| ==> result[i].element == e
  {
    result := [];
    var ti := 0;
    while ti < |Types|
      invariant 0 <= ti <= |Types|
      invariant |result| == ti * |Rarities|
      invariant forall i :: 0 <= i < |result| ==> result[i].element == e
    {
      var ri := 0;
      while ri < |Rarities|
        invariant 0 <= ri <= |Rarities|
        invariant |result| == ti * |Rarities| + ri
        invariant forall i :: 0 <= i < |result| ==> result[i].element == e
      {
        result := result + [CreateItem(e, Types[ti], Rarities[ri])];
        ri := ri + 1;
      }
      ti := ti + 1;
    }
  }

  method AllItems() returns (result: seq<MagicItem>)
    ensures |result| == |Elements| * |Types| * |Rarities|
  {
    result := [];
    var ei := 0;
    while ei < |Elements|
      invariant 0 <= ei <= |Elements|
      invariant |result| == ei * |Types| * |Rarities|
    {
      var items := GenerateAllForElement(Elements[ei]);
      result := result + items;
      ei := ei + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Filtering — Verified Predicates
  // ═══════════════════════════════════════════════════════════════════

  method FilterByRarity(r: Rarity, items: seq<MagicItem>) returns (result: seq<MagicItem>)
    ensures forall i :: 0 <= i < |result| ==> result[i].rarity == r
  {
    result := [];
    var i := 0;
    while i < |items|
      invariant 0 <= i <= |items|
      invariant forall j :: 0 <= j < |result| ==> result[j].rarity == r
    {
      if items[i].rarity == r {
        result := result + [items[i]];
      }
      i := i + 1;
    }
  }

  method FilterByElement(e: Element, items: seq<MagicItem>) returns (result: seq<MagicItem>)
    ensures forall i :: 0 <= i < |result| ==> result[i].element == e
  {
    result := [];
    var i := 0;
    while i < |items|
      invariant 0 <= i <= |items|
      invariant forall j :: 0 <= j < |result| ==> result[j].element == e
    {
      if items[i].element == e {
        result := result + [items[i]];
      }
      i := i + 1;
    }
  }

  method FilterByPower(minPower: nat, items: seq<MagicItem>) returns (result: seq<MagicItem>)
    ensures forall i :: 0 <= i < |result| ==> result[i].power >= minPower
  {
    result := [];
    var i := 0;
    while i < |items|
      invariant 0 <= i <= |items|
      invariant forall j :: 0 <= j < |result| ==> result[j].power >= minPower
    {
      if items[i].power >= minPower {
        result := result + [items[i]];
      }
      i := i + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Display — String Conversions
  // ═══════════════════════════════════════════════════════════════════

  function ElementStr(e: Element): string {
    match e
      case Fire() => "Fire"
      case Water() => "Water"
      case Earth() => "Earth"
      case Air() => "Air"
      case Lightning() => "Lightning"
      case Ice() => "Ice"
      case Light() => "Light"
      case Dark() => "Dark"
  }

  function TypeStr(t: ItemType): string {
    match t
      case Sword() => "Sword"
      case Staff() => "Staff"
      case Ring() => "Ring"
      case Amulet() => "Amulet"
      case Potion() => "Potion"
      case Wand() => "Wand"
      case Dagger() => "Dagger"
      case Shield() => "Shield"
      case Bow() => "Bow"
      case Helmet() => "Helmet"
  }

  function RarityStr(r: Rarity): string {
    match r
      case Common() => "Common"
      case Uncommon() => "Uncommon"
      case Rare() => "Rare"
      case Epic() => "Epic"
      case Legendary() => "Legendary"
      case Mythical() => "Mythical"
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Flavor Text
  // ═══════════════════════════════════════════════════════════════════

  function ElementLore(e: Element): string {
    match e
      case Fire() => "born in the heart of a dying star"
      case Water() => "drawn from the depths of the abyssal ocean"
      case Earth() => "carved from the roots of the world mountain"
      case Air() => "woven from the breath of the eternal wind"
      case Lightning() => "forged in the eye of an endless storm"
      case Ice() => "crystallized from the breath of the winter god"
      case Light() => "blessed by the radiance of the celestial choir"
      case Dark() => "tempered in the shadows between worlds"
  }

  function FlavorIntro(r: Rarity): string {
    match r
      case Mythical() => "A relic beyond mortal comprehension, "
      case Legendary() => "An artifact of immense power, "
      case Epic() => "A masterwork of its kind, "
      case Rare() => "A finely crafted piece, "
      case Uncommon() => "A well-made item, "
      case Common() => "A simple creation, "
  }

  function Description(item: MagicItem): string {
    FlavorIntro(item.rarity) + ElementLore(item.element) + "."
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Output
  // ═══════════════════════════════════════════════════════════════════

  method {:print} PrintItem(item: MagicItem) {
    print item.name;
    print " | ";
    print ElementStr(item.element);
    print " | ";
    print TypeStr(item.itemType);
    print " | ";
    print RarityStr(item.rarity);
    print " | Power: ";
    print item.power;
    print "\n";
  }

  method {:print} PrintItems(items: seq<MagicItem>) {
    var i := 0;
    while i < |items|
      invariant 0 <= i <= |items|
    {
      PrintItem(items[i]);
      i := i + 1;
    }
  }

  method {:print} PrintDetailed(items: seq<MagicItem>) {
    var i := 0;
    while i < |items|
      invariant 0 <= i <= |items|
    {
      var item := items[i];
      PrintItem(item);
      print "  ";
      print Description(item);
      print "\n\n";
      i := i + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Verified Examples — Assertions Proved at Compile Time
  // ═══════════════════════════════════════════════════════════════════

  method Example() {
    // Legendary Fire Sword
    var fireSword := CreateItem(Fire, Sword, Legendary);
    assert fireSword.power == 93;

    // Mythical Ice Amulet
    var iceAmulet := CreateItem(Ice, Amulet, Mythical);
    assert iceAmulet.power == 139;

    // Common Light Wand
    var lightWand := CreateItem(Light, Wand, Common);
    assert lightWand.power == 24;

    // Uncommon Dark Dagger
    var darkDagger := CreateItem(Dark, Dagger, Uncommon);
    assert darkDagger.power == 30;

    // Rare Water Shield
    var waterShield := CreateItem(Water, Shield, Rare);
    assert waterShield.power == 39;

    // Epic Lightning Staff
    var lightningStaff := CreateItem(Lightning, Staff, Epic);
    assert lightningStaff.power == 62;
  }

  // ═══════════════════════════════════════════════════════════════════
  //  Entry Point
  // ═══════════════════════════════════════════════════════════════════

  method {:print} Main() {
    var items := AllItems();
    print "========================================\n";
    print "   MAGIC ITEMS CODEX - Dafny 4.11\n";
    print "========================================\n";
    print "Total items: ";
    print |items|;
    print "\n\n";
    PrintItems(items);
  }
}
