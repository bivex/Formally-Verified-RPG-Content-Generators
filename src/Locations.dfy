module Locations {

  // ═══════════════════════════════════════════════════════════════════
  // Types
  // ═══════════════════════════════════════════════════════════════════

  datatype Biome = Forest | Mountain | Desert | Swamp | Ocean | Tundra | Plains | Volcano
  datatype LocationType = City | Village | Ruins | Dungeon | Fortress | Temple | Cave | Outpost
  datatype Size = Tiny | Small | Medium | Large | Vast | Colossal

  const BiomesSeq        : seq<Biome>        := [Forest, Mountain, Desert, Swamp, Ocean, Tundra, Plains, Volcano]
  const LocationTypesSeq : seq<LocationType> := [City, Village, Ruins, Dungeon, Fortress, Temple, Cave, Outpost]
  const SizesSeq         : seq<Size>         := [Tiny, Small, Medium, Large, Vast, Colossal]

  // ═══════════════════════════════════════════════════════════════════
  // Data Structure
  // ═══════════════════════════════════════════════════════════════════

  datatype Location = Location(
    name: string,
    biome: Biome,
    locationType: LocationType,
    size: Size,
    dangerLevel: nat
  ) {
    predicate Valid() {
      // Danger rules: Huge places in safe biomes won't match small places in deadly biomes
      dangerLevel > 0
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Properties and Balance Rules
  // ═══════════════════════════════════════════════════════════════════

  function SizePrefix(s: Size): string {
    match s
      case Tiny()     => "Hidden "
      case Small()    => "Quiet "
      case Medium()   => ""
      case Large()    => "Grand "
      case Vast()     => "Endless "
      case Colossal() => "Titanic "
  }

  function BiomeAdjective(b: Biome): string {
    match b
      case Forest()   => "Verdant "
      case Mountain() => "Craggy "
      case Desert()   => "Sunbaked "
      case Swamp()    => "Murky "
      case Ocean()    => "Abyssal "
      case Tundra()   => "Frozen "
      case Plains()   => "Windswept "
      case Volcano()  => "Scorched "
  }

  function TypeNoun(l: LocationType): string {
    match l
      case City()     => "Metropolis"
      case Village()  => "Hamlet"
      case Ruins()    => "Wasteland"
      case Dungeon()  => "Labyrinth"
      case Fortress() => "Bastion"
      case Temple()   => "Sanctuary"
      case Cave()     => "Grotto"
      case Outpost()  => "Watch"
  }

  function BaseDanger(l: LocationType): nat {
    match l
      case Dungeon()  => 20
      case Ruins()    => 18
      case Fortress() => 15
      case Cave()     => 12
      case Temple()   => 8
      case Outpost()  => 5
      case City()     => 3
      case Village()  => 1
  }

  function BiomeDangerMultiplier(b: Biome): nat {
    match b
      case Volcano()  => 5
      case Ocean()    => 4
      case Swamp()    => 4
      case Desert()   => 3
      case Tundra()   => 3
      case Mountain() => 2
      case Forest()   => 1
      case Plains()   => 1
  }

  function SizeDangerBonus(s: Size): nat {
    match s
      case Colossal() => 50
      case Vast()     => 30
      case Large()    => 20
      case Medium()   => 10
      case Small()    => 5
      case Tiny()     => 2
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generators
  // ═══════════════════════════════════════════════════════════════════

  function GenerateName(b: Biome, l: LocationType, s: Size): string {
    SizePrefix(s) + BiomeAdjective(b) + TypeNoun(l)
  }

  function CalculateDanger(b: Biome, l: LocationType, s: Size): nat {
    var rawDanger := (BaseDanger(l) * BiomeDangerMultiplier(b)) + SizeDangerBonus(s);
    if rawDanger == 0 then 1 else rawDanger
  }

  function CreateLocation(b: Biome, l: LocationType, s: Size): Location
    ensures CreateLocation(b, l, s).Valid()
  {
    Location(GenerateName(b, l, s), b, l, s, CalculateDanger(b, l, s))
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generation Lists
  // ═══════════════════════════════════════════════════════════════════

  method GenerateAllForBiome(b: Biome) returns (result: seq<Location>)
    ensures |result| == |LocationTypesSeq| * |SizesSeq|
  {
    result := [];
    var li := 0;
    while li < |LocationTypesSeq|
      invariant 0 <= li <= |LocationTypesSeq|
      invariant |result| == li * |SizesSeq|
    {
      var si := 0;
      while si < |SizesSeq|
        invariant 0 <= si <= |SizesSeq|
        invariant |result| == li * |SizesSeq| + si
      {
        result := result + [CreateLocation(b, LocationTypesSeq[li], SizesSeq[si])];
        si := si + 1;
      }
      li := li + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Print Output
  // ═══════════════════════════════════════════════════════════════════

  method {:print} PrintLocation(loc: Location) {
    print loc.name;
    print " | Danger Level: ";
    print loc.dangerLevel;
    print "\n";
  }

  method {:print} PrintLocations(locs: seq<Location>) {
    var i := 0;
    while i < |locs|
      invariant 0 <= i <= |locs|
    {
      PrintLocation(locs[i]);
      i := i + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Verified Logic Examples
  // ═══════════════════════════════════════════════════════════════════

  method Example() {
    var loc1 := CreateLocation(Forest, Village, Medium);
    assert loc1.dangerLevel == 11; // (1 * 1) + 10

    var loc2 := CreateLocation(Volcano, Dungeon, Colossal);
    assert loc2.dangerLevel == 150; // (20 * 5) + 50
  }

  method {:print} Main() {
    var forestLocs := GenerateAllForBiome(Forest);
    var volcanoLocs := GenerateAllForBiome(Volcano);

    print "=== ATLAS OF LOCATIONS ===\n";
    PrintLocations(forestLocs);
    print "\n";
    PrintLocations(volcanoLocs);
  }
}
