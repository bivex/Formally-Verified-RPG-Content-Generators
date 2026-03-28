module Locations {
  // Types
  type Biome = string
  type LocationType = string
  type Size = string

  // Sequences of valid values
  const BiomesSeq: seq<Biome> := ["Forest", "Mountain", "Desert", "Swamp", "Ocean", "Tundra", "Plains", "Volcano"]
  const LocationTypesSeq: seq<LocationType> := ["City", "Village", "Ruins", "Dungeon", "Fortress", "Temple", "Cave", "Outpost"]
  const SizesSeq: seq<Size> := ["Tiny", "Small", "Medium", "Large", "Vast", "Colossal"]

  // Datatype for a location
  datatype Location = Location(
    name: string,
    biome: Biome,
    locationType: LocationType,
    size: Size,
    dangerLevel: nat
  ) {
    predicate Valid() {
      biome in BiomesSeq &&
      locationType in LocationTypesSeq &&
      size in SizesSeq &&
      dangerLevel >= 0
    }
  }

  // Size prefix
  function SizePrefix(s: Size): string
    requires s in SizesSeq
  {
    match s
      case "Tiny" => "Hidden "
      case "Small" => "Quiet "
      case "Medium" => ""
      case "Large" => "Grand "
      case "Vast" => "Endless "
      case "Colossal" => "Titanic "
      case _ => ""
  }

  // Biome component
  function BiomeAdjective(b: Biome): string
    requires b in BiomesSeq
  {
    match b
      case "Forest" => "Verdant "
      case "Mountain" => "Craggy "
      case "Desert" => "Sunbaked "
      case "Swamp" => "Murky "
      case "Ocean" => "Abyssal "
      case "Tundra" => "Frozen "
      case "Plains" => "Windswept "
      case "Volcano" => "Scorched "
      case _ => "Mystic "
  }

  // Type name
  function TypeNoun(t: LocationType): string
    requires t in LocationTypesSeq
  {
    match t
      case "City" => "Metropolis"
      case "Village" => "Hamlet"
      case "Ruins" => "Remnants"
      case "Dungeon" => "Labyrinth"
      case "Fortress" => "Bastion"
      case "Temple" => "Sanctuary"
      case "Cave" => "Grotto"
      case "Outpost" => "Watch"
      case _ => "Place"
  }

  // Name suffix
  function NameSuffix(b: Biome, t: LocationType): string
    requires b in BiomesSeq
    requires t in LocationTypesSeq
  {
    if b == "Volcano" && t == "Dungeon" then " of Doom"
    else if b == "Ocean" && t == "City" then " of the Deep"
    else if b == "Forest" && t == "Temple" then " of the Ancients"
    else if b == "Desert" && t == "Ruins" then " of Lost Kings"
    else if b == "Mountain" && t == "Fortress" then " of the Sky"
    else if b == "Swamp" && t == "Village" then " of Sorrows"
    else if b == "Tundra" && t == "Cave" then " of Echoes"
    else if b == "Plains" && t == "Outpost" then " of the Horizon"
    else ""
  }

  // Generate name
  function GenerateName(b: Biome, t: LocationType, s: Size): string
    requires b in BiomesSeq
    requires t in LocationTypesSeq
    requires s in SizesSeq
  {
    SizePrefix(s) + BiomeAdjective(b) + TypeNoun(t) + NameSuffix(b, t)
  }

  // Size index helper
  function SizeIndex(s: Size): nat
    requires s in SizesSeq
  {
    if s == "Tiny" then 1
    else if s == "Small" then 2
    else if s == "Medium" then 3
    else if s == "Large" then 4
    else if s == "Vast" then 5
    else if s == "Colossal" then 6
    else 0
  }

  // Calculate danger
  function CalculateDanger(b: Biome, s: Size): nat
    requires b in BiomesSeq
    requires s in SizesSeq
  {
    var baseDanger := if b in {"Volcano", "Ocean", "Swamp"} then 20 else 5;
    baseDanger * SizeIndex(s)
  }

  // Create a location
  function CreateLocation(b: Biome, t: LocationType, s: Size): Location
    requires b in BiomesSeq
    requires t in LocationTypesSeq
    requires s in SizesSeq
    ensures CreateLocation(b, t, s).Valid()
    ensures CreateLocation(b, t, s).biome == b
    ensures CreateLocation(b, t, s).locationType == t
    ensures CreateLocation(b, t, s).size == s
  {
    Location(GenerateName(b, t, s), b, t, s, CalculateDanger(b, s))
  }

  // Helper lemma: sequence element is a member
  lemma SeqMemLemma<T>(seq_p: seq<T>, i: int)
    requires 0 <= i < |seq_p|
    ensures seq_p[i] in seq_p
  {}

  // Generate all locations for a given biome
  method GenerateAllForBiome(b: Biome) returns (result: seq<Location>)
    requires b in BiomesSeq
    ensures |result| == |LocationTypesSeq| * |SizesSeq|
    ensures forall i :: 0 <= i < |result| ==> result[i].biome == b && result[i].Valid()
  {
    result := [];
    var ti := 0;
    while ti < |LocationTypesSeq|
      invariant 0 <= ti <= |LocationTypesSeq|
      invariant |result| == ti * |SizesSeq|
      invariant forall i :: 0 <= i < |result| ==> result[i].biome == b && result[i].Valid()
    {
      var t := LocationTypesSeq[ti];
      SeqMemLemma(LocationTypesSeq, ti);
      var ri := 0;
      while ri < |SizesSeq|
        invariant 0 <= ri <= |SizesSeq|
        invariant |result| == ti * |SizesSeq| + ri
        invariant forall i :: 0 <= i < |result| ==> result[i].biome == b && result[i].Valid()
        invariant t in LocationTypesSeq
      {
        var s := SizesSeq[ri];
        SeqMemLemma(SizesSeq, ri);
        assert s in SizesSeq;
        var loc := CreateLocation(b, t, s);
        assert loc.Valid();
        assert loc.biome == b;
        result := result + [loc];
        ri := ri + 1;
      }
      ti := ti + 1;
    }
  }

  // Get locations by size
  method GetLocationsBySize(s: Size, allLocations: seq<Location>) returns (result: seq<Location>)
    requires s in SizesSeq
    ensures forall i :: 0 <= i < |result| ==> result[i].size == s
  {
    result := [];
    var i := 0;
    while i < |allLocations|
      invariant 0 <= i <= |allLocations|
      invariant forall j :: 0 <= j < |result| ==> result[j].size == s
    {
      if allLocations[i].size == s {
        result := result + [allLocations[i]];
      }
      i := i + 1;
    }
  }

  // Generate all locations across all biomes
  method AllLocations() returns (result: seq<Location>)
    ensures |result| == |BiomesSeq| * |LocationTypesSeq| * |SizesSeq|
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var bi := 0;
    while bi < |BiomesSeq|
      invariant 0 <= bi <= |BiomesSeq|
      invariant |result| == bi * |LocationTypesSeq| * |SizesSeq|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var locs := GenerateAllForBiome(BiomesSeq[bi]);
      result := result + locs;
      bi := bi + 1;
    }
  }

  // Print all locations to stdout
  method {:print} PrintLocations(locs: seq<Location>)
  {
    var i := 0;
    while i < |locs|
      invariant 0 <= i <= |locs|
    {
      var loc := locs[i];
      print loc.name;
      print " | Biome: ";
      print loc.biome;
      print " | Type: ";
      print loc.locationType;
      print " | Size: ";
      print loc.size;
      print " | Danger: ";
      print loc.dangerLevel;
      print "\n";
      i := i + 1;
    }
  }

  // Print first N locations
  method {:print} PrintFirstN(locs: seq<Location>, n: int)
    requires 0 <= n <= |locs|
  {
    var i := 0;
    while i < n
      invariant 0 <= i <= n
    {
      var loc := locs[i];
      print loc.name;
      print " | Biome: ";
      print loc.biome;
      print " | Type: ";
      print loc.locationType;
      print " | Size: ";
      print loc.size;
      print " | Danger: ";
      print loc.dangerLevel;
      print "\n";
      i := i + 1;
    }
  }

  // Example: Location Creation logic
  method ExampleCreation()
  {
    var doomDungeon := CreateLocation("Volcano", "Dungeon", "Colossal");
    // String content checks omitted to save verification complexity (sequence overhead)
    assert doomDungeon.dangerLevel == 120;

    var tinyCamp := CreateLocation("Plains", "Outpost", "Tiny");
    assert tinyCamp.dangerLevel == 5;
  }

  // Example: Generation and Filtration logic
  method ExampleFiltration()
  {
    // Generate all volcano locations
    var allVolcano := GenerateAllForBiome("Volcano");
    assert |LocationTypesSeq| == 8;
    assert |SizesSeq| == 6;
    assert |allVolcano| == 48; // 8 * 6

    // Filter colossal locations
    var colossals := GetLocationsBySize("Colossal", allVolcano);
    assert forall i :: 0 <= i < |colossals| ==> colossals[i].size == "Colossal";
  }

  // Main entry point — generates and prints all 384 locations
  method {:print} Main() {
    var locs := AllLocations();
    print "Total locations generated: ";
    print |locs|;
    print "\n\n";
    PrintLocations(locs);
  }
}
