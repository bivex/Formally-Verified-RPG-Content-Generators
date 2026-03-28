module NPCs {

  // ═══════════════════════════════════════════════════════════════════
  // Types
  // ═══════════════════════════════════════════════════════════════════

  datatype Race = Human | Elf | Dwarf | Orc | Halfling | Gnome | Tiefling | Dragonborn
  datatype Profession = Blacksmith | Merchant | Guard | Peasant | Scholar | Noble | Priest | Thief
  datatype Alignment = LawfulGood | NeutralGood | ChaoticGood | LawfulNeutral | TrueNeutral | ChaoticNeutral | LawfulEvil | NeutralEvil | ChaoticEvil

  const RacesSeq       : seq<Race>       := [Human, Elf, Dwarf, Orc, Halfling, Gnome, Tiefling, Dragonborn]
  const ProfessionsSeq : seq<Profession> := [Blacksmith, Merchant, Guard, Peasant, Scholar, Noble, Priest, Thief]
  const AlignmentsSeq  : seq<Alignment>  := [LawfulGood, NeutralGood, ChaoticGood, LawfulNeutral, TrueNeutral, ChaoticNeutral, LawfulEvil, NeutralEvil, ChaoticEvil]

  // ═══════════════════════════════════════════════════════════════════
  // Data Structure
  // ═══════════════════════════════════════════════════════════════════

  datatype NPC = NPC(
    name: string,
    race: Race,
    profession: Profession,
    alignment: Alignment,
    goldCoins: nat,
    influence: nat
  ) {
    predicate Valid() {
      // Noble influence should be reasonably high, peasants should be low.
      (profession == Noble ==> influence >= 50) &&
      (profession == Peasant ==> influence <= 10) &&
      goldCoins >= 0
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Properties and Balance Rules
  // ═══════════════════════════════════════════════════════════════════

  function RaceWealthMultiplier(r: Race): nat {
    match r
      case Dwarf()      => 15
      case Elf()        => 12
      case Dragonborn() => 10
      case Tiefling()   => 8
      case Human()      => 7
      case Halfling()   => 5
      case Gnome()      => 5
      case Orc()        => 2
  }

  function ProfessionWealthBase(p: Profession): nat {
    match p
      case Noble()      => 500
      case Merchant()   => 200
      case Blacksmith() => 80
      case Priest()     => 50
      case Scholar()    => 40
      case Guard()      => 20
      case Thief()      => 15
      case Peasant()    => 2
  }

  function ProfessionInfluenceBase(p: Profession): nat {
    match p
      case Noble()      => 80
      case Priest()     => 60
      case Scholar()    => 50
      case Merchant()   => 40
      case Guard()      => 30
      case Blacksmith() => 20
      case Thief()      => 10
      case Peasant()    => 5
  }

  function AlignmentInfluenceMod(a: Alignment): int {
    match a
      case LawfulGood()     => 15
      case NeutralGood()    => 10
      case LawfulNeutral()  => 5
      case TrueNeutral()    => 0
      case ChaoticGood()    => -5
      case ChaoticNeutral() => -10
      case LawfulEvil()     => 10
      case NeutralEvil()    => 0
      case ChaoticEvil()    => -20
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generators
  // ═══════════════════════════════════════════════════════════════════

  function GenerateName(r: Race, p: Profession): string {
    var title := match p {
      case Noble()      => "Lord "
      case Guard()      => "Captain "
      case Priest()     => "Father "
      case Scholar()    => "Master "
      case Blacksmith() => "Smith "
      case Merchant()   => "Trader "
      case Thief()      => "Shadow "
      case Peasant()    => "Citizen "
    };

    var raceName := match r {
      case Human()      => "Human"
      case Elf()        => "Elf"
      case Dwarf()      => "Dwarf"
      case Orc()        => "Orc"
      case Halfling()   => "Halfling"
      case Gnome()      => "Gnome"
      case Tiefling()   => "Tiefling"
      case Dragonborn() => "Dragonkin"
    };

    title + raceName
  }

  function CalculateWealth(r: Race, p: Profession): nat {
    RaceWealthMultiplier(r) * ProfessionWealthBase(p)
  }

  function CalculateInfluence(p: Profession, a: Alignment): nat {
    var raw := ProfessionInfluenceBase(p) as int + AlignmentInfluenceMod(a);
    var boundedRaw := if raw < 0 then 0 else raw;
    
    // Enforce datatypes validation rules:
    var inf := if p == Noble && boundedRaw < 50 then 50
               else if p == Peasant && boundedRaw > 10 then 10
               else boundedRaw;
    inf as nat
  }

  function CreateNPC(r: Race, p: Profession, a: Alignment): NPC
    ensures CreateNPC(r, p, a).Valid()
  {
    var wealth := CalculateWealth(r, p);
    var influence := CalculateInfluence(p, a);

    NPC(GenerateName(r, p), r, p, a, wealth, influence)
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generation Lists
  // ═══════════════════════════════════════════════════════════════════

  method GenerateAllForRace(r: Race) returns (result: seq<NPC>)
    ensures |result| == |ProfessionsSeq| * |AlignmentsSeq|
  {
    result := [];
    var pi := 0;
    while pi < |ProfessionsSeq|
      invariant 0 <= pi <= |ProfessionsSeq|
      invariant |result| == pi * |AlignmentsSeq|
    {
      var ai := 0;
      while ai < |AlignmentsSeq|
        invariant 0 <= ai <= |AlignmentsSeq|
        invariant |result| == pi * |AlignmentsSeq| + ai
      {
        var inf := CalculateInfluence(ProfessionsSeq[pi], AlignmentsSeq[ai]);
        assert (ProfessionsSeq[pi] == Noble ==> inf >= 50);
        assert (ProfessionsSeq[pi] == Peasant ==> inf <= 10);
        result := result + [CreateNPC(r, ProfessionsSeq[pi], AlignmentsSeq[ai])];
        ai := ai + 1;
      }
      pi := pi + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Print Output
  // ═══════════════════════════════════════════════════════════════════

  method {:print} PrintNPC(n: NPC) {
    print n.name;
    print " | Wealth: ";
    print n.goldCoins;
    print "g | Influence: ";
    print n.influence;
    print "\n";
  }

  method {:print} PrintNPCs(npcs: seq<NPC>) {
    var i := 0;
    while i < |npcs|
      invariant 0 <= i <= |npcs|
    {
      PrintNPC(npcs[i]);
      i := i + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Verified Logic Examples
  // ═══════════════════════════════════════════════════════════════════

  method ExampleCreation() {
    var nobleDwarf := CreateNPC(Dwarf, Noble, LawfulGood);
    assert nobleDwarf.goldCoins == 7500;
    assert nobleDwarf.influence == 95;

    var peasantOrc := CreateNPC(Orc, Peasant, ChaoticEvil);
    assert peasantOrc.goldCoins == 4;
    assert peasantOrc.influence == 0;
  }

  method {:print} Main() {
    var elves := GenerateAllForRace(Elf);
    
    print "=== NPC DIRECTORY ===\n";
    PrintNPCs(elves);
  }
}
