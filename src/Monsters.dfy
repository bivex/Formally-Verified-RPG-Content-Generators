module Monsters {

  // ═══════════════════════════════════════════════════════════════════
  // Types
  // ═══════════════════════════════════════════════════════════════════

  datatype MonsterType = Dragon | Goblin | Golem | Elemental | Undead | Beast | Demon | Slime
  datatype MonsterSize = Swarm | Small | Medium | Large | Huge | Gargantuan
  datatype Element     = Fire | Water | Earth | Air | Lightning | Ice | Dark | None

  const TypesSeq    : seq<MonsterType> := [Dragon, Goblin, Golem, Elemental, Undead, Beast, Demon, Slime]
  const SizesSeq    : seq<MonsterSize> := [Swarm, Small, Medium, Large, Huge, Gargantuan]
  const ElementsSeq : seq<Element>     := [Fire, Water, Earth, Air, Lightning, Ice, Dark, None]

  // ═══════════════════════════════════════════════════════════════════
  // Data Structure
  // ═══════════════════════════════════════════════════════════════════

  datatype Monster = Monster(
    name: string,
    mType: MonsterType,
    mSize: MonsterSize,
    element: Element,
    healthPool: nat,
    attackDamage: nat,
    threatRating: nat
  ) {
    predicate Valid() {
      healthPool > 0 &&
      attackDamage > 0 &&
      threatRating > 0
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Properties and Balance Rules
  // ═══════════════════════════════════════════════════════════════════

  function TypeMultiplier(t: MonsterType): nat {
    match t
      case Dragon()    => 20
      case Demon()     => 15
      case Elemental() => 12
      case Golem()     => 10
      case Undead()    => 6
      case Beast()     => 5
      case Slime()     => 3
      case Goblin()    => 2
  }

  function SizeMultiplier(s: MonsterSize): nat {
    match s
      case Gargantuan() => 25
      case Huge()       => 15
      case Large()      => 8
      case Swarm()      => 5
      case Medium()     => 3
      case Small()      => 1
  }

  function ElementPower(e: Element): nat {
    match e
      case Dark()      => 10
      case Fire()      => 8
      case Lightning() => 7
      case Ice()       => 6
      case Earth()     => 5
      case Water()     => 4
      case Air()       => 3
      case None()      => 0
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generators
  // ═══════════════════════════════════════════════════════════════════

  function GenerateName(t: MonsterType, s: MonsterSize, e: Element): string {
    var sizeStr := match s {
      case Gargantuan() => "Colossal "
      case Huge()       => "Towering "
      case Large()      => "Dire "
      case Medium()     => ""
      case Small()      => "Lesser "
      case Swarm()      => "Swarm of "
    };

    var elemStr := match e {
      case Fire()      => "Infernal "
      case Water()     => "Abyssal "
      case Earth()     => "Stone "
      case Air()       => "Storm "
      case Lightning() => "Volt "
      case Ice()       => "Frost "
      case Dark()      => "Void "
      case None()      => ""
    };

    var typeStr := match t {
      case Dragon()    => "Dragon"
      case Demon()     => "Demon"
      case Elemental() => "Elemental"
      case Golem()     => "Golem"
      case Undead()    => "Revenant"
      case Beast()     => "Beast"
      case Slime()     => "Ooze"
      case Goblin()    => "Goblin"
    };

    sizeStr + elemStr + typeStr
  }

  function CalculateHealth(t: MonsterType, s: MonsterSize, e: Element): nat {
    (SizeMultiplier(s) * 10) + (TypeMultiplier(t) * 5) + (ElementPower(e) * 2)
  }

  function CalculateAttack(t: MonsterType, s: MonsterSize, e: Element): nat {
    (TypeMultiplier(t) * 2) + SizeMultiplier(s) + ElementPower(e)
  }

  function CalculateThreat(health: nat, attack: nat): nat {
    (health / 10) + (attack / 2)
  }

  function CreateMonster(t: MonsterType, s: MonsterSize, e: Element): Monster
    ensures CreateMonster(t, s, e).Valid()
  {
    var hp := CalculateHealth(t, s, e);
    // Add +1 to ensure valid non-zero stats even for the weakest combination
    var health := if hp == 0 then 1 else hp;
    var atk := CalculateAttack(t, s, e);
    var attack := if atk == 0 then 1 else atk;
    var threat := CalculateThreat(health, attack);
    var finalThreat := if threat == 0 then 1 else threat;

    Monster(GenerateName(t, s, e), t, s, e, health, attack, finalThreat)
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generation Lists
  // ═══════════════════════════════════════════════════════════════════

  method GenerateAllForType(t: MonsterType) returns (result: seq<Monster>)
    ensures |result| == |SizesSeq| * |ElementsSeq|
  {
    result := [];
    var si := 0;
    while si < |SizesSeq|
      invariant 0 <= si <= |SizesSeq|
      invariant |result| == si * |ElementsSeq|
    {
      var ei := 0;
      while ei < |ElementsSeq|
        invariant 0 <= ei <= |ElementsSeq|
        invariant |result| == si * |ElementsSeq| + ei
      {
        result := result + [CreateMonster(t, SizesSeq[si], ElementsSeq[ei])];
        ei := ei + 1;
      }
      si := si + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Print Output
  // ═══════════════════════════════════════════════════════════════════

  method {:print} PrintMonster(m: Monster) {
    print m.name;
    print " | HP: ";
    print m.healthPool;
    print " | ATK: ";
    print m.attackDamage;
    print " | Threat Level: ";
    print m.threatRating;
    print "\n";
  }

  method {:print} PrintMonsters(monsters: seq<Monster>) {
    var i := 0;
    while i < |monsters|
      invariant 0 <= i <= |monsters|
    {
      PrintMonster(monsters[i]);
      i := i + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Verified Logic Examples
  // ═══════════════════════════════════════════════════════════════════

  method ExampleCreation() {
    var raidBoss := CreateMonster(Dragon, Gargantuan, Dark);
    assert raidBoss.healthPool == 370;
    assert raidBoss.attackDamage == 75;
    assert raidBoss.threatRating == 74;

    var weakGoblin := CreateMonster(Goblin, Small, None);
    assert weakGoblin.healthPool == 20;
    assert weakGoblin.attackDamage == 5;
    assert weakGoblin.threatRating == 4;
  }

  method ExampleGeneration() {
    var allDragons := GenerateAllForType(Dragon);
    assert |allDragons| == 48; // 6 * 8
  }

  method {:print} MainMonsters() {
    var dragons := GenerateAllForType(Dragon);
    var goblins := GenerateAllForType(Goblin);
    
    print "=== MONSTER CODEX ===\n";
    PrintMonsters(dragons);
    print "\n";
    PrintMonsters(goblins);
  }
}
