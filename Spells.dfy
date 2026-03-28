module Spells {

  // ═══════════════════════════════════════════════════════════════════
  // Types
  // ═══════════════════════════════════════════════════════════════════

  datatype School = Evocation | Abjuration | Conjuration | Necromancy | Illusion | Transmutation
  datatype Distance = Self | Touch | Short | Medium | Long
  datatype PowerLevel = Cantrip | Apprentice | Journeyman | Master | Grandmaster | Legendary

  const SchoolsSeq   : seq<School>     := [Evocation, Abjuration, Conjuration, Necromancy, Illusion, Transmutation]
  const DistancesSeq : seq<Distance>   := [Self, Touch, Short, Medium, Long]
  const LevelsSeq    : seq<PowerLevel> := [Cantrip, Apprentice, Journeyman, Master, Grandmaster, Legendary]

  // ═══════════════════════════════════════════════════════════════════
  // Data Structure
  // ═══════════════════════════════════════════════════════════════════

  datatype Spell = Spell(
    name: string,
    school: School,
    distance: Distance,
    level: PowerLevel,
    manaCost: nat,
    cooldown: nat,
    baseEffect: nat
  ) {
    predicate Valid() {
      // Rule 1: Master and higher spells CANNOT be cast for free
      (level == Grandmaster() || level == Legendary() || level == Master() ==> manaCost >= 20) &&
      
      // Rule 2: If a spell affects things across a Long distance, it must cost at least some mana (except cantrips)
      (distance == Long() && level != Cantrip() ==> manaCost >= 10) &&
      
      // Rule 3: Balance constraint: high impact necessarily implies high cost or cooldown
      (baseEffect > 100 ==> manaCost >= 80 || cooldown >= 3)
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Properties and Balance Rules
  // ═══════════════════════════════════════════════════════════════════

  function LevelMultiplier(l: PowerLevel): nat {
    match l
      case Cantrip()     => 1
      case Apprentice()  => 3
      case Journeyman()  => 8
      case Master()      => 20
      case Grandmaster() => 40
      case Legendary()   => 100
  }

  function SchoolBaseEffect(s: School): nat {
    match s
      case Evocation()     => 30 // High damage
      case Necromancy()    => 25 // Drain/Curse
      case Conjuration()   => 20 // Summons
      case Abjuration()    => 15 // Shields
      case Transmutation() => 10 // Utility
      case Illusion()      => 5  // Pure trickery
  }

  function DistanceCost(d: Distance): nat {
    match d
      case Long()   => 10
      case Medium() => 6
      case Short()  => 3
      case Touch()  => 1
      case Self()   => 0
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generators
  // ═══════════════════════════════════════════════════════════════════

  function GenerateName(s: School, d: Distance, l: PowerLevel): string {
    var prefix := match l {
      case Cantrip()     => "Minor "
      case Apprentice()  => "Basic "
      case Journeyman()  => "Adept "
      case Master()      => "Greater "
      case Grandmaster() => "Supreme "
      case Legendary()   => "Mythic "
    };

    var rangeStr := match d {
      case Long()   => "Sniper's "
      case Medium() => "Ranged "
      case Short()  => "Close "
      case Touch()  => "Contact "
      case Self()   => "Inner "
    };

    var spellType := match s {
      case Evocation()     => "Blast"
      case Abjuration()    => "Ward"
      case Conjuration()   => "Summoning"
      case Necromancy()    => "Curse"
      case Illusion()      => "Mirage"
      case Transmutation() => "Shift"
    };

    prefix + rangeStr + spellType
  }

  function CalculateEffect(s: School, d: Distance, l: PowerLevel): nat {
    // Pure evocation spells scaling linearly with level, and inversely with distance cost 
    // Wait, distance strictly adds utility, meaning raw effect can just be a multiplier.
    SchoolBaseEffect(s) * LevelMultiplier(l)
  }

  function CalculateMana(s: School, d: Distance, l: PowerLevel, effect: nat): nat {
    var baseMana := (effect / 5) + DistanceCost(d) * LevelMultiplier(l);
    // Enforcing validity logic gracefully
    var safeMana := if (l == Grandmaster() || l == Legendary() || l == Master()) && baseMana < 20 then 20 else baseMana;
    var finalMana := if d == Long() && l != Cantrip() && safeMana < 10 then 10 else safeMana;
    finalMana
  }

  function CalculateCooldown(l: PowerLevel): nat {
    match l
      case Legendary()   => 10
      case Grandmaster() => 5
      case Master()      => 3
      case Journeyman()  => 1
      case Apprentice()  => 0
      case Cantrip()     => 0
  }

  function CreateSpell(s: School, d: Distance, l: PowerLevel): Spell
    ensures CreateSpell(s, d, l).Valid()
  {
    var effect := CalculateEffect(s, d, l);
    var mana := CalculateMana(s, d, l, effect);
    var cd := CalculateCooldown(l);

    // Guarantee Rule 3 is satisfied. If effect > 100, we force mana or cd up if not naturally satisfied
    var finalCd := if effect > 100 && mana < 80 && cd < 3 then 3 else cd;

    Spell(GenerateName(s, d, l), s, d, l, mana, finalCd, effect)
  }

  // ═══════════════════════════════════════════════════════════════════
  // Generation Lists
  // ═══════════════════════════════════════════════════════════════════

  method GenerateAllForSchool(s: School) returns (result: seq<Spell>)
    ensures |result| == |DistancesSeq| * |LevelsSeq|
  {
    result := [];
    var di := 0;
    while di < |DistancesSeq|
      invariant 0 <= di <= |DistancesSeq|
      invariant |result| == di * |LevelsSeq|
    {
      var li := 0;
      while li < |LevelsSeq|
        invariant 0 <= li <= |LevelsSeq|
        invariant |result| == di * |LevelsSeq| + li
      {
        result := result + [CreateSpell(s, DistancesSeq[di], LevelsSeq[li])];
        li := li + 1;
      }
      di := di + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Print Output
  // ═══════════════════════════════════════════════════════════════════

  method {:print} PrintSpell(spell: Spell) {
    print spell.name;
    print " | Mana: ";
    print spell.manaCost;
    print " | CD: ";
    print spell.cooldown;
    print "s | Effect Power: ";
    print spell.baseEffect;
    print "\n";
  }

  method {:print} PrintSpells(spells: seq<Spell>) {
    var i := 0;
    while i < |spells|
      invariant 0 <= i <= |spells|
    {
      PrintSpell(spells[i]);
      i := i + 1;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Verified Logic Examples
  // ═══════════════════════════════════════════════════════════════════

  method ExampleCreation() {
    var apocalypse := CreateSpell(Evocation, Long, Legendary);
    assert apocalypse.baseEffect == 3000;
    assert apocalypse.manaCost == 1600; // 3000/5 + 10*100
    assert apocalypse.cooldown == 10;

    var touchHeal := CreateSpell(Transmutation, Touch, Cantrip);
    assert touchHeal.baseEffect == 10;
    assert touchHeal.manaCost == 3;
    assert touchHeal.cooldown == 0;
  }

  method {:print} Main() {
    var evocs := GenerateAllForSchool(Evocation);
    var illusions := GenerateAllForSchool(Illusion);
    
    print "=== GRIMOIRE OF SPELLS ===\n";
    PrintSpells(evocs);
    print "\n";
    PrintSpells(illusions);
  }
}
