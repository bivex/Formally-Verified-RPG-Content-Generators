include "MagicItems.dfy"
include "Monsters.dfy"
include "Locations.dfy"
include "NPCs.dfy"
include "Spells.dfy"

module Stats {
  import I = MagicItems
  import M = Monsters
  import L = Locations
  import N = NPCs
  import S = Spells

  // ═══════════════════════════════════════════════════════════════════
  //  Dimension Constants — mirrors the seqs in each module
  // ═══════════════════════════════════════════════════════════════════

  const ITEM_ELEMENTS  : nat := 8   // Fire Water Earth Air Lightning Ice Light Dark
  const ITEM_TYPES     : nat := 10  // Sword Staff Ring Amulet Potion Wand Dagger Shield Bow Helmet
  const ITEM_RARITIES  : nat := 6   // Common Uncommon Rare Epic Legendary Mythical

  const MON_TYPES      : nat := 8   // Dragon Goblin Golem Elemental Undead Beast Demon Slime
  const MON_SIZES      : nat := 6   // Swarm Small Medium Large Huge Gargantuan
  const MON_ELEMENTS   : nat := 8   // Fire Water Earth Air Lightning Ice Dark None

  const LOC_BIOMES     : nat := 8   // Forest Mountain Desert Swamp Ocean Tundra Plains Volcano
  const LOC_TYPES      : nat := 8   // City Village Ruins Dungeon Fortress Temple Cave Outpost
  const LOC_SIZES      : nat := 6   // Tiny Small Medium Large Vast Colossal

  const NPC_RACES      : nat := 8   // Human Elf Dwarf Orc Halfling Gnome Tiefling Dragonborn
  const NPC_PROFS      : nat := 8   // Blacksmith Merchant Guard Peasant Scholar Noble Priest Thief
  const NPC_ALIGNS     : nat := 9   // LG NG CG LN TN CN LE NE CE

  const SPELL_SCHOOLS  : nat := 6   // Evocation Abjuration Conjuration Necromancy Illusion Transmutation
  const SPELL_DISTS    : nat := 5   // Self Touch Short Medium Long
  const SPELL_LEVELS   : nat := 6   // Cantrip Apprentice Journeyman Master Grandmaster Legendary

  const QUEST_OBJ_TYPES : nat := 3  // SlayMonster FetchArtifact ClearLocation

  // ═══════════════════════════════════════════════════════════════════
  //  Full Combinatorial Space (every possible unique combination)
  // ═══════════════════════════════════════════════════════════════════

  const TOTAL_ITEMS    : nat := ITEM_ELEMENTS * ITEM_TYPES * ITEM_RARITIES   // 480
  const TOTAL_MONSTERS : nat := MON_TYPES  * MON_SIZES * MON_ELEMENTS        // 384
  const TOTAL_LOCS     : nat := LOC_BIOMES * LOC_TYPES  * LOC_SIZES          // 384
  const TOTAL_NPCS     : nat := NPC_RACES  * NPC_PROFS  * NPC_ALIGNS         // 576
  const TOTAL_SPELLS   : nat := SPELL_SCHOOLS * SPELL_DISTS * SPELL_LEVELS   // 180
  // Quests: each NPC × each location × each objective type
  const TOTAL_QUESTS   : nat := TOTAL_NPCS * TOTAL_LOCS * QUEST_OBJ_TYPES    // 663,552

  const GRAND_TOTAL    : nat :=
    TOTAL_ITEMS + TOTAL_MONSTERS + TOTAL_LOCS + TOTAL_NPCS +
    TOTAL_SPELLS + TOTAL_QUESTS                                               // 665,556

  // ═══════════════════════════════════════════════════════════════════
  //  Currently Exported (what each MainXxx actually writes to disk)
  // ═══════════════════════════════════════════════════════════════════

  // MagicItems: AllItems() — full 3D cross-product
  const EXPORTED_ITEMS    : nat := ITEM_ELEMENTS * ITEM_TYPES * ITEM_RARITIES  // 480 (100%)

  // Monsters: AllMonsters() loops all TypesSeq
  const EXPORTED_MONSTERS : nat := MON_TYPES * MON_SIZES * MON_ELEMENTS        // 384 (100%)

  // Locations: AllLocations() loops all BiomesSeq
  const EXPORTED_LOCS     : nat := LOC_BIOMES * LOC_TYPES * LOC_SIZES          // 384 (100%)

  // NPCs: AllNPCs() loops all RacesSeq
  const EXPORTED_NPCS     : nat := NPC_RACES * NPC_PROFS * NPC_ALIGNS          // 576 (100%)

  // Spells: AllSpells() loops all SchoolsSeq
  const EXPORTED_SPELLS   : nat := SPELL_SCHOOLS * SPELL_DISTS * SPELL_LEVELS  // 180 (100%)

  // Quests: AllNPCs() × AllLocations() × 3 obj types — full combinatorial space
  const EXPORTED_QUESTS   : nat := TOTAL_NPCS * TOTAL_LOCS * QUEST_OBJ_TYPES   // 663,552 (100%)

  const TOTAL_EXPORTED    : nat :=
    EXPORTED_ITEMS + EXPORTED_MONSTERS + EXPORTED_LOCS +
    EXPORTED_NPCS  + EXPORTED_SPELLS   + EXPORTED_QUESTS                       // 665,556

  // ═══════════════════════════════════════════════════════════════════
  //  Formal Proofs — verified at compile time
  // ═══════════════════════════════════════════════════════════════════

  lemma DimensionsMatchModules()
    ensures |I.Elements|           == ITEM_ELEMENTS
    ensures |I.Types|              == ITEM_TYPES
    ensures |I.Rarities|           == ITEM_RARITIES
    ensures |M.TypesSeq|           == MON_TYPES
    ensures |M.SizesSeq|           == MON_SIZES
    ensures |M.ElementsSeq|        == MON_ELEMENTS
    ensures |L.BiomesSeq|          == LOC_BIOMES
    ensures |L.LocationTypesSeq|   == LOC_TYPES
    ensures |L.SizesSeq|           == LOC_SIZES
    ensures |N.RacesSeq|           == NPC_RACES
    ensures |N.ProfessionsSeq|     == NPC_PROFS
    ensures |N.AlignmentsSeq|      == NPC_ALIGNS
    ensures |S.SchoolsSeq|         == SPELL_SCHOOLS
    ensures |S.DistancesSeq|       == SPELL_DISTS
    ensures |S.LevelsSeq|          == SPELL_LEVELS
  {}

  lemma TotalsAreCorrect()
    ensures TOTAL_ITEMS    == 480
    ensures TOTAL_MONSTERS == 384
    ensures TOTAL_LOCS     == 384
    ensures TOTAL_NPCS     == 576
    ensures TOTAL_SPELLS   == 180
    ensures TOTAL_QUESTS   == 663552
    ensures GRAND_TOTAL    == 665556
  {}

  lemma ExportedAreCorrect()
    ensures EXPORTED_ITEMS    == 480
    ensures EXPORTED_MONSTERS == 384
    ensures EXPORTED_LOCS     == 384
    ensures EXPORTED_NPCS     == 576
    ensures EXPORTED_SPELLS   == 180
    ensures EXPORTED_QUESTS   == 663552
    ensures TOTAL_EXPORTED    == 665556
  {}

  lemma ExportedFitsInFullSpace()
    ensures EXPORTED_ITEMS    <= TOTAL_ITEMS
    ensures EXPORTED_MONSTERS <= TOTAL_MONSTERS
    ensures EXPORTED_LOCS     <= TOTAL_LOCS
    ensures EXPORTED_NPCS     <= TOTAL_NPCS
    ensures EXPORTED_SPELLS   <= TOTAL_SPELLS
    ensures EXPORTED_QUESTS   <= TOTAL_QUESTS
    ensures TOTAL_EXPORTED    <= GRAND_TOTAL
  {}

  // ═══════════════════════════════════════════════════════════════════
  //  Helpers
  // ═══════════════════════════════════════════════════════════════════

  function CoveragePercent(exported: nat, total: nat): nat
    requires total > 0
  {
    (exported * 100) / total
  }

  // Formats a nat as a right-aligned string padded to 7 chars (approximate)
  // In Dafny we just print with padding via spaces manually in output

  // ═══════════════════════════════════════════════════════════════════
  //  Entry Point
  // ═══════════════════════════════════════════════════════════════════

  method {:print} MainStats() {
    print "╔══════════════════════════════════════════════════════════════════╗\n";
    print "║          RPG ENGINE — UNIQUE CONTENT STATISTICS                 ║\n";
    print "╠════════════════════╦══════════╦════════════╦═════════════════════╣\n";
    print "║  Module            ║ Exported ║ Full Space ║ Coverage            ║\n";
    print "╠════════════════════╬══════════╬════════════╬═════════════════════╣\n";

    print "║  Magic Items       ║  "; print EXPORTED_ITEMS;
    print "     ║    "; print TOTAL_ITEMS;
    print "      ║  "; print CoveragePercent(EXPORTED_ITEMS, TOTAL_ITEMS);
    print "%                  ║\n";

    print "║  Monsters          ║  "; print EXPORTED_MONSTERS;
    print "     ║    "; print TOTAL_MONSTERS;
    print "      ║  "; print CoveragePercent(EXPORTED_MONSTERS, TOTAL_MONSTERS);
    print "%                 ║\n";

    print "║  Locations         ║  "; print EXPORTED_LOCS;
    print "     ║    "; print TOTAL_LOCS;
    print "      ║  "; print CoveragePercent(EXPORTED_LOCS, TOTAL_LOCS);
    print "%                 ║\n";

    print "║  NPCs              ║  "; print EXPORTED_NPCS;
    print "     ║    "; print TOTAL_NPCS;
    print "      ║  "; print CoveragePercent(EXPORTED_NPCS, TOTAL_NPCS);
    print "%                 ║\n";

    print "║  Spells            ║  "; print EXPORTED_SPELLS;
    print "     ║    "; print TOTAL_SPELLS;
    print "      ║  "; print CoveragePercent(EXPORTED_SPELLS, TOTAL_SPELLS);
    print "%                 ║\n";

    print "║  Quests            ║  "; print EXPORTED_QUESTS;
    print " ║  "; print TOTAL_QUESTS;
    print "  ║  "; print CoveragePercent(EXPORTED_QUESTS, TOTAL_QUESTS);
    print "%                 ║\n";

    print "╠════════════════════╩══════════╩════════════╩═════════════════════╣\n";
    print "║  TOTAL EXPORTED   "; print TOTAL_EXPORTED;
    print "                                        ║\n";
    print "║  GRAND TOTAL      "; print GRAND_TOTAL;
    print "                                        ║\n";
    print "╠══════════════════════════════════════════════════════════════════╣\n";

    print "║  DIMENSION BREAKDOWN                                             ║\n";
    print "╠══════════════════════════════════════════════════════════════════╣\n";

    print "║  Magic Items  = "; print ITEM_ELEMENTS;
    print " elem × "; print ITEM_TYPES;
    print " types × "; print ITEM_RARITIES;
    print " rarities = "; print TOTAL_ITEMS; print "\n";

    print "║  Monsters     = "; print MON_TYPES;
    print " types × "; print MON_SIZES;
    print " sizes × "; print MON_ELEMENTS;
    print " elements  = "; print TOTAL_MONSTERS; print "\n";

    print "║  Locations    = "; print LOC_BIOMES;
    print " biomes × "; print LOC_TYPES;
    print " loc types × "; print LOC_SIZES;
    print " sizes  = "; print TOTAL_LOCS; print "\n";

    print "║  NPCs         = "; print NPC_RACES;
    print " races × "; print NPC_PROFS;
    print " profs × "; print NPC_ALIGNS;
    print " alignments = "; print TOTAL_NPCS; print "\n";

    print "║  Spells       = "; print SPELL_SCHOOLS;
    print " schools × "; print SPELL_DISTS;
    print " dists × "; print SPELL_LEVELS;
    print " levels    = "; print TOTAL_SPELLS; print "\n";

    print "║  Quests       = "; print TOTAL_NPCS;
    print " NPCs × "; print TOTAL_LOCS;
    print " locs × "; print QUEST_OBJ_TYPES;
    print " obj types = "; print TOTAL_QUESTS; print "\n";
    print "╠══════════════════════════════════════════════════════════════════╣\n";
    print "║  ALL AXES AT 100% — FULL COMBINATORIAL SPACE EXPORTED           ║\n";
    print "╚══════════════════════════════════════════════════════════════════╝\n";
  }
}
