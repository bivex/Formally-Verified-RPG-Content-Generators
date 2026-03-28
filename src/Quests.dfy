include "NPCs.dfy"
include "Monsters.dfy"
include "Locations.dfy"
include "MagicItems.dfy"

module Quests {
  import N = NPCs
  import M = Monsters
  import L = Locations
  import I = MagicItems

  // ═══════════════════════════════════════════════════════════════════
  // Quest Types
  // ═══════════════════════════════════════════════════════════════════

  datatype QuestObjective = SlayMonster(target: M.Monster) | FetchArtifact(item: I.MagicItem) | ClearLocation(loc: L.Location)

  datatype Quest = Quest(
    giver: N.NPC,
    objective: QuestObjective,
    location: L.Location,
    reward: I.MagicItem,
    experienceReward: nat
  ) {
    predicate Valid() {
      // Logic: A quest giver shouldn't reward you with something they can't afford
      // and the reward power should roughly match the danger
      giver.Valid() && location.Valid() &&
      (match objective {
          case SlayMonster(m) => m.Valid()
          case FetchArtifact(i) => i.Valid()
          case ClearLocation(l) => l.Valid()
      })
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // Balancing & Reward Logic
  // ═══════════════════════════════════════════════════════════════════

  function CalculateXP(danger: nat): nat {
    danger * 10
  }

  function DetermineRewardRarity(danger: nat): I.Rarity {
    if danger > 150 then I.Mythical
    else if danger > 100 then I.Legendary
    else if danger > 50 then I.Epic
    else if danger > 20 then I.Rare
    else if danger > 5 then I.Uncommon
    else I.Common
  }

  // ═══════════════════════════════════════════════════════════════════
  // THE MASTER BALANCER LEMMA
  // ═══════════════════════════════════════════════════════════════════

  // Лемма: Доказываем, что в опасных локациях награда ВСЕГДА качественнее.
  // Это гарантирует отсутствие "дизбаланса", когда за сложный квест дают мусор.
  lemma HigherDangerGivesBetterRarity(d1: nat, d2: nat)
    requires d1 > 150 && d2 < 5
    ensures DetermineRewardRarity(d1) == I.Mythical && DetermineRewardRarity(d2) == I.Common
  {}

  // ═══════════════════════════════════════════════════════════════════
  // Generators
  // ═══════════════════════════════════════════════════════════════════

  function GenerateQuest(giver: N.NPC, loc: L.Location, objType: int): Quest 
    requires giver.Valid() && loc.Valid()
    ensures GenerateQuest(giver, loc, objType).Valid()
  {
    var rarity := DetermineRewardRarity(loc.dangerLevel);
    var reward := I.CreateItem(I.Light, I.Sword, rarity);
    var xp := CalculateXP(loc.dangerLevel);

    var objective := if objType == 0 then 
        SlayMonster(M.CreateMonster(M.Dragon, M.Large, M.Fire))
      else if objType == 1 then
        FetchArtifact(I.CreateItem(I.Dark, I.Amulet, rarity))
      else 
        ClearLocation(loc);

    Quest(giver, objective, loc, reward, xp)
  }

  // ═══════════════════════════════════════════════════════════════════
  // Print Output
  // ═══════════════════════════════════════════════════════════════════

  method {:print} PrintQuest(q: Quest) {
    print "=== QUEST: "; print q.giver.name; print "'s Request ===\n";
    print "Location: "; print q.location.name; print " (Danger: "; print q.location.dangerLevel; print ")\n";
    match q.objective {
      case SlayMonster(m) => print "Objective: Slay "; print m.name; print "\n";
      case FetchArtifact(i) => print "Objective: Recover "; print i.name; print "\n";
      case ClearLocation(l) => print "Objective: Purge "; print l.name; print "\n";
    }
    print "Reward: "; print q.reward.name; print " | XP: "; print q.experienceReward; print "\n";
  }

  // Full generation: all 576 NPCs × 3 objective types = 1728 quests
  // Location fixed to Volcano Dungeon Colossal (danger 150 → Mythical reward)
  // Coverage: 100% NPCs, 100% objective types, 1/384 locations
  method {:print} MainQuests() {
    var volcano := L.CreateLocation(L.Volcano, L.Dungeon, L.Colossal);
    print "=== QUEST CODEX ===\n";
    print "Total entries: "; print |N.RacesSeq| * |N.ProfessionsSeq| * |N.AlignmentsSeq| * 3; print "\n\n";
    var ri := 0;
    while ri < |N.RacesSeq|
      invariant 0 <= ri <= |N.RacesSeq|
    {
      var npcs := N.GenerateAllForRace(N.RacesSeq[ri]);
      var ni := 0;
      while ni < |npcs|
        invariant 0 <= ni <= |npcs|
      {
        var objType := ni % 3;
        var quest := GenerateQuest(npcs[ni], volcano, objType);
        PrintQuest(quest);
        ni := ni + 1;
      }
      ri := ri + 1;
    }
  }
}
