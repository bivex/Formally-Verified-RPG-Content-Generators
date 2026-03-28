include "MagicItems.dfy"
include "Monsters.dfy"
include "Spells.dfy"
include "NPCs.dfy"

module Balancer {
  import MI = MagicItems
  import MO = Monsters
  import SP = Spells
  import NP = NPCs

  // ═══════════════════════════════════════════════════════════════════
  // I. ПРОВЕРКА СПРАВЕДЛИВОСТИ РЕДКОСТИ (Rarity Fairness)
  // ═══════════════════════════════════════════════════════════════════

  // Лемма: Доказываем, что в нашей системе Мифический предмет 
  // ВСЕГДА сильнее Обычного при прочих равных условиях.
  lemma RarityAlwaysMatters(e: MI.Element, t: MI.ItemType)
    ensures MI.CreateItem(e, t, MI.Common).power < MI.CreateItem(e, t, MI.Mythical).power
  {
    // Dafny доказывает это автоматически через развертывание функций CalculatePower
  }

  // ═══════════════════════════════════════════════════════════════════
  // II. АУДИТ БОЕВОГО БАЛАНСА (Combat Sanity)
  // ═══════════════════════════════════════════════════════════════════

  // Предикат "Честного вызова": Монстр не должен убивать игрока с 100 HP за один удар,
  // если его рейтинг угрозы (Threat) низкий.
  predicate IsFairLowLevelMonster(m: MO.Monster) {
    m.threatRating < 10 ==> m.attackDamage < 100
  }

  method AuditMonsterManual() {
    var weakGoblin := MO.CreateMonster(MO.Goblin, MO.Small, MO.None);
    // Проверка: Слабый гоблин должен соответствовать критерию честности
    assert IsFairLowLevelMonster(weakGoblin);
  }

  // ═══════════════════════════════════════════════════════════════════
  // III. ЭКОНОМИЧЕСКИЙ АУДИТ (Economic Audit)
  // ═══════════════════════════════════════════════════════════════════

  // Глобальный Закон Сословий: Дворянин ВСЕГДА богаче Торговца, 
  // независимо от сочетания рас (например, богатый Гном против бедного Полурослика).
  lemma NobleAlwaysWealthierThanMerchant(r1: NP.Race, r2: NP.Race)
    ensures NP.CreateNPC(r1, NP.Noble, NP.TrueNeutral).goldCoins > NP.CreateNPC(r2, NP.Merchant, NP.TrueNeutral).goldCoins
  {
     // Эта лемма заставит Dafny проверить ВСЕ 64 комбинации пар рас.
  }

  // ═══════════════════════════════════════════════════════════════════
  // IV. МАГИЧЕСКИЙ АУДИТ (Magic Efficiency)
  // ═══════════════════════════════════════════════════════════════════

  // "Закон Эффективности": Чем больше урон заклинания, тем больше должен быть его манакост.
  // Мы ищем "имбалансные" спеллы, где цена/качество слишком выгодны.
  predicate IsSpellEfficient(s: SP.Spell) {
    s.baseEffect > 0 ==> (s.manaCost as real / s.baseEffect as real) < 10.0
  }

  // ═══════════════════════════════════════════════════════════════════
  // V. ГЛОБАЛЬНЫЙ ПРОВЕРЯТОР (The Balancer)
  // ═══════════════════════════════════════════════════════════════════

  method {:print} RunFullBalanceAudit() {
    print "--- STARTING FORMAL BALANCE AUDIT ---\n";

    // 1. Проверяем экономику всех рас
    var ri := 0;
    while ri < |NP.RacesSeq| 
      invariant 0 <= ri <= |NP.RacesSeq|
    {
      var noble := NP.CreateNPC(NP.RacesSeq[ri], NP.Noble, NP.TrueNeutral);
      var thief := NP.CreateNPC(NP.RacesSeq[ri], NP.Thief, NP.TrueNeutral);
      
      if noble.goldCoins <= thief.goldCoins {
        print "CRITICAL: Economic Imbalance found in race: ";
        print NP.RacesSeq[ri]; print "\n";
      }
      ri := ri + 1;
    }

    // 2. Ищем "стеклянные пушки" (монстры с огромным уроном при мизерном HP)
    var monster := MO.CreateMonster(MO.Beast, MO.Small, MO.Fire);
    if monster.attackDamage > monster.healthPool * 2 {
       print "WARNING: Glass Cannon detected: "; print monster.name; print "\n";
    }

    print "--- AUDIT COMPLETED SUCCESSFULLY ---\n";
  }

  method {:print} Main() {
    RunFullBalanceAudit();
  }
}
