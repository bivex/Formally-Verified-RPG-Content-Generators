include "Monsters.dfy"
include "Spells.dfy"

module Combat {
  import M = Monsters
  import S = Spells

  // ═══════════════════════════════════════════════════════════════════
  // I. ФОРМАЛЬНАЯ МОДЕЛЬ (Entities & States)
  // ═══════════════════════════════════════════════════════════════════

  datatype PlayerState = PlayerState(
    hp: nat,
    mana: nat,
    equippedSpell: S.Spell
  ) {
    predicate Valid() {
      equippedSpell.Valid()
    }
  }

  datatype CombatEncounter = Encounter(
    player: PlayerState,
    monsterTemplate: M.Monster,
    currentMonsterHp: nat,
    turnCount: nat
  ) {
    predicate Valid() {
      player.Valid() && monsterTemplate.Valid()
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  // II. ACTIONS & STATE TRANSITIONS
  // ═══════════════════════════════════════════════════════════════════

  // Игрок может сделать Trade-Off: потратить всю ману на "Бурст", либо бить слабо, экономя ресурс
  datatype CombatAction = CastSpell | RestForMana

  // Функция перехода состояний (Transition System)
  function ResolveTurn(e: CombatEncounter, a: CombatAction): CombatEncounter
    requires e.Valid()
    // Правила игры: бой не может откатиться во времени
    ensures ResolveTurn(e, a).turnCount == e.turnCount + 1
    ensures ResolveTurn(e, a).Valid()
  {
    match a
      case CastSpell() =>
        if e.player.mana >= e.player.equippedSpell.manaCost then
          // Магическая атака успешна
          var newMana := e.player.mana - e.player.equippedSpell.manaCost;
          var dmg := e.player.equippedSpell.baseEffect;
          var newMonsterHp := if e.currentMonsterHp > dmg then e.currentMonsterHp - dmg else 0;
          
          // Ответный удар монстра: если выжил, бьет
          var monsterDmg := if newMonsterHp > 0 then e.monsterTemplate.attackDamage else 0;
          var newPlayerHp := if e.player.hp > monsterDmg then e.player.hp - monsterDmg else 0;
          
          Encounter(
            PlayerState(newPlayerHp, newMana, e.player.equippedSpell),
            e.monsterTemplate,
            newMonsterHp,
            e.turnCount + 1
          )
        else
          // Не хватило маны — пропуск хода, монстр атакует
          var newPlayerHp := if e.player.hp > e.monsterTemplate.attackDamage then e.player.hp - e.monsterTemplate.attackDamage else 0;
          Encounter(
            PlayerState(newPlayerHp, e.player.mana, e.player.equippedSpell),
            e.monsterTemplate,
            e.currentMonsterHp,
            e.turnCount + 1
          )

      case RestForMana() =>
        // Намеренный пропуск хода: регенерация 50 маны, но гарантированный урон от монстра
        var newPlayerHp := if e.player.hp > e.monsterTemplate.attackDamage then e.player.hp - e.monsterTemplate.attackDamage else 0;
        var newMana := e.player.mana + 50;
        Encounter(
          PlayerState(newPlayerHp, newMana, e.player.equippedSpell),
          e.monsterTemplate,
          e.currentMonsterHp,
          e.turnCount + 1
        )
  }

  // ═══════════════════════════════════════════════════════════════════
  // III. КОНФЛИКТНАЯ МОДЕЛЬ И ПРОВЕРКА ВОЗНАГРАЖДЕНИЯ (REWARD)
  // ═══════════════════════════════════════════════════════════════════

  // Утилитарная функция: игрок жив, а монстр мертв
  predicate IsVictory(e: CombatEncounter) {
    e.player.hp > 0 && e.currentMonsterHp == 0
  }

  // Пример верифицированного боя (Смертельная Дилемма)
  method ExampleCombat() {
    var dragon := M.CreateMonster(M.Dragon, M.Gargantuan, M.Fire);
    var nukeSpell := S.CreateSpell(S.Evocation, S.Short, S.Legendary);

    var player := PlayerState(500, 100, nukeSpell); // Игрок: 500 ХП, 100 маны
    var battle := Encounter(player, dragon, dragon.healthPool, 0);

    // Докажем жесткую механику из Spells.dfy: Легендарные спеллы стоят >= 20 маны
    assert nukeSpell.manaCost >= 20;

    // Ход 1: заклинание требует огромное количество маны, поэтому "CastSpell" пройдет
    var afterTurn1 := ResolveTurn(battle, CastSpell());
    
    // Ход 2: восстанавливаем ману, получая урон
    var afterTurn2 := ResolveTurn(afterTurn1, RestForMana());

    // Dafny доказывает, что счетчик ходов отработал корректно
    assert afterTurn2.turnCount == 2;
  }
}
