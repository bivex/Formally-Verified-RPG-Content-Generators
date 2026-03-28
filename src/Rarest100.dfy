include "Weapons.dfy"

// ═══════════════════════════════════════════════════════════════════════
//  Rarest100 — Top-100 hardest-to-obtain items in the gacha engine
//
//  Formal difficulty model:
//    Score(ref, substat) = ref * 1000 + SubstatPriority(substat) * 10
//
//  Why refinement dominates: obtaining R5 refinement requires 5 copies of
//  the same 5★ weapon.  On LimitedWeapon banner (75/25 featured rate,
//  epitomized path guarantees 2nd copy at most) the worst-case pull cost
//  per copy is:  HARD_PITY_WEAPON * 2  =  80 * 2  =  160 pulls / copy.
//  So R5 worst case = 5 * 160 = 800 pulls = 128 000 primogems.
//
//  Substat priority: CritDMG(7) > CritRate(6) > ATK%(5) >
//                    EnergyRecharge(4) > ElemMastery(3) >
//                    HP%(2) > DEF%(1)
//
//  Result composition (all 5★ star-rating):
//    Ranks   1–35  :  ref=5, all 7 substats × 5 weapon types
//    Ranks  36–70  :  ref=4, all 7 substats × 5 weapon types
//    Ranks  71–100 :  ref=3, top-6 substats × 5 weapon types  (DEF% excluded)
//
//  Formally proved:
//    • |result| == 100
//    • ∀ i, result[i].Valid()
//    • Score is strictly decreasing across the three tiers
// ═══════════════════════════════════════════════════════════════════════

module Rarest100 {
  import opened Weapons
  import opened Characters

  // ─── Difficulty constants ─────────────────────────────────────────

  const WEAPON_HARD_PITY          : nat := 80
  const EPITOMIZED_FACTOR         : nat := 2   // worst-case copies per pull cycle
  const PULLS_PER_COPY_WORST_CASE : nat := WEAPON_HARD_PITY * EPITOMIZED_FACTOR  // 160
  const PRIMOS_PER_PULL           : nat := 160

  // ─── Substat meta-priority ────────────────────────────────────────

  function SubstatPriority(s: Substat): nat {
    match s
      case CritDMG()        => 7
      case CritRate()       => 6
      case ATK_Pct()        => 5
      case EnergyRecharge() => 4
      case ElemMastery()    => 3
      case HP_Pct()         => 2
      case DEF_Pct()        => 1
  }

  // ─── Difficulty score ─────────────────────────────────────────────

  function DifficultyScore(ref: nat, s: Substat): nat
    requires MIN_REF <= ref <= MAX_REF
  {
    ref * 1000 + SubstatPriority(s) * 10
  }

  function WorstCasePulls(ref: nat): nat
    requires MIN_REF <= ref <= MAX_REF
  {
    ref * PULLS_PER_COPY_WORST_CASE
  }

  function WorstCasePrimos(ref: nat): nat
    requires MIN_REF <= ref <= MAX_REF
  {
    WorstCasePulls(ref) * PRIMOS_PER_PULL
  }

  // ─── Proved ordering ──────────────────────────────────────────────

  // Higher refinement → strictly higher score regardless of substat
  lemma HigherRefDominates(r1: nat, r2: nat, s1: Substat, s2: Substat)
    requires MIN_REF <= r1 <= MAX_REF
    requires MIN_REF <= r2 <= MAX_REF
    requires r1 > r2
    ensures DifficultyScore(r1, s1) > DifficultyScore(r2, s2)
  {
    // r1 >= r2 + 1, so r1*1000 >= r2*1000 + 1000
    // SubstatPriority <= 7, so substat contribution <= 70
    // 1000 > 70 * 2 ensures ref gap always wins
  }

  // Higher priority substat (same ref) → strictly higher score
  lemma HigherSubstatWins(ref: nat, s1: Substat, s2: Substat)
    requires MIN_REF <= ref <= MAX_REF
    requires SubstatPriority(s1) > SubstatPriority(s2)
    ensures DifficultyScore(ref, s1) > DifficultyScore(ref, s2)
  {}

  // ─── Generation orders ────────────────────────────────────────────

  // Substats in descending priority order
  const SubstatOrder : seq<Substat> :=
    [CritDMG, CritRate, ATK_Pct, EnergyRecharge, ElemMastery, HP_Pct, DEF_Pct]

  // Weapon types in descending meta relevance
  const TypeOrder : seq<WeaponType> :=
    [Sword, Catalyst, Polearm, Claymore, Bow]

  // Top-6 substats (all except DEF_Pct) for ref=3 tier
  const SubstatOrderTop6 : seq<Substat> :=
    [CritDMG, CritRate, ATK_Pct, EnergyRecharge, ElemMastery, HP_Pct]

  // ─── Size lemmas (help Dafny close arithmetic goals) ──────────────

  lemma SubstatOrderSize()  ensures |SubstatOrder|     == 7 {}
  lemma TypeOrderSize()     ensures |TypeOrder|        == 5 {}
  lemma SubstatTop6Size()   ensures |SubstatOrderTop6| == 6 {}

  // ─── Top-100 generator ────────────────────────────────────────────

  method Top100Weapons() returns (result: seq<Weapon>)
    ensures |result| == 100
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    SubstatOrderSize(); TypeOrderSize(); SubstatTop6Size();
    result := [];

    // ── Tier 1: ref=5, 7 substats × 5 types = 35 (ranks 1-35) ──────
    var si := 0;
    while si < |SubstatOrder|
      invariant 0 <= si <= |SubstatOrder|
      invariant |result| == si * |TypeOrder|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var ti := 0;
      while ti < |TypeOrder|
        invariant 0 <= ti <= |TypeOrder|
        invariant |result| == si * |TypeOrder| + ti
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        result := result + [CreateWeapon(TypeOrder[ti], R5, SubstatOrder[si], 5)];
        ti := ti + 1;
      }
      si := si + 1;
    }
    assert |result| == 35;

    // ── Tier 2: ref=4, 7 substats × 5 types = 35 (ranks 36-70) ─────
    si := 0;
    while si < |SubstatOrder|
      invariant 0 <= si <= |SubstatOrder|
      invariant |result| == 35 + si * |TypeOrder|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var ti := 0;
      while ti < |TypeOrder|
        invariant 0 <= ti <= |TypeOrder|
        invariant |result| == 35 + si * |TypeOrder| + ti
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        result := result + [CreateWeapon(TypeOrder[ti], R5, SubstatOrder[si], 4)];
        ti := ti + 1;
      }
      si := si + 1;
    }
    assert |result| == 70;

    // ── Tier 3: ref=3, top-6 substats × 5 types = 30 (ranks 71-100) ─
    si := 0;
    while si < |SubstatOrderTop6|
      invariant 0 <= si <= |SubstatOrderTop6|
      invariant |result| == 70 + si * |TypeOrder|
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var ti := 0;
      while ti < |TypeOrder|
        invariant 0 <= ti <= |TypeOrder|
        invariant |result| == 70 + si * |TypeOrder| + ti
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        result := result + [CreateWeapon(TypeOrder[ti], R5, SubstatOrderTop6[si], 3)];
        ti := ti + 1;
      }
      si := si + 1;
    }
    assert |result| == 100;
  }

  // ─── Print ────────────────────────────────────────────────────────

  method {:print} PrintRarest(w: Weapon, rank: nat)
    requires MIN_REF <= w.refinement <= MAX_REF
  {
    print "[#"; print rank; print "] ";
    print w.name;
    print " | ATK:"; print w.baseATK;
    print " | "; print SubstatStr(w.substat); print ":"; print w.substatValue;
    print " | Score:"; print DifficultyScore(w.refinement, w.substat);
    print " | WorstCase:"; print WorstCasePulls(w.refinement); print " pulls";
    print " | ~"; print WorstCasePrimos(w.refinement); print " primos";
    print "\n";
  }

  method {:print} MainRarest100() {
    print "╔══════════════════════════════════════════════════════════════════╗\n";
    print "║        TOP 100 HARDEST-TO-OBTAIN ITEMS                          ║\n";
    print "╠══════════════════════════════════════════════════════════════════╣\n";
    print "║  Score  = ref * 1000 + substat_priority * 10                    ║\n";
    print "║  Pulls  = ref * 160  (hard_pity=80 * 2 epitomized copies)       ║\n";
    print "║  Primos = pulls * 160                                            ║\n";
    print "║  Tier 1 (ranks   1-35): R5 ref=5  score 5010-5070               ║\n";
    print "║  Tier 2 (ranks  36-70): R5 ref=4  score 4010-4070               ║\n";
    print "║  Tier 3 (ranks 71-100): R5 ref=3  score 3020-3070  (no DEF%)    ║\n";
    print "╚══════════════════════════════════════════════════════════════════╝\n\n";

    var items := Top100Weapons();
    var i := 0;
    while i < |items|
      invariant 0 <= i <= |items|
    {
      PrintRarest(items[i], i + 1);
      i := i + 1;
    }
  }
}
