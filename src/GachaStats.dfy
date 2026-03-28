include "Characters.dfy"
include "Weapons.dfy"
include "Banners.dfy"
include "Pity.dfy"
include "Economy.dfy"
include "Pulls.dfy"

module GachaStats {
  import opened Characters
  import opened Weapons
  import opened Banners
  import Pi = Pity
  import E  = Economy
  import Pu = Pulls

  // --- Dimension constants ---

  const CHAR_ELEMENTS  : nat := 7
  const CHAR_WEAPONS   : nat := 5
  const CHAR_RARITIES  : nat := 3
  const WEAPON_SUBSTATS: nat := 7
  const WEAPON_REFS    : nat := 5
  const BANNER_TYPES   : nat := 3
  const PITY_5STAR_STATES : nat := Pi.HARD_PITY_5STAR + 1   // 91
  const PITY_4STAR_STATES : nat := Pi.HARD_PITY_4STAR + 1   // 11
  const GUARANTEED_STATES : nat := 2
  const ECONOMY_TIERS  : nat := 180
  const PULL_SCENARIOS : nat := (Pi.HARD_PITY_5STAR + 1) * 2  // 182

  // --- Totals ---

  const TOTAL_CHARACTERS : nat := CHAR_ELEMENTS * CHAR_WEAPONS * CHAR_RARITIES          // 105
  const TOTAL_WEAPONS    : nat := CHAR_WEAPONS * CHAR_RARITIES * WEAPON_SUBSTATS * WEAPON_REFS  // 525
  const TOTAL_BANNERS    : nat := BANNER_TYPES * CHAR_ELEMENTS * CHAR_WEAPONS            // 105
  const TOTAL_PITY_STATES: nat := PITY_5STAR_STATES * PITY_4STAR_STATES * GUARANTEED_STATES     // 2002
  const TOTAL_ECONOMY    : nat := ECONOMY_TIERS                                          // 180
  const TOTAL_PULLS      : nat := PULL_SCENARIOS                                         // 182
  const GRAND_TOTAL      : nat := TOTAL_CHARACTERS + TOTAL_WEAPONS + TOTAL_BANNERS +
                                  TOTAL_PITY_STATES + TOTAL_ECONOMY + TOTAL_PULLS        // 3099

  // --- Proofs ---

  lemma DimensionsMatchModules()
    ensures |Elements|    == CHAR_ELEMENTS
    ensures |WeaponTypes| == CHAR_WEAPONS
    ensures |Rarities|    == CHAR_RARITIES
    ensures |Substats|    == WEAPON_SUBSTATS
    ensures |BannerTypes| == BANNER_TYPES
  {}

  lemma TotalsAreCorrect()
    ensures TOTAL_CHARACTERS  == 105
    ensures TOTAL_WEAPONS     == 525
    ensures TOTAL_BANNERS     == 105
    ensures TOTAL_PITY_STATES == 2002
    ensures TOTAL_ECONOMY     == 180
    ensures TOTAL_PULLS       == 182
    ensures GRAND_TOTAL       == 3099
  {}

  // --- Entry point ---

  method {:print} MainGachaStats() {
    print "╔══════════════════════════════════════════════════════════════╗\n";
    print "║          GACHA ENGINE — CONTENT STATISTICS                  ║\n";
    print "╠══════════╦══════════════════════════════════════════════════╣\n";
    print "║  Module  ║  Count  Dimensions                               ║\n";
    print "╠══════════╬══════════════════════════════════════════════════╣\n";
    print "║ Chars    ║  "; print TOTAL_CHARACTERS;
    print "    = "; print CHAR_ELEMENTS; print " elem x "; print CHAR_WEAPONS;
    print " wtype x "; print CHAR_RARITIES; print " rar\n";
    print "║ Weapons  ║  "; print TOTAL_WEAPONS;
    print "    = "; print CHAR_WEAPONS; print " wtype x "; print CHAR_RARITIES;
    print " rar x "; print WEAPON_SUBSTATS; print " sub x "; print WEAPON_REFS; print " ref\n";
    print "║ Banners  ║  "; print TOTAL_BANNERS;
    print "    = "; print BANNER_TYPES; print " type x "; print CHAR_ELEMENTS;
    print " elem x "; print CHAR_WEAPONS; print " wtype\n";
    print "║ Pity     ║  "; print TOTAL_PITY_STATES;
    print "   = "; print PITY_5STAR_STATES; print " s5 x "; print PITY_4STAR_STATES;
    print " s4 x "; print GUARANTEED_STATES; print " gtd\n";
    print "║ Economy  ║  "; print TOTAL_ECONOMY;
    print "    = pull tiers 1..180\n";
    print "║ Pulls    ║  "; print TOTAL_PULLS;
    print "    = "; print PITY_5STAR_STATES; print " since5 x "; print GUARANTEED_STATES; print " gtd\n";
    print "╠══════════╩══════════════════════════════════════════════════╣\n";
    print "║  GRAND TOTAL: "; print GRAND_TOTAL; print "                                   ║\n";
    print "╠══════════════════════════════════════════════════════════════╣\n";
    print "║  PITY MODEL                                                  ║\n";
    print "║  Hard pity 5star: pull "; print Pi.HARD_PITY_5STAR; print "\n";
    print "║  Soft pity start: pull "; print Pi.SOFT_PITY_START; print "\n";
    print "║  Hard pity 4star: pull "; print Pi.HARD_PITY_4STAR; print "\n";
    print "║  Expected featured 5star: "; print E.EXPECTED_FEATURED_PULLS; print " pulls\n";
    print "║  Expected featured cost:  "; print E.EXPECTED_FEATURED_PULLS * E.PRIMOS_PER_PULL; print " primos\n";
    print "║  F2P monthly: "; print E.F2P_PULLS_MONTHLY; print " pulls = "; print E.F2P_PRIMOS_MONTHLY; print " primos\n";
    print "║  Months to save (expected): ";
    print (E.EXPECTED_FEATURED_PULLS * E.PRIMOS_PER_PULL) / E.F2P_PRIMOS_MONTHLY;
    print " months\n";
    print "╠══════════════════════════════════════════════════════════════╣\n";
    print "║  FORMALLY VERIFIED INVARIANTS                                ║\n";
    print "║  1. Hard pity 5star => next pull MUST be 5star               ║\n";
    print "║  2. After 50/50 loss => next 5star is guaranteed featured    ║\n";
    print "║  3. Any 5star resets both pity counters to 0                 ║\n";
    print "║  4. Non-featured 5star arms the guarantee flag               ║\n";
    print "║  5. All characters: HP>0, ATK>0, DEF>0                      ║\n";
    print "║  6. All weapons: ATK>0, substatValue>0, 1<=ref<=5            ║\n";
    print "║  7. All banners: rate5star<rate4star, softPity<hardPity      ║\n";
    print "║  8. Economy: primoCost == pullCount * 160 (exact)            ║\n";
    print "╚══════════════════════════════════════════════════════════════╝\n";
  }
}
