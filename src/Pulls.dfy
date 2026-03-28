include "Pity.dfy"

module Pulls {
  import P = Pity

  datatype PullScenario = PullScenario(
    startSince5Star : nat,
    startGuaranteed : bool,
    pullsToHardPity : nat,
    softPityAlready : bool,
    isAtHardPity    : bool
  ) {
    predicate Valid() {
      startSince5Star <= P.HARD_PITY_5STAR &&
      pullsToHardPity + startSince5Star == P.HARD_PITY_5STAR &&
      softPityAlready == (startSince5Star >= P.SOFT_PITY_START) &&
      isAtHardPity    == (startSince5Star == P.HARD_PITY_5STAR)
    }
  }

  function CreateScenario(s5: nat, guaranteed: bool): PullScenario
    requires s5 <= P.HARD_PITY_5STAR
    ensures CreateScenario(s5, guaranteed).Valid()
  {
    PullScenario(
      s5,
      guaranteed,
      P.HARD_PITY_5STAR - s5,
      s5 >= P.SOFT_PITY_START,
      s5 == P.HARD_PITY_5STAR
    )
  }

  // 91 since5Star values x 2 guaranteed states = 182
  method AllScenarios() returns (result: seq<PullScenario>)
    ensures |result| == (P.HARD_PITY_5STAR + 1) * 2
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var g := 0;
    while g < 2
      invariant 0 <= g <= 2
      invariant |result| == g * (P.HARD_PITY_5STAR + 1)
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var s := 0;
      while s <= P.HARD_PITY_5STAR
        invariant 0 <= s <= P.HARD_PITY_5STAR + 1
        invariant |result| == g * (P.HARD_PITY_5STAR + 1) + s
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        result := result + [CreateScenario(s, g == 1)];
        s := s + 1;
      }
      g := g + 1;
    }
  }

  method {:print} PrintScenario(sc: PullScenario) {
    print "Since5star:"; print sc.startSince5Star;
    print " | Guaranteed:"; print if sc.startGuaranteed then "YES" else "no";
    print " | PullsLeft:"; print sc.pullsToHardPity;
    print " | SoftPity:"; print if sc.softPityAlready then "ACTIVE" else "no";
    print " | AtHardPity:"; print if sc.isAtHardPity then "NOW" else "no";
    print "\n";
  }
  method {:print} PrintScenarios(scs: seq<PullScenario>) {
    var i := 0;
    while i < |scs| invariant 0 <= i <= |scs| {
      PrintScenario(scs[i]);
      i := i + 1;
    }
  }

  method {:print} MainPulls() {
    print "=== GACHA PULL SCENARIOS ===\n";
    print "Total scenarios: "; print (P.HARD_PITY_5STAR + 1) * 2; print "\n\n";
    var scenarios := AllScenarios();
    PrintScenarios(scenarios);
  }
}
