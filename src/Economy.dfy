module Economy {

  const PRIMOS_PER_PULL       : nat := 160
  const EXPECTED_5STAR_PULLS  : nat := 63   // average pulls per 5star (soft-pity model)
  const HARD_PITY             : nat := 90
  const PITY_4STAR            : nat := 10
  // Expected pulls for featured on limited banner: E[X] * 1.5 for 50/50 factor
  const EXPECTED_FEATURED_PULLS : nat := EXPECTED_5STAR_PULLS + EXPECTED_5STAR_PULLS / 2  // 94
  const WORST_CASE_PULLS        : nat := HARD_PITY * 2     // 180 (hard pity twice)
  const F2P_PRIMOS_MONTHLY      : nat := 2600
  const F2P_PULLS_MONTHLY       : nat := F2P_PRIMOS_MONTHLY / PRIMOS_PER_PULL  // 16

  // Formal economy invariant
  lemma PullCostIsLinear(n: nat)
    requires n > 0
    ensures n * PRIMOS_PER_PULL == PRIMOS_PER_PULL * n
  {}

  lemma ExpectedFeaturedCostBound()
    ensures EXPECTED_FEATURED_PULLS * PRIMOS_PER_PULL < WORST_CASE_PULLS * PRIMOS_PER_PULL
  {}

  datatype PullPackage = PullPackage(
    pullCount    : nat,
    primoCost    : nat,
    expected5Star: nat,
    expected4Star: nat,
    reachesHardPity: bool
  ) {
    predicate Valid() {
      pullCount > 0 && primoCost == pullCount * PRIMOS_PER_PULL
    }
  }

  function CreatePackage(n: nat): PullPackage
    requires n > 0
    ensures CreatePackage(n).Valid()
  {
    var cost   := n * PRIMOS_PER_PULL;
    var e5     := n / EXPECTED_5STAR_PULLS;
    var e4raw  := n / PITY_4STAR;
    var e4     := if e4raw > e5 then e4raw - e5 else 0;
    PullPackage(n, cost, e5, e4, n >= HARD_PITY)
  }

  // Generate n=1..maxPulls
  method AllPackages(maxPulls: nat) returns (result: seq<PullPackage>)
    requires maxPulls > 0
    ensures |result| == maxPulls
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var n := 1;
    while n <= maxPulls
      invariant 1 <= n <= maxPulls + 1
      invariant |result| == n - 1
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      result := result + [CreatePackage(n)];
      n := n + 1;
    }
  }

  method {:print} PrintPackage(p: PullPackage) {
    print "Pulls:"; print p.pullCount;
    print " | Primos:"; print p.primoCost;
    print " | Exp5star:"; print p.expected5Star;
    print " | Exp4star:"; print p.expected4Star;
    print " | HardPity:"; print if p.reachesHardPity then "YES" else "no";
    print "\n";
  }
  method {:print} PrintPackages(pkgs: seq<PullPackage>) {
    var i := 0;
    while i < |pkgs| invariant 0 <= i <= |pkgs| {
      PrintPackage(pkgs[i]);
      i := i + 1;
    }
  }

  method {:print} MainEconomy() {
    print "=== GACHA PULL ECONOMY ===\n";
    print "PrimosPerPull:"; print PRIMOS_PER_PULL;
    print " | Expected5star:"; print EXPECTED_5STAR_PULLS;
    print " pulls | ExpectedFeatured:"; print EXPECTED_FEATURED_PULLS;
    print " pulls | WorstCase:"; print WORST_CASE_PULLS; print " pulls\n";
    print "F2P monthly: "; print F2P_PRIMOS_MONTHLY; print " primos = ";
    print F2P_PULLS_MONTHLY; print " pulls\n\n";
    var pkgs := AllPackages(180);
    PrintPackages(pkgs);
  }
}
