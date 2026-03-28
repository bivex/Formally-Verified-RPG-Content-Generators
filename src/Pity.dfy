module Pity {

  const HARD_PITY_5STAR : nat := 90
  const HARD_PITY_4STAR : nat := 10
  const SOFT_PITY_START : nat := 74

  datatype PullResult = Got5Star(featured: bool) | Got4Star | Got3Star

  datatype PityState = PityState(
    since5Star : nat,
    since4Star : nat,
    guaranteed : bool,
    totalPulls : nat
  ) {
    predicate Valid() {
      since5Star <= HARD_PITY_5STAR && since4Star <= HARD_PITY_4STAR
    }
  }

  const InitialState : PityState := PityState(0, 0, false, 0)

  predicate AtHardPity5(s: PityState) { s.since5Star == HARD_PITY_5STAR }
  predicate AtHardPity4(s: PityState) { s.since4Star == HARD_PITY_4STAR }
  predicate SoftPityActive(s: PityState) { s.since5Star >= SOFT_PITY_START }

  // Constraint: what pull results are valid given a pity state
  // Uses match on r to safely access .featured field only for Got5Star
  predicate ValidPull(s: PityState, r: PullResult)
    requires s.Valid()
  {
    (AtHardPity5(s) ==> r.Got5Star?) &&
    (AtHardPity4(s) && !r.Got5Star? ==> r.Got4Star?) &&
    (match r
       case Got5Star(featured) => (s.guaranteed ==> featured)
       case _ => true)
  }

  function Advance(s: PityState, r: PullResult): PityState
    requires s.Valid()
    requires ValidPull(s, r)
    ensures Advance(s, r).Valid()
  {
    match r
      case Got5Star(featured) =>
        PityState(0, 0, !featured, s.totalPulls + 1)
      case Got4Star =>
        var new5 := s.since5Star + 1;
        PityState(
          if new5 <= HARD_PITY_5STAR then new5 else HARD_PITY_5STAR,
          0, s.guaranteed, s.totalPulls + 1)
      case Got3Star =>
        var new5 := s.since5Star + 1;
        var new4 := s.since4Star + 1;
        PityState(
          if new5 <= HARD_PITY_5STAR then new5 else HARD_PITY_5STAR,
          if new4 <= HARD_PITY_4STAR then new4 else HARD_PITY_4STAR,
          s.guaranteed, s.totalPulls + 1)
  }

  // --- Lemmas ---

  // L1: Hard pity 5star forces a 5star result
  lemma HardPityForcesR5(s: PityState, r: PullResult)
    requires s.Valid() && AtHardPity5(s) && ValidPull(s, r)
    ensures r.Got5Star?
  {}

  // L2: 50/50 guarantee is honoured
  lemma GuaranteeHolds(s: PityState, r: PullResult)
    requires s.Valid() && s.guaranteed && ValidPull(s, r) && r.Got5Star?
    ensures match r case Got5Star(f) => f case _ => false
  {}

  // L3: Any 5star resets both counters
  lemma R5ResetsBothCounters(s: PityState, f: bool)
    requires s.Valid() && ValidPull(s, Got5Star(f))
    ensures Advance(s, Got5Star(f)).since5Star == 0
    ensures Advance(s, Got5Star(f)).since4Star == 0
  {}

  // L4: Non-featured 5star arms the guarantee
  lemma StandardR5SetsGuarantee(s: PityState)
    requires s.Valid() && ValidPull(s, Got5Star(false))
    ensures Advance(s, Got5Star(false)).guaranteed
  {}

  // L5: Featured 5star disarms the guarantee
  lemma FeaturedR5ClearsGuarantee(s: PityState)
    requires s.Valid() && ValidPull(s, Got5Star(true))
    ensures !Advance(s, Got5Star(true)).guaranteed
  {}

  // L6: 4star pity forces at least 4star
  lemma HardPity4ForcesR4orR5(s: PityState, r: PullResult)
    requires s.Valid() && AtHardPity4(s) && ValidPull(s, r) && !r.Got5Star?
    ensures r.Got4Star?
  {}

  // --- Generation: all 91 x 11 x 2 = 2002 valid pity states ---

  method AllPityStates() returns (result: seq<PityState>)
    ensures |result| == (HARD_PITY_5STAR + 1) * (HARD_PITY_4STAR + 1) * 2
    ensures forall i :: 0 <= i < |result| ==> result[i].Valid()
  {
    result := [];
    var g := 0;
    while g < 2
      invariant 0 <= g <= 2
      invariant |result| == g * (HARD_PITY_5STAR + 1) * (HARD_PITY_4STAR + 1)
      invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
    {
      var s5 := 0;
      while s5 <= HARD_PITY_5STAR
        invariant 0 <= s5 <= HARD_PITY_5STAR + 1
        invariant |result| == g * (HARD_PITY_5STAR + 1) * (HARD_PITY_4STAR + 1) + s5 * (HARD_PITY_4STAR + 1)
        invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
      {
        var s4 := 0;
        while s4 <= HARD_PITY_4STAR
          invariant 0 <= s4 <= HARD_PITY_4STAR + 1
          invariant |result| == g * (HARD_PITY_5STAR + 1) * (HARD_PITY_4STAR + 1) + s5 * (HARD_PITY_4STAR + 1) + s4
          invariant forall i :: 0 <= i < |result| ==> result[i].Valid()
        {
          result := result + [PityState(s5, s4, g == 1, 0)];
          s4 := s4 + 1;
        }
        s5 := s5 + 1;
      }
      g := g + 1;
    }
  }

  method {:print} PrintPityState(s: PityState) {
    print "Since5star:"; print s.since5Star;
    print " | Since4star:"; print s.since4Star;
    print " | Guaranteed:"; print if s.guaranteed then "YES" else "no";
    print " | SoftPity:"; print if SoftPityActive(s) then "ACTIVE" else "no";
    print " | HardPity5:"; print if AtHardPity5(s) then "TRIGGER" else "no";
    print " | HardPity4:"; print if AtHardPity4(s) then "TRIGGER" else "no";
    print "\n";
  }
  method {:print} PrintPityStates(states: seq<PityState>) {
    var i := 0;
    while i < |states| invariant 0 <= i <= |states| {
      PrintPityState(states[i]);
      i := i + 1;
    }
  }

  method {:print} MainPity() {
    print "=== GACHA PITY STATE MACHINE ===\n";
    print "HardPity5star:"; print HARD_PITY_5STAR;
    print " | HardPity4star:"; print HARD_PITY_4STAR;
    print " | SoftPityStart:"; print SOFT_PITY_START; print "\n";
    print "Total valid states: "; print (HARD_PITY_5STAR + 1) * (HARD_PITY_4STAR + 1) * 2; print "\n\n";
    var states := AllPityStates();
    PrintPityStates(states);
  }
}
