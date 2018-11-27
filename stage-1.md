```maude
mod STAGE-1 is
    protecting NAT .
    protecting RAT .

    protecting QID .
    vars Q : Qid .

    sort Stakeholder .
    vars SH1 SH2 SH3 SH4 SH5 LEADER : Stakeholder .
    op sh : Qid NzNat -> Stakeholder [ctor] .

    sort StakeholderList .
    subsort Stakeholder < StakeholderList .
    vars SHS SHS1 SHS2 : StakeholderList .
    op emptyStakeholderList : -> StakeholderList [ctor] .
    op _ _ : StakeholderList StakeholderList -> StakeholderList [ctor assoc id: emptyStakeholderList] .

    sort StakeholderMaybe .
    vars LEADER? : StakeholderMaybe .
    subsort Stakeholder < StakeholderMaybe .
    op noneStakeholder : -> StakeholderMaybe [ctor] .

    sort StakeholderMaybeList .
    subsort StakeholderMaybe < StakeholderMaybeList .
    subsort StakeholderList < StakeholderMaybeList .
    vars SHMS SHMS1 SHMS2 : StakeholderMaybeList .
    op _ _ : StakeholderMaybeList StakeholderMaybeList -> StakeholderMaybeList [ditto] .

    sort Slot . subsort Nat < Slot .
    sort Block .
    op block : Slot Stakeholder -> Block [ctor] .

    sort BlockChain .
    subsorts Block < BlockChain .
    op genesisBlock : StakeholderList       -> BlockChain [ctor] .
    op _ _          : BlockChain BlockChain -> BlockChain [ctor assoc id: epsilon] .
    op epsilon      :                       -> BlockChain [ctor] .

    sort BlockChainSet .
    sort NeBlockChainSet .
    subsorts BlockChain < NeBlockChainSet < BlockChainSet .
    op emptyBlockChainSet : -> BlockChainSet                  [ctor] .
    op _;_ : BlockChainSet   BlockChainSet   -> BlockChainSet [ctor assoc comm id: emptyBlockChainSet] .
    op _;_ : NeBlockChainSet BlockChainSet -> NeBlockChainSet [ditto] .

    op _ in _ : BlockChain BlockChainSet -> Bool .
    eq CHAIN  in emptyBlockChainSet = false .
    eq CHAIN  in (CHAIN  ; CHAINS) = true .
    eq CHAIN1 in (CHAIN2 ; CHAINS) = (CHAIN1 in CHAINS) [owise] .

    vars S1 S2 : Slot .
    vars CHAIN CHAIN1 CHAIN2 NEWCHAIN : BlockChain .
    vars CHAINS CHAINS1 CHAINS2 : BlockChainSet .
    vars BLOCK : Block .
    vars N N1 N2 : Nat .
    vars STAKE : NzNat .
    vars R1 R2 : Rat .

    op isValid : BlockChain -> Bool .
    eq isValid(genesisBlock(SHS)) = true .
    eq isValid(genesisBlock(SHS) BLOCK) = true .
    eq isValid(CHAIN block(S1, SH1) block(S2, SH2)) = S1 < S2 .
    eq isValid(epsilon) = false .

    op length : BlockChain -> Nat .
    eq length(epsilon) = 0 .
    eq length(genesisBlock(SHS)) = 1 .
    eq length(CHAIN BLOCK) = 1 + length(CHAIN) .

    op _ \ _ : BlockChain Nat -> BlockChain .
    eq genesisBlock(SHS) \ s(N) = epsilon .
    eq       CHAIN \ 0    = CHAIN .
    eq (CHAIN BLOCK) \ s(N) = CHAIN \ N .

    op last-slot : BlockChain -> Slot .
    eq last-slot(genesisBlock(SHS1))  = 0 .
    eq last-slot(CHAIN block(N, SH1)) = N .

    --- Returns the longest chain in the set breaking ties in favor of the given chain
    op max-valid : BlockChain BlockChainSet -> BlockChain .
    eq max-valid(CHAIN, emptyBlockChainSet) = CHAIN .
   ceq max-valid(CHAIN1, CHAIN2 ; CHAINS) = max-valid(CHAIN1, CHAINS)
    if length(CHAIN1) >= length(CHAIN2) .
    eq max-valid(CHAIN1, CHAIN2 ; CHAINS) = max-valid(CHAIN2, CHAINS) [owise] .

    sort Probability .
    vars P : Probability .
    op prob : Rat -> Probability [ctor] .

    sort ElectionResult .
    vars ER1 ER2 ER3 : ElectionResult .
    subsort StakeholderMaybeList < ElectionResult .

    op _ # _ : ElectionResult Probability    -> ElectionResult [ctor] .
    op _ | _ : ElectionResult ElectionResult -> ElectionResult [ctor assoc comm] .
    op _   _ : ElectionResult ElectionResult -> ElectionResult [ditto] .

    eq (ER1 | ER2) # prob(R1) = (ER1 # prob(R1)) | (ER2 # prob(R1)) .
    eq ER1 # prob(R1) # prob(R2) = ER1 # prob(R1 * R2) .
   ceq (ER1 | ER2) ER3 = (ER1 ER3) | (ER2 ER3)
    if ER3 =/= emptyStakeholderList .
   ceq ER3 (ER1 | ER2) = (ER3 ER1) | (ER3 ER2)
    if ER3 =/= emptyStakeholderList .
    eq (ER1 # prob(R1)) (ER2 # prob(R2)) = (ER1 ER2) # prob(R1 * R2) .
    eq (ER1 # prob(0)) | ER2 = ER2 .

    op total-stake : StakeholderList -> Nat .
    eq total-stake(emptyStakeholderList) = 0 .
    eq total-stake(sh(Q, STAKE) SHS) = STAKE + total-stake(SHS) .

    --- Defined exactly as paragraph below def 4.7
    op leader-election : Slot StakeholderList -> ElectionResult .
    eq leader-election(S1, emptyStakeholderList) = noneStakeholder # prob(1) .
   ceq leader-election(S1, SH1 SHS)
     = (SH1 # prob(R1)) | (leader-election(S1, SHS) # prob(1 - R1))
    if sh(Q, STAKE) := SH1
    /\ R1 := (STAKE / total-stake(SH1 SHS))
     .
   crl leader-election(N, SH1 SHS)
    => leader-election(N, SHS) # prob(1 - STAKE / total-stake(SH1 SHS))
    if sh(Q, STAKE) := SH1
     .

    op leader-elections : Slot Slot StakeholderList -> ElectionResult .
    eq leader-elections(S1, S1, SHS) = emptyStakeholderList # prob(1) .
    eq leader-elections(S1, S2, SHS) =
        leader-election(S1, SHS) leader-elections(S1 + 1, S2, SHS) .

    --- Endorser election is the same as leader election as per first 2 paragraphs of Section 7.1
    op endorser-election : Slot StakeholderList -> ElectionResult .
    rl endorser-election(N, SHS) => leader-election(N, SHS) .

    op reward : Slot StakeholderList -> Rat .

    sort Network .
    vars NW : Network .

    op emptyNetwork :                   -> Network [ctor] .
    op _[_] : Stakeholder BlockChainSet -> Network [ctor] .
    op _ _ : Network Network            -> Network [ctor assoc comm id: emptyNetwork] .

    op network-stakeholders : Network -> StakeholderList .
    eq network-stakeholders(emptyNetwork) = emptyStakeholderList .
    eq network-stakeholders((SH1[CHAINS]) NW) = SH1 network-stakeholders(NW).
```

Modelling the protocol
----------------------

```maude
    sort State .
    vars ST : State .
    op error : Qid -> State [ctor] .
    op { _ | _ | _ | _ -> _ }
     : Network BlockChainSet StakeholderList Slot Slot -> State
       [ctor format (t d nt d nt d nt d d d nt d)] .
    op [ _ | _ | _ | _ -> _ ]
     : Network BlockChainSet StakeholderList Slot Slot -> State
       [ctor format (t d nt d nt d nt d d d nt d)] .

    op state-get-chains : State -> BlockChainSet .
    eq state-get-chains([ NW | CHAINS | SHS | S1 -> S2 ]) = CHAINS .
    eq state-get-chains({ NW | CHAINS | SHS | S1 -> S2 }) = CHAINS .
```

We assume that there is no delay: Leaders have full knowledge of all broadcast chains.

```maude
    rl [ (SH1[CHAINS1           ]) NW | CHAINS2 | SH1 SHS | S1     -> S2 ]
    => { (SH1[CHAINS1 ; CHAINS2 ]) NW | CHAINS2 | SH1 SHS | S1 + 1 -> S2 }
     .
    rl [ NW | CHAINS2 | emptyStakeholderList | S1     -> S2 ]
    => { NW | CHAINS2 | emptyStakeholderList | S1 + 1 -> S2 }
     .
```

Dishonest behaviour
-------------------

Being dishonest allows f

A dishonest leader may choose to **mine a block** to any of their local chains:

```maude
   crl { (LEADER[                            CHAIN ; CHAINS]) NW | CHAINS1 | LEADER SHS | S1 -> S2 }
    => { (LEADER[(CHAIN block(S1, LEADER)) ; CHAIN ; CHAINS]) NW | CHAINS1 | LEADER SHS | S1 -> S2 }
    if last-slot(CHAIN) < S1
    /\ not(CHAIN block(S1, LEADER) in CHAINS)
    /\ sh('dishonest, STAKE) := LEADER
     .
```

A dishonest agent may **broadcast** chains they have whether they are a leader or not:

```maude
   crl { (SH1[CHAIN ; CHAINS]) NW |         CHAINS1 | SHS | S1 -> S2}
    => { (SH1[CHAIN ; CHAINS]) NW | CHAIN ; CHAINS1 | SHS | S1 -> S2}
    if not(CHAIN in CHAINS1)
    /\ sh('dishonest, STAKE) := SH1
     .
```

The leader may **wait** for the slot number to increment:

```maude
   crl { NW | CHAINS | LEADER SHS | S1 -> S2 }
    => [ NW | CHAINS | SHS        | S1 -> S2 ]
    if S1 < S2
    /\ sh('dishonest, STAKE) := LEADER
     .
```

Honest behaviour
----------------

Honest stakeholders must follow the protocol. *No non-determinism is allowed*: they must:
append to a `max-valid` chain and immediately broadcast that chain:

```maude
   crl { (LEADER[           CHAIN ; CHAINS]) NW |            CHAINS1 | LEADER SHS | S1 -> S2 }
    => [ (LEADER[NEWCHAIN ; CHAIN ; CHAINS]) NW | NEWCHAIN ; CHAINS1 | SHS        | S1 -> S2 ]
    if last-slot(CHAIN) < S1
    /\ not(CHAIN block(S1, LEADER) in CHAINS)
    /\ max-valid(CHAIN, CHAINS) = CHAIN
    /\ NEWCHAIN := (CHAIN block(S1, LEADER))
    /\ sh('honest, STAKE) := LEADER
    /\ S1 < S2
     .
```

Rewards
-------

```maude
    sort Rewards .
    vars REWARDS : Rewards .
    op emptyRewards :                 -> Rewards [ctor] .
    op _ |-> _      : Stakeholder Rat -> Rewards [ctor] .
    op _ _          : Rewards Rewards -> Rewards [ctor assoc comm id: emptyRewards] .
    eq (SH1 |-> R1) (SH1 |-> R2) = SH1 |-> (R1 + R2) .

    op total-rewards : Rewards -> Rat .
    eq total-rewards((SH1 |-> R2) REWARDS) = R2 + total-rewards(REWARDS) .
    eq total-rewards(emptyRewards)         = 0 .

    op normalize-rewards : Rewards Rat -> Rewards .
    vars TOTAL : NzRat .
    eq normalize-rewards((SH1 |-> R2) REWARDS, 0)
     = emptyRewards
     .
    eq normalize-rewards((SH1 |-> R2) REWARDS, TOTAL)
     = (SH1 |-> (R2 / TOTAL)) normalize-rewards(REWARDS, TOTAL)
     .
    eq normalize-rewards(emptyRewards, TOTAL) = emptyRewards .

    op chain-rewards : BlockChain -> Rewards .
    eq chain-rewards(epsilon) = emptyRewards .
    eq chain-rewards(genesisBlock(SHS)) = emptyRewards .
    eq chain-rewards(CHAIN block(S1, SH1)) = (SH1 |-> 1) chain-rewards(CHAIN) .

    op unconditional-rewards : StakeholderList -> Rewards .
    eq unconditional-rewards(emptyStakeholderList) = emptyRewards .
    eq unconditional-rewards(SH1 SHS) = (SH1 |-> 1) unconditional-rewards(SHS) .
```

```maude
endm
```

```maude
reduce isValid(genesisBlock(SH1)) .
reduce isValid(epsilon) .
reduce isValid(epsilon genesisBlock(SH1)) .
reduce isValid(genesisBlock(SH1) epsilon) .

reduce length(genesisBlock(SH1)) .
reduce length(epsilon) .
reduce length(epsilon genesisBlock(SH1)) .
reduce length(genesisBlock(SH1) epsilon) .
reduce length(genesisBlock(SH1) block(1, SH1) block(1, SH1) block(1, SH1)) .

reduce genesisBlock(SH1) \ 1 .
reduce (epsilon genesisBlock(SH1)) \ 1 .
reduce (genesisBlock(SH1) epsilon) \ 2 .
reduce (block(1, SH1)) \ 1 .
reduce (genesisBlock(SH1) block(1, SH1)) \ 1 .
reduce (genesisBlock(SH1) block(1, SH1) block(1, SH1) block(1, SH1)) \ 2 .

reduce max-valid(   genesisBlock(SH1), emptyBlockChainSet) .
reduce max-valid(   genesisBlock(SH1), genesisBlock(SH2) block(2, SH2) ) .
reduce max-valid(   genesisBlock(SH1),
                   ( genesisBlock(SH2) block(2, SH2) )
                 ; ( genesisBlock(SH3) block(2, SH3) )
               ) .
reduce max-valid(   genesisBlock(SH1) block(1, SH2) block(2, SH2) block(3, SH2)
               ,   ( genesisBlock(SH1) block(1, SH3) block(2, SH3) block(3, SH3) )
                 ; ( genesisBlock(SH1) block(1, SH4) block(2, SH4) block(3, SH4) )
                 ; ( genesisBlock(SH1) block(1, SH5) block(2, SH5) block(3, SH5) )
               ) .
reduce leader-election (1,    sh('a, 3) sh('b, 6) sh('c, 1)) .
reduce leader-elections(1, 4, sh('a, 3) sh('b, 6) sh('c, 1)) .

reduce genesisBlock(sh('honest, 51) sh('dishonest, 49)) in epsilon .

rewrite [ (sh('honest, 51)[emptyBlockChainSet]) sh('dishonest, 49)[emptyBlockChainSet]
        | genesisBlock(sh('honest, 51) sh('dishonest, 49))
        | sh('honest, 51) sh('honest, 51)
        | 0 -> 4
        ] .

mod EXPECTATIONS is
    protecting META-LEVEL .
    protecting STAGE-1 .

    vars SHS SHS1 : StakeholderList .
    vars SH SH1 SH2 : Stakeholder .
    vars ST : State .
    vars S1 S2 : Slot .
    vars ER ER1 ER2 : ElectionResult .
    vars NW : Network .
    vars CHAINS : BlockChainSet .
    vars P1 P2 : Probability .
    vars R1 R2 : Rat .
    vars RTRIPLE? : ResultTriple? .
    vars S : NzNat .
    vars N : Nat .

    vars REWARDS REWARDS1 REWARDS2 REWARDS1REST REWARDS2REST : Rewards .

    sort PRewards .
    vars PR1 PR2 : PRewards .
    op _ # _ : Rewards Probability -> PRewards [ctor] .
    op _ | _ : PRewards PRewards -> PRewards [ctor assoc comm] .

    op E[ _ ] : PRewards -> Rewards .
    eq E[ PR1 | PR2 ] = E[ PR1 ] E[ PR2 ] .

    eq E[ emptyRewards # prob(R2) ]
     = emptyRewards
     .
    eq E[ ((SH1 |-> R1) REWARDS) # prob(R2) ]
     = (SH1 |-> R1 * R2) E[ (REWARDS) # prob(R2) ]
     .

    sort RewardsSet .
    vars REWARDSSET : RewardsSet .
    subsort Rewards < RewardsSet .
    op emptyRewardsSet : -> RewardsSet               [ctor] .
    op _;_ : RewardsSet RewardsSet -> RewardsSet [ctor assoc comm id: emptyRewardsSet] .

    op max-dishonest-reward           : State -> Rewards .
    op rewards-from-nth-solution      : State Nat -> RewardsSet .
    op max-dishonest-reward.rewardset : RewardsSet -> Rewards .
    eq max-dishonest-reward(ST) = max-dishonest-reward.rewardset(rewards-from-nth-solution(ST, 0)) .

   ceq rewards-from-nth-solution(ST, N)
     = emptyRewardsSet
    if RTRIPLE? := metaSearch(upModule('EXPECTATIONS, false)
                             , upTerm(ST)
                             , 'ST1:State
                             , nil
                             , '!
                             , unbounded
                             , N
                             )
     /\ RTRIPLE? == failure
      .
   ceq rewards-from-nth-solution(ST, N)
     = normalize-rewards(REWARDS, total-rewards(REWARDS))
     ; rewards-from-nth-solution(ST, N + 1)
    if RTRIPLE? := metaSearch(upModule('EXPECTATIONS, false)
                             , upTerm(ST)
                             , 'ST1:State
                             , nil
                             , '!
                             , unbounded
                             , N
                             )
     /\ RTRIPLE? =/= failure
     /\ REWARDS := chain-rewards(max-valid( epsilon
                                          , state-get-chains(downTerm( getTerm(RTRIPLE?)
                                                                     , error('bad-term)
                                )         )                 )        )
      .

    eq max-dishonest-reward.rewardset(emptyRewardsSet) = emptyRewards .
    eq max-dishonest-reward.rewardset(REWARDS1) = REWARDS1 .
    eq max-dishonest-reward.rewardset( emptyRewards ; (REWARDSSET) )
     = max-dishonest-reward.rewardset( (REWARDSSET) )
     .
   ceq max-dishonest-reward.rewardset( ((sh('dishonest, S) |-> R1) REWARDS1)
                                ; ((sh('dishonest, S) |-> R2) REWARDS2)
                                ; (REWARDSSET)
                                )
     = max-dishonest-reward.rewardset( ((sh('dishonest, S) |-> R1) REWARDS1)
                                ; (REWARDSSET)
                                )
    if R1 >= R2 --- TODO: This is non-confluent.
     .

  ---- Case where there is a rewardset where dishonest does not get a reward
    eq max-dishonest-reward.rewardset( ((sh('dishonest, S) |-> R1) REWARDS1)
                                     ; (                           REWARDS2)
                                     ; (REWARDSSET)
                                     )
     = max-dishonest-reward.rewardset( ((sh('dishonest, S) |-> R1) REWARDS1)
                                     ; (REWARDSSET)
                                     )
       [owise]
     .

    op expected-dishonest-chain-reward    : Network BlockChainSet Slot Slot                -> Rewards .
    op expected-dishonest-chain-reward.er : Network BlockChainSet ElectionResult Slot Slot -> PRewards .

    eq expected-dishonest-chain-reward(NW, CHAINS, S1, S2)
     = E[ expected-dishonest-chain-reward.er(NW, CHAINS, leader-elections(S1, S2, network-stakeholders(NW)), S1, S2) ]
     .
    eq expected-dishonest-chain-reward.er(NW, CHAINS, (SHS1 # P1) | ER, S1, S2)
     =   (max-dishonest-reward([NW | CHAINS | SHS1 | S1 -> S2]) # P1)
       | expected-dishonest-chain-reward.er(NW, CHAINS, ER, S1, S2)
     .
    eq expected-dishonest-chain-reward.er(NW, CHAINS, (SHS1 # P1) , S1, S2)
     =   (max-dishonest-reward([NW | CHAINS | SHS1 | S1 -> S2]) # P1)
     .

    op expected-reward : Network BlockChainSet Slot Slot -> Rewards .
    op expected-reward.er : ElectionResult -> PRewards .

    eq expected-reward(NW, CHAINS, S1, S2)
     = E[ expected-reward.er(leader-elections(S1, S2, network-stakeholders(NW))) ]
     .
    eq expected-reward.er((SHS1 # P1) | ER)
     = expected-reward.er((SHS1 # P1)) | expected-reward.er(ER)
     .
    eq expected-reward.er((SHS1 # P1))
     =   (normalize-rewards(unconditional-rewards(SHS1), total-rewards(unconditional-rewards(SHS1))) # P1)
     .
endm

reduce expected-dishonest-chain-reward( (sh('honest,    51)[emptyBlockChainSet])
            (sh('dishonest, 49)[emptyBlockChainSet])
          , genesisBlock(sh('honest, 51) sh('dishonest, 49))
          , 0 , 3
          ) .

reduce expected-reward( (sh('honest,    51)[emptyBlockChainSet])
                        (sh('dishonest, 49)[emptyBlockChainSet])
                      , genesisBlock(sh('honest, 51) sh('dishonest, 49))
                      , 0 , 3
                      ) .
                      
reduce expected-reward( (sh('honest, 51)[emptyBlockChainSet])
                        (sh('honest, 49)[emptyBlockChainSet])
                      , genesisBlock(sh('honest, 51) sh('honest, 49))
                      , 0 , 3
                      ) .
```
