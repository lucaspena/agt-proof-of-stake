```maude
mod STAGE-1 is
    protecting NAT .
    protecting RAT .

    protecting QID .
    vars Q : Qid .

    sort Stakeholder .
    vars SH1 SH2 SH3 SH4 SH5 LEADER : Stakeholder .
    op sh : Qid NzNat -> Stakeholder [ctor] .

    sort StakeholderList . subsort Stakeholder < StakeholderList .
    vars SHS SHS1 SHS2 : StakeholderList .
    op emptyStakeholderList : -> StakeholderList [ctor] .
    op _ _ : StakeholderList StakeholderList -> StakeholderList [ctor assoc id: emptyStakeholderList] .
    
    sort StakeholderMaybe .
    vars LEADER? : StakeholderMaybe .
    subsort Stakeholder < StakeholderMaybe .
    op noneStakeholder : -> StakeholderMaybe [ctor] .

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

    sort PTerm .
    vars PT PT1 PT2 : PTerm .
    op _ # _ : PTerm Probability -> PTerm    [ctor] .
    op _ | _ : PTerm PTerm -> PTerm [ctor assoc comm] .
    eq (PT1 # prob(R1)) # prob(R2) = PT1 # prob(R1 * R2) .
    eq (PT1 | PT2) # P = (PT1 # P) | (PT2 # P) .
    eq (PT1 # prob(R1)) | (PT1 # prob(R2)) = (PT1 # prob(R1 + R2)) .
    eq (PT1 # prob(0)) | PT2 = PT2 .

    sort PStakeholderMaybe .
    subsort StakeholderMaybe < PStakeholderMaybe < PTerm .
    op _ # _ : PStakeholderMaybe Probability     -> PStakeholderMaybe [ctor] .
    op _ | _ : PStakeholderMaybe PStakeholderMaybe -> PStakeholderMaybe [ditto] .

    op total-stake : StakeholderList -> Nat .
    eq total-stake(emptyStakeholderList) = 0 .
    eq total-stake(sh(Q, STAKE) SHS) = STAKE + total-stake(SHS) .

    --- Defined exactly as paragraph below def 4.7
    op leader-election : Slot StakeholderList -> PStakeholderMaybe .
    eq leader-election(N, emptyStakeholderList) = noneStakeholder .
   ceq leader-election(N, SH1 SHS)
     = (SH1 # prob(R1)) | (leader-election(N, SHS) # prob(1 - R1))
    if sh(Q, STAKE) := SH1
    /\ R1 := (STAKE / total-stake(SH1 SHS))
     .
   crl leader-election(N, SH1 SHS)
    => leader-election(N, SHS) # prob(1 - STAKE / total-stake(SH1 SHS))
    if sh(Q, STAKE) := SH1
     .

    --- Endorser election is the same as leader election as per first 2 paragraphs of Section 7.1
    op endorser-election : Slot StakeholderList -> PStakeholderMaybe .
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

    sort State PState .
    subsort State < PState < PTerm .
    op impossible : -> PState [ctor] .
    op _ # _ : PState Probability -> PState [ctor] .
    op _ | _ : PState PState      -> PState [ditto] .
    vars ST : State .
    eq ST # prob(0) = impossible .
    eq PT1 | impossible = PT1 .

    op { _ | _ | _ | _ -> _ }
     : Network BlockChainSet PStakeholderMaybe Slot Slot -> State
       [ctor format (t d nt d nt d nt d d d nt d)] .
```

Stakeholders can add broadcasted chains into their local chain set:

```maude
   crl { (SH1[CHAINS1])         NW | CHAIN ; CHAINS2 | LEADER | S1 -> S2 }
    => { (SH1[CHAIN ; CHAINS1]) NW | CHAIN ; CHAINS2 | LEADER | S1 -> S2 }
    if not(CHAIN in CHAINS1)
     .
```

Stakeholders can broadcast chains they have know about:
TODO: Here we assume that that agents have knowledge of the broadcast chains

```maude
   crl { (SH1[CHAIN ; CHAINS]) NW |         CHAINS1 | LEADER | S1 -> S2}
    => { (SH1[CHAIN ; CHAINS]) NW | CHAIN ; CHAINS1 | LEADER | S1 -> S2}
    if not(CHAIN in CHAINS1)
     .
```

A dishonest leader can choose to add a block to any of their local chains:
TODO: We've hardcoded the bad stakeholder here.

```maude
   crl { (LEADER[                            CHAIN ; CHAINS]) NW | CHAINS1 | LEADER | S1 -> S2 }
    => { (LEADER[(CHAIN block(S1, LEADER)) ; CHAIN ; CHAINS]) NW | CHAINS1 | LEADER | S1 -> S2 }
    if last-slot(CHAIN) < S1 and not(CHAIN block(S1, LEADER) in CHAINS)
    /\ sh('dishonest, STAKE) := LEADER
     .
```

Honest stakeholders must append a `max-valid` chain and immediately broadcast that chain:

```maude
   crl { (LEADER[           CHAIN ; CHAINS]) NW |            CHAINS1 | LEADER | S1     -> S2 }
    => { (LEADER[NEWCHAIN ; CHAIN ; CHAINS]) NW | NEWCHAIN ; CHAINS1 | noneStakeholder | S1 + 1 -> S2 }
    if last-slot(CHAIN) < S1
    /\ not(CHAIN block(S1, LEADER) in CHAINS)
    /\ max-valid(CHAIN, CHAINS) = CHAIN
    /\ NEWCHAIN := (CHAIN block(S1, LEADER))
    /\ sh('honest, STAKE) := LEADER
    /\ S1 < S2
     .
```

When the slot increments, a new leader must be selected:

```maude
   crl { NW | CHAINS | LEADER          | S1     -> S2 }
    => { NW | CHAINS | noneStakeholder | S1 + 1 -> S2 }
    if S1 < S2
    /\ sh('dishonest, STAKE) := LEADER
     .
```

```maude
   crl { NW | CHAINS | noneStakeholder                               | S1     -> S2 }
    => { NW | CHAINS | leader-election(S1, network-stakeholders(NW)) | S1     -> S2 }
    if S1 < S2
     .
    eq { NW | CHAINS | (PT1 | PT2)    | S1 -> S2 }
     = { NW | CHAINS |  PT1           | S1 -> S2 }
       | { NW | CHAINS |        PT2     | S1 -> S2 }
     .
    eq { NW | CHAINS | PT1 # prob(R1) | S1 -> S2 }
     = { NW | CHAINS | PT1            | S1 -> S2 } # prob(R1)
     .
```

```maude
    sort Rewards .
    op emptyRewards :                 -> Rewards [ctor] .
    op _ |-> _      : Stakeholder Nat -> Rewards [ctor] .
    op _ _          : Rewards Rewards -> Rewards [ctor assoc comm id: emptyRewards] .
    eq (SH1 |-> N1) (SH1 |-> N2) = SH1 |-> (N1 + N2) .

    op chain-rewards : BlockChain -> Rewards .
    eq chain-rewards(epsilon) = emptyRewards .
    eq chain-rewards(genesisBlock(SHS)) = emptyRewards .
    eq chain-rewards(CHAIN block(S1, SH1)) = (SH1 |-> 1) chain-rewards(CHAIN) .
```

```maude
    op reward : Rewards -> State .
    rl { NW | CHAIN ; CHAINS | noneStakeholder | S1 -> S1 }
    => reward(chain-rewards(max-valid(CHAIN, CHAINS))) .
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
reduce leader-election(1, sh('a, 3) sh('b, 6) sh('c, 1)) .

reduce genesisBlock(sh('honest, 51) sh('dishonest, 49)) in epsilon .

search { emptyNetwork | epsilon | noneStakeholder | 0 -> 99 } # prob(1) =>! ST .

rewrite { (sh('honest, 51)[emptyBlockChainSet]) sh('dishonest, 49)[emptyBlockChainSet]
       | genesisBlock(sh('honest, 51) sh('dishonest, 49))
       | noneStakeholder
       | 1 -> 4
       } .
```
