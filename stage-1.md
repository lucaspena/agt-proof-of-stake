```maude
mod STAGE-1 is
    protecting NAT .
    protecting RAT .

    protecting QID .
    vars Q : Qid .

    sort Stakeholder .
    op sh : Qid NzNat -> Stakeholder [ctor] .

    sort StakeholderList . subsort Stakeholder < StakeholderList .
    op emptyStakeholderList : -> StakeholderList [ctor] .
    op _ _ : StakeholderList StakeholderList -> StakeholderList [ctor assoc id: emptyStakeholderList] .

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

    vars SHS SHS1 SHS2 : StakeholderList .
    vars SH1 SH2 SH3 SH4 SH5 : Stakeholder .
    vars S1 S2 : Slot .
    vars CHAIN CHAIN1 CHAIN2 : BlockChain .
    vars CHAINS CHAINS1 CHAINS2 : BlockChainSet .
    vars BLOCK : Block .
    vars N : Nat .
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
    op maxValid : BlockChain BlockChainSet -> BlockChain .
    eq maxValid(CHAIN, emptyBlockChainSet) = CHAIN .
   ceq maxValid(CHAIN1, CHAIN2 ; CHAINS) = maxValid(CHAIN1, CHAINS)
    if length(CHAIN1) >= length(CHAIN2) .
    eq maxValid(CHAIN1, CHAIN2 ; CHAINS) = maxValid(CHAIN2, CHAINS) [owise] .

    sort Probability .
    op prob : Rat -> Probability [ctor] .

    sort ElectionResult .
    subsort Stakeholder < ElectionResult .
    vars ER1 ER2 : ElectionResult .

    op _ # _ : ElectionResult Probability -> ElectionResult [ctor] .
    op bad-election : -> ElectionResult [ctor] .
    eq (ER1 # prob(R1)) # prob(R2) = ER1 # prob(R1 * R2) .

    op total-stake : StakeholderList -> Nat .
    eq total-stake(emptyStakeholderList) = 0 .
    eq total-stake(sh(Q, STAKE) SHS) = STAKE + total-stake(SHS) .

    --- Defined exactly as paragraph below def 4.7
    op leader-election : Slot StakeholderList -> ElectionResult .
    rl leader-election(N, emptyStakeholderList) => bad-election .
   crl leader-election(N, SH1 SHS)
    => SH1 # prob(STAKE / total-stake(SH1 SHS))
    if sh(Q, STAKE) := SH1
     .
   crl leader-election(N, SH1 SHS)
    => leader-election(N, SHS) # prob(1 - STAKE / total-stake(SH1 SHS))
    if sh(Q, STAKE) := SH1
     .

    --- Endorser election is the same as leader election as per first 2 paragraphs of Section 7.1
    op endorser-election : Slot StakeholderList -> ElectionResult .
    rl endorser-election(N, SHS) => leader-election(N, SHS) .

    op reward : Slot StakeholderList -> Rat .

    sort Network .
    vars NW : Network .

    op emptyNetwork :                   -> Network [ctor] .
    op _[_] : Stakeholder BlockChainSet -> Network [ctor] .
    op _ _ : Network Network            -> Network [ctor assoc comm id: emptyNetwork] .

    sort State .
    vars ST : State .

    op { _ | _ | _ | _ } : Network BlockChainSet StakeholderList Slot -> State [ctor] .

   crl { (SH1[CHAINS1])         NW | CHAIN ; CHAINS2 | SHS | S1 }
    => { (SH1[CHAIN ; CHAINS1]) NW | CHAIN ; CHAINS2 | SHS | S1 }
    if not(CHAIN in CHAINS1)
     .
   crl { (SH1[CHAIN ; CHAINS]) NW |         CHAINS1 | SHS | S1 }
    => { (SH1[CHAIN ; CHAINS]) NW | CHAIN ; CHAINS1 | SHS | S1 }
    if not(CHAIN in CHAINS1)
     .
   crl { (SH1[                         CHAIN ; CHAINS]) NW | CHAINS1 | SH1 SHS | S1 }
    => { (SH1[(CHAIN block(S1, SH1)) ; CHAIN ; CHAINS]) NW | CHAINS1 | SH1 SHS | S1 }
    if last-slot(CHAIN) < S1 and not(CHAIN block(S1, SH1) in CHAINS)
     .
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

reduce maxValid(   genesisBlock(SH1), emptyBlockChainSet) .
reduce maxValid(   genesisBlock(SH1), genesisBlock(SH2) block(2, SH2) ) .
reduce maxValid(   genesisBlock(SH1), 
                   ( genesisBlock(SH2) block(2, SH2) )
                 ; ( genesisBlock(SH3) block(2, SH3) )
               ) .
reduce maxValid(   genesisBlock(SH1) block(1, SH2) block(2, SH2) block(3, SH2)
               ,   ( genesisBlock(SH1) block(1, SH3) block(2, SH3) block(3, SH3) )
                 ; ( genesisBlock(SH1) block(1, SH4) block(2, SH4) block(3, SH4) )
                 ; ( genesisBlock(SH1) block(1, SH5) block(2, SH5) block(3, SH5) )
               ) .

search leader-election(1, sh('a, 3) sh('b, 6) sh('c, 1)) =>! ER1 .
search leader-election(1, sh('a, 3) sh('b, 6) sh('c, 1)) =>! bad-election # prob(R1) .

reduce genesisBlock(sh('good, 51) sh('bad, 49)) in epsilon .

search { emptyNetwork | epsilon | emptyStakeholderList | N } =>! ST .
rewrite { (sh('good, 51)[emptyBlockChainSet]) sh('bad, 49)[emptyBlockChainSet]
       | genesisBlock(sh('good, 51) sh('bad, 49))
       | sh('good, 51) sh('bad, 49)
       | 3
       } .
search { (sh('good, 51)[emptyBlockChainSet]) sh('bad, 49)[emptyBlockChainSet]
       | genesisBlock(sh('good, 51) sh('bad, 49))
       | sh('good, 51) sh('bad, 49)
       | 3
       }
   =>! ST
     .
```
