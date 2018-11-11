```maude
mod STAGE-1 is
  protecting NAT .
  protecting RAT .
  
  protecting QID .
  vars Q : Qid .

  sort Stakeholder .
  op sh : Qid NzNat -> Stakeholder [ctor] .

  sort StakeholderList . subsort Stakeholder < StakeholderList .
  op emptyStakeHolderList : -> StakeholderList [ctor] .
  op _ _ : StakeholderList StakeholderList -> StakeholderList [ctor assoc id: emptyStakeHolderList] .
 
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
  op emptyBlockChainSet : -> BlockChainSet                       [ctor] .
  op _;_ : BlockChainSet   BlockChainSet   -> BlockChainSet [ctor assoc comm id: emptyBlockChainSet] .
  op _;_ : NeBlockChainSet BlockChainSet -> NeBlockChainSet [ditto] .
  
  vars SHS : StakeholderList .
  vars SH1 SH2 SH3 SH4 SH5 : Stakeholder .
  vars S1 S2 : Slot .
  vars CHAIN CHAIN1 CHAIN2 : BlockChain .
  vars CHAINS : BlockChainSet .
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

  op _ | _ : ElectionResult Probability -> ElectionResult [ctor] .
  op bad-election : -> ElectionResult [ctor] .
  eq (ER1 | prob(R1)) | prob(R2) = ER1 | prob(R1 * R2) .
  
  op total-stake : StakeholderList -> Nat .
  eq total-stake(emptyStakeHolderList) = 0 .
  eq total-stake(sh(Q, STAKE) SHS) = STAKE + total-stake(SHS) .

---- Defined exactly as paragraph below def 4.7
  op leader-election : Slot StakeholderList -> ElectionResult .
  rl leader-election(N, emptyStakeHolderList) => bad-election .
 crl leader-election(N, SH1 SHS)
  => SH1 | prob(STAKE / total-stake(SH1 SHS))
  if sh(Q, STAKE) := SH1
   .
 crl leader-election(N, SH1 SHS)
  => leader-election(N, SHS) | prob(1 - STAKE / total-stake(SH1 SHS))
  if sh(Q, STAKE) := SH1
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
---search leader-election(1, SH1 SH2 SH3) =>! leader-election(1, emptyStakeHolderList) | prob(R1) .
```
