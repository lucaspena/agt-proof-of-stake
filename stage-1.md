```maude
mod STAGE-1 is
  protecting NAT .
  protecting QID .
  

  sort Stakeholder     . subsort Qid         < Stakeholder .
  sort StakeholderList . subsort Stakeholder < StakeholderList .
  op _ _ : StakeholderList StakeholderList -> StakeholderList [ctor assoc] .
 
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
  op empty : -> BlockChainSet                       [ctor] .
  op _;_ : BlockChainSet   BlockChainSet   -> BlockChainSet [ctor assoc comm id: empty] .
  op _;_ : NeBlockChainSet BlockChainSet -> NeBlockChainSet [ditto] .
  
  var SHS : StakeholderList .
  vars SH1 SH2 : Stakeholder .
  vars S1 S2 : Slot .
  vars CHAIN CHAIN1 CHAIN2 : BlockChain .
  var CHAINS : BlockChainSet .
  var BLOCK : Block .
  var N : Nat .

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

  op leader : StakeholderList -> Stakeholder .
  
  --- Returns the longest chain in the set breaking ties in favor of the given chain
  op maxValid : BlockChain BlockChainSet -> BlockChain . 
  eq maxValid(CHAIN, empty) = CHAIN .
 ceq maxValid(CHAIN1, CHAIN2 ; CHAINS) = maxValid(CHAIN1, CHAINS)
  if length(CHAIN1) >= length(CHAIN2) .
  eq maxValid(CHAIN1, CHAIN2 ; CHAINS) = maxValid(CHAIN2, CHAINS) [owise] .
 
endm
```

```maude
reduce isValid(genesisBlock('a)) .
reduce isValid(epsilon) .
reduce isValid(epsilon genesisBlock('a)) .
reduce isValid(genesisBlock('a) epsilon) .

reduce length(genesisBlock('a)) .
reduce length(epsilon) .
reduce length(epsilon genesisBlock('a)) .
reduce length(genesisBlock('a) epsilon) .
reduce length(genesisBlock('a) block(1, 'a) block(1, 'a) block(1, 'a)) .

reduce genesisBlock('a) \ 1 .
reduce (epsilon genesisBlock('a)) \ 1 .
reduce (genesisBlock('a) epsilon) \ 2 .
reduce (block(1, 'a)) \ 1 .
reduce (genesisBlock('a) block(1, 'a)) \ 1 .
reduce (genesisBlock('a) block(1, 'a) block(1, 'a) block(1, 'a)) \ 2 .

reduce maxValid(   genesisBlock('a), empty) .
reduce maxValid(   genesisBlock('a), genesisBlock('b) block(2, 'b) ) .
reduce maxValid(   genesisBlock('a), 
                   ( genesisBlock('b) block(2, 'b) )
                 ; ( genesisBlock('c) block(2, 'c) )
               ) .
reduce maxValid(   genesisBlock('a) block(1, 'b) block(2, 'b) block(3, 'b)
               ,   ( genesisBlock('a) block(1, 'c) block(2, 'c) block(3, 'c) )
                 ; ( genesisBlock('a) block(1, 'd) block(2, 'd) block(3, 'd) )
                 ; ( genesisBlock('a) block(1, 'e) block(2, 'e) block(3, 'e) )
               ) .
  
```
