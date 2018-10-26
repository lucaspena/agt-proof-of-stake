```maude
mod STAGE-1 is
  protecting NAT .
  protecting QID .
  
  sort Slot .
  subsort Nat < Slot .
  
  sort Stakeholder . --- Qid
  subsort Qid < Stakeholder .
  sort PublicKey .
  
  op Stakeholder : PublicKey Nat -> Stakeholder [ctor] .
 
  sort StakeholderList .
  subsort Stakeholder < StakeholderList .
  op _ _ : StakeholderList StakeholderList -> StakeholderList [ctor assoc] .
 
  sort Block .
  op block : Slot Stakeholder -> Block [ctor] .

  sort BlockChain .
  subsorts Block < BlockChain .
  op genesisBlock : StakeholderList       -> BlockChain [ctor] . 
  op _ _          : BlockChain BlockChain -> BlockChain [ctor assoc id: epsilon] .
  op epsilon      :                       -> BlockChain [ctor] .
  
  var SHS : StakeholderList .
  vars SH1 SH2 : Stakeholder .
  vars S1 S2 : Slot .
  var CHAIN : BlockChain .
  var BLOCK : Block .
  var N : Nat .

  op isValid : BlockChain -> Bool .
  eq isValid(genesisBlock(SHS)) = true .
  eq isValid(genesisBlock(SHS) BLOCK) = true .
  eq isValid(CHAIN block(S1, SH1) block(S2, SH2)) = S1 < S2 .
  eq isValid(epsilon) = false .

  op _ \ _ : BlockChain Nat -> BlockChain .
  eq genesisBlock(SHS) \ s(N) = epsilon .
  eq       CHAIN \ 0    = CHAIN .
  eq (CHAIN BLOCK) \ s(N) = CHAIN \ N .
endm
```

```maude
reduce isValid(genesisBlock('a)) .
reduce isValid(epsilon) .
reduce isValid(epsilon genesisBlock('a)) .
reduce isValid(genesisBlock('a) epsilon) .

reduce genesisBlock('a) \ 1 .
reduce (epsilon genesisBlock('a)) \ 1 .
reduce (genesisBlock('a) epsilon) \ 2 .
reduce (block(1, 'a)) \ 1 .
reduce (genesisBlock('a) block(1, 'a)) \ 1 .
reduce (genesisBlock('a) block(1, 'a) block(1, 'a) block(1, 'a)) \ 2 .
```
