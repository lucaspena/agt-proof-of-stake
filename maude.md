Juxtaposition of rewards for the same stakeholder sums them:

```
eq (SH1 |-> R1) (SH1 |-> R2) = SH1 |-> (R1 + R2) .
```

...

Expectation (`E[ _ ]`) takes a `PRewards` (a set of rewards for independent
events with probabilities attached) and returns the expected reward:

```
op E[ _ ] : PRewards -> Rewards .
eq E[ PR1 | PR2 ] = E[ PR1 ] E[ PR2 ] .
eq E[ emptyRewards # prob(R2) ] = emptyRewards .
eq E[ ((SH1 |-> R1) REWARDS) # prob(R2) ]
 =     (SH1 |-> R1 * R2)
   E[ (REWARDS) # prob(R2) ]
 .
```
