---
title: Incentive Compatibility Analysis of Ouroboros
author: Nishant Rodrigues, Lucas Peña
institute: University of Illinois
date: November 25, 2018
---

# Introduction

As cryptocurrencies like bitcoin become more and more popular, energy efficiency
is becoming a growing concern. Cryptotocurrencies generally utilize a "proof of
work" scheme to deter denial of service and other attacks, while achieving
concensus. A key aspect of proof of work schemes is that they must be expensive
to compute, yet easy to verify. Most major cryptocurrency networks use CPU bound
schemes that, for example, involve repeatedly calculating cryptographic hashes.
While this scheme is effecitve in securing the network, it is extremely
energy-expensive. It has been estimated that globally, bitcoin mining consumes
electricity on a scale comaprable to the that of Ireland. Should proof of work
remain the state-of-the-art, this inefficiency will only worsen.

An alternative, proof of stake, attempts to address this. It attempts to choose
a block through a voting mechanism. However, the dynamics of this mechanism is
complex, and there are various incentives working at cross-purposes (if the
block I vote for gets selected I get rewarded; voters could control miners;
voters could attempt denial of service attacks; etc). Still, truthfullness in
this domain is of the utmost importance. Cryptocurrency would inevitably fail if
it was in miners' best interest to lie about things like block validity, a
transaction occurring, or which blockchain to append blocks to. In the domain of
proof of stake, these security concerns are heightened. As users rather than
miners now have control over the introduction of new currency, it is perhaps
more critical that a proof of stake protocol is honest.

One such proof of stake scheme is Ouroboros [@ouroboros]. Ouroboros is one of
the first proof of stake based blockchain protocols, used in the coin Cardano.
In this paper, we analyze an abstraction of the Ouroboros protocol using the
Maude System (see Section 2).

The remainder of the paper is as follows: We first briefly discuss the Maude
system used for our analysis. Then, we discuss the Ouroboros protocol, including
how we model the protocol in Maude. We also discuss our main results n this
section. Finally, we conclude and discuss opportunities for future work.

# Maude System

The Maude System is a programming language often used for modeling and
verification of systems. It has been used to verify a wide spectrum of systems,
from biological systems (Pathway Logic [@pathwaylogic]), to cryptographic
protocols (Maude NPA [@NPA]), to concensus algorithms, to programming languages
(KFramework [@kmaude]), and so on (see [@twentyears] for a comprehensive survey
of such applications). Maude allows specifying systems, including their
non-deterministic behaviours, as a transition system using rewriting logic. For
model checking purposes they provide a very high level formalism for
axiomatizing possibly infinite Kripke structures. This is exploited in Maude for
formal analysis purposes, since concurrent systems specified as rewrite theories
can be analyzed using Maude's LTL model checker and other model checkers and
theorem proving tools in Maude's formal environment.

# Ouroboros

In Ouroboros [@ouroboros], The proof of stake algorithm is split into four
stages. Each stage adds complexity regarding details such as delay of the
system, endorsers of transactions, and more. We focus on the simplest version of
the protocol for our analysis.

## Preliminaries

In this section, we go into detail regarding definitions needed to understand
the specific algorithm we are modelling. Most definitions are taken from
Ouroboros [@ouroboros]. We also show how each of these are defined in Maude.

\begin{definition}[Stakeholder]
A stakeholder is a participant of the Ouroboros proof of stake algorithm.
\end{definition}

\begin{definition}[Stake]
Stake is the amount of currency a stakeholder has put up as part of the Ouroboros
algorithm. By definition, we assume the stake is nonzero for each stakeholder.
\end{definition}

```maude
  sort Stakeholder .
  op sh : Qid NzNat -> Stakeholder [ctor] .
```

\noindent A \texttt{Qid} is a quoted identifier in Maude. We use it here to name the
stakeholder. \texttt{NzNat} represents the nonzero natural number corresponding
to the stake of the stakeholder.

\begin{definition}[Slot]
A slot is a discrete unit of time used for the protocol. We use natural numbers to model slots.
\end{definition}

```maude
  sort Slot . subsort Nat < Slot .
```

\begin{definition}[Block]
A block is generated at a particular slot $sl_i$ by a stakeholder $s_i$.
It contains information regarding the slot number at which the block was created
as well as which stakeholder created the block.
\end{definition}

```maude
  sort Block .
  op block : Slot Stakeholder -> Block [ctor] .
```

\begin{definition}[Genesis Block]
The genesis block only contains the list of stakeholders participating in the
protocol.
\end{definition}

\begin{definition}[Blockchain]
A blockchain is any sequence of blocks.
\end{definition}

```maude
  sort BlockChain .
  subsorts Block < BlockChain .
  op genesisBlock : StakeholderList       -> BlockChain [ctor] .
  op _ _          : BlockChain BlockChain -> BlockChain
                    [ctor assoc id: epsilon] .
  op epsilon      :                       -> BlockChain [ctor] .
```

\begin{definition}[Valid Blockchain]
A valid blockchain is a blockchain with strictly increasing slots that is rooted
at the genesis block.
\end{definition}

```maude
  op isValid : BlockChain -> Bool .
```

\begin{definition}[Epoch]
An epoch is a set of $R$ adjacent slots $S = \{sl_1, \ldots, sl_R\}$.
\end{definition}

\noindent We do not define an epochs explicitly in Maude. Instead, we model it simply by
using two \texttt{Slot}s representing the start slot and end slot of an epoch.

## Leader Election

The Ouroboros algorithm crucially needs to elect a leader for each slot. The
leader creates a new block and controls which blockchain that block is appended
to.

In order to incentivize participation in the protocol, we need to fairly elect a
leader for each slot. This is done proportional to the amount of stake each
participant has. That is, if there are $n$ stakeholders, then for each slot $sl_j$,
stakeholder $i$ should be elected leader with probability

$$ p_i = \frac{s_i}{\sum_{k=1}^n s_k} $$

To implement this, the protocol flips a biased coin based on the relative stake
of participant $j$ in relation to participants $j+1,\ldots,n$, provided no
leader has been chosen yet. This ensures the leader of each slot is elected with
the desired probability.

```maude
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
```

\noindent In Maude, we use the notation \texttt{SH1 \# prob(R1)} represents that
stakeholder \texttt{S1} is elected as the slot leader with probability
\texttt{R1}. The \texttt{\_ | \_} notation represents choice, so
\texttt{SH1 \# prob(R1) | SH2 \# prob(R2)} means that \texttt{SH1} is elected with probability
\texttt{R1} and \texttt{SH2} is elected with probability \texttt{R2}. Thus, a
single call to \texttt{leader-election} returns all possible leaders and
associated probabilities that each leader gets elected. For example:

```maude
  leader-election(1, sh('a, 3) sh('b, 6) sh('c, 1))
```
returns
```maude
  sh('a, 3) # prob(3/10) | sh('b, 6) # prob(3/5) | sh('c, 1) # prob(1/10)
```

We use \texttt{leader-election} as a helper function in
\texttt{leader-elections} which returns all possible lists of stakeholders that
could have won elections between two given slots, as well as the associated
probability of each list. That is, calling \texttt{leader-elections} on two
participants \texttt{'a} and \texttt{'b} between slots 1 and 2 (inclusive)
returns four lists \texttt{aa}, \texttt{ab}, \texttt{ba}, and \texttt{bb}, along
with associated probabilities of each list. If \texttt{'a} had 60% of stake,
then the probability of \texttt{aa} would be \texttt{prob(9/25)}, and so on for
each election result.

## Ideal Protocol

Before covering the idealized version of the protocol where each participant is
honest, we provide a couple more definitions:

\begin{definition}[Network]
A network contains all stakeholders participating in the protocol, as well as
all possible each stakeholder has in scope at any given point.
\end{definition}

```maude
  sort Network .
  op emptyNetwork :                   -> Network [ctor] .
  op _[_] : Stakeholder BlockChainSet -> Network [ctor] .
  op _ _ : Network Network            -> Network
           [ctor assoc comm id: emptyNetwork] .
```

\begin{definition}[State]
The state of a system contains the current network, all publicly available
blockchains, a list of stakeholders that will be the leader for all remaining
slots, a beginning slot, and an ending slot. The state is either ``active'' (curly
braces) or ``frozen'' (square brackets).
\end{definition}

```maude
  sort State .
  op { _ | _ | _ | _ -> _ }
   : Network BlockChainSet StakeholderList Slot Slot -> State [ctor] .
  op [ _ | _ | _ | _ -> _ ]
   : Network BlockChainSet StakeholderList Slot Slot -> State [ctor] .
```

At a high-level, the idealized protocol elects a leader for each slot. That
leader should add all publicly broadcasted blockhains into a local set. Then,
the leader will create a block for that slot and append that block to the
longest block in her local set. Finally, she should broadcast that blockchain
out to all other stakeholders, and all stakeholders should update their local
blockchains with the newly broadcasted blockchain from the leader.

We model this protocol in Maude with the following rewrite rules:

```maude
 --- Stakeholders add broadcasted chains into their local chain set
 --- while state is frozen. Slot is incremented and state becomes active.
  rl [ (SH1[CHAINS1          ]) NW | CHAINS2 | SH1 SHS | S1     -> S2 ]
  => { (SH1[CHAINS1 ; CHAINS2]) NW | CHAINS2 | SH1 SHS | S1 + 1 -> S2 } .

 --- Leader creates block and appends it to max valid chain, then
 --- immediately broadcasts that chain. State is frozen.
 crl { (LEADER[CHAIN ; CHAINS]) NW | CHAINS1 | LEADER SHS | S1 -> S2 }
  => [ (LEADER[NEWCHAIN ; CHAIN ; CHAINS]) NW
     | NEWCHAIN ; CHAINS1 | SHS | S1 -> S2
     ]
  if last-slot(CHAIN) < S1
  /\ not(CHAIN block(S1, LEADER) in CHAINS)
  /\ max-valid(CHAIN, CHAINS) = CHAIN
  /\ NEWCHAIN := (CHAIN block(S1, LEADER))
  /\ S1 < S2 .
```

## Accommodating Dishonest Behavior

As given in the previous section, this protocol is completely deterministic and
thus relatively uninteresting. In order for analysis of this protocol to be
interesting, an adversary must have some potential flexibility with how he or
she interacts with the protocol. First, note that a crucial assumption present
in Ouroboros [@ouroboros] (and most blockchain protocols) is that at least 51%
of the participants are acting truthfully. While the practicality of this
assumption can be argued, it is out of the scope of this paper. Thus, we will
assume at least 51% follow the protocol precisely as outlined in the beginning
of this section, and we will discuss potential behaviors of the "adversarial
49%" in this subsection.

An adversary has multiple ways to deviate from the protocol. For example, he
need not update his local blockchain set accordingly with all blockchains
previously leaders had broadcasted. However, this makes it more unlikely that
the chain the adversary adds his created block to will ultimately be the longest
chain in an epoch. Thus, as we will see when we discussing rewards in Section
3.5, the adversary will never be incentivized to not update his local blockchain
set.

Next, crucially, the adversary can choose not to immediately broadcast his
updated blockchain to all other participants of the protocol. This is the main
adversarial behavior we analyze in this paper. By doing this, an adversary
potentially could mask the actual longest blockchain until the end of the epoch,
and force honest leaders to append blocks to what will turn out to not be the
longest blockchain. Thus, the adversary may yield a larger reward with this
dishonest behavior, as he would have created a larger percentage of blocks on
the ultimately longest chain. We call this attack a "withholding attack".

Since we assume all honest participants deterministically follow the protocol,
we model all honest stakeholders as one stakeholder with 51% of stake:
\texttt{sh('honest, 51)}. Similarly, since we can assume all dishonest
participants adversarially collude, we model all dishonest stakeholders as one
stakeholder with 49% of stake: \texttt{sh('dishonest, 49)}.

Because the adversary will always be incentivized to completely update his local
blockchain set, the first rule from the previous section remains
unchanged. However, the second rule is now only true for honest participants, so
it is slightly modified:

\small
\begin{Verbatim}[commandchars=\\\{\}]
 --- \textcolor{red}{Honest} leader creates block and appends it to max valid chain,
 --- then immediately broadcasts that chain. State is frozen.
 crl \{ (LEADER[CHAIN ; CHAINS]) NW | CHAINS1 | LEADER SHS | S1 -> S2 \}
  => [ (LEADER[NEWCHAIN ; CHAIN ; CHAINS]) NW
     | NEWCHAIN ; CHAINS1 | SHS | S1 -> S2
     ]
  if last-slot(CHAIN) < S1
  /\textbackslash not(CHAIN block(S1, LEADER) in CHAINS)
  /\textbackslash max-valid(CHAIN, CHAINS) = CHAIN
  /\textbackslash NEWCHAIN := (CHAIN block(S1, LEADER))
  \textcolor{red}{/\textbackslash sh('honest, STAKE) := LEADER}
  /\textbackslash S1 < S2 .
\end{Verbatim}

\normalsize

In addition, we have the following rules which correspond to how a dishonest
participant may interact with the protocol:

```maude
 --- Dishonest leader can add a block to any of his local chains.
 crl { (LEADER[CHAIN ; CHAINS]) NW | CHAINS1 | LEADER SHS | S1 -> S2 }
  => { (LEADER[(CHAIN block(S1, LEADER)) ; CHAIN ; CHAINS]) NW 
     | CHAINS1 | LEADER SHS | S1 -> S2
     }
  if last-slot(CHAIN) < S1
  /\ not(CHAIN block(S1, LEADER) in CHAINS)
  /\ sh('dishonest, STAKE) := LEADER .

 --- Dishonest stakeholders can broadcast chains they know about.
 crl { (SH1[CHAIN ; CHAINS]) NW |         CHAINS1 | SHS | S1 -> S2 }
  => { (SH1[CHAIN ; CHAINS]) NW | CHAIN ; CHAINS1 | SHS | S1 -> S2 }
  if not(CHAIN in CHAINS1)
  /\ sh('dishonest, STAKE) := SH1 .

 --- Dishonest leader can choose to add a block to any of his local chains.
 crl { (LEADER[CHAIN ; CHAINS]) NW | CHAINS1 | LEADER SHS | S1 -> S2 }
  => { (LEADER[(CHAIN block(S1, LEADER)) ; CHAIN ; CHAINS]) NW
     | CHAINS1 | LEADER SHS | S1 -> S2
     }
  if last-slot(CHAIN) < S1
  /\ not(CHAIN block(S1, LEADER) in CHAINS)
  /\ sh('dishonest, STAKE) := LEADER .

 --- Dishonest leader can freeze state at any time, preparing for slot
 --- to be incremented.
 crl { NW | CHAINS | LEADER SHS | S1 -> S2 }
  => [ NW | CHAINS | SHS        | S1 -> S2 ]
  if S1 < S2
  /\ sh('dishonest, STAKE) := LEADER .
```

## Reward System

After each iteration of the protocol, agents publish additional blocks onto an
exisiting chain for the slot that they are a leader.  Once concensus is achieved
only blocks on the longest chain are kept and all other chains (along with
blocks on these chains) are discarded.  While it may seem intuitive to award
only miners whos blocks are on the longest chain, this allows adverseries to
employ withholding attacks to have dispropotionate control over the network.

For example, in Figure \ref{wh-attack}, the dishonest stakeholder is elected
leader at slots 1 and 3, while the honest stakeholder is elected leader at slots
0 and 2. If the dishonest stakeholder does not broadcast the fork after mining a
block, then the honest stakeholder at slot 2 is forced to build a block directly
off of the block built at slot 0. Then, the dishonest stakeholder can continue
building off his withheld fork in slot 3, inhibiting the rewards of the honest
player. If the dishonest player now chooses to broadcast his fork, the maximum
valid chain does not include the block mined at slot 1.

\begin{figure}\label{wh-attack}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto]
   \node[state,accepting,initial] (h_0)   {$h_0$}; 
   \node[state] (d_1) [below right=of h_0] {$d_1$};
   \node[state,accepting] (h_2) [above right=of d_1] {$h_2$}; 
   \node[state](d_3) [below right=of h_2] {$d_3$};
    \path[->] 
    (h_0) edge  node {} (h_2)
          edge  node [swap] {} (d_1)
    (d_1) edge  node  {} (d_3);
\end{tikzpicture}
\caption{Withholding Attack Example}
\end{figure}

We call this (flawed) reward mechanism `chain-rewards`
and define it in Maude as follows:

```maude
  op chain-rewards : BlockChain -> Rewards .
  eq chain-rewards(epsilon) = emptyRewards .
  eq chain-rewards(genesisBlock(SHS)) = emptyRewards .
  eq chain-rewards(CHAIN block(S1, SH1)) = (SH1 |-> 1) chain-rewards(CHAIN) .
```

Ideally, we would only reward stakeholders that issue a block on any fork.
However, the reward mechanism is implemented in the blockchain itself, and cannot
know about blocks issued in other forks. We cannot tell the difference between
a stakeholder that was offline during its slot, and a stakeholder that issued
a block to a fork that was not accepted by the network.
So, we simply reward all stakeholders that have been elected as leader for a
slot. We call this mechanism `unconditional-rewards`:

```maude
  op unconditional-rewards : StakeholderList -> Rewards .
  eq unconditional-rewards(emptyStakeholderList) = emptyRewards .
  eq unconditional-rewards(SH1 SHS) = (SH1 |-> 1) unconditional-rewards(SHS) .
```

In our analysis, we compare these two reward mechanisms using Maude's `search`
capability to show that the first mechanism is *not* incentive compatible. To do
this, we need to calculate the expected value of reward for a dishonest player
assuming he makes the optimum choice of blocks to mine and when to broadcast. In
our model, the only non-deterministic behavior is in the choices the dishonest
player can make. (The probabilistic election results are computed as a closed
form expression; honest players are not allowed to make any choices). Thus
finding the best-response reward for the dishonest stakeholder is simply a
search for the state reachable via rewriting that gives him the largest reward,
given an election result. We then compute the expectation for this reward over
all election results. We achieve this using the following two functions
(implementation is omitted for brevity):

```maude
  op max-dishonest-reward : State -> Rewards .
  op expected-dishonest-chain-reward : Network BlockChainSet Slot Slot -> Rewards .
```

Since the unconditional rewards is a function only of the election result,
we can simply iterate over each probable election result:

```maude
  op expected-reward : Network BlockChainSet Slot Slot -> Rewards .
  op expected-reward.er : ElectionResult -> PRewards .
```

We run these for a simple network with two stakeholders for an epoch of three slots:

```
reduce expected-dishonest-chain-reward( (sh('dishonest, 49)[ emptyBlockChainSet])
                                        (sh('honest, 51)[emptyBlockChainSet])
                                      , genesisBlock(sh('honest, 51) sh('dishonest, 49))
                                      , 0, 3) .
result Rewards: (sh('dishonest, 49) |-> 1355683/2000000)
                (sh('honest,    51) |->  644317/2000000)
```

Notice that while the dishonest stakeholder has only 49% of the stake he is able
to secure more than two thirds of the reward! With both players displaying
honest behavior we see expected rewards proportional to their stake [@git-repo].
Clearly the dishonest player has incentive to game the system.

Selection `unconditional-reward` as the reward mechanism gives us much better results:

```
reduce expected-reward( (sh('dishonest, 49)[emptyBlockChainSet])
                        (sh('honest,    51)[emptyBlockChainSet])
                      , genesisBlock( sh('honest, 51)
                                      sh('dishonest, 49)
                                    )
                      , 0, 3) .
result Rewards: (sh('dishonest, 49) |-> 49/100) sh('honest, 51) |-> 51/100
```


# Conclusion

We have successfully modeled an abstraction of the Ouroboros protocol in
Maude. We've analyzed two different reward mechanisms for the protocol, and
showed that a naive reward mechanism is not incentive compatible, and in fact is
not even a Nash equilibrium. We also briefly covered the modified reward
mechanism and showed how it fixes the issue for the example that fails with the
first reward mechanism. Finally, having a formal model of this protocol will
facilitate research in many future directions.

# Future Work

There are many directions for future work with this project. Most such areas
involve tightening the abstraction between our Maude implementation and the
Ouroboros protocol. The most immediate adjustment would be to allow participants
to have dynamic stake rather than static stake. This allows participants to add
or remove the stake they invest in this protocol, which is a very desirable
property in these proof of stake protocols, as well as a property that full
Ouroboros has.

Another way to tighten the abstraction would be to consider actual transactions
in a particular block. The main intricacy this adds is that the full Ouroboros
protocol includes elected \textit{endorsers} that confirm the validity of
transactions. Endorsers are elected and rewarded similarly to block leaders in
the protocol, but they still add another layer of complexity, as endorses
themselves can be either honest or not.

An alternative area for future work is considering other proof of stake
protocols. The main competitor to Ouroboros is Casper [@casper] which is a
proof of stake protocol developed by the Ethereum Foundation. Casper greatly
differs from Ouroboros in a few areas. Primarily, it is developed as a "finality
gadget" that finalizes blocks in a proof of stake manner \textit{on top of} a
proof of work scheme. Additionally, Casper requires a $\frac23$ majority instead
of a $\frac12$ majority as in Ouroboros. These differences lead to a much
different protocol, and analyzing game-theoretic properties of Casper is
definitely worthy of its own rigorous treatment.

# References
