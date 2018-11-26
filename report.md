---
title: Incentive Compatibility Analysis of Ouroboros
author: Nishant Rodrigues, Lucas Peña
institute: University of Illinois
date: November 25, 2018
---

# Introduction

As cryptocurrencies like bitcoin become more and more popular, energy efficiency
is becoming a growing concern. Cryptotocurrencies generally utilize a "proof of
work" scheme to deter denial of service and other attacks. A key aspect to proof
of work schemes is that they must be expensive to compute, yet easy to
verify. Most major cryptocurrency networks use CPU bound schemes that, for
example, involve repeatedly calculating cryptographic hashes. While this scheme
is effecitve in securing the network, it is extremely energy-expensive. It has
been estimated that globally, bitcoin mining consumes electricity on a scale
comaprable to the that of Ireland. Should proof work remain the
state-of-the-art, this inefficiency will only worsen.

An alternative, proof of stake, attempts to address this. It attempts to choose
a block through a voting mechanism. However, the dynamics of this mechanism is
complex, and there are various incentives working at cross-purposes (if the
block I vote for gets selected I get rewarded; voters could control miners;
voters could attempt denial of service attacks; etc). Still, truthfulness in
this domain is of the utmost importance. Cryptocurrency would inevitably fail if
it was in a miners' best interest to lie about things like block validity, a
transaction occurring, or which blockchain to append blocks to. In the domain of
proof of stake, these security concerns are heightened. As users rather than
miners now have control over the introduction of new currency, it is perhaps
more critical that a proof of stake protocol is truthful.

One such proof of stake scheme is [Ouroboros][ouroboros]. Ouroboros is one of
the first proof of stake based blockchain protocols, used in the coin Cardano.
In this paper, we analyze an abstraction of the Ouroboros protocol using the
Maude System (see Section 3).

The remainder of the paper is as follows: We first discuss the Ouroboros
algorithm in some detail, as well as the specific algorithm we use for
verification. We then discuss the Maude System, and how we can use it to verify
properties about Ouroboros. Next, we discuss our key results. Finally, we
conclude and discuss opportunities for future work.

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

TODO: more here

# Ouroboros

In this section we discuss the proof of stake algorithm used in Ouroboros, as
well as the assumptions we are making about the algorithm in this paper.

In Ouroboros [@ouroboros], The proof of stake algorithm is split into four
stages. Each stage adds complexity regarding details such as delay of the
system, endorsers of transactions, and more. We focus on the simplest version of
the prtocol for our analysis.

## Preliminaries

In this section, we go into detail regarding definitions needed to understand
the speicific algorithm we are modelling. Most definitions are taken from
Ouroboros [@ouroboros]. We also show how each of these are defined in Maude.

\begin{definition}[Stakeholder]
A stakeholder is a participant of the Ouroboros proof of stake algorithm.
\end{definition}

\begin{definition}[Stake]
Stake is the amount of money a stakeholder has put up as part of the Ouroboros
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
  eq isValid(genesisBlock(SHS)) = true .
  eq isValid(genesisBlock(SHS) BLOCK) = true .
  eq isValid(CHAIN block(S1, SH1) block(S2, SH2)) = S1 < S2 .
  eq isValid(epsilon) = false .
```

\begin{definition}[Epoch]
An epoch is a set of $R$ adjacent slots $S = \{sl_1, \ldots, sl_R\}$.
\end{definition}

\noindent We do not define an epochs explicitly in Maude. Instead, we model it simply by
using two \texttt{Slot}s representing the start slot and end slot in an epoch.

## Leader Election

The Ouroboros algorithm crucially needs to elect a leader for each slot. The
leader creates a new slot and controls which blockchain that block is appended
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

## Idealized Protocol

Before covering the idealized verson of the protocol where each participant is
honest, we provide a couple more definitions:

\begin{definition}[Network]
A network contains all stakeholders participating in the protocol, as well as
all possible blockchains each stakeholder has in scope at any given point.
\end{definition}

\begin{verbatim}
sort Network .
op emptyNetwork :                   -> Network [ctor] .
op _[_] : Stakeholder BlockChainSet -> Network [ctor] .
op _ _ : Network Network            -> Network
         [ctor assoc comm id: emptyNetwork] .
\end{verbatim}

\begin{definition}[State]
The state of a system contains the current network, all publicly available
blockchains, a list of stakeholders that will be the leader for all remaining
slots, a beginning slot, and an ending slot. The state is either "active" (curly
braces) or "frozen" (square brackets).
\end{definition}

\begin{verbatim}
sort State .
op { _ | _ | _ | _ -> _ }
 : Network BlockChainSet StakeholderList Slot Slot -> State [ctor] .
op [ _ | _ | _ | _ -> _ ]
 : Network BlockChainSet StakeholderList Slot Slot -> State [ctor] .
\end{verbatim}

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
  => { (SH1[CHAINS1 ; CHAINS2]) NW | CHAINS2 | SH1 SHS | S1 + 1 -> S2 }
   .
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
  /\ S1 < S2
```

## Nondeterminism

In order for analysis of this protocol to be interesting, an adversary must have
some potential flexibility with how he or she interacts with the
protocol. First, note that a crucial assumption present in
[Ouroboros][ouroboros] (and most blockchain protocols) is that at least 51% of
the participants are acting truthfully. While the practicality of this
assumption can be argued, it is out of the scope of this paper. Thus, we will
assume at least 51% follow the protocol precisely as outlined in the beginning
of this section, and we will discuss potential behaviors of the "adversarial
49%" in this subsection.

An adversary has multiple ways to deviate from the protocol. For example, he
need not update his local blockchain set accordingly with all blockchains
previously leaders had broadcasted. However, this makes it more unlikely that
the chain the adversary adds his created block to will ultimately be the longest
chain in an epoch. Thus, with the first reward system mentioned, the adversary
will never be incentivized to not update his local blockchain set.

Next, crucially, the adversary can choose not to immediately broadcast his
updated blockchain to all other participants of the protocol. This is the main
adversarial behavior we analyze in this paper. By doing this, an adversary
potentially could mask the actual longest blockchain until the end of the epoch,
and force honest leaders to append blocks to what will turn out to not be the
longest blockchain. Thus, the adversary may yield a larger reward with this
dishonest behavior, as he would have created a larger percentage of blocks on
the ultimately longest chain.

## Reward System

The next intricacy of this algorithm involves the reward system given to the
stakeholders. We first analyze a reward scheme that does not incentivize
truthfulness, then show how this reward scheme can be modified.
TODO: need more here

## Analysis

Since we assume all honest participants deterministically follow the protocol,
we model all honest stakeholders as one stakeholder with 51% of stake:
\texttt{sh('honest, 51)}. Similarly, since we can assume all dishonest
participants adversarially collude, we model all dishonest stakeholders as one
stakeholder with 49% of stake: \texttt{sh('dishonest, 49)}.

Before covering the analysis of the protocol, we provide a couple more
definitions:

TODO: rules for honest

This states

The rules for the dishonest participants is as follows:

TODO: rules for dishonest

These rules emulate the nondeterminism mentioned in the previous
section. Specifically,

## Conclusion

## Future Work

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
themselves can be either truthful or not.

An alternative area for future work is considering other proof of stake
protocols. The main competitor to Ouroboros is Casper (TODO: cite) which is a
proof of stake protocol developed by the Ethereum Foundation. Casper greatly
differs from Ouroboros in a few areas. Primarily, it is developed as a "finality
gadget" that finalizes blocks in a proof of stake manner \textit{on top of} a
proof of work scheme.

Casper also requires a $\frac23$ majority instead of a $\frac12$ majority as in
Ouroboros. However, the $\frac23$ majority need only be \textit{rational} as
opposed to non-adversarial in Ouroboros (TODO: check this).  All these
differences lead to a much different protocol, and analyzing game-theoretic
properties of Casper is definitely worthy of its own rigorous treatment.

Finally, we also would like to consider different game theoretic properties of
this protocol. TODO: more here

# References

[ouroboros]: https://eprint.iacr.org/2016/889.pdf
[casper]: https://arxiv.org/abs/1710.09437
[blockchain-agt]: https://dl.acm.org/citation.cfm?id=2772879.2773270
[pathwaylogic]: https://doi.org/10.1016/S1571-0661(05)82533-2
[NPA]: http://www.sciencedirect.com/science/article/pii/S0304397506005780
[kmaude]: http://dx.doi.org/10.1007/978-3-642-16310-4_8
[twentyears]: http://www.sciencedirect.com/science/article/pii/S1567832612000707
