---
title: Incentive Compatibility Analysis of Ouroboros
author: Nishant Rodrigues, Lucas Peña
date: November 25, 2018
header-includes: |
   \newtheorem{definition}{Definition}
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

# Ouroboros

In this section we discuss the proof of stake algorithm used in Ouroboros, as
well as the assumptions we are making about the algorithm in this paper.

In [Ouroboros][ouroboros], The proof of stake algorithm is split into four
stages. Each stage adds complexity regarding details such as delay of the
system, endorsers of transactions, and more. We focus on the simplest version of
the prtocol for our analysis.

## Preliminaries

In this section, we go into detail regarding definitions needed to understand
the speicific algorithm we are modelling. Most definitions are taken from
[Ouroboros][ouroboros].

\begin{definition}[Stakeholder]
A stakeholder is a participant of the Ouroboros proof of stake algorithm.
\end{definition}

\begin{definition}[Stake]
Stake is the amount of money a stakeholder has put up as part of the Ouroboros 
algorithm. By definition, we assume the stake is nonzero for each stakeholder.
\end{definition}

\begin{definition}[Slot]
A slot is a discrete unit of time used for the protocol. We use natural numbers to model slots.
\end{definition}

\begin{definition}[Block]
A block is generated at a particular slot $sl_i$ by a stakeholder $s_i$.
It contains information regarding the slot number at which the block was created
as well as which stakeholder created the block.
\end{definition}

\begin{definition}[Blockchain]
A blockchain is a sequence of blocks with strictly increasing slots.
\end{definition}

\begin{definition}[Epoch]
An epoch is a set of $R$ adjacent slots $S = \{sl_1, \ldots, sl_R\}$.
\end{definition}

## Algorithm

At a high-level, the algorithm elects a leader for each slot. That leader should
add all publicly broadcasted blockhains into a local set. Then, the leader will
then create a block for that slot and append that block to the longest block in
her local set. Finally, she should broadcast that blockchain out to all other
stakeholders, and all stakeholders should update their local blockchains with
the newly broadcasted blockchain from the leader.

There are many subtleties with this algorithm. First, we need to fairly elect a
leader for each slot. This is done proportional to the amount of stake each
participant has. That is, if there are $n$ stakeholders, then for each slot $sl_j$,
stakeholder $i$ should be elected leader with probability

$$ p_i = \frac{s_i}{\sum_{k=1}^n s_k} $$

To implement this, the protocol flips a biased coin based on the relative stake
of participant $j$ in relation to participants $j+1,\ldots,n$, provided no
leader has been chosen yet. This ensures the leader of each slot is elected with
the desired probability.

The next intricacy of this algorithm involves the reward system given to the
stakeholders. We first analyze a reward scheme that does not incentivize
truthfulness, then show how this reward scheme can be modified.
TODO: need more here

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

## Analysis

## Conclusion and Future Work

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
