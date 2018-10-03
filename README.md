# Incentive Compatibility Analysis of Ouroboros (Research)

Authors: Lucas Peña, Nishant Rodrigues

# Proposal

Crypotocurrencies generally utilize a "proof of work" scheme to deter denial of
service and other attacks. A key aspect to proof of work schemes is that they
must be expensive to compute, yet easy to verify. Most major Cryptocurrency
networks use CPU bound schemes that, for example, involve repeatedly calculating
cryptographic hashes. While this scheme is effecitve in securing the network, it
is extremely energy-hungry. It has been estimated that globally, bitcoin mining
consumes electricity on a scale comaprable to the that of Ireland. An
alternative, proof of stake, attempts to address this. It attempts to chose the
a block through a voting mechanism. The dynamics of this mechanism is however
complex, are various incentives working at cross-purposes (if the block I vote
for gets selected I rewarded; voters could control miners; voters could attempt
denial of service attacks; etc).

In the blockchain domain, security is of the utmost importance. Cryptocurrency
would inevitably fail if it was in a miner's best interest to lie about things
like block validity or a transaction occurring. In the domain of proof of stake,
these security concerns are heightened. As users rather than miners now have
control over the introduction of new currency, it is perhaps more critical that
a proof of stake protocol is truthful.

Our project focuses on Ouroboros [ouroboros], one of the first proof of stake
based blockchain protocols, used in the coin Cardano. Ouroboros is a complicated
algorithm, so we first plan on producing a high-level abstraction of this proof
of stake algorithm, amenable to modelling and proving complex properties. Then
we will perform an incentive compatibility analysis of our abstraction. We will
determine if the abstraction is dominant-strategy-incentive-compatible (DSIC) or
Bayesian-incentive-compatible (BIC) in the weaker case. If not, we will attempt
to make minor adjustments in order to achieve these nice properties. Next, we
will focus on a formal analysis in Maude.

The Maude System is a programming language often used for modeling and
verification of systems. It has been used to verify a wide spectrum of systems,
from biological systems (Pathway Logic [pathwaylogic]), to Cryptographic
Protocols (Maude NPA [NPA]), to concensus algorithms, to programming languages
(KFramework [kmaude]), and so on (see [twentyears] for a comprehensive survey
of such applications). Maude allows specifying systems, including their
non-deterministic behaviours, as a transition system using rewriting logic. for
model checking purposes they provide a very high level formalism for
axiomatizing possibly infinite Kripke structures. This is exploited in Maude for
formal analysis purposes, since concurrent systems specified as rewrite theories
can be analyzed using Maude's LTL model checker and other model checkers and
theorem proving tools in Maude's formal environment.

We intend to leverage these capabilities of Maude to write a high level
specification (eliding details that aren't important to an AGT analysis),
and to use this specification to formally verify certain game theoretic properties
of the protocol.

This project has many opportunities for future work. First of all, we can work
on tightening our abstraction until we match all the specifications of
Ouroboros. This would provide the utmost confidence with the truthfulness (or
lack thereof) of the scheme as defined in [ouroboros]. We can also compare and
contrast the truthfulness of Ouroboros with other proof of stake schemes such as
Casper [casper], a currently in-development proof of stake protocol for
Ethereum.

It is possible this project is more ambitious than anticipated. Our plan is to
at least have an abstraction of Ouroboros and prove DSIC and BIC properties
about our abstraction.

# References

[ouroboros]: https://eprint.iacr.org/2016/889.pdf
[casper]: https://arxiv.org/abs/1710.09437
[blockchain-agt]: https://dl.acm.org/citation.cfm?id=2772879.2773270

[pathwaylogic]: https://doi.org/10.1016/S1571-0661(05)82533-2
[NPA] : http://www.sciencedirect.com/science/article/pii/S0304397506005780
[kmaude]: http://dx.doi.org/10.1007/978-3-642-16310-4_8
[twentyears] : http://www.sciencedirect.com/science/article/pii/S1567832612000707
