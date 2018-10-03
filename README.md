# Incentive Compatibility Analysis of Ouroboros

Authors: Lucas Peña, Nishant Rodrigues

# Proposal

- PoW -> PoS summary (Nishant)

- Truthfulness importance for blockchain protocols
In the blockchain domain, security is of the utmost importance. Cryptocurrency would inevitably fail if it was in a miner's best interest to lie about things like block validity or a transaction occurring. In the domain of proof of stake, these security concerns are heightened. As users rather than miners now have control over the introduction of new currency, it is perhaps more critical that a proof of stake protocol is truthful.

- High-level abstraction of Ouroboros
Our project focuses on Ouroboros [1], one of the first proof of stake based blockchain protocols, used in the coin Cardano. Ouroboros is a complicated algorithm, so we first plan on producing a high-level abstraction of this proof of stake algorithm, amenable to modelling and proving complex properties. Then we will perform an incentive compatibility analysis of our abstraction. We will determine if the abstraction is dominant-strategy-incentive-compatible (DSIC) or Bayesian-incentive-compatible (BIC) in the weaker case. If not, we will attempt to make minor adjustments in order to achieve these nice properties. Next, we will focus on a formal analysis in Maude.

- Maude intro, application to formal analysis (Nishant)

- Formal analysis of abstraction in Maude (Nishant)

- Future work/extensions/other directions (Casper, paper analysis)
This project has many opportunities for future work. First of all, we can work on tightening our abstraction until we match all the specifications of Ouroboros. This would provide the utmost confidence with the truthfulness (or lack thereof) of the scheme as defined in [1]. We can also compare and contrast the truthfulness of Ouroboros with other proof of stake schemes such as Casper [2], a currently in-development proof of stake protocol for Ethereum.

It is possible this project is more ambitious than anticipated. Our plan is to at least have an abstraction of Ouroboros and prove DSIC and BIC properties about our abstraction.

# References

- https://eprint.iacr.org/2016/889.pdf
- Maude
- Proof of work/Proof of stake/combined paper
- https://arxiv.org/abs/1710.09437
- https://arxiv.org/abs/1710.09437
- other AGT blockchain paper(s)

