# Research Log

## 2024-06-24

Wrote [draft proposal](https://docs.google.com/document/d/1V-U1vVb2OKdwG549wcsOmCZ_3yPOwCGFRYqZKMhQzP0/edit) for research project on “universal message passing” style modeling for distributed protocols.

Working on Raft model in the “universal” message passing style. As a starting point, trying to get to a basic, correct model e.g. satisfying high level NoLogDivergence safety property. After that, one tentative goal may be to think about how you would then go from the “universal” version of the protocol to different variants with different communication/messaging patterns. For example, 
A standard variant of Raft with AppendEntries and RequestVote, 
Another one where LearnCommit is separated into a different message pathway. 
Version where secondaries eagerly advance commit point before primary does it for them (?)
Version with chained replication i.e. secondaries can sync log entries from any other node?

Note [this counterexample](https://github.com/will62794/dist-protocol-canonicalization/blob/2381f58d9f9b725f4f0bcc8964a79fa75b51c9ff/notes/raft_truncate_univ_cex.txt) related to log truncation, where a node rolls back a log entry behind its commit point because there is a divergent log with newer term sitting around in the message history, but that branch (in term 2) was actually also rolled back and is stale now. Does this imply that log truncation implicitly also needs some kind of term checking in order to be safe? The node that rolls back in that case is in term 3, and the node it is rolling back against is in term 2.

Different notions of “committed”: log entry is present on every future leader vs. “committed entry is never rolled back”. Possible to be safe if you mark an entry as committed but do roll it back in some cases, as long as, globally, that entry will be durable on every future leader?

We can [allow commit index](https://github.com/will62794/dist-protocol-canonicalization/commit/e6839d4f07825814d23f0c9d3b62df1745d0c11d) to move backwards when rolling back log entries in some cases, while retaining safety? 

From Slack chat:

```
Agreed. And to ensure remaining a bit grounded/targeted for the summer, do you think those are two good concrete goals to aim for as initial case studies? i.e.

1. Chain replication in Raft
2. Secondaries advance commit points
3. LeaseGuard related optimizations (details to be clarified?)

And, separate from a full paper, I'm also just thinking about tentative, concrete results that would be interesting to present at the end of the summer. If we could demonstrate even those kinds of optimizations within our model, that seems a valuable/interesting result to others, yes?
```

N.B. As a stretch goal we should also find a protocol that is non-Paxos.

*Tomorrow let's plan to come up with a technical report by the end of 10 weeks. It is very reasonable to have a paper submission draft by the end of 10 weeks*.

Is there also some notion of "maximal" progress that a node can take at each step of a protocol, based on the information currently available to it in the network and on its current state? Like, updating log and commit point and/or rolling back all in one go. This might also be split up into several different atomic actions?