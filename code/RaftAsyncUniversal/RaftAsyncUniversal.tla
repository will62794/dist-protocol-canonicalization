--------------------------------- MODULE RaftAsyncUniversal ---------------------------------

\* 
\* Asynchronous specification of Raft, in a "universal" message passing style.
\* 
\* Some original spec sources: 
\* https://github.com/ongardie/raft.tla
\* https://github.com/Vanlightly/raft-tlaplus/blob/main/specifications/standard-raft/Raft.tla
\* 

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, Bags, TLC, Randomization

\* The set of server IDs
CONSTANTS Server

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* 
\* Global set of all sent messages.
\* 
VARIABLE msgs

\* 
\* Server-local state variables
\* 

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex


\* 
\* Variable sets.
\* 

serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>
candidateVars == <<votesGranted>>
leaderVars == <<nextIndex, matchIndex>>
vars == <<msgs, msgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex>>

\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* Is log li a prefix of log lj.
IsPrefix(li,lj) == 
    /\ Len(li) <= Len(lj)
    /\ SubSeq(li, 1, Len(li)) = SubSeq(lj, 1, Len(li))

\* Return the minimum value from a set, or undefined if the set is empty.
\* Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
\* Max(s) == CHOOSE x \in s : \A y \in s : x >= y

--------

\* Initial states.
Init == 
    /\ msgs = {}
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Follower]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ votesGranted = [i \in Server |-> {}]
    /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]        
    /\ log             = [i \in Server |-> << >>]
    /\ commitIndex     = [i \in Server |-> 0]
    
\* 
\* Universal message type sent from server s. 
\* Includes that node's full state along with their node id.
\* 
\* Can omit unused information.
\* 
BroadcastUniversalMsg(s) == 
    msgs' = msgs \cup {[
        from |-> s,
        currentTerm |-> currentTerm'[s],
        state |-> state'[s],
        votedFor |-> votedFor'[s],
        log |-> log'[s],
        commitIndex |-> commitIndex'[s]
        \* votesGranted |-> votesGranted[s],
        \* nextIndex |-> nextIndex[s],
        \* matchIndex |-> matchIndex[s]    
    ]}

\* Update yourself to some newer term.
UpdateTerm(i, m) ==
    /\ m.currentTerm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.currentTerm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    /\ UNCHANGED <<msgs, candidateVars, leaderVars, logVars, msgs>>

\* Server increments its term and becomes a candidate for election.
BecomeCandidate(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ UNCHANGED <<leaderVars, logVars>>
    /\ BroadcastUniversalMsg(i)

\* Server i grants its vote to a candidate server.
GrantVote(i, m) ==
    \* /\ m.currentTerm <= currentTerm[i]
    /\ LET  j     == m.from
            logOk == \/ LastTerm(m.log) > LastTerm(log[i])
                     \/ /\ LastTerm(m.log) = LastTerm(log[i])
                        /\ Len(m.log) >= Len(log[i])
            grant == /\ m.currentTerm >= currentTerm[i]
                     /\ logOk
                     /\ votedFor[i] \in {Nil, j} IN
            \* /\ m.currentTerm <= currentTerm[i]
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m.currentTerm]
            /\ UNCHANGED <<state, candidateVars, leaderVars, logVars>>
            /\ BroadcastUniversalMsg(i)


\* Server i records a vote that was granted for it in its current term.
RecordGrantedVote(i, m) ==
    /\ m.currentTerm = currentTerm[i]
    /\ state[i] = Candidate
    /\ votesGranted' = [votesGranted EXCEPT ![i] = 
                            \* The sender must have voted for us in this term.
                            votesGranted[i] \cup 
                                IF (i = m.votedFor) THEN {m.from} ELSE {}]
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, msgs>>

\* Candidate i becomes a leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<msgs, currentTerm, votedFor, candidateVars, logVars, msgs>>
    /\ BroadcastUniversalMsg(i)

\* Leader i appends a new entry in its log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<serverVars, candidateVars,leaderVars, commitIndex>>
    /\ BroadcastUniversalMsg(i)

\* Server i appends a new log entry from some other server.
AppendEntry(i, m) ==
    /\ m.currentTerm = currentTerm[i]
    /\ state[i] \in { Follower, Candidate } \* is this precondition necessary?
    \* Can always append an entry if we are a prefix of the other log, and will only
    \* append if other log actually has more entries than us.
    /\ IsPrefix(log[i], m.log)
    /\ Len(m.log) > Len(log[i])
    \* Only update logs in this action. Commit learning is done separately.
    /\ log' = [log EXCEPT ![i] = Append(log[i], m.log[Len(log[i]) + 1])]
    /\ UNCHANGED <<candidateVars, commitIndex, leaderVars, votedFor, currentTerm, state>>
    /\ BroadcastUniversalMsg(i)

\* Server i truncates its log based on detection of some other divergent log in a newer term.
TruncateEntry(i, m) ==
    \* /\ m.currentTerm = currentTerm[m.mdest]
    /\ state[i] \in { Follower, Candidate }
    \* Neither log is a prefix of the other.
    /\ ~IsPrefix(m.log, log[i])
    /\ ~IsPrefix(log[i], m.log)
    \* Can't truncate an empty log.
    /\ Len(log[i]) > 0
    \* Their log term is newer than yours.
    /\ LastTerm(m.log) > LastTerm(log[i])
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    \* If we do roll back an entry, adjust our commit index accordingly so it
    \* doesn't point to something past the end of our new log. (TODO: is this safe?)
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({commitIndex[i], Len(log[i])-1})]
    \* There is no need to broadcast your state on this action.
    /\ UNCHANGED <<candidateVars, msgs, leaderVars, votedFor, currentTerm>>

\* Server i learns that another server has applied an entry up to some point in its log.
LeaderLearnsOfAppliedEntry(i, m) ==
    /\ state[i] = Leader
    \* Entry is applied in current term.
    /\ m.currentTerm = currentTerm[i]
    \* Only need to update if newer.
    /\ Len(m.log) > matchIndex[i][m.from]
    \* Follower must have a matching log entry.
    /\ Len(m.log) \in DOMAIN log[i]
    /\ m.log[Len(m.log)] = log[i][Len(m.log)]
    \* Update matchIndex to highest index of their log.
    /\ matchIndex' = [matchIndex EXCEPT ![i][m.from] = Len(m.log)]
    /\ UNCHANGED <<serverVars, candidateVars, logVars, nextIndex, msgs>>

\* The set of servers that agree up through index.
Agree(i, index) == {i} \cup {k \in Server : matchIndex[i][k] >= index }

\* Leader i advances its commitIndex.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) : Agree(i, index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)] = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, log>>
    /\ BroadcastUniversalMsg(i)

\* 
\* Server i learns of a new commitIndex from some other server.
\* 
\* The requirement is that the server it learned from is on the same branch of
\* history, which is checked \* via the log prefix check.
\* 
LearnCommit(i, m) ==
    /\ m.currentTerm = currentTerm[i]
    /\ state[i] \in { Follower, Candidate }
    \* We can learn a commitIndex as long as our log is on the same history branch as the log of
    \* the node we are learning commitIndex from.
    /\ IsPrefix(log[i], m.log)
    /\ m.commitIndex > commitIndex[i] \* no need to ever decrement our commitIndex.
    \* Update commit index, without advancing to a point beyond the end of our log. 
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.commitIndex, Len(log[i])})]
    \* No need to send a response message since we are not updating our logs.
    /\ UNCHANGED <<candidateVars, msgs, leaderVars, log, votedFor, currentTerm, state, msgs>>

\* Defines how the variables may transition.
Next == 
    \/ \E i \in Server : \E m \in msgs : UpdateTerm(i, m)
    \/ \E i \in Server : BecomeCandidate(i)
    \/ \E i \in Server : \E m \in msgs : GrantVote(i, m)
    \/ \E i \in Server : \E m \in msgs : RecordGrantedVote(i, m)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i \in Server : \E m \in msgs : AppendEntry(i, m)
    \/ \E i \in Server : \E m \in msgs : TruncateEntry(i, m)
    \/ \E i \in Server : \E m \in msgs : LeaderLearnsOfAppliedEntry(i, m)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i \in Server : \E m \in msgs : LearnCommit(i, m)

Spec == Init /\ [][Next]_vars

-----------------------

\* 
\* Invariants.
\* 

MinCommitIndex(s1, s2) ==
    IF commitIndex[s1] < commitIndex[s2]
        THEN commitIndex[s1]
        ELSE commitIndex[s2]


\* INV: NoLogDivergence
\* The log index is consistent across all servers (on those
\* servers whose commitIndex is equal or higher than the index).
H_NoLogDivergence ==
    \A s1, s2 \in Server :
        (s1 # s2) =>
            \A index \in 1..MinCommitIndex(s1, s2) : 
                /\ index \in DOMAIN log[s1]
                /\ index \in DOMAIN log[s2]
                /\ log[s1][index] = log[s2][index]

H_OnePrimaryPerTerm == 
    \A s,t \in Server : 
        (s # t /\ state[s] = Leader /\ state[t] = Leader) => currentTerm[s] # currentTerm[t]


-----------------------

\* Model checking stuff.

CONSTANT MaxTerm
CONSTANT MaxLogLen

Terms == 0..MaxTerm
LogIndices == 1..MaxLogLen
LogIndicesWithZero == 0..MaxLogLen


StateConstraint == 
    /\ \A s \in Server : currentTerm[s] <= MaxTerm
    /\ \A s \in Server : Len(log[s]) <= MaxLogLen

Symmetry == Permutations(Server)

\* In this spec we send at most 1 log entry per AppendEntries message. 
\* We encode this in the type invariant for convenience.
MaxMEntriesLen == 1

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

NextUnchanged == UNCHANGED vars

UpdateTermAction == \E i \in Server : \E m \in msgs : UpdateTerm(i, m)
BecomeCandidateAction == \E i \in Server : BecomeCandidate(i)
GrantVoteAction == \E i \in Server : \E m \in msgs : GrantVote(i, m)
RecordGrantedVoteAction == \E i \in Server : \E m \in msgs : RecordGrantedVote(i, m)
BecomeLeaderAction == \E i \in Server : BecomeLeader(i)
ClientRequestAction == \E i \in Server : ClientRequest(i)
AppendEntryAction == \E i \in Server : \E m \in msgs : AppendEntry(i, m)
TruncateEntryAction == \E i \in Server : \E m \in msgs : TruncateEntry(i, m)
LeaderLearnsOfAppliedEntryAction == \E i \in Server : \E m \in msgs : LeaderLearnsOfAppliedEntry(i, m)
AdvanceCommitIndexAction == \E i \in Server : AdvanceCommitIndex(i)
LearnCommitAction == \E i \in Server : \E m \in msgs : LearnCommit(i, m)

===============================================================================