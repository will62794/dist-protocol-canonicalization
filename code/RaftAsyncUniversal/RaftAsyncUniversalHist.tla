--------------------------------- MODULE RaftAsyncUniversalHist ---------------------------------

\* 
\* Asynchronous specification of Raft, in a "canonicalized" message passing style.
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

\* Global set of all sent messages.
VARIABLE msgs

\* 
\* Server-local state variables
\* 

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The candidate the server voted for in its current term, or Nil if it hasn't voted.
VARIABLE votedFor

\* A sequence of log entries. The index into this sequence is the index of the log entry.
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

\* Variable sets.

serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>
candidateVars == <<votesGranted>>
leaderVars == <<nextIndex, matchIndex>>
vars == <<msgs, msgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex>>

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* Is log li a prefix of log lj.
IsPrefix(li,lj) == 
    /\ Len(li) <= Len(lj)
    /\ SubSeq(li, 1, Len(li)) = SubSeq(lj, 1, Len(li))

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
\* Includes that node's full state along with their node id (omit unused information).
\* 
BroadcastUniversalMsg(s) == 
    msgs' = msgs \cup {[
        from |-> s,
        currentTerm |-> currentTerm'[s],
        state |-> state'[s],
        votedFor |-> votedFor'[s],
        log |-> log'[s],
        commitIndex |-> commitIndex'[s]
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
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ UNCHANGED <<leaderVars, logVars, state>>
    /\ BroadcastUniversalMsg(i)

\* Server i grants its vote to a candidate server.
GrantVote(i, m) ==
    /\ m.currentTerm >= currentTerm[i]
    /\ LET  j     == m.from
            logOk == \/ LastTerm(m.log) > LastTerm(log[i])
                     \/ /\ LastTerm(m.log) = LastTerm(log[i])
                        /\ Len(m.log) >= Len(log[i])
            grant == /\ m.currentTerm >= currentTerm[i]
                     /\ logOk
                     /\ votedFor[i] \in {Nil, j} IN
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = IF grant THEN m.currentTerm ELSE currentTerm[i]]
            /\ UNCHANGED <<state, candidateVars, leaderVars, logVars>>
            /\ BroadcastUniversalMsg(i)

\* Leader i appends a new entry in its log.
ClientRequest(i) ==
    \* I am leader (history query).
    /\ \E Q \in Quorum : \A j \in Q : \E m \in msgs : m.currentTerm = currentTerm[i] /\ m.from = j /\ m.votedFor = i
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex>>
    /\ BroadcastUniversalMsg(i)

\* Server i appends a new log entry from some other server.
AppendEntry(i, m) ==
    /\ m.currentTerm = currentTerm[i]
    /\ state[i] \in { Follower } \* is this precondition necessary?
    \* Can always append an entry if we are a prefix of the other log, and will only
    \* append if other log actually has more entries than us.
    /\ IsPrefix(log[i], m.log)
    /\ Len(m.log) > Len(log[i])
    \* Only update logs in this action. Commit learning is done separately.
    /\ log' = [log EXCEPT ![i] = Append(log[i], m.log[Len(log[i]) + 1])]
    /\ UNCHANGED <<candidateVars, commitIndex, leaderVars, votedFor, currentTerm, state>>
    /\ BroadcastUniversalMsg(i)

\* Leader i advances its commitIndex using quorum Q.
AdvanceCommitIndex(i, Q, newCommitIndex) ==
    \* Leader precondition as query (state[i] = Leader).
    /\ \E LQ \in Quorum : \A j \in LQ : \E m \in msgs : m.currentTerm = currentTerm[i] /\ m.from = j /\ m.votedFor = i
    /\ newCommitIndex > commitIndex[i]
    \* History query precondition.
    /\ \A j \in Q : \E m \in msgs : 
        /\ m.from = j 
        /\ Len(m.log) >= newCommitIndex
        /\ log[i][newCommitIndex] = m.log[newCommitIndex]
        /\ m.currentTerm = currentTerm[i]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, log>>
    /\ BroadcastUniversalMsg(i)

\* Server i truncates its log based on detection of some other divergent log in a newer term.
TruncateEntry(i, m) ==
    \* I am not currently acting as leader of a term (history query).
    /\ ~(\E Q \in Quorum : \A j \in Q : \E mx \in msgs : mx.currentTerm = currentTerm[i] /\ mx.from = j /\ mx.votedFor = i)
    \* Neither log is a prefix of the other.
    /\ ~IsPrefix(m.log, log[i]) /\ ~IsPrefix(log[i], m.log)
    \* Can't truncate an empty log.
    /\ Len(log[i]) > 0
    \* Their log term is newer than yours.
    /\ LastTerm(m.log) > LastTerm(log[i])
    /\ state' = state \* [state EXCEPT ![i] = Follower]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    \* There is no need to broadcast your state on this action.
    /\ UNCHANGED <<candidateVars, msgs, leaderVars, votedFor, currentTerm, commitIndex>>

\* 
\* Server i learns of a new commitIndex from some other server.
\* 
\* The server it learned from must be on the same branch of
\* history, which is checked via the log prefix check.
\* 
LearnCommit(i, m) ==
    /\ m.currentTerm = currentTerm[i]
    /\ state[i] \in { Follower, Candidate }
    \* We can learn a commitIndex as long as our log is on the same history
    \* branch as the log of the node we are learning commitIndex from.
    /\ IsPrefix(log[i], m.log)
    /\ m.commitIndex > commitIndex[i] \* no need to ever decrement our commitIndex.
    \* Update commit index, without advancing to a point beyond the end of our log. 
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.commitIndex, Len(log[i])})]
    \* No need to send a response message since we are not updating our logs.
    /\ UNCHANGED <<candidateVars, msgs, leaderVars, log, votedFor, currentTerm, state, msgs>>

\* Defines how the variables may transition.
Next == 
    \/ \E i \in Server : BecomeCandidate(i)
    \/ \E i \in Server : \E m \in msgs : GrantVote(i, m)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i \in Server : \E m \in msgs : AppendEntry(i, m)
    \/ \E i \in Server, Q \in Quorum : \E newCommitIndex \in 1..Len(log[i]) : AdvanceCommitIndex(i, Q, newCommitIndex)
    \/ \E i \in Server : \E m \in msgs : UpdateTerm(i, m)
    \/ \E i \in Server : \E m \in msgs : TruncateEntry(i, m)
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
    \* /\ Cardinality(msgs) < 12

Symmetry == Permutations(Server)

\* In this spec we send at most 1 log entry per AppendEntries message. 
\* We encode this in the type invariant for convenience.
MaxMEntriesLen == 1

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

NextUnchanged == UNCHANGED vars

\* UpdateTermAction == \E i \in Server : \E m \in msgs : UpdateTerm(i, m)
\* BecomeCandidateAction == \E i \in Server : BecomeCandidate(i)
\* GrantVoteAction == \E i \in Server : \E m \in msgs : GrantVote(i, m)
\* RecordGrantedVoteAction == \E i \in Server : \E m \in msgs : RecordGrantedVote(i, m)
\* BecomeLeaderAction == \E i \in Server : BecomeLeader(i)
\* ClientRequestAction == \E i \in Server : ClientRequest(i)
\* AppendEntryAction == \E i \in Server : \E m \in msgs : AppendEntry(i, m)
\* TruncateEntryAction == \E i \in Server : \E m \in msgs : TruncateEntry(i, m)
\* LeaderLearnsOfAppliedEntryAction == \E i \in Server : \E m \in msgs : LeaderLearnsOfAppliedEntry(i, m)
\* \* AdvanceCommitIndexAction == \E i \in Server : AdvanceCommitIndex(i)
\* LearnCommitAction == \E i \in Server : \E m \in msgs : LearnCommit(i, m)

===============================================================================