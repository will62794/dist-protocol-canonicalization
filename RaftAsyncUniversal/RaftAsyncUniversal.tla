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

\* Global set of all sent messages.
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
\* All variables.
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

\* Return the minimum value from a set, or undefined if the set is empty.
\* Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
\* Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log             = [i \in Server |-> << >>]
               /\ commitIndex     = [i \in Server |-> 0]

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
UniversalMsg(s) == 
    [
        from |-> s,
        currentTerm |-> currentTerm[s],
        \* state |-> state[s],
        votedFor |-> votedFor[s],
        log |-> log[s],
        commitIndex |-> commitIndex[s]
        \* votesGranted |-> votesGranted[s],
        \* nextIndex |-> nextIndex[s],
        \* matchIndex |-> matchIndex[s]    
    ]

\* Server increments its term and becomes a candidate for election.
BecomeCandidate(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ msgs' = msgs \cup {UniversalMsg(i)}
    /\ UNCHANGED <<leaderVars, logVars>>

\* Candidate i becomes a leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<msgs, currentTerm, votedFor, candidateVars, logVars, msgs>>

\* Leader i appends a new entry in its log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ msgs' = msgs \cup {UniversalMsg(i)}
    /\ UNCHANGED <<serverVars, candidateVars,leaderVars, commitIndex>>

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
    /\ UNCHANGED <<msgs, serverVars, candidateVars, leaderVars, log, msgs>>

\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(dest) ==
    \E m \in msgs :
        /\ m.currentTerm > currentTerm[dest]
        /\ currentTerm'    = [currentTerm EXCEPT ![dest] = m.currentTerm]
        /\ state'          = [state       EXCEPT ![dest] = Follower]
        /\ votedFor'       = [votedFor    EXCEPT ![dest] = Nil]
           \* messages is unchanged so m can be processed further.
        /\ UNCHANGED <<msgs, candidateVars, leaderVars, logVars, msgs>>

\* Server i grants its vote to a candidate server.
GrantVote(i, m) ==
    /\ m.currentTerm <= currentTerm[i]
    /\ LET  j     == m.from
            logOk == \/ LastTerm(m.log) > LastTerm(log[i])
                     \/ /\ LastTerm(m.log) = LastTerm(log[i])
                        /\ Len(m.log) >= Len(log[i])
            grant == /\ m.currentTerm = currentTerm[i]
                     /\ logOk
                     /\ votedFor[i] \in {Nil, j} IN
            /\ m.currentTerm <= currentTerm[i]
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ msgs' = {UniversalMsg(i)}
            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* Server i records a vote that was granted for it in its current term.
RecordGrantedVote(i, m) ==
    /\ m.currentTerm = currentTerm[i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = 
                            \* The sender must have voted for us in this term.
                            votesGranted[i] \cup 
                                IF (i = m.votedFor) THEN {m.from} ELSE {}]
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, msgs>>

\* Is log li a prefix of log lj.
IsPrefix(li,lj) == 
    /\ Len(li) <= Len(lj)
    /\ SubSeq(li, 1, Len(li)) = SubSeq(lj, 1, Len(li))

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
    /\ msgs' = msgs \cup {UniversalMsg(i)}
    /\ UNCHANGED <<candidateVars, commitIndex, leaderVars, votedFor, currentTerm, state >>
       
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
    \* There is no need to broadcast your state on this action.
    /\ UNCHANGED <<candidateVars, msgs, leaderVars, commitIndex, votedFor, currentTerm>>

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

UpdateTermAction == \E i \in Server : UpdateTerm(i)
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

\* Defines how the variables may transition.
Next == 
    \/ UpdateTermAction
    \/ BecomeCandidateAction
    \/ GrantVoteAction
    \/ RecordGrantedVoteAction
    \/ BecomeLeaderAction
    \/ ClientRequestAction
    \/ AppendEntryAction
    \/ TruncateEntryAction
    \/ LeaderLearnsOfAppliedEntryAction
    \/ AdvanceCommitIndexAction
    \/ LearnCommitAction

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

\* RequestVoteRequestType == [
\*     mtype         : {RequestVoteRequest},
\*     mterm         : Terms,
\*     mlastLogTerm  : Terms,
\*     mlastLogIndex : LogIndicesWithZero,
\*     msource       : Server,
\*     mdest         : Server
\* ]

\* RequestVoteRequestTypeOp(T) == [
\*     mtype         : {RequestVoteRequest},
\*     mterm         : T,
\*     mlastLogTerm  : Terms,
\*     mlastLogIndex : LogIndicesWithZero,
\*     msource       : Server,
\*     mdest         : Server
\* ]


\* RequestVoteResponseType == [
\*     mtype        : {RequestVoteResponse},
\*     mterm        : Terms,
\*     mvoteGranted : BOOLEAN,
\*     msource      : Server,
\*     mdest        : Server
\* ]

\* RequestVoteResponseTypeOp(T) == [
\*     mtype        : {RequestVoteResponse},
\*     mterm        : T,
\*     mvoteGranted : BOOLEAN,
\*     msource      : Server,
\*     mdest        : Server
\* ]

\* AppendEntriesRequestType == [
\*     mtype      : {AppendEntriesRequest},
\*     mterm      : Terms,
\*     mprevLogIndex  : LogIndices,
\*     mprevLogTerm   : Terms,
\*     mentries       : BoundedSeq(Terms, MaxMEntriesLen),
\*     mcommitIndex   : LogIndicesWithZero,
\*     msource        : Server,
\*     mdest          : Server
\* ]

\* AppendEntriesResponseType == [
\*     mtype        : {AppendEntriesResponse},
\*     mterm        : Terms,
\*     msuccess     : BOOLEAN,
\*     mmatchIndex  : LogIndices,
\*     msource      : Server,
\*     mdest        : Server
\* ]


\* Set of all subsets of a set of size <= k.
\* kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

\* 
\* Work around size limitations of TLC subset computations.
\* 

\* RequestVoteResponseTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteResponseTypeOp({t})) : t \in Terms }
\* RequestVoteRequestTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteRequestTypeOp({t})) : t \in Terms }

\* RequestVoteType == RandomSetOfSubsets(3, 3, RequestVoteRequestType) \cup RandomSetOfSubsets(3, 3, RequestVoteResponseType)  
\* AppendEntriesType == RandomSetOfSubsets(3, 3, AppendEntriesRequestType) \cup RandomSetOfSubsets(3, 3, AppendEntriesResponseType)  

\* TypeOK == 
\*     /\ msgs \in RequestVoteType
\*     /\ msgs \in AppendEntriesType
\*     /\ currentTerm \in [Server -> Terms]
\*     /\ state       \in [Server -> {Leader, Follower, Candidate}]
\*     /\ votedFor    \in [Server -> ({Nil} \cup Server)]
\*     /\ votesGranted \in [Server -> (SUBSET Server)]
\*     /\ nextIndex  \in [Server -> [Server -> LogIndices]]
\*     /\ matchIndex \in [Server -> [Server -> LogIndicesWithZero]]        
\*     /\ log             \in [Server -> BoundedSeq(Terms, MaxLogLen)]
\*     /\ commitIndex     \in [Server -> LogIndicesWithZero]
\*     \* Encode these basic invariants into type-correctness.
\*     /\ \A m \in msgs : m.msource # m.mdest
\*     /\ \A m \in msgs : m.msource # m.mdest



-----------------------


\********************
\* Various lemmas.
\********************

\* \* Is log entry e = <<index, term>> in the log of node 'i'.
\* InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.
\* CommittedEntriesReachMajority ==
\*     IF \E i \in Server : state[i] = Leader /\ commitIndex[i] > 0
\*     THEN \E i \in Server :
\*            /\ state[i] = Leader
\*            /\ commitIndex[i] > 0
\*            /\ \E quorum \in SUBSET Server :
\*                /\ Cardinality(quorum) = (Cardinality(Server) \div 2) + 1
\*                /\ i \in quorum
\*                /\ \A j \in quorum :
\*                    /\ Len(log[j]) >= commitIndex[i]
\*                    /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
\*     ELSE TRUE

\* H_QuorumsSafeAtTerms ==
\*     \A s \in Server : (state[s] = Leader) => 
\*         \E Q \in Quorum : 
\*             \A t \in Q : 
\*                 /\ currentTerm[t] >= currentTerm[s]
\*                 /\ (currentTerm[t] = currentTerm[s]) => votedFor[t] # Nil

\* \* If two nodes are in the same term, then their votes granted
\* \* sets cannot have intersecting voters.
\* H_CandidateVotesGrantedInTermAreUnique ==
\*     \A s,t \in Server :
\*         (/\ s # t
\*          /\ state[s] = Candidate
\*          /\ state[t] = Candidate
\*          /\ currentTerm[s] = currentTerm[t]) =>
\*             (votesGranted[s] \cap votesGranted[t]) = {}

\* \* If a node has garnered votes in a term as candidate, there must
\* \* be no other leader in that term in existence.
\* H_CandidateWithVotesGrantedInTermImplyNoOtherLeader ==
\*     \A s,t \in Server :
\*         (/\ s # t
\*          /\ state[s] = Candidate
\*          /\ votesGranted[s] \in Quorum
\*          /\ currentTerm[s] = currentTerm[t]) =>
\*             state[t] # Leader

\* \* Does there exist a quorum of RequestVote responses in term T
\* \* that support voting for server 'dest'.
\* ExistsRequestVoteResponseQuorum(T, dest) == 
\*     \E ms \in SUBSET msgs : 
\*         /\ \A m \in ms : m.mtype = RequestVoteResponse
\*             /\ m.mterm = T
\*             /\ m.mdest = dest
\*             /\ m.mvoteGranted
\*         \* Responses form a quorum.
\*         /\ ({m.msource : m \in ms} \cup {dest}) \in Quorum

\* \* If a successful quorum of request vote repsonses was sent in term T, then 
\* \* there can be no logs that exist in term T.
\* \* TODO: Fix this to get a correct statement here.
\* H_SuccessfulRequestVoteQuorumInTermImpliesNoLogsInTerm ==
\*     \A t \in Terms : 
\*     \E dest \in Server : 
\*         (/\ ExistsRequestVoteResponseQuorum(t, dest)
\*          /\ (~\E l \in Server : state[l] = Leader /\ currentTerm[l] = t)) => 
\*             \A s \in Server : \A ind \in DOMAIN log[s] : log[s][ind] # t

\* H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm ==
\*     \A s,t \in Server :
\*         (state[s] = Candidate /\ votesGranted[s] \in Quorum) =>
\*             ~(\E i \in DOMAIN log[t] : log[t][i] = currentTerm[s])

\* H_RequestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm == 
\*     \A s \in Server :
\*         (/\ state[s] = Candidate
\*          /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
\*             /\ \A n \in Server : \A ind \in DOMAIN log[n] : log[n][ind] # currentTerm[s]
\*             /\ \A n \in Server : ~(state[n] = Leader /\ currentTerm[n] = currentTerm[s])

\* H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm == 
\*     \A s \in Server :
\*         (/\ state[s] = Candidate
\*          /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
\*             ~(\E m \in msgs :   
\*                 /\ m.mtype = AppendEntriesRequest
\*                 /\ m.mentries # <<>>
\*                 /\ m.mentries[1] = currentTerm[s])

\* H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm ==
\*     \A s \in Server :
\*         (state[s] = Candidate /\ votesGranted[s] \in Quorum) =>
\*         ~(\E m \in msgs :   
\*             /\ m.mtype = AppendEntriesRequest
\*             /\ m.mentries # <<>>
\*             /\ m.mentries[1] = currentTerm[s])


\* \* If request vote response message has been sent in term T,
\* \* then the sender must be at least in term T.
\* H_RequestVoteResponseTermsMatchSource ==
\*     \A m \in msgs :
\*         m.mtype = RequestVoteResponse => 
\*             /\ currentTerm[m.msource] >= m.mterm
\*             /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest


\* \* If a candidate C has garnered a set of granted votes in term T, 
\* \* then all of those voters must be at term T or newer, and if they
\* \* are in term T, then they must have voted for C.
\* H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm ==
\*     \A s \in Server : 
\*         (state[s] = Candidate) =>
\*             \A v \in votesGranted[s] : 
\*                 /\ currentTerm[v] >= currentTerm[s]
\*                 /\ currentTerm[v] = currentTerm[s] => votedFor[v] # Nil

\* \* H_CandidateWithVotesGrantedInTermImplyVotedForSafeAtTerm ==
\* \*     \A s \in Server : 
\* \*         (state[s] = Candidate /\ votesGranted[s] \in Quorum) =>
\* \*             \A v \in votesGranted[s] : 
\* \*                 /\ currentTerm[v] = currentTerm[s] => votedFor[v] # Nil

\* \* If a server exists in voteGranted for some server in term T, and the node is still in
\* \* term T, then it must have voted for that node.
\* H_VoteInGrantedImpliesVotedFor == 
\*     \A s,t \in Server :
\*         (/\ state[s] = Candidate
\*          /\ t \in votesGranted[s]) => 
\*             /\ currentTerm[t] >= currentTerm[s]
\*             /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s


\* \* If a server has granted its vote to a server S in term T, then
\* \* there can't be a vote response message from that server to some other server R # S.
\* H_VoteGrantedImpliesVoteResponseMsgConsistent ==
\*     \A s,t \in Server : 
\*         ( /\ state[s] = Candidate 
\*           /\ t \in votesGranted[s]) =>
\*             ~\E m \in msgs :
\*                 /\ m.mtype = RequestVoteResponse
\*                 /\ m.mterm = currentTerm[s]
\*                 /\ m.msource = t
\*                 /\ m.mdest # s
\*                 /\ m.mvoteGranted

\* H_VotesCantBeGrantedTwiceToCandidatesInSameTerm ==
\*     \A s,t \in Server : 
\*         ( /\ s # t 
\*           /\ state[s] = Candidate 
\*           /\ state[t] = Candidate
\*           /\ currentTerm[s] = currentTerm[t]) =>
\*             \* Cannot be intersection between voters that gave votes to candidates in same term.
\*             votesGranted[s] \cap votesGranted[t] = {}

\* \* H_VotesCantBeGrantedTwiceToCandidatesInSameTerm == 
\* \*     \A s,t \in Server : 
\* \*         \* If s voted for t.
\* \*         (votedFor[s] = t)

\* H_CurrentTermAtLeastAsLargeAsLogTerms == 
\*     \A s \in Server : 
\*         (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* \* A server's current term is always at least as large as the terms in its log.
\* H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary == 
\*     \A s \in Server : 
\*         (state[s] = Leader) => 
\*             (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* H_LogTermsMonotonic == 
\*     \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])

\* H_LogTermsMonotonicAppendEntries == 
\*     \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])

\* \* If a log entry exists in term T and there is a primary in term T, then this
\* \* log entry should be present in that primary's log.
\* H_PrimaryHasEntriesItCreated == 
\*     \A i,j \in Server :
\*     (state[i] = Leader) => 
\*     \* Can't be that another node has an entry in this primary's term
\*     \* but the primary doesn't have it.
\*         ~(\E k \in DOMAIN log[j] :
\*             /\ log[j][k] = currentTerm[i]
\*             /\ ~InLog(<<k,log[j][k]>>, i))

\* \* If an AppendEntries request has been sent with some log entries in term T, then a current
\* \* leader in term T must have these log entries.
\* H_PrimaryHasEntriesItCreatedAppendEntries == 
\*     \A s \in Server :
\*     \A m \in msgs :
\*         (/\ m.mtype = AppendEntriesRequest
\*          /\ m.mentries # <<>> 
\*          /\ m.mentries[1] = currentTerm[s]
\*          /\ state[s] = Leader) =>
\*             /\ (m.mprevLogIndex + 1) \in DOMAIN log[s]
\*             /\ log[s][m.mprevLogIndex + 1] = m.mentries[1]

\* \* Existence of an entry in term T implies a past election in T, so 
\* \* there must be some quorum at this term or greater.
\* H_LogEntryInTermImpliesSafeAtTerm == 
\*     \A s \in Server : 
\*     \A i \in DOMAIN log[s] :
\*         \E Q \in Quorum : \A n \in Q : 
\*             /\ currentTerm[n] >= log[s][i]
\*             /\ currentTerm[n] = log[s][i] => (votedFor[n] # Nil)


\* \* If an AppendEntries request was sent in term T, then there must have been a successful 
\* \* election in term T.
\* H_AppendEntriesRequestInTermImpliesSafeAtTerms == 
\*     \A m \in msgs : 
\*         m.mtype = AppendEntriesRequest =>
\*             \E Q \in Quorum : \A t \in Q : currentTerm[t] >= m.mterm

\* H_LogEntryInTermImpliesSafeAtTermAppendEntries ==
\*     \A m \in msgs : 
\*         (/\ m.mtype = AppendEntriesRequest
\*          /\ m.mentries # <<>>) =>
\*             \E Q \in Quorum : \A n \in Q : 
\*                 /\ currentTerm[n] >= m.mentries[1]
\*                 /\ currentTerm[n] = m.mentries[1] => (votedFor[n] # Nil)


\* \* <<index, term>> pairs uniquely identify log prefixes.
\* H_LogMatching == 
\*     \A s,t \in Server : 
\*     \A i \in DOMAIN log[s] :
\*         (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
\*         (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* H_LogMatchingInmsgs ==
\*     \* If a server contains the log entry being sent in this AppendEntries, 
\*     \* then the server's previous entry must match the AppendEntries previous entry.
\*     \A m \in msgs : 
\*     \A s \in Server : 
\*         (\E ind \in DOMAIN log[s] : 
\*             /\ m.mtype = AppendEntriesRequest
\*             /\ m.mentries # <<>>
\*             /\ ind = m.mprevLogIndex + 1 
\*             /\ log[s][ind] = m.mentries[1]
\*             /\ m.mprevLogIndex \in DOMAIN log[s]) =>
\*                 log[s][m.mprevLogIndex] = m.mprevLogTerm

\* \* Has a candidate server garnered all votes to win election in its term.
\* CandidateWithVoteQuorumGranted(s) == 
\*     /\ state[s] = Candidate
\*     /\ votesGranted[s] \in Quorum

\* H_DivergentEntriesInmsgsForRequestVoteQuorum ==
\*     \A m \in msgs : 
\*     \A s \in Server : 
\*         (/\ m.mtype = AppendEntriesRequest
\*          /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)
\*          /\ m.mprevLogIndex + 1 > Len(log[s])) => 
\*             (m.mentries # <<>> => m.mentries[1] # currentTerm[s]) 

\* H_DivergentEntriesInmsgs == 
\*     \* An AppendEntries cannot contain log entries in term T at newer indices than
\*     \* a leader or pending candidate's log in term T.
\*     \A m \in msgs : 
\*     \A s \in Server : 
\*         (/\ m.mtype = AppendEntriesRequest
\*          /\ (state[s] = Leader \/ CandidateWithVoteQuorumGranted(s))
\*          /\ m.mprevLogIndex + 1 > Len(log[s])) => 
\*             (m.mentries # <<>> => m.mentries[1] # currentTerm[s]) 

\* \* If a leader server has a match index recorded, the remote node's log
\* \* must match its own log up to this index.

\* H_RequestVotesNeverSentToSelf == 
\*     \A m \in msgs : m.msource # m.mdest

\* H_AppendEntriesNeverSentToSelf == 
\*     \A m \in msgs : m.msource # m.mdest

\* H_AppendEntriesCommitIndexCannotBeLargerThanTheSender == 
\*     \A m \in msgs :
\*         m.mtype = AppendEntriesRequest => 
\*         m.mcommitIndex <= commitIndex[m.msource] 

\* \* Match index records for a leader must always be <= its own log length.
\* H_LeaderMatchIndexBound == 
\*     \A s \in Server : (state[s] = Leader) => 
\*         \A t \in Server : matchIndex[s][t] <= Len(log[s])

\* ExistsNodeQuorumThatVotedAtTermFor(T, s) == 
\*     \E Q \in Quorum :
\*     \A t \in Q :
\*         /\ votedFor[t] = s
\*         /\ currentTerm[t] = T

\* H_NodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm == 
\*     \A s \in Server :
\*         (/\ state[s] = Candidate
\*          /\ ExistsNodeQuorumThatVotedAtTermFor(currentTerm[s], s)) =>
\*             ~(\E m \in msgs : 
\*                 /\ m.mtype = AppendEntriesRequest
\*                 /\ m.mterm = currentTerm[s])


\* H_RequestVoteQuorumInTermImpliesNoAppendEntriesRequestsInTerm == 
\*     \A s \in Server :
\*         (/\ state[s] = Candidate
\*          /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
\*             ~(\E m \in msgs : 
\*                 /\ m.mtype = AppendEntriesRequest
\*                 /\ m.mterm = currentTerm[s])

\* \* If a server candidate has won votes in term T, there can't be
\* \* any AppendEntries messages already sent in that term.
\* H_CandidateWithVotesGrantedImpliesNoAppendEntriesRequestsInTerm == 
\*       \A s \in Server :
\*         (/\ state[s] = Candidate
\*          /\ votesGranted[s] \in Quorum) =>
\*             ~\E m \in msgs : 
\*                 /\ m.mtype = AppendEntriesRequest
\*                 /\ m.mterm = currentTerm[s]

\* \* The logs in any AppendEntries message sent in term T must be present
\* \* in the logs of a leader in term T.
\* H_AppendEntriesRequestLogEntriesMustBeInLeaderLog == 
\*     \A m \in msgs : 
\*         (/\ m.mtype = AppendEntriesRequest
\*          /\ m.mentries # <<>>
\*          /\ state[m.msource] = Leader
\*          /\ m.mprevLogIndex > 0
\*          /\ currentTerm[m.msource] = m.mterm) =>
\*             /\ Len(log[m.msource]) >= m.mprevLogIndex + 1
\*             /\ log[m.msource][m.mprevLogIndex + 1] = m.mentries[1]
\*             /\ log[m.msource][m.mprevLogIndex] = m.mprevLogTerm


\* \* If a AppendEntries response has been sent in term T recording a match up to
\* \* index I, then the sender node should have the same entry as the leader.
\* H_LeaderMatchIndexValidAppendEntries == 
\*     \A m \in msgs : 
\*         (/\ m.mtype = AppendEntriesResponse
\*          /\ m.msuccess
\*          /\ m.mmatchIndex > 0
\*          /\ state[m.mdest] = Leader
\*          /\ m.mterm = currentTerm[m.mdest]) =>
\*             /\ Len(log[m.msource]) >= m.mmatchIndex
\*             /\ Len(log[m.mdest]) >= m.mmatchIndex
\*             /\ log[m.msource][m.mmatchIndex] = log[m.mdest][m.mmatchIndex]

\* \* If matchIndex on a leader has quorum agreement on an index, then this entry must
\* \* be present on a quorum of servers.
\* H_LeaderMatchIndexValid == 
\*     \A s \in Server :
\*     \A ind \in DOMAIN log[s] :
\*     \E Q \in Quorum : 
\*     \A t \in Q :
\*         (/\ state[s] = Leader 
\*          /\ Agree(s, ind) \in Quorum ) => 
\*             /\ ind \in DOMAIN log[t]
\*             /\ log[t][ind] = log[s][ind]

\* H_CommitIndexCoversEntryImpliesExistsOnQuorum == 
\*     \A s \in Server :
\*         (commitIndex[s] > 0) => 
\*             \E Q \in Quorum :
\*             \A t \in Q :
\*                 /\ Len(log[s]) >= commitIndex[s] 
\*                 /\ Len(log[t]) >= commitIndex[s] 
\*                 /\ log[t][commitIndex[s]] = log[s][commitIndex[s]]

\* \* If a commit index covers a log entry in some term,
\* \* then no primary in an earlier term can be enabled to commit any entries
\* \* in its own log.
\* H_CommitIndexAtEntryInTermDisabledEarlierCommits == 
\*     \A s,t \in Server :
\*         (/\ s # t 
\*          /\ commitIndex[s] > 0
\*          /\ state[t] = Leader
\*          /\ currentTerm[t] < log[s][commitIndex[s]]) =>
\*                 \A ind \in DOMAIN log[t] : Agree(t, ind) \notin Quorum 


\* \* If an AppendEntries has been sent with a commitIndex that covers some 
\* \* log entry in the message, there must be some node that has that entry 
\* \* and equal or newer commitIndex.
\* H_CommitIndexInAppendEntriesImpliesCommittedEntryExists == 
\*     \A m \in msgs : 
\*         ( /\ m.mtype = AppendEntriesRequest 
\*           /\ m.mcommitIndex > 0
\*           /\ m.mentries # <<>> 
\*           /\ m.mprevLogIndex > 0) =>
\*             (\E n \in Server :
\*              \E ind \in DOMAIN log[n] :
\*                 (/\ ind = m.mprevLogIndex
\*                  /\ log[n][ind] = m.mprevLogTerm
\*                  /\ commitIndex[n] >= m.mcommitIndex))


\* H_LogEntryInTermDisablesEarlierCommits == 
\*     \A s,t \in Server :
\*     \A si \in DOMAIN log[s] :
\*         (/\ s # t 
\*          /\ state[t] = Leader
\*          /\ currentTerm[t] < log[s][si]) =>
\*                 \A ind \in DOMAIN log[t] : (Agree(t, ind) > commitIndex[t]) => Agree(t, ind) \notin Quorum 

\*             \* \A t \in Q : Len(log[t]) >= commitIndex[s] /\ log[t][commitIndex[s]] = log[s][commitIndex[s]]

\* \* Commit index is no greater than the log length on any node.
\* H_CommitIndexBoundValid == 
\*     \A s \in Server : commitIndex[s] <= Len(log[s])


\* INV: Used in debugging
TestInv ==
    \* ~\E s,t \in Server : state[s] = Leader /\ state[s] = Candidate /\ Len(log[t]) > 0 /\ currentTerm[s] = currentTerm[t]
    \* \A s \in Server : state[s] = Candidate => Len(log[s]) = 0
    \* ~\E s,t \in Server : s # t /\ commitIndex[s] > 0 /\ commitIndex[t] > 0
    \* /\ ~\E msgs \in SUBSET msgs : msgs # {}
    \* /\ ~(\E msgs \in (SUBSET msgs) : 
    \*         /\ PrintT(SUBSET msgs)
    \*         /\ msgs # {} 
    \*         /\ (\A m \in msgs : m.mtype = RequestVoteResponse))
    \* /\ PrintT({s \in Server : ExistsRequestVoteResponseQuorum(1, s)})
    \* \A n \in Server : 
    \* \A t \in Terms : 
    \*     ~ExistsRequestVoteResponseQuorum(t, n)


    \* ~\E m \in msgs : (m.mtype = RequestVoteResponse /\ m.mvoteGranted)
    \* ~\E s \in Server : Cardinality(votesGranted[s]) > 1
    \* /\ ~\E s,t \in Server : s # t /\ log[s] # <<>> /\ log[t] # <<>>
    [][~LearnCommitAction]_vars
    \* ~\E s \in Server : state[s] = Leader
===============================================================================