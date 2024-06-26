--------------------------------- MODULE RaftAsyncUniversal_RequestVote ---------------------------------
EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, Bags

CONSTANTS Server
CONSTANTS Follower, Candidate, Leader
CONSTANTS Nil

CONSTANT MaxTerm
CONSTANT MaxLogLen


VARIABLE msgs
VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
VARIABLE log
VARIABLE commitIndex
VARIABLE votesGranted
VARIABLE nextIndex
VARIABLE matchIndex

serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>
candidateVars == <<votesGranted>>
leaderVars == <<nextIndex, matchIndex>>
vars == <<msgs, msgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex>>

BroadcastUniversalMsgLabeled(s, l) == 
    msgs' = msgs \cup {[
        from |-> s,
        currentTerm |-> currentTerm[s],
        state |-> state[s],
        votedFor |-> votedFor[s],
        log |-> log[s],
        commitIndex |-> commitIndex[s],
        \* votesGranted |-> votesGranted[s],
        \* nextIndex |-> nextIndex[s],
        \* matchIndex |-> matchIndex[s]   
        label |-> l
    ]}

RaftUniv == INSTANCE RaftAsyncUniversal WITH
                        Server <- Server,
                        Follower <- Follower,
                        Candidate <- Candidate,
                        Leader <- Leader,
                        Nil <- Nil,
                        msgs <- msgs,
                        currentTerm <- currentTerm,
                        state <- state,
                        votedFor <- votedFor,
                        log <- log,
                        commitIndex <- commitIndex,
                        votesGranted <- votesGranted,
                        nextIndex <- nextIndex,
                        matchIndex <- matchIndex,
                        MaxTerm <- MaxTerm,
                        MaxLogLen <- MaxLogLen

\* Server increments its term and becomes a candidate for election.
BecomeCandidate(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ BroadcastUniversalMsgLabeled(i, "RequestVoteRequest")
    /\ UNCHANGED <<leaderVars, logVars>>

\* Server i grants its vote to a candidate server.
GrantVote(i, m) ==
    /\ "label" \in DOMAIN m /\ m.label = "RequestVoteRequest"
    /\ m.state = Candidate
    /\ m.currentTerm <= currentTerm[i]
    /\ LET  j     == m.from
            logOk == \/ RaftUniv!LastTerm(m.log) > RaftUniv!LastTerm(log[i])
                     \/ /\ RaftUniv!LastTerm(m.log) = RaftUniv!LastTerm(log[i])
                        /\ Len(m.log) >= Len(log[i])
            grant == /\ m.currentTerm = currentTerm[i]
                     /\ logOk
                     /\ votedFor[i] \in {Nil, j} IN
            /\ m.currentTerm <= currentTerm[i]
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ BroadcastUniversalMsgLabeled(i, "RequestVoteResponse")
            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* Server i records a vote that was granted for it in its current term.
RecordGrantedVote(i, m) ==
    /\ "label" \in DOMAIN m /\ m.label = "RequestVoteResponse"
    /\ m.currentTerm = currentTerm[i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = 
                            \* The sender must have voted for us in this term.
                            votesGranted[i] \cup 
                                IF (i = m.votedFor) THEN {m.from} ELSE {}]
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, msgs>>

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


Next == 
    \/ \E i \in Server : \E m \in msgs : RaftUniv!UpdateTerm(i, m)
    \/ \E i \in Server : BecomeCandidate(i)
    \/ \E i \in Server : \E m \in msgs : GrantVote(i, m)
    \/ \E i \in Server : \E m \in msgs : RecordGrantedVote(i, m)
    \/ \E i \in Server : RaftUniv!BecomeLeader(i)
    \/ \E i \in Server : RaftUniv!ClientRequest(i)
    \/ \E i \in Server : \E m \in msgs : RaftUniv!AppendEntry(i, m)
    \/ \E i \in Server : \E m \in msgs : RaftUniv!TruncateEntry(i, m)
    \/ \E i \in Server : \E m \in msgs : RaftUniv!LeaderLearnsOfAppliedEntry(i, m)
    \/ \E i \in Server : RaftUniv!AdvanceCommitIndex(i)
    \/ \E i \in Server : \E m \in msgs : RaftUniv!LearnCommit(i, m)

Spec == Init /\ [][Next]_vars

RaftUnivSpec == RaftUniv!Spec

H_NoLogDivergence == RaftUniv!H_NoLogDivergence
H_OnePrimaryPerTerm == RaftUniv!H_OnePrimaryPerTerm
StateConstraint == RaftUniv!StateConstraint
Symmetry == RaftUniv!Symmetry

===============================================================================