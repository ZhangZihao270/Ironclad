include "../../Protocol/RSL/Acceptor.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

module LiveRSL__AcceptorModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__Acceptor_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__Environment_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__ParametersState_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__Types_i
  import opened Impl__LiveRSL__Broadcast_i
  import opened Collections__Maps_i
  import opened Collections__Maps2_s
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Common__UdpClient_i
  import opened Environment_s
  import opened Collections__CountMatches_i
  import opened GenericRefinement_i
  // import opened Collections__CountMatches_i

  /* ----------------------------------------- */

  datatype CAcceptor =
    CAcceptor
    (
      constants : CReplicaConstants ,
      max_bal : CBallot ,
      votes : CVotes ,
      last_checkpointed_operation : seq<COperationNumber> ,
      log_truncation_point : COperationNumber
    )

  predicate CAcceptorIsValid(
    s : CAcceptor)

  {
    CAcceptorIsAbstractable(s)
    &&
    CReplicaConstantsIsValid(s.constants)
    &&
    CBallotIsValid(s.max_bal)
    &&
    CVotesIsValid(s.votes)
    &&
    (forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsValid(i))
    &&
    COperationNumberIsValid(s.log_truncation_point)
    && /* Manually added */
    |s.last_checkpointed_operation| == |s.constants.all.config.replica_ids|
  }

  predicate CAcceptorIsAbstractable(
    s : CAcceptor)

  {
    CReplicaConstantsIsAbstractable(s.constants)
    &&
    CBallotIsAbstractable(s.max_bal)
    &&
    CVotesIsAbstractable(s.votes)
    &&
    (forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsAbstractable(i))
    &&
    COperationNumberIsAbstractable(s.log_truncation_point)
  }

  function AbstractifyCAcceptorToLAcceptor(
    s : CAcceptor) : LAcceptor
    requires CAcceptorIsAbstractable(s)
  {
    LAcceptor(
      AbstractifyCReplicaConstantsToLReplicaConstants(s.constants),
      AbstractifyCBallotToBallot(s.max_bal),
      AbstractifyCVotesToVotes(s.votes),
      // AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),
      /* Timeout */
      AbstractifyCLastCheckpointedMapToOperationNumberSequence(s.last_checkpointed_operation),
      AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point))
  }

  function method {:opaque} CIsLogTruncationPointValid(
    log_truncation_point : COperationNumber ,
    last_checkpointed_operation : seq<COperationNumber> ,
                                      config : CConfiguration) : bool
    requires COperationNumberIsValid(log_truncation_point)
    requires (forall i :: i in last_checkpointed_operation ==> COperationNumberIsValid(i))
    requires CConfigurationIsValid(config)
    /* Failed */
    ensures var bc := CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config); var bl := IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCConfigurationToLConfiguration(config)); bl == bc
  {
    assert AbstractifySeq(last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == last_checkpointed_operation;
    IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, CMinQuorumSize(config))
  }

  function method {:opaque} CRemoveVotesBeforeLogTruncationPoint(
    votes : CVotes ,
    log_truncation_point : COperationNumber) : CVotes
    requires CVotesIsValid(votes)
    requires COperationNumberIsValid(log_truncation_point)
    ensures var votes' := CRemoveVotesBeforeLogTruncationPoint(votes, log_truncation_point); CVotesIsValid(votes') && RemoveVotesBeforeLogTruncationPoint(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
  {
    /* Axiom Lemma */
    var votes' :=
      map opn | opn in votes && opn >= log_truncation_point :: votes[opn]
      ;
    lemma_voteLen(votes');
    votes'  }

  function method {:opaque} CAddVoteAndRemoveOldOnes(
    votes : CVotes ,
    new_opn : COperationNumber ,
    new_vote : CVote ,
    log_truncation_point : COperationNumber) : CVotes
    requires CVotesIsValid(votes)
    requires COperationNumberIsValid(new_opn)
    requires CVoteIsValid(new_vote)
    requires COperationNumberIsValid(log_truncation_point)
    ensures var votes' := CAddVoteAndRemoveOldOnes(votes, new_opn, new_vote, log_truncation_point); CVotesIsValid(votes') && LAddVoteAndRemoveOldOnes(AbstractifyCVotesToVotes(votes), AbstractifyCVotesToVotes(votes'), AbstractifyCOperationNumberToOperationNumber(new_opn), AbstractifyCVoteToVote(new_vote), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
  {
    /* Axiom Lemma */
    var votes' :=
      map opn | opn in (votes.Keys + {new_opn}) && opn >= log_truncation_point :: (if opn == new_opn then new_vote else votes[opn])
      ;
    lemma_voteLen(votes');
    votes'	}

  function method {:opaque} CAcceptorInit(
    c : CReplicaConstants) : CAcceptor
    requires CReplicaConstantsIsValid(c)
    ensures var a := CAcceptorInit(c); CAcceptorIsValid(a) && LAcceptorInit(AbstractifyCAcceptorToLAcceptor(a), AbstractifyCReplicaConstantsToLReplicaConstants(c))
  {
    CAcceptor(constants := c, last_checkpointed_operation := seq(|c.all.config.replica_ids|, idx => 0), log_truncation_point := 0, max_bal := CBallot(0, 0), votes := map[])
  }

  function method {:opaque} CAcceptorProcess1a(
    s : CAcceptor ,
    inp : CPacket) : (CAcceptor, CBroadcast)
    requires inp.msg.CMessage_1a?
    requires CAcceptorIsValid(s)
    requires CPacketIsValid(inp)
    ensures var (s', sent_packets) := CAcceptorProcess1a(s, inp); CAcceptorIsValid(s') && CBroadcastIsValid(sent_packets) && LAcceptorProcess1a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
  {
    var m := inp.msg;
    if inp.src in s.constants.all.config.replica_ids && CBalLt(s.max_bal, m.bal_1a) /* && CReplicaConstantsValid(s.constants) */
    then
    (
      s.(
      max_bal := m.bal_1a
    ),
      CBroadcast(s.constants.all.config.replica_ids[s.constants.my_index], [inp.src], CMessage_1b(m.bal_1a, s.log_truncation_point, s.votes))
    )
    else
    (
      s,
      CBroadcastNop
    )
  }

  function method {:opaque} CAcceptorProcess2a(
    s : CAcceptor ,
    inp : CPacket) : (CAcceptor, CBroadcast)
    requires inp.msg.CMessage_2a?
    requires inp.src in s.constants.all.config.replica_ids
    requires CBalLeq(s.max_bal, inp.msg.bal_2a)
    requires CLeqUpperBound(inp.msg.opn_2a, s.constants.all.params.max_integer_val)
    requires CAcceptorIsValid(s)
    requires CPacketIsValid(inp)
    ensures var (s', sent_packets) := CAcceptorProcess2a(s, inp); CAcceptorIsValid(s') && CBroadcastIsValid(sent_packets) && LAcceptorProcess2a(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
  {
    var m := inp.msg;
    var newLogTruncationPoint := if inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point then inp.msg.opn_2a - s.constants.all.params.max_log_length + 1 else s.log_truncation_point;
    if s.log_truncation_point <= inp.msg.opn_2a
    then
    (
      s.(
      constants := s.constants,
      last_checkpointed_operation := s.last_checkpointed_operation,
      log_truncation_point := newLogTruncationPoint,
      max_bal := m.bal_2a,
      votes := CAddVoteAndRemoveOldOnes(s.votes, m.opn_2a, CVote(m.bal_2a, m.val_2a), newLogTruncationPoint)
    ),
                                                                 BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(m.bal_2a, m.opn_2a, m.val_2a))
    )
    else
    (
      s.(
      constants := s.constants,
      last_checkpointed_operation := s.last_checkpointed_operation,
      log_truncation_point := newLogTruncationPoint,
      max_bal := m.bal_2a,
      votes := s.votes
    ),
      BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2b(m.bal_2a, m.opn_2a, m.val_2a))
    )
  }

  function method {:opaque} CAcceptorProcessHeartbeat(
    s : CAcceptor ,
    inp : CPacket) : CAcceptor
    requires inp.msg.CMessage_Heartbeat?
    requires CAcceptorIsValid(s)
    requires CPacketIsValid(inp)
    ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
  {
    if inp.src in s.constants.all.config.replica_ids
    then
      var sender_index := CGetReplicaIndex(inp.src, s.constants.all.config);
      if 0 <= sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index]
      then
        s.(
      constants := s.constants,
      last_checkpointed_operation := s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt],
                                                                   log_truncation_point := s.log_truncation_point,
                                                                   max_bal := s.max_bal,
                                                                   votes := s.votes
    )
      else
        s
    else
      s
  }

  function method {:opaque} CAcceptorTruncateLog(
    s : CAcceptor ,
    opn : COperationNumber) : CAcceptor
    requires CAcceptorIsValid(s)
    requires COperationNumberIsValid(opn)
    ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
  {
    if opn <= s.log_truncation_point
    then
      s
    else
      s.(
      log_truncation_point := opn,
      votes := CRemoveVotesBeforeLogTruncationPoint(s.votes, opn)
    )
  }

  /* ----------------------------------------- */

  function {:opaque} AbstractifyCLastCheckpointedMapToOperationNumberSequence(s:seq<COperationNumber>) : seq<OperationNumber>
    ensures |AbstractifyCLastCheckpointedMapToOperationNumberSequence(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> AbstractifyCOperationNumberToOperationNumber(s[i]) == AbstractifyCLastCheckpointedMapToOperationNumberSequence(s)[i]
  {
    if |s| == 0 then []
    else [AbstractifyCOperationNumberToOperationNumber(s[0])] + AbstractifyCLastCheckpointedMapToOperationNumberSequence(s[1..])
  }

  predicate CommonAcceptorPreconditions(acceptor:CAcceptor, in_msg:CMessage, sender:EndPoint)
  {
    && CAcceptorIsValid(acceptor)
    && CAcceptorIsAbstractable(acceptor)
    && CReplicaConstantsIsValid(acceptor.constants)
    && CMessageIsMarshallable(in_msg)
    && CMessageIsAbstractable(in_msg)
  }

  predicate NextCAcceptor_ProcessHeartbeatPreconditions(acceptor:CAcceptor, in_msg:CMessage, sender:EndPoint)
  {
    && CommonAcceptorPreconditions(acceptor, in_msg, sender)
    && in_msg.CMessage_Heartbeat?
    && CConfigurationIsAbstractable(acceptor.constants.all.config)
  }

  predicate NextCAcceptor_Phase1Preconditions(acceptor:CAcceptor, in_msg:CMessage, sender:EndPoint)
  {
    && CommonAcceptorPreconditions(acceptor, in_msg, sender)
    && in_msg.CMessage_1a?
  }

  predicate NextCAcceptor_Phase2Preconditions_AlwaysEnabled(acceptor:CAcceptor, in_msg:CMessage, sender:EndPoint)
  {
    && CommonAcceptorPreconditions(acceptor, in_msg, sender)
    && in_msg.CMessage_2a?
    && CConfigurationIsAbstractable(acceptor.constants.all.config)
  }

  function method CCountMatchesInSeq<T(!new)>(s:seq<T>, f:T-->bool):int
    reads f.reads
    requires forall x :: f.requires(x)
  {
    if |s| == 0 then
      0
    else
      CCountMatchesInSeq(s[1..], f) + if f(s[0]) then 1 else 0
  }

  predicate method CIsNthHighestValueInSequence(v:int, s:seq<int>, n:int)
  {
    && 0 < n <= |s|
    && v in s
    && CCountMatchesInSeq(s, x => x > v) < n as int
    && CCountMatchesInSeq(s, x => x >= v) >= n as int
  }

  lemma {:axiom} lemma_voteLen(votes:CVotes)
    ensures |votes| < max_votes_len()

  predicate NextCAcceptor_InitPostconditions(acceptor:CAcceptor, rcs:CReplicaConstants)
    requires CReplicaConstantsIsValid(rcs)
  {
    && CAcceptorIsValid(acceptor)
    && CAcceptorIsAbstractable(acceptor)
    && acceptor.constants == rcs
    && LAcceptorInit(AbstractifyCAcceptorToLAcceptor(acceptor), AbstractifyCReplicaConstantsToLReplicaConstants(rcs))
  }

  lemma {:axiom} lemma_CAcceptorInit(rcs:CReplicaConstants, acceptor:CAcceptor)
    requires CReplicaConstantsIsValid(rcs)
    ensures NextCAcceptor_InitPostconditions(acceptor, rcs)

}
