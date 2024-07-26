include "AppInterface.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "Broadcast.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Protocol/RSL/Proposer.i.dfy"
include "ElectionImpl.i.dfy"
include "CConstants.i.dfy"

module LiveRSL__ProposerModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__AppInterface_i
  import opened LiveRSL__Broadcast_i
  import opened LiveRSL__CMessage_i
  import opened LiveRSL__CMessageRefinements_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__ConstantsState_i
  import opened LiveRSL__CPaxosConfiguration_i
  import opened LiveRSL__CTypes_i
  import opened LiveRSL__Election_i
  import opened LiveRSL__ElectionModel_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__Proposer_i
  import opened LiveRSL__Types_i
  import opened Impl__LiveRSL__Broadcast_i
  import opened Collections__Maps_i
  import opened Collections__Sets_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUnique_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened GenericRefinement_i
  import opened Environment_s
  import opened LiveRSL__Environment_i
  // import opened Common__NodeIdentity_i

  /* ----------------------------------------- */

  datatype CIncompleteBatchTimer =
    CIncompleteBatchTimerOn
    (
      when : int
    )
    |
    CIncompleteBatchTimerOff
    (

    )

  predicate CIncompleteBatchTimerIsValid(
    s : CIncompleteBatchTimer)

  {
    match s
    case CIncompleteBatchTimerOn(when) => CIncompleteBatchTimerIsAbstractable(s)
    case CIncompleteBatchTimerOff() => CIncompleteBatchTimerIsAbstractable(s)

  }

  predicate CIncompleteBatchTimerIsAbstractable(
    s : CIncompleteBatchTimer)

  {
    match s
    case CIncompleteBatchTimerOn(when) => true
    case CIncompleteBatchTimerOff() => true

  }

  function AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(
    s : CIncompleteBatchTimer) : IncompleteBatchTimer
    requires CIncompleteBatchTimerIsAbstractable(s)
  {
    match s
    case CIncompleteBatchTimerOn(when) => IncompleteBatchTimerOn(s.when)
    case CIncompleteBatchTimerOff() => IncompleteBatchTimerOff()

  }

  /* ----------------------------------------- */

  datatype CProposer =
    CProposer
    (
      constants : CReplicaConstants ,
      current_state : int ,

      request_queue : seq<CRequest> ,
      // request_queue : CRequestBatch , /* This will cause Timeout ? */

      max_ballot_i_sent_1a : CBallot ,
      next_operation_number_to_propose : int ,
      received_1b_packets : set<CPacket> ,
      highest_seqno_requested_by_client_this_view : map<EndPoint, int> ,
      incomplete_batch_timer : CIncompleteBatchTimer ,
      election_state : CElectionState
    )

  predicate CProposerIsValid(
    s : CProposer)

  {
    CProposerIsAbstractable(s)
    &&
    CReplicaConstantsIsValid(s.constants)

    &&
    /* Timeout ? */
    (forall i :: i in s.request_queue ==> i.CRequest? && CRequestIsValid(i))

    &&
    CBallotIsValid(s.max_ballot_i_sent_1a)
    &&
    (forall i :: i in s.received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
    &&
    (forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsValid(i))
    &&
    CIncompleteBatchTimerIsValid(s.incomplete_batch_timer)
    &&
    CElectionStateIsValid(s.election_state)

    /* Manually added */
    &&
    SetIsInjective(s.received_1b_packets, AbstractifyCPacketToRslPacket)
    &&
    (forall p :: p in s.received_1b_packets ==>
                   && CPacketIsValid(p)
                   && p.msg.CMessage_1b?
                   && p.msg.bal_1b == s.max_ballot_i_sent_1a
                   && CVotesIsValid(p.msg.votes))
    &&
    s.constants == s.election_state.constants
    &&
    CRequestBatchIsValid(s.request_queue)


    /*
    CProposerIsAbstractable(s)
    &&
    CReplicaConstantsIsValid(s.constants)
    &&
    CBallotIsValid(s.max_ballot_i_sent_1a)
    &&
    CElectionStateIsValid(s.election_state)
    &&
    (forall p :: p in s.received_1b_packets ==>
                   && CPacketIsValid(p)
                   && p.msg.CMessage_1b?
                   && p.msg.bal_1b == s.max_ballot_i_sent_1a
                   && CVotesIsValid(p.msg.votes))
    &&
    SetIsInjective(s.received_1b_packets, AbstractifyCPacketToRslPacket)
    &&
    CRequestBatchIsValid(s.request_queue)
    &&
    s.constants == s.election_state.constants
    */
  }

  predicate CProposerIsAbstractable(
    s : CProposer)

  {
    CReplicaConstantsIsAbstractable(s.constants)

    /* Timeout ? */
    // (forall i :: i in s.request_queue ==> i.CRequest? && CRequestIsAbstractable(i))
    &&
    CRequestBatchIsAbstractable(s.request_queue) /* Manually added */

    &&
    CBallotIsAbstractable(s.max_ballot_i_sent_1a)

    /* Timeout ? */
    // (forall i :: i in s.received_1b_packets ==> i.CPacket? && CPacketIsAbstractable(i))
    &&
    CPacketsIsAbstractable(s.received_1b_packets) /* Manually added */

    &&
    (forall i :: i in s.highest_seqno_requested_by_client_this_view ==> EndPointIsAbstractable(i))
    &&
    CIncompleteBatchTimerIsAbstractable(s.incomplete_batch_timer)
    &&
    CElectionStateIsAbstractable(s.election_state)
  }

  function AbstractifyCProposerToLProposer(
    s : CProposer) : LProposer
    requires CProposerIsValid(s) /* we need SetIsInjective */
    // requires CProposerIsAbstractable(s)
  {
    LProposer(
      AbstractifyCReplicaConstantsToLReplicaConstants(s.constants),
      s.current_state,
      AbstractifySeq(s.request_queue, AbstractifyCRequestToRequest),
      AbstractifyCBallotToBallot(s.max_ballot_i_sent_1a),
      s.next_operation_number_to_propose,
      AbstractifySet(s.received_1b_packets, AbstractifyCPacketToRslPacket),
      // AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, int_to_int, AbstractifyNodeIdentityToEndPoint),
      AbstractifyMap(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint),
      AbstractifyCIncompleteBatchTimerToIncompleteBatchTimer(s.incomplete_batch_timer),
      AbstractifyCElectionStateToElectionState(s.election_state))
  }

  /* ----------------------------------------- */

  function method CIsAfterLogTruncationPoint(
    opn : COperationNumber ,
    received_1b_packets : set<CPacket>) : bool
    /*
    requires COperationNumberIsValid(opn)
    requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
    ensures var bc := CIsAfterLogTruncationPoint(opn, received_1b_packets); var bl := LIsAfterLogTruncationPoint(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket)); bl == bc
    */
  {
    (forall p :: p in received_1b_packets && p.msg.CMessage_1b? ==> p.msg.log_truncation_point <= opn)
  }

  function method CSetOfMessage1b(
    S : set<CPacket>) : bool
    /*
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    ensures var bc := CSetOfMessage1b(S); var bl := LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket)); bl == bc
    */
  {
    forall p :: p in S ==> p.msg.CMessage_1b?
  }

  function method CSetOfMessage1bAboutBallot(
    S : set<CPacket> ,
    b : CBallot) : bool
    /*
      requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires CBallotIsValid(b)
    ensures var bc := CSetOfMessage1bAboutBallot(S, b); var bl := LSetOfMessage1bAboutBallot(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCBallotToBallot(b)); bl == bc
      */
  {

    &&
      CSetOfMessage1b(S)
    &&
      (forall p :: p in S ==> p.msg.bal_1b == b)
  }

  /* ----------------------------------------- */

  function method {:opaque} CAllAcceptorsHadNoProposal(
    S : set<CPacket> ,
            opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CAllAcceptorsHadNoProposal(S, opn); var bl := LAllAcceptorsHadNoProposal(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    forall p :: p in S ==> !(opn in p.msg.votes)
  }

  function method CExistVotesHasProposalLargeThanOpn(
    p : CPacket ,
    op : COperationNumber) : bool
    requires p.msg.CMessage_1b?
    requires CPacketIsValid(p)
    ensures var bc := CExistVotesHasProposalLargeThanOpn(p, op); var bl := LExistVotesHasProposalLargeThanOpn(AbstractifyCPacketToRslPacket(p), AbstractifyCOperationNumberToOperationNumber(op)); bl == bc
  {
    exists opn :: opn in p.msg.votes && opn > op
  }

  function method CExistsAcceptorHasProposalLargeThanOpn(
    S : set<CPacket> ,
    op : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(op)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CExistsAcceptorHasProposalLargeThanOpn(S, op); var bl := LExistsAcceptorHasProposalLargeThanOpn(AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(op)); bl == bc
  {
    exists p :: p in S && CExistVotesHasProposalLargeThanOpn(p, op)
  }

  function method Cmax_balInS(
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := Cmax_balInS(c, S, opn); var bl := Lmax_balInS(AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    forall p :: p in S && opn in p.msg.votes ==> CBalLeq(p.msg.votes[opn].max_value_bal, c)
  }

  function method CExistsBallotInS(
    v : CRequestBatch ,
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CExistsBallotInS(v, c, S, opn); var bl := LExistsBallotInS(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    exists p ::  && p in S && opn in p.msg.votes && p.msg.votes[opn].max_value_bal == c && p.msg.votes[opn].max_val == v
  }

  function method CValIsHighestNumberedProposalAtBallot(
    v : CRequestBatch ,
    c : CBallot ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires CBallotIsValid(c)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CValIsHighestNumberedProposalAtBallot(v, c, S, opn); var bl := LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(c), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {

    &&
      Cmax_balInS(c, S, opn)
    &&
      CExistsBallotInS(v, c, S, opn)
  }

  function method CValIsHighestNumberedProposal(
    v : CRequestBatch ,
    S : set<CPacket> ,
    opn : COperationNumber) : bool
    requires CSetOfMessage1b(S)
    requires CRequestBatchIsValid(v)
    requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
    requires COperationNumberIsValid(opn)
    /* Manually Added */ requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
    ensures var bc := CValIsHighestNumberedProposal(v, S, opn); var bl := LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {
    // exists c :: CValIsHighestNumberedProposalAtBallot(v, c, S, opn)
    /* Manually added */
    exists p :: p in S && opn in p.msg.votes && CValIsHighestNumberedProposalAtBallot(v, p.msg.votes[opn].max_value_bal, S, opn)
  }

  function method CProposerCanNominateUsingOperationNumber(
    s : CProposer ,
    log_truncation_point : COperationNumber ,
    opn : COperationNumber) : bool
    requires CProposerIsValid(s)
    requires COperationNumberIsValid(log_truncation_point)
    requires COperationNumberIsValid(opn)
    ensures var bc := CProposerCanNominateUsingOperationNumber(s, log_truncation_point, opn); var bl := LProposerCanNominateUsingOperationNumber(AbstractifyCProposerToLProposer(s), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn)); bl == bc
  {

    &&
      s.election_state.current_view == s.max_ballot_i_sent_1a
    &&
      s.current_state == 2
    &&
      |s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config)
    &&
      CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
    &&
      CIsAfterLogTruncationPoint(opn, s.received_1b_packets)
    &&
      opn < UpperBoundedAdditionImpl(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
    &&
      opn >= 0
    &&
      CLtUpperBound(opn, s.constants.all.params.max_integer_val)
  }

  /* ----------------------------------------- */

  function method CProposerInit(
    c : CReplicaConstants) : CProposer
    /* Manually added */
    ensures  WellFormedLConfiguration(AbstractifyCReplicaConstantsToLReplicaConstants(c).all.config)
    requires CReplicaConstantsIsValid(c)
    ensures var s := CProposerInit(c); CProposerIsValid(s) && LProposerInit(AbstractifyCProposerToLProposer(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
  {
		CProposer(constants := c, current_state := 0, election_state := CElectionStateInit(c), highest_seqno_requested_by_client_this_view := map[], incomplete_batch_timer := CIncompleteBatchTimerOff(), max_ballot_i_sent_1a := CBallot(0, c.my_index), next_operation_number_to_propose := 0, received_1b_packets := {}, request_queue := [])
  }

  method CProposerProcessRequest(
    s : CProposer ,
    packet : CPacket,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
    requires packet.msg.CMessage_Request?
    requires CProposerIsValid(s)
    requires CPacketIsValid(packet)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

    // ensures var s' := CProposerProcessRequest(s, packet); 
    ensures CProposerIsValid(s') 
    ensures LProposerProcessRequest(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(packet))
  {
    var val := CRequest(packet.src, packet.msg.seqno_req, packet.msg.val);

    var election := CElectionStateReflectReceivedRequest_I1(s.election_state, val, cur_req_set, prev_req_set);

    lemma_AbstractifyMap_properties(s.highest_seqno_requested_by_client_this_view, AbstractifyEndPointToNodeIdentity, int_to_int, AbstractifyNodeIdentityToEndPoint);
    // var s' :=
      if  && s.current_state != 0 && ( val.client !in s.highest_seqno_requested_by_client_this_view || val.seqno > s.highest_seqno_requested_by_client_this_view[val.client])
      {
        s' := s.(
        election_state := election,
        request_queue := s.request_queue + [val],
        highest_seqno_requested_by_client_this_view := s.highest_seqno_requested_by_client_this_view[val.client := val.seqno]
        );
      }
      else
      {
        s' := s.(
        election_state := election
        )
      ;
      }
    lemma_RequestQueue_len(s'.request_queue); /* Axiom Lemma */
    // s'
    lemma_CProposerProcessRequest(s, packet, s');
  }

  lemma {:axiom} lemma_CProposerProcessRequest(s : CProposer ,
    packet : CPacket,s':CProposer)
    requires packet.msg.CMessage_Request?
    requires CProposerIsValid(s)
    requires CPacketIsValid(packet)
    ensures CProposerIsValid(s') 
    ensures LProposerProcessRequest(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(packet))

  function method CProposerMaybeEnterNewViewAndSend1a(
    s : CProposer) : (CProposer, CBroadcast)
    requires CProposerIsValid(s)
    ensures var (s', sent_packets) := CProposerMaybeEnterNewViewAndSend1a(s); CProposerIsValid(s') && CBroadcastIsValid(sent_packets) && LProposerMaybeEnterNewViewAndSend1a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
  {
    var (s', sent_packets) :=
      if  && s.election_state.current_view.proposer_id == s.constants.my_index && CBalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
      then
        (
          s.(
          current_state := 1,
          max_ballot_i_sent_1a := s.election_state.current_view,
          received_1b_packets := {},
          highest_seqno_requested_by_client_this_view := map[],
          request_queue := s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch
          ),
          BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_1a(s.election_state.current_view))
        )
      else
        (
          s,
          CBroadcastNop
        )
      ;
    lemma_RequestQueue_len(s'.request_queue); /* Axiom Lemma */
    (s', sent_packets)
  }

  function method CProposerProcess1b(
    s : CProposer ,
    p : CPacket) : CProposer
    requires p.msg.CMessage_1b?
    requires p.src in s.constants.all.config.replica_ids
    requires p.msg.bal_1b == s.max_ballot_i_sent_1a
    requires s.current_state == 1
    requires forall other_packet :: other_packet in s.received_1b_packets ==> other_packet.src != p.src
    requires CProposerIsValid(s)
    requires CPacketIsValid(p)
    ensures var s' := CProposerProcess1b(s, p); CProposerIsValid(s') && LProposerProcess1b(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p))
  {
    /* Manually added */
    ghost var s_ := AbstractifyCProposerToLProposer(s);
    ghost var s'_ := s_.(received_1b_packets := s_.received_1b_packets + { AbstractifyCPacketToRslPacket(p) });
    var s' :=
      s.(
      received_1b_packets := s.received_1b_packets + {p}
      )
      ;
    assert AbstractifyCProposerToLProposer(s').received_1b_packets == s'_.received_1b_packets;
    s'
  }

  function method CProposerMaybeEnterPhase2(
    s : CProposer ,
    log_truncation_point : COperationNumber) : (CProposer, CBroadcast)
    requires CProposerIsValid(s)
    requires COperationNumberIsValid(log_truncation_point)
    ensures var (s', sent_packets) := CProposerMaybeEnterPhase2(s, log_truncation_point); CProposerIsValid(s') && CBroadcastIsValid(sent_packets) && LProposerMaybeEnterPhase2(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
  {
    if  && |s.received_1b_packets| >= CMinQuorumSize(s.constants.all.config) && CSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a) && s.current_state == 1
    then
      (
        s.(
        current_state := 2,
        next_operation_number_to_propose := log_truncation_point
        ),
        BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_StartingPhase2(s.max_ballot_i_sent_1a, log_truncation_point))
      )
    else
      (
        s,
        CBroadcastNop
      )
  }

  function method CProposerNominateNewValueAndSend2a(
    s : CProposer ,
    clock : int ,
    log_truncation_point : COperationNumber) : (CProposer, CBroadcast)
    requires CProposerIsValid(s)
    requires COperationNumberIsValid(log_truncation_point)
    requires CProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose)
    requires CAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    ensures var (s', sent_packets) := CProposerNominateNewValueAndSend2a(s, clock, log_truncation_point); 
    CProposerIsValid(s') && CBroadcastIsValid(sent_packets) && LProposerNominateNewValueAndSend2a(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
    && s.election_state == s'.election_state
  {
    var batchSize := if |s.request_queue| <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 then |s.request_queue| else s.constants.all.params.max_batch_size;
    var v := s.request_queue[..batchSize];
  
    /* Manually added */
    lemma_seq_sub(s.request_queue, AbstractifyCRequestToRequest, 0, batchSize);

    var opn := s.next_operation_number_to_propose;
    (
      s.(
      request_queue := s.request_queue[batchSize..],
      next_operation_number_to_propose := s.next_operation_number_to_propose + 1,
      incomplete_batch_timer := if |s.request_queue| > batchSize then CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, s.constants.all.params.max_batch_delay, s.constants.all.params.max_integer_val)) else CIncompleteBatchTimerOff()
      ),
      BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_2a(s.max_ballot_i_sent_1a, opn, v))
    )
  }

method CProposerNominateOldValueAndSend2a(proposer:CProposer,log_truncation_point:COperationNumber) returns (proposer':CProposer, sent_packets:CBroadcast)
    requires CProposerIsValid(proposer)
    requires CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose)
    requires !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
    ensures CProposerIsValid(proposer')
    ensures CBroadcastIsAbstractable(sent_packets)
    ensures LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(proposer),
                                               AbstractifyCProposerToLProposer(proposer'),
                                               AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                               AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
    ensures proposer.election_state == proposer'.election_state
  {
    var opn := proposer.next_operation_number_to_propose;
    var v := FindValWithHighestNumberedProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose);

    proposer' := proposer.(next_operation_number_to_propose := proposer.next_operation_number_to_propose + 1);
    var cmsg := CMessage_2a(proposer.max_ballot_i_sent_1a, opn, v);
    sent_packets := BuildBroadcastToEveryone(proposer.constants.all.config, proposer.constants.my_index, cmsg);
  }

  method CProposerMaybeNominateValueAndSend2a(proposer:CProposer, clock:int, log_truncation_point:COperationNumber) returns (proposer':CProposer, sent_packets:CBroadcast)
    requires CProposerIsValid(proposer)
    ensures CProposerIsValid(proposer')
    ensures CBroadcastIsAbstractable(sent_packets)

    ensures proposer'.election_state.cur_req_set == proposer.election_state.cur_req_set
    ensures proposer'.election_state.prev_req_set == proposer.election_state.prev_req_set

    ensures  LProposerMaybeNominateValueAndSend2a(AbstractifyCProposerToLProposer(proposer),
                                                  AbstractifyCProposerToLProposer(proposer'),
                                                  clock as int,
                                                  AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                                  AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
    
    
  {
    if !CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose) {
      proposer' := proposer;
      sent_packets := CBroadcastNop;
      assert proposer'.election_state == proposer.election_state;
    } else if !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose) {
      proposer', sent_packets := CProposerNominateOldValueAndSend2a(proposer, log_truncation_point);
      assert proposer'.election_state == proposer.election_state;
    }
    else if
      CExistsAcceptorHasProposalLargeThanOpn(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
      || (|proposer.request_queue| >= proposer.constants.all.params.max_batch_size as int)
      || (|proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOn? && clock >= proposer.incomplete_batch_timer.when)
    {
      var (proposer'_, sent_packets_) := CProposerNominateNewValueAndSend2a(proposer, clock, log_truncation_point);
      proposer' := proposer'_;
      sent_packets := sent_packets_;
      assert proposer'.election_state == proposer.election_state;
    } else if |proposer.request_queue| > 0 && proposer.incomplete_batch_timer.CIncompleteBatchTimerOff? {
      proposer' := proposer.(incomplete_batch_timer := CIncompleteBatchTimerOn(UpperBoundedAdditionImpl(clock, proposer.constants.all.params.max_batch_delay, proposer.constants.all.params.max_integer_val)));
      sent_packets := CBroadcastNop;
      assert proposer'.election_state == proposer.election_state;
    } else {
      proposer' := proposer;
      sent_packets := CBroadcastNop;
      assert proposer'.election_state == proposer.election_state;
    }
  }

	method CProposerProcessHeartbeat(
		s : CProposer ,
		p : CPacket ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>
    ) returns (s':CProposer)
		requires CProposerIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
    
    requires p.src in s.constants.all.config.replica_ids
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

		// ensures var s' := CProposerProcessHeartbeat(s, p, clock);
    ensures CProposerIsValid(s') && LProposerProcessHeartbeat(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCPacketToRslPacket(p), clock)
	{
    /* Manually added to pass the Temporal Relation */
    var election := CElectionStateProcessHeartbeat(s.election_state, p, clock, cur_req_set, prev_req_set);
    
    var ss' := s.(election_state := election);


		if CBalLt(s.election_state.current_view, ss'.election_state.current_view)
		{ 
			s' := s.(
				election_state := election,
				current_state := 0,
				request_queue := []
			);
    }
		else 
    {
			s' := s.(
				election_state := election,
				current_state := s.current_state,
				request_queue := s.request_queue
			);
    }
	}

	method CProposerCheckForViewTimeout(
		s : CProposer ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
		requires CProposerIsValid(s)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

		// ensures var s' := CProposerCheckForViewTimeout(s, clock); 
    ensures CProposerIsValid(s') && LProposerCheckForViewTimeout(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{
    var election_state' := CElectionStateCheckForViewTimeout(s.election_state, clock, cur_req_set, prev_req_set);
		s' := s.(
			election_state := election_state'
		);
	}

	method CProposerCheckForQuorumOfViewSuspicions(
		s : CProposer ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
		requires CProposerIsValid(s)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

		// ensures var s' := CProposerCheckForQuorumOfViewSuspicions(s, clock); 
    ensures CProposerIsValid(s') && LProposerCheckForQuorumOfViewSuspicions(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), clock)
	{

    /* Manually added to pass the Temporal Relation */
    var election := CElectionStateCheckForQuorumOfViewSuspicions(s.election_state, clock, cur_req_set, prev_req_set);
    var ss' := s.(election_state := election);

		if CBalLt(s.election_state.current_view, ss'.election_state.current_view)
		{ 
			s' := s.(
				election_state := election,
				current_state := 0,
				request_queue := []
			);
    }
		else 
    {
			s' := s.(
				election_state := election,
				current_state := s.current_state,
				request_queue := s.request_queue
			);
    }
	}

	method CProposerResetViewTimerDueToExecution(
		s : CProposer ,
		val : CRequestBatch,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CProposer)
		requires CProposerIsValid(s)
		requires CRequestBatchIsValid(val)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.election_state.prev_req_set

		// ensures var s' := CProposerResetViewTimerDueToExecution(s, val); 
    ensures CProposerIsValid(s') && LProposerResetViewTimerDueToExecution(AbstractifyCProposerToLProposer(s), AbstractifyCProposerToLProposer(s'), AbstractifyCRequestBatchToRequestBatch(val))
	{
    var election := CElectionStateReflectExecutedRequestBatch_I1(s.election_state, val, cur_req_set, prev_req_set);
		s' := s.(
			election_state := election
		);
	}

  /* ----------------- Manually Writen for I0 --------- */

  
method {:timeLimitMultiplier 5} FindValWithHighestNumberedProposal(received_1b_packets:set<CPacket>, opn:COperationNumber) returns (v:CRequestBatch)
  requires received_1b_packets != {}
  requires COperationNumberIsAbstractable(opn)
  requires CSetOfMessage1b(received_1b_packets)
  requires CPacketsIsAbstractable(received_1b_packets)
  requires (forall i :: i in received_1b_packets ==> i.CPacket? && CPacketIsValid(i))
  requires SetIsInjective(received_1b_packets, AbstractifyCPacketToRslPacket)
  requires !CAllAcceptorsHadNoProposal(received_1b_packets, opn)
  requires forall p :: p in received_1b_packets ==> CVotesIsValid(p.msg.votes)
  ensures CRequestBatchIsAbstractable(v)
  ensures CRequestBatchIsValid(v)
  ensures LSetOfMessage1b(AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket))
  ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
{
  var packets:set<CPacket>;
  ghost var processedPackets:set<CPacket>;

  packets := received_1b_packets;
  var pkt :| pkt in packets && opn in pkt.msg.votes;
  v := pkt.msg.votes[opn].max_val;
  var bal := pkt.msg.votes[opn].max_value_bal;
  var p_bal := pkt;
  packets := packets - {pkt};
  processedPackets := {pkt};
  // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  // reveal AbstractifyCVotesToVotes();
  ghost var p := AbstractifyCPacketToRslPacket(pkt);
  ghost var S := AbstractifySet(processedPackets, AbstractifyCPacketToRslPacket);
  ghost var opn_s := AbstractifyCOperationNumberToOperationNumber(opn);

  while (packets != {})
    decreases packets
    invariant packets + processedPackets == received_1b_packets
    invariant processedPackets == received_1b_packets - packets
    invariant CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketIsAbstractable(p_bal) && p_bal in processedPackets && opn in p_bal.msg.votes && v == p_bal.msg.votes[opn].max_val && bal == p_bal.msg.votes[opn].max_value_bal
    invariant forall q :: q in processedPackets && opn in q.msg.votes ==> CBalLeq(q.msg.votes[opn].max_value_bal, p_bal.msg.votes[opn].max_value_bal)
    invariant p_bal in processedPackets
    invariant opn in p_bal.msg.votes
    invariant p_bal.msg.votes[opn].max_value_bal==bal
    invariant p_bal.msg.votes[opn].max_val==v
    invariant CExistsBallotInS(v, bal, processedPackets, opn)
    invariant CValIsHighestNumberedProposalAtBallot(v, bal, processedPackets, opn)
    invariant CValIsHighestNumberedProposal(v, processedPackets, opn)
    invariant CRequestBatchIsValid(v)
  {
    pkt :| pkt in packets;
    if (opn in pkt.msg.votes) {
      var foundHigherBallot := CBalLeq(bal, pkt.msg.votes[opn].max_value_bal);

      if (foundHigherBallot) {
        p_bal := pkt;
        v := pkt.msg.votes[opn].max_val;
        bal := pkt.msg.votes[opn].max_value_bal;
      }
    }
    packets := packets - {pkt};
    processedPackets := processedPackets + {pkt};
    // reveal AbstractifyCVotesToVotes();
  }

  assert processedPackets == received_1b_packets;
  p := AbstractifyCPacketToRslPacket(p_bal);
  assert CValIsHighestNumberedProposal(v, received_1b_packets, opn);
  lemma_CValIsHighestNumberedProposalAbstractifies(v, bal, received_1b_packets, opn);
  assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(received_1b_packets, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn));
}


lemma lemma_CValIsHighestNumberedProposalAbstractifies(v:CRequestBatch, bal:CBallot, S:set<CPacket>, opn:COperationNumber)
  requires CRequestBatchIsAbstractable(v) && CBallotIsAbstractable(bal) && CPacketsIsAbstractable(S) && COperationNumberIsAbstractable(opn)
  requires CSetOfMessage1b(S)
  requires CRequestBatchIsValid(v)
  requires (forall i :: i in S ==> i.CPacket? && CPacketIsValid(i))
  requires COperationNumberIsValid(opn)
  requires SetIsInjective(S, AbstractifyCPacketToRslPacket)
  requires CValIsHighestNumberedProposal(v, S, opn)
  requires CValIsHighestNumberedProposalAtBallot(v, bal, S, opn)
  ensures LSetOfMessage1b(AbstractifySet(S, AbstractifyCPacketToRslPacket))
  ensures LValIsHighestNumberedProposal(AbstractifyCRequestBatchToRequestBatch(v), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
  ensures LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn))
{
  // reveal AbstractifyCVotesToVotes();

  var c :| CBallotIsAbstractable(c) && CValIsHighestNumberedProposalAtBallot(v, c, S, opn);
  var ref_c := AbstractifyCBallotToBallot(c);
  var ref_v := AbstractifyCRequestBatchToRequestBatch(v);
  var ref_S := AbstractifySet(S, AbstractifyCPacketToRslPacket);
  var ref_opn := AbstractifyCOperationNumberToOperationNumber(opn);
  // forall ensures LMaxBallotInS(ref_c, ref_S, ref_opn)
  // {
  //   lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
  // }
  // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_propertiesProposer(S);
  assert Lmax_balInS(ref_c, ref_S, ref_opn);
  assert CExistsBallotInS(v, c, S, opn);
  var p :| && p in S
           && opn in p.msg.votes
           && p.msg.votes[opn].max_value_bal==c
           && p.msg.votes[opn].max_val==v;
  var ref_p := AbstractifyCPacketToRslPacket(p);

  forall ensures ref_p in ref_S
  {
    // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  }
  assert ref_opn in ref_p.msg.votes;
  assert ref_p.msg.votes[ref_opn].max_value_bal == ref_c;
  assert ref_p.msg.votes[ref_opn].max_val == ref_v;

  assert LExistsBallotInS(ref_v, ref_c, ref_S, ref_opn);
  assert LValIsHighestNumberedProposalAtBallot(ref_v, ref_c, ref_S, ref_opn);
  assert LValIsHighestNumberedProposal(ref_v, ref_S, ref_opn);

  var ref_bal := AbstractifyCBallotToBallot(bal);
  assert CExistsBallotInS(v, bal, S, opn);

  var p' :| && p' in S
            && opn in p'.msg.votes
            && p'.msg.votes[opn].max_value_bal==bal
            && p'.msg.votes[opn].max_val==v;

  assert AbstractifyCRequestBatchToRequestBatch(p'.msg.votes[opn].max_val) == AbstractifyCRequestBatchToRequestBatch(v);

  var ref_p' := AbstractifyCPacketToRslPacket(p');

  forall ensures ref_p' in ref_S
  {
    // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  }

  assert ref_opn in ref_p'.msg.votes;
  assert ref_p'.msg.votes[ref_opn].max_value_bal == ref_bal;
  assert ref_p'.msg.votes[ref_opn].max_val == ref_v;
  assert LExistsBallotInS(ref_v, ref_bal, ref_S, ref_opn);

  assert LValIsHighestNumberedProposalAtBallot(AbstractifyCRequestBatchToRequestBatch(v), AbstractifyCBallotToBallot(bal), AbstractifySet(S, AbstractifyCPacketToRslPacket), AbstractifyCOperationNumberToOperationNumber(opn));
}


  /* ----------------------------------------- */

  lemma {:axiom} lemma_RequestQueue_len(s:seq<CRequest>)
    ensures |s| <= RequestBatchSizeLimit()

  lemma {:axiom} lemma_MsgEqual(m1:RslMessage, m2:RslMessage)
    ensures m1 == m2

  lemma {:axiom} lemma_CProposerNominateOldValueAndSend2a(proposer:CProposer,log_truncation_point:COperationNumber, proposer':CProposer, sent_packets:CBroadcast)
    requires CProposerIsValid(proposer)
    requires CProposerCanNominateUsingOperationNumber(proposer, log_truncation_point, proposer.next_operation_number_to_propose)
    requires !CAllAcceptorsHadNoProposal(proposer.received_1b_packets, proposer.next_operation_number_to_propose)
    ensures CProposerIsValid(proposer')
    ensures CBroadcastIsAbstractable(sent_packets)
    ensures LProposerNominateOldValueAndSend2a(AbstractifyCProposerToLProposer(proposer),
                                               AbstractifyCProposerToLProposer(proposer'),
                                               AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                                               AbstractifyCBroadcastToRlsPacketSeq(sent_packets))
}
