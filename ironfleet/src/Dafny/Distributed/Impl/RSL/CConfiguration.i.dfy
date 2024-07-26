include "../../Protocol/RSL/Constants.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "PacketParsing.i.dfy"
include "CParameters.i.dfy"

module LiveRSL__CPaxosConfiguration_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveRSL__Constants_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__PacketParsing_i
  import opened LiveRSL__ParametersState_i
  import opened Common__NodeIdentity_i
  import opened Common__SeqIsUniqueDef_i
  import opened Common__UdpClient_i
  import opened Collections__Seqs_i
  import opened GenericRefinement_i


  /* ----------------------------------- */

  datatype CConfiguration =
    CConfiguration
    (
      replica_ids : seq<EndPoint>
    )

  predicate CConfigurationIsValid(
    s : CConfiguration)

  {

    &&
      CConfigurationIsAbstractable(s)
    &&
      SeqIsValid(s.replica_ids, EndPointIsValid)

    /* Below is manually added */
    &&
      0 < |s.replica_ids| < 0xffff_ffff_ffff_ffff
    &&
      (forall i, j :: CReplicasDistinct(s.replica_ids,i,j))
    &&
      (forall i,j :: 0 <= i < |s.replica_ids| && 0 <= j < |s.replica_ids| && s.replica_ids[i] == s.replica_ids[j] ==> i == j)
    &&
      LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(s)) <= |s.replica_ids|
  }

  predicate CConfigurationIsAbstractable(
    s : CConfiguration)

  {
    &&
      (forall e :: e in s.replica_ids ==> e.EndPoint? && EndPointIsAbstractable(e))

    /* Below is manually added */
    &&
      SeqIsUnique(s.replica_ids)
  }

  function AbstractifyCConfigurationToLConfiguration(
    s : CConfiguration) : LConfiguration
    requires CConfigurationIsAbstractable(s)
  {
    /* {} is manually added */
    LConfiguration({}, AbstractifySeq(s.replica_ids, AbstractifyEndPointToNodeIdentity))
  }

  /* ----------------------------------- */

  function method {:opaque} CMinQuorumSize(
    c : CConfiguration) : int
    requires CConfigurationIsValid(c)
    ensures var r' := CMinQuorumSize(c); var r := LMinQuorumSize(AbstractifyCConfigurationToLConfiguration(c)); r == r'
  {
    |c.replica_ids| / 2 + 1
  }

  function method {:opaque} CReplicasDistinct(
    replica_ids : seq<EndPoint> ,
                      i : int ,
                      j : int) : bool
    requires SeqIsValid(replica_ids, EndPointIsValid)
    requires (forall i :: i in replica_ids ==> EndPointIsAbstractable(i))
    ensures var bc := CReplicasDistinct(replica_ids, i, j); var bl := ReplicasDistinct(AbstractifySeq(replica_ids, AbstractifyEndPointToNodeIdentity), i, j); bl == bc
  {
    0 <= i < |replica_ids| && 0 <= j < |replica_ids| && replica_ids[i] == replica_ids[j] ==> i == j
  }

  /* Not used, removed
 function method CWellFormedLConfiguration(
  c : CConfiguration) : bool
  requires CConfigurationIsValid(c)
  ensures var bc := CWellFormedLConfiguration(c); var bl := WellFormedLConfiguration(AbstractifyCConfigurationToLConfiguration(c)); bl == bc
 {

  &&
  0 < |c.replica_ids|
  &&
  (forall i, j :: CReplicasDistinct(c.replica_ids, i, j))
 }
  */

  function method {:opaque} CIsReplicaIndex(
    idx : int ,
    id : EndPoint ,
    c : CConfiguration) : bool
    requires EndPointIsValid(id)
    requires CConfigurationIsValid(c)
    ensures var bc := CIsReplicaIndex(idx, id, c); var bl := IsReplicaIndex(idx, AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c));  && bl == bc
  {

    &&
      0 <= idx < |c.replica_ids|
    &&
      c.replica_ids[idx] == id
  }

  function method {:opaque} CGetReplicaIndex(
    id : EndPoint ,
    c : CConfiguration) : int
    requires id in c.replica_ids
    ensures var idx := CGetReplicaIndex(id, c); 0 <= idx < |c.replica_ids| && c.replica_ids[idx] == id
    requires EndPointIsValid(id)
    requires CConfigurationIsValid(c)
    ensures var r' := CGetReplicaIndex(id, c); var r := GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c));  && r == r'
  {
    FindIndexInSeq(c.replica_ids, id)
  }

  /* ----------------------------------- */

  predicate ReplicaIndexValid(idx:int, c:CConfiguration)
  {
    && 0 <= idx < |c.replica_ids|
  }

}
