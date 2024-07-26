include "../../Protocol/SHT/Host.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "Parameters.i.dfy"

module SHT__ConstantsState_i {
import opened Common__SeqIsUniqueDef_i
import opened Native__Io_s
import opened SHT__Host_i
import opened Common__NodeIdentity_i
import opened Impl_Parameters_i

datatype ConstantsState = ConstantsState(
    rootIdentity:EndPoint,
    hostIds:seq<EndPoint>,
    params:CParameters)

predicate CConstantsIsAbstractable(constants:ConstantsState) {
       EndPointIsAbstractable(constants.rootIdentity)
    && SeqOfEndPointsIsAbstractable(constants.hostIds)
}

function AbstractifyToConstants(constants:ConstantsState) : Constants
    requires CConstantsIsAbstractable(constants);
{
    Constants(AbstractifyEndPointToNodeIdentity(constants.rootIdentity), AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params))
}

predicate ConstantsStateIsValid(constants:ConstantsState) {
    CConstantsIsAbstractable(constants)
 && CParametersIsValid(constants.params)
 && SeqIsUnique(constants.hostIds)
}
} 
