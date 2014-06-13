from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;

#*************************************************************
#Resource Reservation Definitions
#*************************************************************

res = Const('res', Resource);
conflictOverlap = Real('conflictOverlap');
reservationLength = Real('reservationLength');
resource = Function('resource', Message, Resource);

prio = Function('prio', Entity, IntSort());
valid = Function('valid', Message, BoolSort());    
validationTime = Function('validationTime', Message, Time);    

def conflicts (m, mp):
    return And(resource(m) == resource(mp),
               msgtype(m) == Req,
               msgtype(mp) == Req,
               startt(m) < (endt(mp) + conflictOverlap),
               startt(mp) < (endt(m) + conflictOverlap));

def validated(m,t):
    return And(valid(m),
               validationTime(m) <= t);

#*************************************************************
#Resource Reservation Constraints
#*************************************************************

def getResourceReservationConstraints():
    m,mp = Consts('m mp', Message);
    e,ep = Consts('e ep', Entity);
    t,tp = Consts('t tp', Time);
    s,sp = Consts('s sp', SystemState);
    res = Const('res', Resource);
    
    resourceRes = [];

    # #Source of req
    resourceRes.append(ForAll([s], source(req(s)) == ego,
                               qid="reqSource"));
    

    resourceRes.append(ForAll([m], Implies(valid(m),
                                           startt(m)+reservationLength < endt(m)),
                              qid="requestMinimumLength"));

    resourceRes.append(ForAll([m], startt(m) < sendtime(m) + maxTimeFromSend,
                              qid="maxTimeFromSend"));

    resourceRes.append(ForAll([m], startt(m) > sendtime(m) + minTimeFromSend,
                              qid="minTimeFromSend"));
    
    resourceRes.append(ForAll(m, Implies(valid(m),sent(m)),
                              patterns=[valid(m)],
                              qid="validIsSent"));

    resourceRes.append(ForAll(m, Implies(valid(m),msgtype(m) == Req),
                              patterns=[valid(m)],
                              qid="validIsReq"));

    # If a message is valid, then the validation time is smaller than the
    #starttime and larger than the sendtime
    resourceRes.append(ForAll(m, And(validationTime(m) < startt(m),
                                     validationTime(m) > sendtime(m)),
                              patterns=[valid(m)],
                              qid="validationTime"));


    #If a message is validated, then the source node has received Acks
    #from all entities in the area
    resourceRes.append(ForAll([e,m],
                              Or(Not(valid(m)), 
                                 Not(inArea(e)), 
                                 source(m) == e,
                                 received(getAck(m,e),source(m))),
                              patterns=[MultiPattern(valid(m),inArea(e))],
                              qid="validHasAcks"));

    resourceRes.append(ForAll([e,m],
                              Implies(And(valid(m), inArea(e), source(m) != e),
                                      receivetime(getAck(m,e),source(m)) <= validationTime(m)),
                              patterns=[MultiPattern(valid(m),inArea(e))],
                              qid="validAfterAcks"));
    
    
    #If a message is validated, then the sender has not received a
    #conflicting Req from a higher priority entity
    resourceRes.append(ForAll([m,mp],Or(Not(valid(m)),
                                        Not(hasReceived(source(m),mp,validationTime(m))),
                                        m == mp,
                                        prio(source(mp)) < prio(source(m)),
                                        Not(conflicts(m,mp))),
                              patterns=[MultiPattern(valid(m),received(mp,source(m)))],
                              qid="validNoConfl"));
   
    # CurrentRequest cannot conflict with a received request
    resourceRes.append(ForAll([m,mp], Or(m == mp,
                                         Not(conflicts(m,mp)),
                                         Not(received(mp,source(m))),
                                         receivetime(mp,source(m)) > sendtime(m),
                                         Not(sent(m))),
                              patterns=[MultiPattern(sent(m),received(mp,source(m)))],
                              qid = "currentrequestnotconflicts"));

    
    
    #Priorities are unique (at least within the active area)
    resourceRes.append(ForAll([e,ep], Or(Not(inArea(e)),
                                         Not(inArea(ep)),
                                         e == ep,
                                         prio(e) != prio(ep)),
                              patterns=[MultiPattern(inArea(e),inArea(ep))],
                              qid="uniquePrio"));


    #ego car is in the area
    resourceRes.append(inArea(ego));

    #If another car has requested a resource, it must be in the area
    resourceRes.append(ForAll([m], Or(source(m) == ego,
                                      msgtype(m) != Req,
                                      inArea(source(m))),
                              patterns = [source(m)], 
                              qid="hasResInArea"));
    
    return resourceRes;
