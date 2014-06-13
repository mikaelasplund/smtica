from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from resourceenv import *;
from variables import *;
#*************************************************************
#Progress const
#*************************************************************

def getProgressConstraints():
    e,ep = Consts('e ep', Entity);
    m,mp = Consts('m mp', Message);
    t = Const('t', Time);
    s = Const('s', SystemState);
    progress = [];
    
    progress.append(ForAll([m,e], Implies(And(msgtype(m) == Req,
                                              received(m,e)),
                                          sent(getAck(m,e))),
                           patterns=[getAck(m,e)],
                           qid="reqImpliesAck"));

    progress.append(ForAll([m,e], Implies(msgtype(m) == Req,
                                          sendtime(getAck(m,e)) <= receivetime(m,e)+ackDelay)));
    
    progress.append(ForAll([e], Or(e == ego,
                                   Not(inArea(e)),
                                   prio(e) < prio(ego))));
    
    return progress;

def validateMessageDecision(s,sp):
    e = Const('e', Entity);
    mp = Const('mp', Message);
    m = req(s);
    t = time(sp);
    return Implies(And(Not(valid(m)),
                       hasBeenSent(m,t)),
                   Or(Exists(e, And(inArea(e),
                                    e != ego,
                                    receivetime(getAck(m,e),ego) > startt(m))),
                      Exists(e, And(inArea(e),
                                    e != ego,
                                    Not(hasReceived(ego,getAck(m,e),t)))),
                      Exists(e, And(inArea(e),
                                    e != ego,
                                    prio(e) > prio(ego))),
                      ));


                   
def sendReqDecision(s,sp):
    return (egopos(s) >= resourceStarts(res)-senddist) == hasBeenSent(req(s),time(sp));



def progressDecisions(s,sp):
    return And(sendReqDecision(s,sp),
               validateMessageDecision(s,sp),
               );
