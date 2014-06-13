from z3 import *;
init("libz3.so");

from basictypes import *;
#*************************************************************
#Communication
#*************************************************************

#Message attributes
source = Function('source', Message, Entity);
sendtime = Function('sendtime', Message, Time);
msgtype = Function('msgtype', Message, MsgType);
startt = Function('startt', Message, Time);
endt = Function('endt', Message, Time);
sent = Function('sent', Message, BoolSort());
received = Function('received', Message, Entity, BoolSort());
receivetime = Function('receivetime', Message, Entity, Time);

getAck = Function('getAck', Message, Entity, Message);

def hasBeenSent(m,t):
    return And(sent(m), t >= sendtime(m));

def hasReceived(e,m,t):
    return And(received(m,e), t >= receivetime(m,e));

def getCommunicationConstraints():
    m = Const('m', Message);
    mp = Const('mp', Message);
    e = Const('e', Entity);
    t = Const('t', Time);

    communication = [];

    #Sender in area
    communication.append(ForAll([m], Implies(sent(m),inArea(source(m))),
                                patterns=[inArea(source(m))],
                                qid="senderInArea"));

    
    #Sender in area
    communication.append(ForAll([m,e], Implies(sent(m),inArea(source(m))),
                                qid="senderInArea"));

    #It takes non-zero time for a message to be delivered
    communication.append(ForAll([m,e], receivetime(m,e) > sendtime(m),
                                patterns=[receivetime(m,e)],
                                qid="nonZeroDelay"));


    #Total order!
    communication.append(ForAll([m,mp,e], Or(sendtime(mp) <= sendtime(m),
                                             receivetime(mp,e)> receivetime(m,e),
                                             mp == m,
                                             Not(sent(m)),
                                             Not(sent(mp))
                                             ),
                                patterns=[MultiPattern(receivetime(mp,e),receivetime(m,e))],
                                qid="fifo"));


    #If a message is reveived at time t, then it has been sent at an
    #earlier (or the same) time
    communication.append(ForAll([m,e],Implies(received(m,e),sent(m)),
                                patterns=[received(m,e)],
                                qid="receivedWasSent"));
    

    communication.append(ForAll([m,e], Implies(msgtype(m) == Req,
                                               And(msgtype(getAck(m,e)) == Ack,
                                                   source(getAck(m,e)) == e)),
                                patterns=[getAck(m,e)],
                                qid="ackConsistency"));

    #If an Ack message has been sent by node e, then it has received a req
    #message before
    communication.append(ForAll([m,e], Implies(And(msgtype(m) == Req,
                                                   sent(getAck(m,e))),
                                               received(m,e)),
                                patterns=[getAck(m,e)],
                                qid="ackImpliesReq"));

    communication.append(ForAll([m,e], Implies(And(msgtype(m) == Req,
                                                   sent(getAck(m,e))),
                                               receivetime(m,e) <= sendtime(getAck(m,e))),
                                patterns=[getAck(m,e)],
                                qid="ackSentAfterReqReceived"));

    return communication;

minTimeFromSend = Real('minTimeFromSend');
maxTimeFromSend = Real('maxTimeFromSend');

perfectCommDelay = Real('perfectCommDelay');
ackDelay = Real('ackDelay');

def perfectCommunication():
    m = Const('m', Message);
    e = Const('e', Entity);
    t = Const('t', Time);

    communication = [];

    communication.append(ForAll([m,e],Implies(And(sent(m),
                                                  inArea(e)),
                                              received(m,e)),
                                qid="allSentReceived"));


    communication.append(ForAll([m,e],receivetime(m,e) <= sendtime(m)+perfectCommDelay,
                                qid="boundedDelay"));

    return communication;
