from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from environment import *;
from resourceenv import *;
from variables import *;
from statemachine import *;

#*************************************************************
#Print functions
#*************************************************************

def print_state(m,s):
    ts = targetSpeed(s);
    pos = egopos(s);
    res = nextOrLastResource(s);
    restime = (resourceEnds(res)-pos)/ts+(ts-speed(s))/acceleration;
    print "Time: ", m.evaluate(time(s));
    print "Ego pos: ", m.evaluate(egopos(s));
    print "speed: ", m.evaluate(speed(s));
    print "targetSpeed: ", m.evaluate(targetSpeed(s));
    print "acc: ", m.evaluate(acc(s));
    print "location: ", m.evaluate(loc(s));
    print "willEnter: ", m.evaluate(willEnter(s));
    print "nextOrLastResource: ", m.evaluate(res);
    print "resource start", m.evaluate(resourceStarts(res));
    print "resource end", m.evaluate(resourceEnds(res));
    print "has resource for ", m.evaluate(restime), " seconds:", m.evaluate(egoHasResource(res,s,(resourceEnds(res)-pos)/ts+(ts-speed(s))/acceleration));
    print "req: ", print_message(m,m.evaluate(req(s)));
    print "Validated: ", m.evaluate(validated(req(s),time(s)));
    print "Waiting: ", m.evaluate(waiting(s));
    print "Stuck: ", m.evaluate(stuck(s));
    print "Last Time Not Waiting: ", m.evaluate(ltnw(s));
    print "Delay: ", m.evaluate(delay(s));
    
    
def print_trace(m,S,s1,s2,showsucc):
    print "";
    print "Route: ", m.evaluate(route(ego));
    print "acceleration: ", m.evaluate(acceleration);
    print "breaking: ", m.evaluate(breaking);
    print "closeDist: ", m.evaluate(closeDist);
    print "interSize: ", m.evaluate(interSize);
    print "";
    for i in range (s1,s2+1):
        print "State: ", i;
        print_state(m,S[i]);
        print " ";
    if showsucc:
        print "Succsor to last state";
        print_state(m,succ(S[s2]));


def print_message(mod,m):
    print m;
    print "Source: ", mod.evaluate(source(m)), " Type: ", mod.evaluate(msgtype(m)), " Sent: ", mod.evaluate(sent(m)), " Sendtime: ", mod.evaluate(sendtime(m)), " validationTime: ", mod.evaluate(validationTime(m));
    print "Valid: ", mod.evaluate(valid(m));
    print "resouce", mod.evaluate(resource(m));
    print "startt: ", mod.evaluate(startt(m)), " endt: ", mod.evaluate(endt(m));
    for e in mod[Entity]:
        if (is_true(mod.evaluate(received(m,e)))):
            print "Received by ", e, " at ", mod.evaluate(receivetime(m,e));
#            if (is_true(mod.evaluate(accepted(e,m)))):
#                print "Accepted";
        if (is_true(mod.evaluate(received(getAck(m,e),source(m))))):
            print "Got Ack sent at ", mod.evaluate(sendtime(getAck(m,e))), " received at ", mod.evaluate(receivetime(getAck(m,e),source(m)));

def printEntity(mod,e):
    print e;
    print "In area: ", mod.evaluate(inArea(e));
    print "Prio: ", mod.evaluate(prio(e));


def printResource(mod,r):
    print r;
    print "start: ", mod.evaluate(resourceStarts(r));
    print "end: ", mod.evaluate(resourceEnds(r));


def printIntersection(mod,i):
    print i;
    print "otherRoute: ", mod.evaluate(otherRoute(i));
    print "interPos: ", mod.evaluate(interPos(i));
    print "otherInterPos: ", mod.evaluate(otherInterPos(i));
    print "resource: ", mod.evaluate(getResource(i));

def ppModel(mod):
    print "Ego: ", mod.evaluate(ego);
    for e in mod[Entity]:
        printEntity(mod,e);
        print "";
    if (mod[Intersection]!= None):
        for i in mod[Intersection]:
            printIntersection(mod,i);
            print "";
    for r in mod[Resource]:
        printResource(mod,r);
        print "";
    for m in mod[Message]:
        if(is_true(mod.evaluate(And(sent(m),msgtype(m)==Req)))):
            print_message(mod,m);
            print "";

