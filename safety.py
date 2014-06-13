from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from environment import *;
from resourceenv import *;
from statemachine import *;
#*************************************************************
#Safety properties
#*************************************************************

def stateDistSafe(s):
    e= Const('e', Entity);
    i= Const('i', Intersection);
    return ForAll([e,i], Or(e == ego,
                            Not(entityInIntersection(e,i,s)),
                            Not(egoInIntersection(i,s))));
                            
def inResHasRes(s):
    t = time(s);
    res = nextOrLastResource(s);
    ts = targetSpeed(s);
    pos = egopos(s);
    margin = If(speed(s) > ts, 0, (ts-speed(s))/acceleration);
    restime = (resourceEnds(res)-pos)/ts+margin;
    return Or(Not(egoInResource(res,s)),
              And(egoHasResource(res,s,restime),
                  ts == inInterTS
                  ));

def willEnterCorrect(s):
    t = time(s);
    res = nextOrLastResource(s);
    ts = targetSpeed(s);
    pos = egopos(s);
    margin = If(speed(s) > ts, 0, (ts-speed(s))/acceleration);
    restime = (resourceEnds(res)-pos)/ts+margin;
    return Implies(And(willEnter(s),
                       egopos(s) < resourceEnds(res)),
                   egoHasResource(res,s,restime));

def beforeInterSpeed(s):
    res = nextOrLastResource(s);
    ts = targetSpeed(s);
    return Or(loc(s) != close,
              If(willEnter(s),
                 ts == willEnterTS,
                 speed(s)*speed(s)*1.1 < 2*(resourceStarts(res) - egopos(s)-beforeResourceMargin) * breaking));

def inv(s):
    return And(validState(s),
               stateDistSafe(s),
               willEnterCorrect(s),
               discretisedSpeed(s),
               validLocation(s),
               inResHasRes(s),
               beforeInterSpeed(s),
               );
