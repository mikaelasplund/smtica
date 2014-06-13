from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from environment import *;
from resourceenv import *;
from progress import *;
from statemachine import *;

#*************************************************************
#Successor function
#*************************************************************

def succ(s):
    res = nextOrLastResource(s);
    distanceTimeInc = If(loc(s) == farAway,
                                 (resourceStarts(res)-closeDist - egopos(s)) / 1000,
                                 If(loc(s) == close,
                                    (resourceStarts(res) - egopos(s)) / 1000,
                                    If (loc(s) == inInter,
                                        (resourceEnds(res) - egopos(s)) / 1000,
                                              0.001)));
    validationTimeInc = If(validationTime(req(s)) > time(s),
                           validationTime(req(s))-time(s),
                           0.001);
    starttTimeInc = If(startt(req(s)) > time(s),
                       startt(req(s)) - time(s),
                       0.001);
    nextTimeInc = myMin(validationTimeInc,starttTimeInc);
    smallTimeInc = 0.001;
    newTime = time(s) + myMin(distanceTimeInc,myMin(nextTimeInc,smallTimeInc));
    newSpeed = targetSpeed(s);
    t = time(s);
    newloc = If(And(egopos(s) >= resourceStarts(res)-closeDist, egopos(s) < resourceStarts(res)),
                close,
                If(And(egopos(s) >= resourceStarts(res), egopos(s) < resourceEnds(res)),
                   inInter,
                   If(egopos(s) >= resourceEnds(res),
                      passed,
                      farAway)));
    newWillEnter = If(And(egopos(s) <= resourceStarts(res),
                          egoHasResource(res,s,needResourceInterval)),
                      True,
                      willEnter(s));
    newDiscLTNW = If(And(Not(newWillEnter),
                         newloc == close),
                     ltnw(s),
                     time(s));
    newContLTNW = If(And(Not(willEnter(s)),
                         loc(s) == close),
                     ltnw(s),
                     newTime);
    newTS = If(newloc == close,
               If(newWillEnter, willEnterTS, 0),
               defaultTS);
    newAcc = If(newTS == speed(s),
                const,
                If(newTS > speed(s),
                   incr,
                   decr));
    #Continuous case
    return If(delay(s),
              #Continuous case
              SystemState.mkstate(newTime,
                                  loc(s),
                                  egopos(s)+((speed(s)+newSpeed)/2)*(newTime - time(s)),
                                  newSpeed,
                                  targetSpeed(s),
                                  False,
                                  req(s),
                                  willEnter(s),
                                  newContLTNW,
                                  acc(s),
                                  ),
              #Discrete case
              SystemState.mkstate(time(s),
                                  newloc,
                                  egopos(s),
                                  speed(s),
                                  newTS,
                                  True,
                                  req(s),
                                  newWillEnter,
                                  newDiscLTNW,
                                  newAcc,
                                  ));
