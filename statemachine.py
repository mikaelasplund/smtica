from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from environment import *;
from resourceenv import *;
from helpers import *;
from variables import *;
from progress import *;
#*************************************************************
#State machine
#*************************************************************

willEnterTS = Int('willEnterTS');
inInterTS = Int('inInterTS');
defaultTS = Int('defaultTS');
speedDivider = 1;
maxSpeed = 20;
speedSteps= int(speedDivider*maxSpeed);
speeds = [0,0.5,0.55,0.6,0.65,0.7,0.75,0.8,0.85,0.9,0.95,
          1.0,1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,
          2.0,2.2,2.4,2.6,2.8,
          3.0,3.3,3.6,3.9,
          4.0,4.4,4.8,
          5.0,5.5,
          6.0,6.5,
          7.0,7.5,
          8.0,8.5,
          9.0,9.5,
          10,11,12,13,14,15,16,17,18,19];

def egoHasResource(res,s,duration):
    m = req(s);
    t = time(s);
    return And(resource(m) == res,
               source(m) == ego,
               validated(m,t),
               startt(m) <= t,
               endt(m) >= t + duration);


def entityHasResource(res,e,s):
    m = Const('m',Message);
    return Exists(m, And(resource(m) == res,
                         validated(m,time(s)),
                         source(m) == e,
                         time(s) >= startt(m),
                         time(s) <= endt(m)));


def validState(s):
    #Next resource must come after current location, or be the last
    res = nextOrLastResource(s);
    return And(msgtype(req(s)) == Req,
               source(req(s)) == ego,
               );
    

def validLocation(s):
    res = nextOrLastResource(s);
    return And(Implies(loc(s) == farAway, egopos(s) <= resourceStarts(res)-closeDist),
               Implies(loc(s) == close, And(egopos(s) >= resourceStarts(res)-closeDist, 
                                            egopos(s) <= resourceStarts(res))),
               Implies(loc(s) == inInter, And(egopos(s) >= resourceStarts(res), 
                                              egopos(s) <= resourceEnds(res))),
               Implies(loc(s) == passed, egopos(s) >= resourceEnds(res)));

def discretisedSpeed(s):
    return And(Or([(speed(s) == i) for i in speeds]),
               Or([(targetSpeed(s) == i) for i in speeds]));

def allowedMovement(s,sp):
    avgSpeed = (speed(s) + speed(sp))/2;
    upperspeed = avgSpeed+1;
    timeDiff = time(sp)-time(s);
    return If(avgSpeed == 0,
              egopos(sp) == egopos(s),
              If(avgSpeed <= 0.5,
                 And(egopos(sp) >= egopos(s),
                     egopos(sp) <= egopos(s)+avgSpeed*timeDiff*1.1),
                 And(egopos(sp) >= egopos(s)+avgSpeed*timeDiff,
                     egopos(sp) <= egopos(s)+avgSpeed*timeDiff*1.1)));
              
def allowedSpeedChange(s,sp):
    timeDiff = time(sp) - time(s);
    speedChange = targetSpeed(s) - speed(s);
    speedDiff = speed(sp) - speed(s);
    return If(speedChange == 0,
              speed(sp) == speed(s),
              If(targetSpeed(s) < speed(s),
                 If(timeDiff == myAbs(speedChange)/breaking,
                    speed(sp)==targetSpeed(s),
                    And(speed(sp) <= (speed(s)-timeDiff*breaking),
                        speed(sp) >= targetSpeed(s))),
                 If(timeDiff == myAbs(speedChange)/acceleration,
                    speed(sp)==targetSpeed(s),
                    And(speed(sp) >= (speed(s)+timeDiff*acceleration),
                        speed(sp) <= targetSpeed(s)))));
                 

def timePass(s,sp):
    return time(sp) > time(s);

def continuousConsts(s,sp):
    return And(targetSpeed(s) == targetSpeed (sp),
               loc(s) == loc(sp),
               acc(s) == acc(sp),
               req(s) == req(sp),
               willEnter(s) == willEnter(sp));

def reqDiscTransOnCertainTimes(s,sp):
    return And(Or(Not(valid(req(sp))),
                  validationTime(req(sp)) >= time(sp),
                  validationTime(req(sp)) <= time (s)),
               Or(startt(req(sp)) >= time(sp),
                  startt(req(sp)) <= time(s)));

def speedChangeDuration(s,sp):
    return And(Implies(Not(targetSpeed(s) > speed(s)),
                       time(sp) <= time(s) + myAbs(targetspeed(s)-speed(s))/acceleration),
               Implies(Not(targetSpeed(s) < speed(s)),
                       time(sp) <= time(s) + myAbs(targetspeed(s)-speed(s))/breaking));
               

def waiting(s):
    return And(Not(willEnter(s)),
               hasBeenSent(req(s),time(s)),
               loc(s)==close);

def updateLTNW(s,sp):
    return If(waiting(sp),
              ltnw(sp)==ltnw(s),
              ltnw(sp)==time(sp));

def continuousTrans(s,sp):
    return And(
        reqDiscTransOnCertainTimes(s,sp),
        validLocation(sp),
        timePass(s,sp),
        continuousConsts(s,sp),
        allowedSpeedChange(s,sp),
        discretisedSpeed(sp),
        allowedMovement(s,sp),
        validState(sp),
        updateLTNW(s,sp),
        );

def discreteConsts(s,sp):
    return And(time(s) == time(sp),
               speed(s) == speed(sp),
               req(s) == req(sp),
               egopos(s) == egopos(sp)
               );

def willEnterDecision(s,sp):
    res = nextOrLastResource(s);
    t = time(s);
    return If(And(egopos(s) <= resourceStarts(res),
                  egoHasResource(res,s,needResourceInterval)),
              willEnter(sp),
              willEnter(s) == willEnter(sp));

def changeLocationState(s,sp):
    res = nextOrLastResource(s);
    return If(And(egopos(s) >= resourceStarts(res)-closeDist, egopos(s) < resourceStarts(res)),
              loc(sp) == close,
              If(And(egopos(s) >= resourceStarts(res), egopos(s) < resourceEnds(res)),
                 loc(sp) == inInter,
                 If(egopos(s) >= resourceEnds(res),
                    loc(sp) == passed,
                    loc(sp) == farAway)));

def changeTargetSpeed(s,sp):
    return If(loc(sp) == close,
              If(willEnter(sp),
                 targetSpeed(sp) == willEnterTS,
                 targetSpeed(sp) == 0),
              If(loc(sp) == inInter,
                 targetSpeed(sp) == inInterTS,
                 targetSpeed(sp) == defaultTS,
                 ));

def changeAcceleration(s,sp):
    return If(targetSpeed(sp) == speed(sp),
              acc(sp) == const,
              If(targetSpeed(sp) > speed(sp),
                 acc(sp) == incr,
                 acc(sp) == decr));
                    
def somethingChanges(s,sp):
    return Or(loc(s) != loc(sp),
              targetSpeed(s) != targetSpeed(sp),
              req(s) != req(sp),
              acc(s) != acc(sp),
              willEnter(s) != willEnter(sp));


def discreteTrans(s,sp):
    return And(
        changeAcceleration(s,sp),
        discreteConsts(s,sp),
        willEnterDecision(s,sp),
        changeTargetSpeed(s,sp),
        changeLocationState(s,sp),
        progressDecisions(s,sp),
        updateLTNW(s,sp),
        validState(sp),
        );

def T(s,sp):
    return Or(And(continuousTrans(s,sp), 
                  delay(s), 
                  Not(delay(sp))),
              And(discreteTrans(s,sp), 
                  Not(delay(s)), 
                  delay(sp)));

def getInitConstraints(S):
    s = S[0];
    t = time(s);
    m = req(s);
    res = Const('res', Resource);
    init = [And(targetSpeed(S[0]) == defaultTS,
                t == 0,
                speed(s) == defaultTS,
                egopos(s) == resourceStarts(res)-senddist-10,
                Not(hasBeenSent(m,t)),
                ForAll(res,loc(s) == farAway),
                Not(willEnter(s)),
                validState(s),
                ltnw(s) == 0,
                )];
    return init;

def stuck(s): 
    return And(waiting(s),
               time(s)-ltnw(s) > stuckTime);

def notStuck(s):
    return Not(stuck(s));
