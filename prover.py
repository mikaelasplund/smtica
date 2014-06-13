from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from environment import *;
from resourceenv import *;
from progress import *;
from statemachine import *;
from successor import *;
from safety import *;
from printing import *;
from variables import *;
from otherentities import *;
from printing import *;

#*************************************************************
#Check functions
#*************************************************************

def checkModel(M):
    s = Solver();
    s.add(And(M));
    if s.check() == sat:
        return 2;
    elif s.check() == unsat:
        return 0;
    else:
        return 1;

def debugModel(M):
    s = Solver();
    s.add(And(M));
    result = s.check();
    if result == unsat:
        print " Unsat";
        print s.unsat_core();
    elif result == sat:
        print s.model();
    else:
        print " unknown";
        print s.reason_unknown();
        try:
            print s.model()
        except Z3Exception:
            return


def myProver(M,stmt):
    s = Solver();
    s.add(M);
    s.add(Not(stmt));
    result = s.check();
    if result == unsat:
        print " Proved";
    elif result == sat:
        print " Counterexample";
        mod = s.model();
        print mod;
        ppModel(mod);
    else:
        print " unknown, could not prove";
        print s.reason_unknown();
        try:
            print s.model()
        except Z3Exception:
            return

def myProverWithStates(M,stmt,S,s1,s2,showsucc):
    s = Solver();
    s.reset();
    s.add(M);
    s.add(Not(stmt));
    result = s.check();
    if result == unsat:
        print " Proved";
        return 2;
    elif result == sat:
        print " Counterexample";
        ppModel(s.model());
        print_trace(s.model(),S,s1,s2,showsucc);
        return 0;
    else:
        print " unknown, could not prove";
        print s.reason_unknown();
        try:
            print s.model()
            return 1;
        except Z3Exception:
            return 1;


def path(S,n):
    return And([ T(S[i],S[i+1]) for i in range(n) ])

def checkPath(M,S,n,p):
    print "Check that there is a path from 0 to ", n, " where ", p, " is true";
    isPath = Bool('isPath');
    s = Solver();
    s.add(And(M));
    s.add(And(path(S,n)),p(S[n]));
    result = s.check();
    if result == sat:
        print "Found path";
        ppModel(s.model());
        print_trace(s.model(),S,0,n,False);
    elif result == unsat:
        print "No path exists";
    else:
        print "unknown, no path found";
        print s.reason_unknown();

def checkConditionCanHold(M,c):
    s = Solver();
    s.add(And(M));
    s.add(c);
    result = s.check();
    if result == unsat:
        print " Unsat";
        print s.unsat_core();
    elif result == sat:
        print " Sat";
    else:
        print " unknown";
        print s.reason_unknown();
        try:
            print s.model()
        except Z3Exception:
            return

def proveInitialSafe(M,S,k):
    print "Prove that initial", k, "states are safe"
    stmt = Implies(And([T(S[i],S[i+1]) for i in range(k)]),
                       And([inv(S[i]) for i in range(k+1)])
                   );
    return myProverWithStates(M,stmt,S,0,k,False);



def invariantHolds(M,S,k):
    print "Prove system safe"
    result = 2;
    result = min(result,proveInitialSafe(M,S,k));
    systemSafe = Implies(And(And([inv(S[i]) for i in range(1,k+1)]),
                             And([T(S[i],S[i+1]) for i in range(1,k+1)])),
                         stateDistSafe(S[k+1]));
    basicInvs = Implies(And(And([inv(S[i]) for i in range(1,k+1)]),
                             And([T(S[i],S[i+1]) for i in range(1,k+1)])),
                         And(validState(S[k+1]),
                             willEnterCorrect(S[k+1]),
                             discretisedSpeed(S[k+1]),
                             validLocation(S[k+1]),
                             inResHasRes(S[k+1])));
    speedInv = Implies(And(And([inv(S[i]) for i in range(1,k+1)]),
                             And([T(S[i],S[i+1]) for i in range(1,k+1)])),
                         beforeInterSpeed(S[k+1]));                     
    print "safety holds";
    result = min(result,myProverWithStates(M,systemSafe,S,1,k+1,False));
    print "basic invariant";
    result = min(result,myProverWithStates(M,basicInvs,S,1,k+1,False));
    print "speed invariant";
    result = min(result,myProverWithStates(M,speedInv,S,1,k+1,False));
    return result;


def proveX(M,S,X,k):
    stmt = Implies(And(And([inv(S[i]) for i in range(1,k+1)]),
                             And([T(S[i],S[i+1]) for i in range(1,k+1)])),
                         X);
    myProverWithStates(M,stmt,S,1,k+1,False);


def proveInInter(M,S,k):
    print "in inter"
    X = inResHasRes(S[k+1]);
    proveX(M,S,X,k);

def proveStateDist(M,S,k):
    print "statedist"
    X = stateDistSafe(S[k+1]);
    proveX(M,S,X,k);
    

def proveBeforeInter(M,S,k):
    print "before inter"
    X = beforeInterSpeed(S[k+1]);
    proveX(M,S,X,k);



def deadlockFree(M,S):
    print "Prove no deadlock"
    noDeadlock = Implies(And(T(S[1],S[2]),
                             inv(S[1]),
                             inv(S[2]),
                             progressDecisions(S[2],succ(S[2]))
                             ), 
                         T(S[2],succ(S[2])));
    return myProverWithStates(M,noDeadlock,S,1,2,True);
    
    
def willEnterInv(s):
    return  Implies(And(egopos(s) <= resourceStarts(res),
                        validated(req(s),time(s)),
                        startt(req(s)) < time(s)),
                    willEnter(s));
def ltnwOk(s):
    return ltnw(s) <= time(s);

def sentLtnw(s):
    return Implies(hasBeenSent(req(s),time(s)),
                   ltnw(s) >= sendtime(req(s)));

def progressInvariant(s):
    res = nextOrLastResource(s);
    return And(notStuck(s),
               willEnterInv(s),
               ltnwOk(s),
               sentLtnw(s),
               );

def hasProgress(M,S,k):
    print "Prove progress"
    print "First show that the first k steps are not stuck"
    result = 2;
    for j in range(1,k+1):
        print "j = ", j;
        stmt = Implies(And([T(S[i],S[i+1]) for i in range(j)]),
                       And([progressInvariant(S[i]) for i in range(j+1)])
                       );
        result = min(result,myProverWithStates(M,stmt,S,0,j,False));
    stmt = Implies(And(And([progressInvariant(S[i]) for i in range(1,k+1)]),
                       And([inv(S[i]) for i in range(1,k+1)]),
                       And([T(S[i],S[i+1]) for i in range(1,k+1)])),
                   progressInvariant(S[k+1]));
    result = min(result,myProverWithStates(M,stmt,S,1,k+1,False));
    return result;

#*************************************************************
#Resource reservation model checks
#*************************************************************
    
def getEgoCan():
    m = Const('m', Message);
    return Exists(m, And(source(m) == ego,
                         valid(m)));

def getOtherCan():
    m = Const('m', Message);
    return Exists(m, And(source(m) != ego,
                         valid(m)));

def getNoTwoValid():
    t = Const('t', Time);
    e,ep = Consts('e ep', Entity);
    m,mp = Consts('m mp', Message);
    res = Const('res', Resource);
    return ForAll([m,mp], Or(Not(valid(m)),
                             Not(valid(mp)),
                             Not(conflicts(m,mp)),
                             source(m) == source(mp)));
);

def getMutex():
    e,ep = Consts('e ep', Entity);
    s = Const('s', SystemState);
    res = Const('res', Resource);
    return ForAll([e,s,res],Or(e == ego,
                           Not(egoHasResource(res,s,0)),
                           Not(entityHasResource(res,e,s))));
                           

def getInInterInRes():
    s = Const('s', SystemState);
    i = Const('i', Intersection);
    return ForAll([i,s],Or(Not(egoInIntersection(i,s)),
                           egoInResource(getResource(i),s)));


def getMutexImpliesSafe():
    s = Const('s', SystemState);
    return ForAll([s],Or(Not(inResHasRes(s)),
                         stateDistSafe(s)));


def verify(baseModel, progressConstraints, params, S):
    consts = []
    for p in params:
        consts.append(p[0] == p[1]);

    M = [];
    M.extend(baseModel);
    M.extend(consts);

    modelConsistent = checkModel(M);
    dfree = deadlockFree(M,S);
    safe = invariantHolds(M,S,3);
    
    M.extend(progressConstraints);

    progress = hasProgress(M,S,2);    
    return [modelConsistent, dfree, safe, progress];
