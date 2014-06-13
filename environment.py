from z3 import *;
init("libz3.so");

from basictypes import *;
#*************************************************************
#Physical environment
#*************************************************************

#Route = IntSort();
Route = DeclareSort('Route');
route = Function('route', Entity, Route);

#Intersection = IntSort();
Intersection = DeclareSort('Intersection');
otherRoute = Function('otherRoute', Intersection, Route);
interPos = Function('interPos', Intersection, RealSort());
interPosInv = Function('interPosInv', RealSort(), Intersection);
otherInterPos = Function('otherInterPos', Intersection, RealSort());
inter1 = Const('inter1', Intersection);

closeDist = Int('closeDist');
interSize = Int('interSize');

def entityInIntersection(e,i,s):
    return And(route(e) == otherRoute(i),
               pos(e,s) - otherInterPos(i) < interSize,
               pos(e,s) - otherInterPos(i) >= -interSize);

def egoInIntersection(i,s):
    return And((egopos(s) - interPos(i)) < interSize,
               (egopos(s) - interPos(i)) >= -interSize);

def getEnvironmentConstraints():
    i,ip = Consts('i ip', Intersection);
    r = Const('r', Route);
    s = Const('s', SystemState);
    environment = [];

    environment.append(interPos(inter1) == 0);

    environment.append(ForAll([i,ip], i == ip));
    environment.append(ForAll([i], interPos(i)==0));
    
    environment.append(ForAll(i, interPosInv(interPos(i)) == i,
                              patterns=[interPos(i)],
                              qid = "intersectionsDiffer"));

    environment.append(ForAll(i,otherRoute(i) != route(ego),
                              qid="noSelfIntersections"));
    return environment;
