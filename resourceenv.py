from z3 import *;
init("libz3.so");

from basictypes import *;
from resources import *;
from environment import *;
#*************************************************************
#Interface between resource and physical environment
#*************************************************************

resourceStarts = Function('resourceStarts', Resource, RealSort());
resourceEnds = Function('resourceEnds', Resource, RealSort());
lastResource = Const('lastResource', Resource);
nextOrLastResource = Function('nextOrLastResource', SystemState, Resource);
enteredResource = Function('enteredResource',Entity, Resource, SystemState, BoolSort());

#For every intersection, there is a resource
getResource = Function('getResource', Intersection, Resource);

def egoInResource(res,s):
    return And(egopos(s) >= resourceStarts(res),
               egopos(s) < resourceEnds(res));


def getPhysResConstraints():
    e = Const('e', Entity);
    r = Const('r', Route);
    s = Const('s', SystemState);
    i,ip = Consts('i ip', Intersection);
    res,resp = Consts('res resp', Resource);
    physRes = [];

    # #Resource ends after it starts
    physRes.append(ForAll([res], resourceEnds(res) >= resourceStarts(res),
                          qid = "resourceEndsAfterItStarts"));

    #There are no resources that do not belong to an intersection
    physRes.append(ForAll([res],Exists(i, getResource(i)==res)));

    #last resource is last
    physRes.append(ForAll([res], resourceEnds(res) <= resourceEnds(lastResource),
                          qid="lastResource"));

    physRes.append(ForAll(i,resourceStarts(getResource(i)) == interPos(i) - interSize));
    physRes.append(ForAll(i,resourceEnds(getResource(i)) == (interPos(i) + interSize)));
        
    physRes.append(ForAll(s,Or(nextOrLastResource(s) == lastResource,
                               resourceEnds(nextOrLastResource(s)) >= egopos(s))));

    physRes.append(ForAll([res,s], Or(res == nextOrLastResource(s),
                                      resourceEnds(res) < egopos(s),
                                      resourceStarts(res) > resourceStarts(nextOrLastResource(s)))));

    return physRes;
