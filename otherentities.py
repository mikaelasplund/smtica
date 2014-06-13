from z3 import *;
init("libz3.so");

from basictypes import *;
from communication import *;
from resources import *;
from environment import *;
from resourceenv import *;
from progress import *;
from statemachine import *;
from variables import *;

#*************************************************************
#Restrictions on other entities
#*************************************************************

def getOtherEntitiesConstraints():
    e = Const('e',Entity);
    m = Const('m',Message);
    s = Const('s',SystemState);
    res = Const('res',Resource);
    i = Const('i',Intersection);
    #If another car is in the intersection, it must have the resource
    otherEntities = [];

    otherEntities.append(ForAll([e,i,s], 
                                Or(ego == e,
                                   Not(entityInIntersection(e,i,s)),
                                   entityHasResource(getResource(i),e,s)),
                                patterns = [enteredResource(e,getResource(i),s)]));
    
    return otherEntities;

