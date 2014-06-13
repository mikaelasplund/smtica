from z3 import *;
init("libz3.so");

import math;

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
from prover import *;
from otherentities import *;

from BeautifulSoup import BeautifulSoup
import xml.etree.ElementTree as ET

set_option(warning=False)
set_option(soft_timeout=65000)
set_option(rational_to_decimal=True)
          
defaultParams = [[perfectCommDelay, 0.2],
                 [ackDelay, 0.5],
                 [needResourceInterval, 12],
                 [reservationLength, needResourceInterval],
                 [minTimeFromSend, 2],
                 [maxTimeFromSend, 3],
                 [acceleration, 3],
                 [breaking, 7],
                 [closeDist, 30],
                 [senddist, closeDist],
                 [interSize, 10],
                 [willEnterTS, 10],
                 [inInterTS, 10],
                 [defaultTS, 10],
                 [stuckTime, 5],
                 [conflictOverlap, 1],
                 [beforeResourceMargin, 1]];
consts = []
for p in defaultParams:
    consts.append(p[0] == p[1]);

M = [];

#Populate model with all constraints
M.extend(consts);
M.extend(getCommunicationConstraints());
M.extend(getResourceReservationConstraints());
M.extend(getEnvironmentConstraints());
M.extend(getOtherEntitiesConstraints());
M.extend(getPhysResConstraints());


#<vehicle id="3" pos="7.28" speed="2.18"/>
# <vehicle id="3" pos="11.66" speed="4.38"/>


import xml.etree.ElementTree as ET
tree = ET.parse('movement_data.xml')
root = tree.getroot()
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

vehicles = {};

def checkall():
    f = open('validation-output.txt','w');
    for child in root:
        t = float(child.get('time'));
        for l in child.findall('./edge/lane'):
            lane = l.get('id');
            for v in l.findall('vehicle'):
                id=v.get('id');
                pos = float(v.get('pos'));
                logpoint = {}
                logpoint['vehicle']=id;
                logpoint['time']=t;
                logpoint['pos']=pos;
                logpoint['speed']=float(v.get('speed'));
                logpoint['lane'] = lane;
            vehiclepointlist = vehicles.get(id,[]);
            vehiclepointlist.append(logpoint);
            vehicles[id] = vehiclepointlist;
    #Now go throug all vehicles
    for v,l in vehicles.iteritems():
        while len(l) > 1:
            after = l.pop();
            before = l[-1];
            if before['lane'] != after['lane']:
                continue;
            print v, before['time'];
            xmlspeed = after['speed'];
            if xmlspeed == 0.0:
                nomspeed = 0;
            elif xmlspeed < 0.5:
                nomspeed = 0.5;
            else:
                for i in speeds[::-1]:
                    if xmlspeed > i:
                        nomspeed = i;
                        break;
            s1 = Const('s1', SystemState);
            s2 = Const('s2', SystemState);
            s = Solver();
            s.add(And(M));
            movement = And(time(s1)==before['time'],
                           time(s2)==after['time'],
                           egopos(s1)==before['pos']-1000,
                           egopos(s2)==after['pos']-1000,
                           (speed(s1)+speed(s2))/2==nomspeed);

            
            s.add(movement);
            s.add(T(s1,s2));
            result = s.check();
            if result == unsat:
                f.write("Unsat!\n");
                f.write(str(before));
                f.write(str(after));
                f.write(str(movement));


checkall();
