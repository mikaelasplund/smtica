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
from prover import *;
from otherentities import *;

set_option(warning=False)
set_option(soft_timeout=65000)
set_option(rational_to_decimal=True)

def runExperiment(M,progress, defaultParams, varParams, S,f):
    p1 = varParams[0][0];
    p2 = varParams[1][0];
    for i in varParams[0][1]:
        for j in varParams[1][1]:
            params = [];
            params.extend(defaultParams);
            params.append([p1,i]);
            params.append([p2,j]);
            f.write(str(i) + " " + str(j) + " ");
            result =  verify(M,progress, params, S);
            for k in result:
                f.write(str(k) + " ");
            f.write("\n");
            f.flush();
        
           
#*************************************************************
#Breaking vs. closeDist
#*************************************************************

def runBreakinVsCloseDistExperiment():
    defaultParams = [[perfectCommDelay, 0.2],
                     [ackDelay, 0.5],
                     [needResourceInterval, 40],
                     [reservationLength, needResourceInterval],
                     [minTimeFromSend, 2],
                     [maxTimeFromSend, 3],
                     [acceleration, 3],
                     [senddist, closeDist],
                     [interSize, 10],
                     [willEnterTS, 10],
                     [inInterTS, 10],
                     [defaultTS, 10],
                     [stuckTime, 5],
                     [conflictOverlap, 1],
                     [beforeResourceMargin, 1]];
    varParams = [[breaking, [3, 4, 5, 6, 7, 8, 9, 10]],
                 [closeDist, [10, 20, 30, 40, 50, 60, 70]]];
    f = open('result-breaking-closeDist.txt', 'w')
    runExperiment(M,progress, defaultParams, varParams, S,f);
    f.close();

#*************************************************************
#acceleration vs. needsResourceInterval
#*************************************************************

def runAccelerationVsNeedsResourceIntervalExperiment():
    defaultParams = [[perfectCommDelay, 0.2],
                     [ackDelay, 0.5],
                     [reservationLength, needResourceInterval],
                     [minTimeFromSend, 2],
                     [maxTimeFromSend, 3],
                     [breaking, 7],
                     [closeDist, 25],
                     [senddist, closeDist],
                     [interSize, 10],
                     [willEnterTS, 10],
                     [inInterTS, 10],
                     [defaultTS, 10],
                     [stuckTime, 5],
                     [conflictOverlap, 1],
                     [beforeResourceMargin, 1]];
    varParams = [[acceleration, [1, 2, 3, 4, 5, 6, 7]],
                 [needResourceInterval, [4,6,8,10,12,14,16,18,20]]];
    f = open('result-acceleration-resourceInterval.txt', 'w')
    runExperiment(M,progress, defaultParams, varParams, S,f);
    f.close();


#*************************************************************
#ackDelay vs stuckTime
#*************************************************************

def runAckDelayVsStuckTimeExperiment():
    defaultParams = [[perfectCommDelay, 0.2],
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
                     [conflictOverlap, 1],
                     [beforeResourceMargin, 4]];
    varParams = [[ackDelay, [0, 0.5, 1, 1.5, 2, 2.5]],
                 [stuckTime, [1,2,3,4,5]]];
    f = open('result-ackDelay-stuckTime.txt', 'w')
    runExperiment(M,progress, defaultParams, varParams, S,f);
    f.close();

#Create states
S = [ Const(('state%s' % i), SystemState) for i in range(20) ]

M = [];

#Populate model with all constraints
M.extend(getCommunicationConstraints());
M.extend(getResourceReservationConstraints());
M.extend(getEnvironmentConstraints());
M.extend(getOtherEntitiesConstraints());
M.extend(getInitConstraints(S));
M.extend(getPhysResConstraints());

progress = []
progress.extend(perfectCommunication());
progress.extend(getProgressConstraints());


runBreakinVsCloseDistExperiment();
runAccelerationVsNeedsResourceIntervalExperiment();
#runAckDelayVsStuckTimeExperiment();
