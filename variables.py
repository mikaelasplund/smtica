from z3 import *;
init("libz3.so");

acceleration = Real('acceleration');
breaking = Real('breaking');
senddist = Real('senddist');
needResourceInterval = Real('needResourceInterval');
stuckTime = Real('stuckTime');
beforeResourceMargin = Real('beforeResourceMargin');
