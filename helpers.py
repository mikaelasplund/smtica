from z3 import *;
init("libz3.so");

#*************************************************************
#Helper functions
#*************************************************************

def myAbs(a):
    return If(a < 0, -a, a);

def myMin(a,b):
    return If(a < b, a, b);
